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
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*, uint8_t);
lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
lean_object* l_Lean_Meta_delta_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "step:\n"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__6___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__7_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__2;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__3 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__3_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__4;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___closed__0 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___closed__0_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "whnfReducibleLHS succeeded"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "simpMatch\? succeeded"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "simpIf\? succeeded"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10;
static const lean_array_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__11 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__11_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__14;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__16;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__18;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "simpTargetStar closed the goal"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__22 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__22_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "deltaRHS\? succeeded"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__24 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__24_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "casesOnStuckLHS\? succeeded"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__26 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__26_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "splitTarget\? succeeded"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__28 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__28_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "no progress at goal\n"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__30 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__30_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "simpTargetStar modified the goal"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__32 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__32_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "tryContadiction succeeded"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__34 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__34_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tryURefl succeeded"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__36 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__36_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Structural_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Structural_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Structural_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Structural_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Structural"};
static const lean_object* l_Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "eqnInfoExt"};
static const lean_object* l_Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(14, 221, 148, 2, 30, 47, 242, 74)}};
static const lean_ctor_object l_Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(119, 216, 81, 142, 241, 75, 113, 77)}};
static const lean_object* l_Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PreDefinition"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 172, 242, 185, 134, 214, 81, 182)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(201, 185, 97, 74, 150, 8, 57, 175)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Eqns"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(169, 19, 250, 232, 19, 103, 59, 84)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(236, 64, 85, 238, 73, 235, 224, 238)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(237, 241, 197, 13, 174, 23, 186, 239)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(123, 232, 160, 88, 66, 78, 213, 243)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(141, 117, 235, 94, 194, 72, 147, 153)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(100, 146, 13, 135, 45, 158, 59, 107)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__17_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(109, 222, 70, 43, 201, 77, 119, 184)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__17_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__17_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__17_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 51, 79, 28, 160, 228, 197, 175)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(130, 14, 83, 143, 58, 41, 180, 194)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__20_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(197, 131, 204, 33, 154, 17, 78, 114)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__20_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__20_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__21_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__20_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(51, 169, 96, 182, 175, 131, 16, 69)}};
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
v___x_26_ = lean_apply_7(v_k_18_, v_b_19_, v_c_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, lean_box(0));
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg___lam__0___boxed(lean_object* v_k_27_, lean_object* v_b_28_, lean_object* v_c_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg___lam__0(v_k_27_, v_b_28_, v_c_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_);
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
v___x_106_ = lean_apply_8(v_k_96_, v___x_97_, v_x_98_, v___x_105_, v___y_99_, v___y_100_, v___y_101_, v___y_102_, lean_box(0));
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__2___boxed(lean_object* v___x_107_, lean_object* v_k_108_, lean_object* v___x_109_, lean_object* v_x_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__2(v___x_107_, v_k_108_, v___x_109_, v_x_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__0(lean_object* v_typeName_117_, lean_object* v_idx_118_, lean_object* v_x_119_, lean_object* v_k_120_, lean_object* v_brecOnApp_121_, lean_object* v_x_122_, lean_object* v_c_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_129_ = l_Lean_mkProj(v_typeName_117_, v_idx_118_, v_c_123_);
v___x_130_ = l_Lean_mkAppN(v___x_129_, v_x_119_);
v___x_131_ = lean_apply_8(v_k_120_, v_brecOnApp_121_, v_x_122_, v___x_130_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, lean_box(0));
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__0___boxed(lean_object* v_typeName_132_, lean_object* v_idx_133_, lean_object* v_x_134_, lean_object* v_k_135_, lean_object* v_brecOnApp_136_, lean_object* v_x_137_, lean_object* v_c_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__0(v_typeName_132_, v_idx_133_, v_x_134_, v_k_135_, v_brecOnApp_136_, v_x_137_, v_c_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_);
lean_dec_ref(v_x_134_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg___lam__0(lean_object* v_k_145_, lean_object* v_b_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = lean_apply_6(v_k_145_, v_b_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, lean_box(0));
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v_k_153_, lean_object* v_b_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg___lam__0(v_k_153_, v_b_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
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
lean_inc(v___y_302_);
lean_inc_ref(v___y_301_);
lean_inc(v___y_300_);
lean_inc_ref(v___y_299_);
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
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
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
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
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
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
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
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
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
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___boxed(lean_object* v_e_391_, lean_object* v_k_392_, lean_object* v_x_393_, lean_object* v_x_394_, lean_object* v_x_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg(v_e_391_, v_k_392_, v_x_393_, v_x_394_, v_x_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
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
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___lam__0(lean_object* v___x_506_, uint8_t v___x_507_, lean_object* v_brecOnApp_508_, lean_object* v_x_509_, lean_object* v_c_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
lean_object* v___x_516_; 
lean_inc(v___y_514_);
lean_inc_ref(v___y_513_);
lean_inc(v___y_512_);
lean_inc_ref(v___y_511_);
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
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
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
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
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
uint8_t v___x_687__boxed_559_; lean_object* v_res_560_; 
v___x_687__boxed_559_ = lean_unbox(v___x_550_);
v_res_560_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___lam__0(v___x_549_, v___x_687__boxed_559_, v_brecOnApp_551_, v_x_552_, v_c_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
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
lean_dec(v_a_571_);
lean_dec_ref(v_a_570_);
lean_dec(v_a_569_);
lean_dec_ref(v_a_568_);
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
lean_inc(v___y_655_);
lean_inc_ref(v___y_654_);
lean_inc(v___y_653_);
lean_inc_ref(v___y_652_);
lean_inc(v_mvarId_650_);
v___x_657_ = l_Lean_MVarId_getType_x27(v_mvarId_650_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_726_; 
v_a_658_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_726_ == 0)
{
v___x_660_ = v___x_657_;
v_isShared_661_ = v_isSharedCheck_726_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_657_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_726_;
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
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
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
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
lean_del_object(v___x_660_);
v___x_669_ = l_Lean_Expr_appArg_x21(v_a_658_);
v___x_670_ = l_Lean_Expr_consumeMData(v___x_669_);
lean_dec_ref(v___x_669_);
v___x_671_ = l_Lean_Meta_delta_x3f(v___x_670_, v___f_651_, v___y_654_, v___y_655_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_717_; 
v_a_672_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_717_ == 0)
{
v___x_674_ = v___x_671_;
v_isShared_675_ = v_isSharedCheck_717_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_671_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_717_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
if (lean_obj_tag(v_a_672_) == 1)
{
lean_object* v_val_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_712_; 
lean_del_object(v___x_674_);
v_val_676_ = lean_ctor_get(v_a_672_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v_a_672_);
if (v_isSharedCheck_712_ == 0)
{
v___x_678_ = v_a_672_;
v_isShared_679_ = v_isSharedCheck_712_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_val_676_);
lean_dec(v_a_672_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_712_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_680_ = l_Lean_Expr_appFn_x21(v_a_658_);
lean_dec(v_a_658_);
v___x_681_ = l_Lean_Expr_appArg_x21(v___x_680_);
lean_dec_ref(v___x_680_);
lean_inc(v___y_655_);
lean_inc_ref(v___y_654_);
lean_inc(v___y_653_);
lean_inc_ref(v___y_652_);
v___x_682_ = l_Lean_Meta_mkEq(v___x_681_, v_val_676_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v_a_683_; lean_object* v___x_684_; 
v_a_683_ = lean_ctor_get(v___x_682_, 0);
lean_inc(v_a_683_);
lean_dec_ref(v___x_682_);
v___x_684_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_650_, v_a_683_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_695_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_695_ == 0)
{
v___x_687_ = v___x_684_;
v_isShared_688_ = v_isSharedCheck_695_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_dec(v___x_684_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_695_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_690_; 
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 0, v_a_685_);
v___x_690_ = v___x_678_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_a_685_);
v___x_690_ = v_reuseFailAlloc_694_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
lean_object* v___x_692_; 
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v___x_690_);
v___x_692_ = v___x_687_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_690_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
else
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
lean_del_object(v___x_678_);
v_a_696_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_684_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_684_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
else
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_711_; 
lean_del_object(v___x_678_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v_mvarId_650_);
v_a_704_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_711_ == 0)
{
v___x_706_ = v___x_682_;
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_682_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_709_; 
if (v_isShared_707_ == 0)
{
v___x_709_ = v___x_706_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_a_704_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
}
else
{
lean_object* v___x_713_; lean_object* v___x_715_; 
lean_dec(v_a_672_);
lean_dec(v_a_658_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v_mvarId_650_);
v___x_713_ = lean_box(0);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 0, v___x_713_);
v___x_715_ = v___x_674_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
else
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
lean_dec(v_a_658_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v_mvarId_650_);
v_a_718_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___x_671_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_671_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_718_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
}
}
else
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec_ref(v___f_651_);
lean_dec(v_mvarId_650_);
v_a_727_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___x_657_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_657_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__1___boxed(lean_object* v_mvarId_735_, lean_object* v___f_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__1(v_mvarId_735_, v___f_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(lean_object* v_mvarId_743_, lean_object* v_declName_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_){
_start:
{
lean_object* v___f_750_; lean_object* v___f_751_; lean_object* v___x_752_; 
v___f_750_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_750_, 0, v_declName_744_);
lean_inc(v_mvarId_743_);
v___f_751_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__1___boxed), 7, 2);
lean_closure_set(v___f_751_, 0, v_mvarId_743_);
lean_closure_set(v___f_751_, 1, v___f_750_);
v___x_752_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_743_, v___f_751_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___boxed(lean_object* v_mvarId_753_, lean_object* v_declName_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_753_, v_declName_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(lean_object* v_cls_764_, lean_object* v___y_765_){
_start:
{
lean_object* v_options_767_; uint8_t v_hasTrace_768_; 
v_options_767_ = lean_ctor_get(v___y_765_, 2);
v_hasTrace_768_ = lean_ctor_get_uint8(v_options_767_, sizeof(void*)*1);
if (v_hasTrace_768_ == 0)
{
lean_object* v___x_769_; lean_object* v___x_770_; 
lean_dec(v_cls_764_);
v___x_769_ = lean_box(v_hasTrace_768_);
v___x_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
return v___x_770_;
}
else
{
lean_object* v_inheritedTraceOptions_771_; lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v_inheritedTraceOptions_771_ = lean_ctor_get(v___y_765_, 13);
v___x_772_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___closed__1));
v___x_773_ = l_Lean_Name_append(v___x_772_, v_cls_764_);
v___x_774_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_771_, v_options_767_, v___x_773_);
lean_dec(v___x_773_);
v___x_775_ = lean_box(v___x_774_);
v___x_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
return v___x_776_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___boxed(lean_object* v_cls_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_777_, v___y_778_);
lean_dec_ref(v___y_778_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(lean_object* v_cls_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_781_, v___y_784_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___boxed(lean_object* v_cls_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
return v_res_794_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_795_ = lean_unsigned_to_nat(32u);
v___x_796_ = lean_mk_empty_array_with_capacity(v___x_795_);
v___x_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
return v___x_797_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_798_ = ((size_t)5ULL);
v___x_799_ = lean_unsigned_to_nat(0u);
v___x_800_ = lean_unsigned_to_nat(32u);
v___x_801_ = lean_mk_empty_array_with_capacity(v___x_800_);
v___x_802_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__0);
v___x_803_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_803_, 0, v___x_802_);
lean_ctor_set(v___x_803_, 1, v___x_801_);
lean_ctor_set(v___x_803_, 2, v___x_799_);
lean_ctor_set(v___x_803_, 3, v___x_799_);
lean_ctor_set_usize(v___x_803_, 4, v___x_798_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg(lean_object* v___y_804_){
_start:
{
lean_object* v___x_806_; lean_object* v_traceState_807_; lean_object* v_traces_808_; lean_object* v___x_809_; lean_object* v_traceState_810_; lean_object* v_env_811_; lean_object* v_nextMacroScope_812_; lean_object* v_ngen_813_; lean_object* v_auxDeclNGen_814_; lean_object* v_cache_815_; lean_object* v_messages_816_; lean_object* v_infoState_817_; lean_object* v_snapshotTasks_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_837_; 
v___x_806_ = lean_st_ref_get(v___y_804_);
v_traceState_807_ = lean_ctor_get(v___x_806_, 4);
lean_inc_ref(v_traceState_807_);
lean_dec(v___x_806_);
v_traces_808_ = lean_ctor_get(v_traceState_807_, 0);
lean_inc_ref(v_traces_808_);
lean_dec_ref(v_traceState_807_);
v___x_809_ = lean_st_ref_take(v___y_804_);
v_traceState_810_ = lean_ctor_get(v___x_809_, 4);
v_env_811_ = lean_ctor_get(v___x_809_, 0);
v_nextMacroScope_812_ = lean_ctor_get(v___x_809_, 1);
v_ngen_813_ = lean_ctor_get(v___x_809_, 2);
v_auxDeclNGen_814_ = lean_ctor_get(v___x_809_, 3);
v_cache_815_ = lean_ctor_get(v___x_809_, 5);
v_messages_816_ = lean_ctor_get(v___x_809_, 6);
v_infoState_817_ = lean_ctor_get(v___x_809_, 7);
v_snapshotTasks_818_ = lean_ctor_get(v___x_809_, 8);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_837_ == 0)
{
v___x_820_ = v___x_809_;
v_isShared_821_ = v_isSharedCheck_837_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_snapshotTasks_818_);
lean_inc(v_infoState_817_);
lean_inc(v_messages_816_);
lean_inc(v_cache_815_);
lean_inc(v_traceState_810_);
lean_inc(v_auxDeclNGen_814_);
lean_inc(v_ngen_813_);
lean_inc(v_nextMacroScope_812_);
lean_inc(v_env_811_);
lean_dec(v___x_809_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_837_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
uint64_t v_tid_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_835_; 
v_tid_822_ = lean_ctor_get_uint64(v_traceState_810_, sizeof(void*)*1);
v_isSharedCheck_835_ = !lean_is_exclusive(v_traceState_810_);
if (v_isSharedCheck_835_ == 0)
{
lean_object* v_unused_836_; 
v_unused_836_ = lean_ctor_get(v_traceState_810_, 0);
lean_dec(v_unused_836_);
v___x_824_ = v_traceState_810_;
v_isShared_825_ = v_isSharedCheck_835_;
goto v_resetjp_823_;
}
else
{
lean_dec(v_traceState_810_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_835_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_826_; lean_object* v___x_828_; 
v___x_826_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__1);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v___x_826_);
v___x_828_ = v___x_824_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_826_);
lean_ctor_set_uint64(v_reuseFailAlloc_834_, sizeof(void*)*1, v_tid_822_);
v___x_828_ = v_reuseFailAlloc_834_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
lean_object* v___x_830_; 
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 4, v___x_828_);
v___x_830_ = v___x_820_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_env_811_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v_nextMacroScope_812_);
lean_ctor_set(v_reuseFailAlloc_833_, 2, v_ngen_813_);
lean_ctor_set(v_reuseFailAlloc_833_, 3, v_auxDeclNGen_814_);
lean_ctor_set(v_reuseFailAlloc_833_, 4, v___x_828_);
lean_ctor_set(v_reuseFailAlloc_833_, 5, v_cache_815_);
lean_ctor_set(v_reuseFailAlloc_833_, 6, v_messages_816_);
lean_ctor_set(v_reuseFailAlloc_833_, 7, v_infoState_817_);
lean_ctor_set(v_reuseFailAlloc_833_, 8, v_snapshotTasks_818_);
v___x_830_ = v_reuseFailAlloc_833_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = lean_st_ref_set(v___y_804_, v___x_830_);
v___x_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_832_, 0, v_traces_808_);
return v___x_832_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___boxed(lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg(v___y_838_);
lean_dec(v___y_838_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg(v___y_844_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___boxed(lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v___y_847_, v___y_848_, v___y_849_, v___y_850_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
return v_res_852_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(lean_object* v_opts_853_, lean_object* v_opt_854_){
_start:
{
lean_object* v_name_855_; lean_object* v_defValue_856_; lean_object* v_map_857_; lean_object* v___x_858_; 
v_name_855_ = lean_ctor_get(v_opt_854_, 0);
v_defValue_856_ = lean_ctor_get(v_opt_854_, 1);
v_map_857_ = lean_ctor_get(v_opts_853_, 0);
v___x_858_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_857_, v_name_855_);
if (lean_obj_tag(v___x_858_) == 0)
{
uint8_t v___x_859_; 
v___x_859_ = lean_unbox(v_defValue_856_);
return v___x_859_;
}
else
{
lean_object* v_val_860_; 
v_val_860_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_val_860_);
lean_dec_ref(v___x_858_);
if (lean_obj_tag(v_val_860_) == 1)
{
uint8_t v_v_861_; 
v_v_861_ = lean_ctor_get_uint8(v_val_860_, 0);
lean_dec_ref(v_val_860_);
return v_v_861_;
}
else
{
uint8_t v___x_862_; 
lean_dec(v_val_860_);
v___x_862_ = lean_unbox(v_defValue_856_);
return v___x_862_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___boxed(lean_object* v_opts_863_, lean_object* v_opt_864_){
_start:
{
uint8_t v_res_865_; lean_object* v_r_866_; 
v_res_865_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_opts_863_, v_opt_864_);
lean_dec_ref(v_opt_864_);
lean_dec_ref(v_opts_863_);
v_r_866_ = lean_box(v_res_865_);
return v_r_866_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1(void){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_868_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__0));
v___x_869_ = l_Lean_stringToMessageData(v___x_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0(lean_object* v_mvarId_870_, lean_object* v_x_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_877_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1);
v___x_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_878_, 0, v_mvarId_870_);
v___x_879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_877_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
return v___x_880_;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(lean_object* v_____r_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_895_ = lean_box(0);
v___x_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1___boxed(lean_object* v_____r_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_____r_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__9(lean_object* v_opts_904_, lean_object* v_opt_905_){
_start:
{
lean_object* v_name_906_; lean_object* v_defValue_907_; lean_object* v_map_908_; lean_object* v___x_909_; 
v_name_906_ = lean_ctor_get(v_opt_905_, 0);
v_defValue_907_ = lean_ctor_get(v_opt_905_, 1);
v_map_908_ = lean_ctor_get(v_opts_904_, 0);
v___x_909_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_908_, v_name_906_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_inc(v_defValue_907_);
return v_defValue_907_;
}
else
{
lean_object* v_val_910_; 
v_val_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_val_910_);
lean_dec_ref(v___x_909_);
if (lean_obj_tag(v_val_910_) == 3)
{
lean_object* v_v_911_; 
v_v_911_ = lean_ctor_get(v_val_910_, 0);
lean_inc(v_v_911_);
lean_dec_ref(v_val_910_);
return v_v_911_;
}
else
{
lean_dec(v_val_910_);
lean_inc(v_defValue_907_);
return v_defValue_907_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__9___boxed(lean_object* v_opts_912_, lean_object* v_opt_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__9(v_opts_912_, v_opt_913_);
lean_dec_ref(v_opt_913_);
lean_dec_ref(v_opts_912_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__8___redArg(lean_object* v_x_915_){
_start:
{
if (lean_obj_tag(v_x_915_) == 0)
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
v_a_917_ = lean_ctor_get(v_x_915_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v_x_915_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v_x_915_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v_x_915_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
lean_ctor_set_tag(v___x_919_, 1);
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
v_a_925_ = lean_ctor_get(v_x_915_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v_x_915_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v_x_915_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v_x_915_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
lean_ctor_set_tag(v___x_927_, 0);
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__8___redArg___boxed(lean_object* v_x_933_, lean_object* v___y_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__8___redArg(v_x_933_);
return v_res_935_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__6(lean_object* v_e_936_){
_start:
{
if (lean_obj_tag(v_e_936_) == 0)
{
uint8_t v___x_937_; 
v___x_937_ = 2;
return v___x_937_;
}
else
{
uint8_t v___x_938_; 
v___x_938_ = 0;
return v___x_938_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__6___boxed(lean_object* v_e_939_){
_start:
{
uint8_t v_res_940_; lean_object* v_r_941_; 
v_res_940_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__6(v_e_939_);
lean_dec_ref(v_e_939_);
v_r_941_ = lean_box(v_res_940_);
return v_r_941_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__7_spec__8(size_t v_sz_942_, size_t v_i_943_, lean_object* v_bs_944_){
_start:
{
uint8_t v___x_945_; 
v___x_945_ = lean_usize_dec_lt(v_i_943_, v_sz_942_);
if (v___x_945_ == 0)
{
return v_bs_944_;
}
else
{
lean_object* v_v_946_; lean_object* v_msg_947_; lean_object* v___x_948_; lean_object* v_bs_x27_949_; size_t v___x_950_; size_t v___x_951_; lean_object* v___x_952_; 
v_v_946_ = lean_array_uget_borrowed(v_bs_944_, v_i_943_);
v_msg_947_ = lean_ctor_get(v_v_946_, 1);
lean_inc_ref(v_msg_947_);
v___x_948_ = lean_unsigned_to_nat(0u);
v_bs_x27_949_ = lean_array_uset(v_bs_944_, v_i_943_, v___x_948_);
v___x_950_ = ((size_t)1ULL);
v___x_951_ = lean_usize_add(v_i_943_, v___x_950_);
v___x_952_ = lean_array_uset(v_bs_x27_949_, v_i_943_, v_msg_947_);
v_i_943_ = v___x_951_;
v_bs_944_ = v___x_952_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__7_spec__8___boxed(lean_object* v_sz_954_, lean_object* v_i_955_, lean_object* v_bs_956_){
_start:
{
size_t v_sz_boxed_957_; size_t v_i_boxed_958_; lean_object* v_res_959_; 
v_sz_boxed_957_ = lean_unbox_usize(v_sz_954_);
lean_dec(v_sz_954_);
v_i_boxed_958_ = lean_unbox_usize(v_i_955_);
lean_dec(v_i_955_);
v_res_959_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__7_spec__8(v_sz_boxed_957_, v_i_boxed_958_, v_bs_956_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__7(lean_object* v_oldTraces_960_, lean_object* v_data_961_, lean_object* v_ref_962_, lean_object* v_msg_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v_fileName_969_; lean_object* v_fileMap_970_; lean_object* v_options_971_; lean_object* v_currRecDepth_972_; lean_object* v_maxRecDepth_973_; lean_object* v_ref_974_; lean_object* v_currNamespace_975_; lean_object* v_openDecls_976_; lean_object* v_initHeartbeats_977_; lean_object* v_maxHeartbeats_978_; lean_object* v_quotContext_979_; lean_object* v_currMacroScope_980_; uint8_t v_diag_981_; lean_object* v_cancelTk_x3f_982_; uint8_t v_suppressElabErrors_983_; lean_object* v_inheritedTraceOptions_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_1039_; 
v_fileName_969_ = lean_ctor_get(v___y_966_, 0);
v_fileMap_970_ = lean_ctor_get(v___y_966_, 1);
v_options_971_ = lean_ctor_get(v___y_966_, 2);
v_currRecDepth_972_ = lean_ctor_get(v___y_966_, 3);
v_maxRecDepth_973_ = lean_ctor_get(v___y_966_, 4);
v_ref_974_ = lean_ctor_get(v___y_966_, 5);
v_currNamespace_975_ = lean_ctor_get(v___y_966_, 6);
v_openDecls_976_ = lean_ctor_get(v___y_966_, 7);
v_initHeartbeats_977_ = lean_ctor_get(v___y_966_, 8);
v_maxHeartbeats_978_ = lean_ctor_get(v___y_966_, 9);
v_quotContext_979_ = lean_ctor_get(v___y_966_, 10);
v_currMacroScope_980_ = lean_ctor_get(v___y_966_, 11);
v_diag_981_ = lean_ctor_get_uint8(v___y_966_, sizeof(void*)*14);
v_cancelTk_x3f_982_ = lean_ctor_get(v___y_966_, 12);
v_suppressElabErrors_983_ = lean_ctor_get_uint8(v___y_966_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_984_ = lean_ctor_get(v___y_966_, 13);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___y_966_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_986_ = v___y_966_;
v_isShared_987_ = v_isSharedCheck_1039_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_inheritedTraceOptions_984_);
lean_inc(v_cancelTk_x3f_982_);
lean_inc(v_currMacroScope_980_);
lean_inc(v_quotContext_979_);
lean_inc(v_maxHeartbeats_978_);
lean_inc(v_initHeartbeats_977_);
lean_inc(v_openDecls_976_);
lean_inc(v_currNamespace_975_);
lean_inc(v_ref_974_);
lean_inc(v_maxRecDepth_973_);
lean_inc(v_currRecDepth_972_);
lean_inc(v_options_971_);
lean_inc(v_fileMap_970_);
lean_inc(v_fileName_969_);
lean_dec(v___y_966_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_1039_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_988_; lean_object* v_traceState_989_; lean_object* v_traces_990_; lean_object* v_ref_991_; lean_object* v___x_993_; 
v___x_988_ = lean_st_ref_get(v___y_967_);
v_traceState_989_ = lean_ctor_get(v___x_988_, 4);
lean_inc_ref(v_traceState_989_);
lean_dec(v___x_988_);
v_traces_990_ = lean_ctor_get(v_traceState_989_, 0);
lean_inc_ref(v_traces_990_);
lean_dec_ref(v_traceState_989_);
v_ref_991_ = l_Lean_replaceRef(v_ref_962_, v_ref_974_);
lean_dec(v_ref_974_);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 5, v_ref_991_);
v___x_993_ = v___x_986_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_fileName_969_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v_fileMap_970_);
lean_ctor_set(v_reuseFailAlloc_1038_, 2, v_options_971_);
lean_ctor_set(v_reuseFailAlloc_1038_, 3, v_currRecDepth_972_);
lean_ctor_set(v_reuseFailAlloc_1038_, 4, v_maxRecDepth_973_);
lean_ctor_set(v_reuseFailAlloc_1038_, 5, v_ref_991_);
lean_ctor_set(v_reuseFailAlloc_1038_, 6, v_currNamespace_975_);
lean_ctor_set(v_reuseFailAlloc_1038_, 7, v_openDecls_976_);
lean_ctor_set(v_reuseFailAlloc_1038_, 8, v_initHeartbeats_977_);
lean_ctor_set(v_reuseFailAlloc_1038_, 9, v_maxHeartbeats_978_);
lean_ctor_set(v_reuseFailAlloc_1038_, 10, v_quotContext_979_);
lean_ctor_set(v_reuseFailAlloc_1038_, 11, v_currMacroScope_980_);
lean_ctor_set(v_reuseFailAlloc_1038_, 12, v_cancelTk_x3f_982_);
lean_ctor_set(v_reuseFailAlloc_1038_, 13, v_inheritedTraceOptions_984_);
lean_ctor_set_uint8(v_reuseFailAlloc_1038_, sizeof(void*)*14, v_diag_981_);
lean_ctor_set_uint8(v_reuseFailAlloc_1038_, sizeof(void*)*14 + 1, v_suppressElabErrors_983_);
v___x_993_ = v_reuseFailAlloc_1038_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_994_; size_t v_sz_995_; size_t v___x_996_; lean_object* v___x_997_; lean_object* v_msg_998_; lean_object* v___x_999_; lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1037_; 
v___x_994_ = l_Lean_PersistentArray_toArray___redArg(v_traces_990_);
lean_dec_ref(v_traces_990_);
v_sz_995_ = lean_array_size(v___x_994_);
v___x_996_ = ((size_t)0ULL);
v___x_997_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__7_spec__8(v_sz_995_, v___x_996_, v___x_994_);
v_msg_998_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_998_, 0, v_data_961_);
lean_ctor_set(v_msg_998_, 1, v_msg_963_);
lean_ctor_set(v_msg_998_, 2, v___x_997_);
v___x_999_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(v_msg_998_, v___y_964_, v___y_965_, v___x_993_, v___y_967_);
lean_dec_ref(v___x_993_);
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1002_ = v___x_999_;
v_isShared_1003_ = v_isSharedCheck_1037_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_999_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1037_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1004_; lean_object* v_traceState_1005_; lean_object* v_env_1006_; lean_object* v_nextMacroScope_1007_; lean_object* v_ngen_1008_; lean_object* v_auxDeclNGen_1009_; lean_object* v_cache_1010_; lean_object* v_messages_1011_; lean_object* v_infoState_1012_; lean_object* v_snapshotTasks_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1036_; 
v___x_1004_ = lean_st_ref_take(v___y_967_);
v_traceState_1005_ = lean_ctor_get(v___x_1004_, 4);
v_env_1006_ = lean_ctor_get(v___x_1004_, 0);
v_nextMacroScope_1007_ = lean_ctor_get(v___x_1004_, 1);
v_ngen_1008_ = lean_ctor_get(v___x_1004_, 2);
v_auxDeclNGen_1009_ = lean_ctor_get(v___x_1004_, 3);
v_cache_1010_ = lean_ctor_get(v___x_1004_, 5);
v_messages_1011_ = lean_ctor_get(v___x_1004_, 6);
v_infoState_1012_ = lean_ctor_get(v___x_1004_, 7);
v_snapshotTasks_1013_ = lean_ctor_get(v___x_1004_, 8);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1015_ = v___x_1004_;
v_isShared_1016_ = v_isSharedCheck_1036_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_snapshotTasks_1013_);
lean_inc(v_infoState_1012_);
lean_inc(v_messages_1011_);
lean_inc(v_cache_1010_);
lean_inc(v_traceState_1005_);
lean_inc(v_auxDeclNGen_1009_);
lean_inc(v_ngen_1008_);
lean_inc(v_nextMacroScope_1007_);
lean_inc(v_env_1006_);
lean_dec(v___x_1004_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1036_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
uint64_t v_tid_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1034_; 
v_tid_1017_ = lean_ctor_get_uint64(v_traceState_1005_, sizeof(void*)*1);
v_isSharedCheck_1034_ = !lean_is_exclusive(v_traceState_1005_);
if (v_isSharedCheck_1034_ == 0)
{
lean_object* v_unused_1035_; 
v_unused_1035_ = lean_ctor_get(v_traceState_1005_, 0);
lean_dec(v_unused_1035_);
v___x_1019_ = v_traceState_1005_;
v_isShared_1020_ = v_isSharedCheck_1034_;
goto v_resetjp_1018_;
}
else
{
lean_dec(v_traceState_1005_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1034_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1024_; 
v___x_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1021_, 0, v_ref_962_);
lean_ctor_set(v___x_1021_, 1, v_a_1000_);
v___x_1022_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_960_, v___x_1021_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 0, v___x_1022_);
v___x_1024_ = v___x_1019_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1022_);
lean_ctor_set_uint64(v_reuseFailAlloc_1033_, sizeof(void*)*1, v_tid_1017_);
v___x_1024_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1026_; 
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 4, v___x_1024_);
v___x_1026_ = v___x_1015_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_env_1006_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v_nextMacroScope_1007_);
lean_ctor_set(v_reuseFailAlloc_1032_, 2, v_ngen_1008_);
lean_ctor_set(v_reuseFailAlloc_1032_, 3, v_auxDeclNGen_1009_);
lean_ctor_set(v_reuseFailAlloc_1032_, 4, v___x_1024_);
lean_ctor_set(v_reuseFailAlloc_1032_, 5, v_cache_1010_);
lean_ctor_set(v_reuseFailAlloc_1032_, 6, v_messages_1011_);
lean_ctor_set(v_reuseFailAlloc_1032_, 7, v_infoState_1012_);
lean_ctor_set(v_reuseFailAlloc_1032_, 8, v_snapshotTasks_1013_);
v___x_1026_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1027_ = lean_st_ref_set(v___y_967_, v___x_1026_);
v___x_1028_ = lean_box(0);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 0, v___x_1028_);
v___x_1030_ = v___x_1002_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_1028_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__7___boxed(lean_object* v_oldTraces_1040_, lean_object* v_data_1041_, lean_object* v_ref_1042_, lean_object* v_msg_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__7(v_oldTraces_1040_, v_data_1041_, v_ref_1042_, v_msg_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
lean_dec(v___y_1047_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
return v_res_1049_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__1(void){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__0));
v___x_1052_ = l_Lean_stringToMessageData(v___x_1051_);
return v___x_1052_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__2(void){
_start:
{
lean_object* v___x_1053_; double v___x_1054_; 
v___x_1053_ = lean_unsigned_to_nat(0u);
v___x_1054_ = lean_float_of_nat(v___x_1053_);
return v___x_1054_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__4(void){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__3));
v___x_1057_ = l_Lean_stringToMessageData(v___x_1056_);
return v___x_1057_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__5(void){
_start:
{
lean_object* v___x_1058_; double v___x_1059_; 
v___x_1058_ = lean_unsigned_to_nat(1000u);
v___x_1059_ = lean_float_of_nat(v___x_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6(lean_object* v_cls_1060_, uint8_t v_collapsed_1061_, lean_object* v_tag_1062_, lean_object* v_opts_1063_, uint8_t v_clsEnabled_1064_, lean_object* v_oldTraces_1065_, lean_object* v_msg_1066_, lean_object* v_resStartStop_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v_fst_1073_; lean_object* v_snd_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1164_; 
v_fst_1073_ = lean_ctor_get(v_resStartStop_1067_, 0);
v_snd_1074_ = lean_ctor_get(v_resStartStop_1067_, 1);
v_isSharedCheck_1164_ = !lean_is_exclusive(v_resStartStop_1067_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1076_ = v_resStartStop_1067_;
v_isShared_1077_ = v_isSharedCheck_1164_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_snd_1074_);
lean_inc(v_fst_1073_);
lean_dec(v_resStartStop_1067_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1164_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v_data_1081_; lean_object* v_fst_1084_; lean_object* v_snd_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1163_; 
v_fst_1084_ = lean_ctor_get(v_snd_1074_, 0);
v_snd_1085_ = lean_ctor_get(v_snd_1074_, 1);
v_isSharedCheck_1163_ = !lean_is_exclusive(v_snd_1074_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1087_ = v_snd_1074_;
v_isShared_1088_ = v_isSharedCheck_1163_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_snd_1085_);
lean_inc(v_fst_1084_);
lean_dec(v_snd_1074_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1163_;
goto v_resetjp_1086_;
}
v___jp_1078_:
{
lean_object* v___x_1082_; 
v___x_1082_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__7(v_oldTraces_1065_, v_data_1081_, v___y_1079_, v___y_1080_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
lean_dec(v___y_1071_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v___x_1083_; 
lean_dec_ref(v___x_1082_);
v___x_1083_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__8___redArg(v_fst_1073_);
return v___x_1083_;
}
else
{
lean_dec(v_fst_1073_);
return v___x_1082_;
}
}
v_resetjp_1086_:
{
lean_object* v___x_1089_; uint8_t v___x_1090_; lean_object* v___y_1092_; lean_object* v_a_1093_; uint8_t v___y_1117_; double v___y_1148_; 
v___x_1089_ = l_Lean_trace_profiler;
v___x_1090_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_opts_1063_, v___x_1089_);
if (v___x_1090_ == 0)
{
v___y_1117_ = v___x_1090_;
goto v___jp_1116_;
}
else
{
lean_object* v___x_1153_; uint8_t v___x_1154_; 
v___x_1153_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1154_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_opts_1063_, v___x_1153_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; lean_object* v___x_1156_; double v___x_1157_; double v___x_1158_; double v___x_1159_; 
v___x_1155_ = l_Lean_trace_profiler_threshold;
v___x_1156_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__9(v_opts_1063_, v___x_1155_);
v___x_1157_ = lean_float_of_nat(v___x_1156_);
v___x_1158_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__5);
v___x_1159_ = lean_float_div(v___x_1157_, v___x_1158_);
v___y_1148_ = v___x_1159_;
goto v___jp_1147_;
}
else
{
lean_object* v___x_1160_; lean_object* v___x_1161_; double v___x_1162_; 
v___x_1160_ = l_Lean_trace_profiler_threshold;
v___x_1161_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__9(v_opts_1063_, v___x_1160_);
v___x_1162_ = lean_float_of_nat(v___x_1161_);
v___y_1148_ = v___x_1162_;
goto v___jp_1147_;
}
}
v___jp_1091_:
{
uint8_t v_result_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1099_; 
v_result_1094_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__6(v_fst_1073_);
v___x_1095_ = l_Lean_TraceResult_toEmoji(v_result_1094_);
v___x_1096_ = l_Lean_stringToMessageData(v___x_1095_);
v___x_1097_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__1);
if (v_isShared_1088_ == 0)
{
lean_ctor_set_tag(v___x_1087_, 7);
lean_ctor_set(v___x_1087_, 1, v___x_1097_);
lean_ctor_set(v___x_1087_, 0, v___x_1096_);
v___x_1099_ = v___x_1087_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1096_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v___x_1097_);
v___x_1099_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
lean_object* v_m_1101_; 
if (v_isShared_1077_ == 0)
{
lean_ctor_set_tag(v___x_1076_, 7);
lean_ctor_set(v___x_1076_, 1, v_a_1093_);
lean_ctor_set(v___x_1076_, 0, v___x_1099_);
v_m_1101_ = v___x_1076_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1099_);
lean_ctor_set(v_reuseFailAlloc_1109_, 1, v_a_1093_);
v_m_1101_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; double v___x_1104_; lean_object* v_data_1105_; 
v___x_1102_ = lean_box(v_result_1094_);
v___x_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
v___x_1104_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__2);
lean_inc_ref(v_tag_1062_);
lean_inc_ref(v___x_1103_);
lean_inc(v_cls_1060_);
v_data_1105_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1105_, 0, v_cls_1060_);
lean_ctor_set(v_data_1105_, 1, v___x_1103_);
lean_ctor_set(v_data_1105_, 2, v_tag_1062_);
lean_ctor_set_float(v_data_1105_, sizeof(void*)*3, v___x_1104_);
lean_ctor_set_float(v_data_1105_, sizeof(void*)*3 + 8, v___x_1104_);
lean_ctor_set_uint8(v_data_1105_, sizeof(void*)*3 + 16, v_collapsed_1061_);
if (v___x_1090_ == 0)
{
lean_dec_ref(v___x_1103_);
lean_dec(v_snd_1085_);
lean_dec(v_fst_1084_);
lean_dec_ref(v_tag_1062_);
lean_dec(v_cls_1060_);
v___y_1079_ = v___y_1092_;
v___y_1080_ = v_m_1101_;
v_data_1081_ = v_data_1105_;
goto v___jp_1078_;
}
else
{
lean_object* v_data_1106_; double v___x_1107_; double v___x_1108_; 
lean_dec_ref(v_data_1105_);
v_data_1106_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1106_, 0, v_cls_1060_);
lean_ctor_set(v_data_1106_, 1, v___x_1103_);
lean_ctor_set(v_data_1106_, 2, v_tag_1062_);
v___x_1107_ = lean_unbox_float(v_fst_1084_);
lean_dec(v_fst_1084_);
lean_ctor_set_float(v_data_1106_, sizeof(void*)*3, v___x_1107_);
v___x_1108_ = lean_unbox_float(v_snd_1085_);
lean_dec(v_snd_1085_);
lean_ctor_set_float(v_data_1106_, sizeof(void*)*3 + 8, v___x_1108_);
lean_ctor_set_uint8(v_data_1106_, sizeof(void*)*3 + 16, v_collapsed_1061_);
v___y_1079_ = v___y_1092_;
v___y_1080_ = v_m_1101_;
v_data_1081_ = v_data_1106_;
goto v___jp_1078_;
}
}
}
}
v___jp_1111_:
{
lean_object* v_ref_1112_; lean_object* v___x_1113_; 
v_ref_1112_ = lean_ctor_get(v___y_1070_, 5);
lean_inc(v___y_1071_);
lean_inc_ref(v___y_1070_);
lean_inc(v___y_1069_);
lean_inc_ref(v___y_1068_);
lean_inc(v_fst_1073_);
v___x_1113_ = lean_apply_6(v_msg_1066_, v_fst_1073_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, lean_box(0));
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v_a_1114_; 
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc(v_a_1114_);
lean_dec_ref(v___x_1113_);
lean_inc(v_ref_1112_);
v___y_1092_ = v_ref_1112_;
v_a_1093_ = v_a_1114_;
goto v___jp_1091_;
}
else
{
lean_object* v___x_1115_; 
lean_dec_ref(v___x_1113_);
v___x_1115_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__4);
lean_inc(v_ref_1112_);
v___y_1092_ = v_ref_1112_;
v_a_1093_ = v___x_1115_;
goto v___jp_1091_;
}
}
v___jp_1116_:
{
if (v_clsEnabled_1064_ == 0)
{
if (v___y_1117_ == 0)
{
lean_object* v___x_1118_; lean_object* v_traceState_1119_; lean_object* v_env_1120_; lean_object* v_nextMacroScope_1121_; lean_object* v_ngen_1122_; lean_object* v_auxDeclNGen_1123_; lean_object* v_cache_1124_; lean_object* v_messages_1125_; lean_object* v_infoState_1126_; lean_object* v_snapshotTasks_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1146_; 
lean_del_object(v___x_1087_);
lean_dec(v_snd_1085_);
lean_dec(v_fst_1084_);
lean_del_object(v___x_1076_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec_ref(v_msg_1066_);
lean_dec_ref(v_tag_1062_);
lean_dec(v_cls_1060_);
v___x_1118_ = lean_st_ref_take(v___y_1071_);
v_traceState_1119_ = lean_ctor_get(v___x_1118_, 4);
v_env_1120_ = lean_ctor_get(v___x_1118_, 0);
v_nextMacroScope_1121_ = lean_ctor_get(v___x_1118_, 1);
v_ngen_1122_ = lean_ctor_get(v___x_1118_, 2);
v_auxDeclNGen_1123_ = lean_ctor_get(v___x_1118_, 3);
v_cache_1124_ = lean_ctor_get(v___x_1118_, 5);
v_messages_1125_ = lean_ctor_get(v___x_1118_, 6);
v_infoState_1126_ = lean_ctor_get(v___x_1118_, 7);
v_snapshotTasks_1127_ = lean_ctor_get(v___x_1118_, 8);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1129_ = v___x_1118_;
v_isShared_1130_ = v_isSharedCheck_1146_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_snapshotTasks_1127_);
lean_inc(v_infoState_1126_);
lean_inc(v_messages_1125_);
lean_inc(v_cache_1124_);
lean_inc(v_traceState_1119_);
lean_inc(v_auxDeclNGen_1123_);
lean_inc(v_ngen_1122_);
lean_inc(v_nextMacroScope_1121_);
lean_inc(v_env_1120_);
lean_dec(v___x_1118_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1146_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
uint64_t v_tid_1131_; lean_object* v_traces_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1145_; 
v_tid_1131_ = lean_ctor_get_uint64(v_traceState_1119_, sizeof(void*)*1);
v_traces_1132_ = lean_ctor_get(v_traceState_1119_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v_traceState_1119_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1134_ = v_traceState_1119_;
v_isShared_1135_ = v_isSharedCheck_1145_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_traces_1132_);
lean_dec(v_traceState_1119_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1145_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1136_; lean_object* v___x_1138_; 
v___x_1136_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1065_, v_traces_1132_);
lean_dec_ref(v_traces_1132_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 0, v___x_1136_);
v___x_1138_ = v___x_1134_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1136_);
lean_ctor_set_uint64(v_reuseFailAlloc_1144_, sizeof(void*)*1, v_tid_1131_);
v___x_1138_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
lean_object* v___x_1140_; 
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 4, v___x_1138_);
v___x_1140_ = v___x_1129_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_env_1120_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_nextMacroScope_1121_);
lean_ctor_set(v_reuseFailAlloc_1143_, 2, v_ngen_1122_);
lean_ctor_set(v_reuseFailAlloc_1143_, 3, v_auxDeclNGen_1123_);
lean_ctor_set(v_reuseFailAlloc_1143_, 4, v___x_1138_);
lean_ctor_set(v_reuseFailAlloc_1143_, 5, v_cache_1124_);
lean_ctor_set(v_reuseFailAlloc_1143_, 6, v_messages_1125_);
lean_ctor_set(v_reuseFailAlloc_1143_, 7, v_infoState_1126_);
lean_ctor_set(v_reuseFailAlloc_1143_, 8, v_snapshotTasks_1127_);
v___x_1140_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = lean_st_ref_set(v___y_1071_, v___x_1140_);
lean_dec(v___y_1071_);
v___x_1142_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__8___redArg(v_fst_1073_);
return v___x_1142_;
}
}
}
}
}
else
{
goto v___jp_1111_;
}
}
else
{
goto v___jp_1111_;
}
}
v___jp_1147_:
{
double v___x_1149_; double v___x_1150_; double v___x_1151_; uint8_t v___x_1152_; 
v___x_1149_ = lean_unbox_float(v_snd_1085_);
v___x_1150_ = lean_unbox_float(v_fst_1084_);
v___x_1151_ = lean_float_sub(v___x_1149_, v___x_1150_);
v___x_1152_ = lean_float_decLt(v___y_1148_, v___x_1151_);
v___y_1117_ = v___x_1152_;
goto v___jp_1116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___boxed(lean_object* v_cls_1165_, lean_object* v_collapsed_1166_, lean_object* v_tag_1167_, lean_object* v_opts_1168_, lean_object* v_clsEnabled_1169_, lean_object* v_oldTraces_1170_, lean_object* v_msg_1171_, lean_object* v_resStartStop_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
uint8_t v_collapsed_boxed_1178_; uint8_t v_clsEnabled_boxed_1179_; lean_object* v_res_1180_; 
v_collapsed_boxed_1178_ = lean_unbox(v_collapsed_1166_);
v_clsEnabled_boxed_1179_ = lean_unbox(v_clsEnabled_1169_);
v_res_1180_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6(v_cls_1165_, v_collapsed_boxed_1178_, v_tag_1167_, v_opts_1168_, v_clsEnabled_boxed_1179_, v_oldTraces_1170_, v_msg_1171_, v_resStartStop_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
lean_dec_ref(v_opts_1168_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(lean_object* v_cls_1184_, lean_object* v_msg_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v_ref_1191_; lean_object* v___x_1192_; lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1237_; 
v_ref_1191_ = lean_ctor_get(v___y_1188_, 5);
v___x_1192_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(v_msg_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1195_ = v___x_1192_;
v_isShared_1196_ = v_isSharedCheck_1237_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1192_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1237_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1197_; lean_object* v_traceState_1198_; lean_object* v_env_1199_; lean_object* v_nextMacroScope_1200_; lean_object* v_ngen_1201_; lean_object* v_auxDeclNGen_1202_; lean_object* v_cache_1203_; lean_object* v_messages_1204_; lean_object* v_infoState_1205_; lean_object* v_snapshotTasks_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1236_; 
v___x_1197_ = lean_st_ref_take(v___y_1189_);
v_traceState_1198_ = lean_ctor_get(v___x_1197_, 4);
v_env_1199_ = lean_ctor_get(v___x_1197_, 0);
v_nextMacroScope_1200_ = lean_ctor_get(v___x_1197_, 1);
v_ngen_1201_ = lean_ctor_get(v___x_1197_, 2);
v_auxDeclNGen_1202_ = lean_ctor_get(v___x_1197_, 3);
v_cache_1203_ = lean_ctor_get(v___x_1197_, 5);
v_messages_1204_ = lean_ctor_get(v___x_1197_, 6);
v_infoState_1205_ = lean_ctor_get(v___x_1197_, 7);
v_snapshotTasks_1206_ = lean_ctor_get(v___x_1197_, 8);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1208_ = v___x_1197_;
v_isShared_1209_ = v_isSharedCheck_1236_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_snapshotTasks_1206_);
lean_inc(v_infoState_1205_);
lean_inc(v_messages_1204_);
lean_inc(v_cache_1203_);
lean_inc(v_traceState_1198_);
lean_inc(v_auxDeclNGen_1202_);
lean_inc(v_ngen_1201_);
lean_inc(v_nextMacroScope_1200_);
lean_inc(v_env_1199_);
lean_dec(v___x_1197_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1236_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
uint64_t v_tid_1210_; lean_object* v_traces_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1235_; 
v_tid_1210_ = lean_ctor_get_uint64(v_traceState_1198_, sizeof(void*)*1);
v_traces_1211_ = lean_ctor_get(v_traceState_1198_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v_traceState_1198_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1213_ = v_traceState_1198_;
v_isShared_1214_ = v_isSharedCheck_1235_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_traces_1211_);
lean_dec(v_traceState_1198_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1235_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1215_; double v___x_1216_; uint8_t v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1225_; 
v___x_1215_ = lean_box(0);
v___x_1216_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__2);
v___x_1217_ = 0;
v___x_1218_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___closed__0));
v___x_1219_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1219_, 0, v_cls_1184_);
lean_ctor_set(v___x_1219_, 1, v___x_1215_);
lean_ctor_set(v___x_1219_, 2, v___x_1218_);
lean_ctor_set_float(v___x_1219_, sizeof(void*)*3, v___x_1216_);
lean_ctor_set_float(v___x_1219_, sizeof(void*)*3 + 8, v___x_1216_);
lean_ctor_set_uint8(v___x_1219_, sizeof(void*)*3 + 16, v___x_1217_);
v___x_1220_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___closed__1));
v___x_1221_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1219_);
lean_ctor_set(v___x_1221_, 1, v_a_1193_);
lean_ctor_set(v___x_1221_, 2, v___x_1220_);
lean_inc(v_ref_1191_);
v___x_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1222_, 0, v_ref_1191_);
lean_ctor_set(v___x_1222_, 1, v___x_1221_);
v___x_1223_ = l_Lean_PersistentArray_push___redArg(v_traces_1211_, v___x_1222_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v___x_1223_);
v___x_1225_ = v___x_1213_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1223_);
lean_ctor_set_uint64(v_reuseFailAlloc_1234_, sizeof(void*)*1, v_tid_1210_);
v___x_1225_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v___x_1227_; 
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 4, v___x_1225_);
v___x_1227_ = v___x_1208_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_env_1199_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v_nextMacroScope_1200_);
lean_ctor_set(v_reuseFailAlloc_1233_, 2, v_ngen_1201_);
lean_ctor_set(v_reuseFailAlloc_1233_, 3, v_auxDeclNGen_1202_);
lean_ctor_set(v_reuseFailAlloc_1233_, 4, v___x_1225_);
lean_ctor_set(v_reuseFailAlloc_1233_, 5, v_cache_1203_);
lean_ctor_set(v_reuseFailAlloc_1233_, 6, v_messages_1204_);
lean_ctor_set(v_reuseFailAlloc_1233_, 7, v_infoState_1205_);
lean_ctor_set(v_reuseFailAlloc_1233_, 8, v_snapshotTasks_1206_);
v___x_1227_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1231_; 
v___x_1228_ = lean_st_ref_set(v___y_1189_, v___x_1227_);
v___x_1229_ = lean_box(0);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 0, v___x_1229_);
v___x_1231_ = v___x_1195_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1229_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___boxed(lean_object* v_cls_1238_, lean_object* v_msg_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1238_, v_msg_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
return v_res_1245_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6(void){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5));
v___x_1257_ = l_Lean_stringToMessageData(v___x_1256_);
return v___x_1257_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8(void){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7));
v___x_1260_ = l_Lean_stringToMessageData(v___x_1259_);
return v___x_1260_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10(void){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9));
v___x_1263_ = l_Lean_stringToMessageData(v___x_1262_);
return v___x_1263_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__14(void){
_start:
{
lean_object* v___x_1266_; 
v___x_1266_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1266_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15(void){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1267_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__14, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__14_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__14);
v___x_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1267_);
return v___x_1268_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12(void){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1269_ = lean_box(0);
v___x_1270_ = lean_unsigned_to_nat(16u);
v___x_1271_ = lean_mk_array(v___x_1270_, v___x_1269_);
return v___x_1271_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13(void){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1272_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
v___x_1273_ = lean_unsigned_to_nat(0u);
v___x_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1273_);
lean_ctor_set(v___x_1274_, 1, v___x_1272_);
return v___x_1274_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__16(void){
_start:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; uint8_t v___x_1277_; lean_object* v___x_1278_; 
v___x_1275_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15);
v___x_1276_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13);
v___x_1277_ = 1;
v___x_1278_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1278_, 0, v___x_1276_);
lean_ctor_set(v___x_1278_, 1, v___x_1275_);
lean_ctor_set_uint8(v___x_1278_, sizeof(void*)*2, v___x_1277_);
return v___x_1278_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__18(void){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1279_ = lean_unsigned_to_nat(32u);
v___x_1280_ = lean_mk_empty_array_with_capacity(v___x_1279_);
v___x_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
return v___x_1281_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19(void){
_start:
{
size_t v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1282_ = ((size_t)5ULL);
v___x_1283_ = lean_unsigned_to_nat(0u);
v___x_1284_ = lean_unsigned_to_nat(32u);
v___x_1285_ = lean_mk_empty_array_with_capacity(v___x_1284_);
v___x_1286_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__18, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__18);
v___x_1287_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1287_, 0, v___x_1286_);
lean_ctor_set(v___x_1287_, 1, v___x_1285_);
lean_ctor_set(v___x_1287_, 2, v___x_1283_);
lean_ctor_set(v___x_1287_, 3, v___x_1283_);
lean_ctor_set_usize(v___x_1287_, 4, v___x_1282_);
return v___x_1287_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20(void){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1288_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19);
v___x_1289_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15);
v___x_1290_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1289_);
lean_ctor_set(v___x_1290_, 1, v___x_1289_);
lean_ctor_set(v___x_1290_, 2, v___x_1289_);
lean_ctor_set(v___x_1290_, 3, v___x_1288_);
return v___x_1290_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17(void){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1291_ = lean_unsigned_to_nat(0u);
v___x_1292_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15);
v___x_1293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1292_);
lean_ctor_set(v___x_1293_, 1, v___x_1291_);
return v___x_1293_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21(void){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1294_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20);
v___x_1295_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17);
v___x_1296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1295_);
lean_ctor_set(v___x_1296_, 1, v___x_1294_);
return v___x_1296_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23(void){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__22));
v___x_1299_ = l_Lean_stringToMessageData(v___x_1298_);
return v___x_1299_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25(void){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__24));
v___x_1302_ = l_Lean_stringToMessageData(v___x_1301_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(lean_object* v_declName_1303_, lean_object* v_as_1304_, size_t v_i_1305_, size_t v_stop_1306_, lean_object* v_b_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
uint8_t v___x_1313_; 
v___x_1313_ = lean_usize_dec_eq(v_i_1305_, v_stop_1306_);
if (v___x_1313_ == 0)
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = lean_array_uget_borrowed(v_as_1304_, v_i_1305_);
lean_inc(v___y_1311_);
lean_inc_ref(v___y_1310_);
lean_inc(v___y_1309_);
lean_inc_ref(v___y_1308_);
lean_inc(v___x_1314_);
lean_inc(v_declName_1303_);
v___x_1315_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1303_, v___x_1314_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1316_; size_t v___x_1317_; size_t v___x_1318_; 
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_a_1316_);
lean_dec_ref(v___x_1315_);
v___x_1317_ = ((size_t)1ULL);
v___x_1318_ = lean_usize_add(v_i_1305_, v___x_1317_);
v_i_1305_ = v___x_1318_;
v_b_1307_ = v_a_1316_;
goto _start;
}
else
{
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v_declName_1303_);
return v___x_1315_;
}
}
else
{
lean_object* v___x_1320_; 
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v_declName_1303_);
v___x_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1320_, 0, v_b_1307_);
return v___x_1320_;
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27(void){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1322_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__26));
v___x_1323_ = l_Lean_stringToMessageData(v___x_1322_);
return v___x_1323_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29(void){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1325_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__28));
v___x_1326_ = l_Lean_stringToMessageData(v___x_1325_);
return v___x_1326_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31(void){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__30));
v___x_1329_ = l_Lean_stringToMessageData(v___x_1328_);
return v___x_1329_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33(void){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1331_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__32));
v___x_1332_ = l_Lean_stringToMessageData(v___x_1331_);
return v___x_1332_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35(void){
_start:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__34));
v___x_1335_ = l_Lean_stringToMessageData(v___x_1334_);
return v___x_1335_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37(void){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1337_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__36));
v___x_1338_ = l_Lean_stringToMessageData(v___x_1337_);
return v___x_1338_;
}
}
static double _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38(void){
_start:
{
lean_object* v___x_1339_; double v___x_1340_; 
v___x_1339_ = lean_unsigned_to_nat(1000000000u);
v___x_1340_ = lean_float_of_nat(v___x_1339_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(lean_object* v_val_1341_, lean_object* v___x_1342_, lean_object* v_declName_1343_, lean_object* v_____r_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; 
v___x_1350_ = lean_array_get_size(v_val_1341_);
v___x_1351_ = lean_box(0);
v___x_1352_ = lean_nat_dec_lt(v___x_1342_, v___x_1350_);
if (v___x_1352_ == 0)
{
lean_object* v___x_1353_; 
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec(v_declName_1343_);
v___x_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1351_);
return v___x_1353_;
}
else
{
uint8_t v___x_1354_; 
v___x_1354_ = lean_nat_dec_le(v___x_1350_, v___x_1350_);
if (v___x_1354_ == 0)
{
if (v___x_1352_ == 0)
{
lean_object* v___x_1355_; 
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec(v_declName_1343_);
v___x_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1351_);
return v___x_1355_;
}
else
{
size_t v___x_1356_; size_t v___x_1357_; lean_object* v___x_1358_; 
v___x_1356_ = ((size_t)0ULL);
v___x_1357_ = lean_usize_of_nat(v___x_1350_);
v___x_1358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1343_, v_val_1341_, v___x_1356_, v___x_1357_, v___x_1351_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
return v___x_1358_;
}
}
else
{
size_t v___x_1359_; size_t v___x_1360_; lean_object* v___x_1361_; 
v___x_1359_ = ((size_t)0ULL);
v___x_1360_ = lean_usize_of_nat(v___x_1350_);
v___x_1361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1343_, v_val_1341_, v___x_1359_, v___x_1360_, v___x_1351_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
return v___x_1361_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(lean_object* v_declName_1362_, lean_object* v_mvarId_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_){
_start:
{
lean_object* v_options_1381_; uint8_t v_hasTrace_1382_; lean_object* v_cls_1383_; 
v_options_1381_ = lean_ctor_get(v_a_1366_, 2);
v_hasTrace_1382_ = lean_ctor_get_uint8(v_options_1381_, sizeof(void*)*1);
v_cls_1383_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4));
if (v_hasTrace_1382_ == 0)
{
lean_object* v___x_1384_; 
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_mvarId_1363_);
v___x_1384_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; uint8_t v___x_1386_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1385_);
lean_dec_ref(v___x_1384_);
v___x_1386_ = lean_unbox(v_a_1385_);
lean_dec(v_a_1385_);
if (v___x_1386_ == 0)
{
lean_object* v___x_1387_; 
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_mvarId_1363_);
v___x_1387_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v_a_1388_; uint8_t v___x_1389_; 
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
lean_inc(v_a_1388_);
lean_dec_ref(v___x_1387_);
v___x_1389_ = lean_unbox(v_a_1388_);
lean_dec(v_a_1388_);
if (v___x_1389_ == 0)
{
lean_object* v___x_1390_; 
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_mvarId_1363_);
v___x_1390_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_a_1391_; 
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_a_1391_);
lean_dec_ref(v___x_1390_);
if (lean_obj_tag(v_a_1391_) == 1)
{
lean_object* v_val_1392_; lean_object* v___x_1393_; 
lean_dec(v_mvarId_1363_);
v_val_1392_ = lean_ctor_get(v_a_1391_, 0);
lean_inc(v_val_1392_);
lean_dec_ref(v_a_1391_);
v___x_1393_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; uint8_t v___x_1395_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1394_);
lean_dec_ref(v___x_1393_);
v___x_1395_ = lean_unbox(v_a_1394_);
lean_dec(v_a_1394_);
if (v___x_1395_ == 0)
{
v_mvarId_1363_ = v_val_1392_;
goto _start;
}
else
{
lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1397_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6);
v___x_1398_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_1397_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_dec_ref(v___x_1398_);
v_mvarId_1363_ = v_val_1392_;
goto _start;
}
else
{
lean_dec(v_val_1392_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_declName_1362_);
return v___x_1398_;
}
}
}
else
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
lean_dec(v_val_1392_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_declName_1362_);
v_a_1400_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v___x_1393_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1393_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1400_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
else
{
lean_object* v___x_1408_; 
lean_dec(v_a_1391_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_mvarId_1363_);
v___x_1408_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1408_) == 0)
{
lean_object* v_a_1409_; 
v_a_1409_ = lean_ctor_get(v___x_1408_, 0);
lean_inc(v_a_1409_);
lean_dec_ref(v___x_1408_);
if (lean_obj_tag(v_a_1409_) == 1)
{
lean_object* v_val_1410_; lean_object* v___x_1411_; 
lean_dec(v_mvarId_1363_);
v_val_1410_ = lean_ctor_get(v_a_1409_, 0);
lean_inc(v_val_1410_);
lean_dec_ref(v_a_1409_);
v___x_1411_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1412_; uint8_t v___x_1413_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_a_1412_);
lean_dec_ref(v___x_1411_);
v___x_1413_ = lean_unbox(v_a_1412_);
lean_dec(v_a_1412_);
if (v___x_1413_ == 0)
{
v_mvarId_1363_ = v_val_1410_;
goto _start;
}
else
{
lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1415_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1416_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_1415_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_dec_ref(v___x_1416_);
v_mvarId_1363_ = v_val_1410_;
goto _start;
}
else
{
lean_dec(v_val_1410_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_declName_1362_);
return v___x_1416_;
}
}
}
else
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
lean_dec(v_val_1410_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_declName_1362_);
v_a_1418_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1420_ = v___x_1411_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1411_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1418_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
else
{
uint8_t v___x_1426_; lean_object* v___x_1427_; 
lean_dec(v_a_1409_);
v___x_1426_ = 1;
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_mvarId_1363_);
v___x_1427_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1363_, v___x_1426_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
lean_inc(v_a_1428_);
lean_dec_ref(v___x_1427_);
if (lean_obj_tag(v_a_1428_) == 1)
{
lean_object* v_val_1429_; lean_object* v___x_1430_; 
lean_dec(v_mvarId_1363_);
v_val_1429_ = lean_ctor_get(v_a_1428_, 0);
lean_inc(v_val_1429_);
lean_dec_ref(v_a_1428_);
v___x_1430_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; uint8_t v___x_1432_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
lean_dec_ref(v___x_1430_);
v___x_1432_ = lean_unbox(v_a_1431_);
lean_dec(v_a_1431_);
if (v___x_1432_ == 0)
{
v_mvarId_1363_ = v_val_1429_;
goto _start;
}
else
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
v___x_1435_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_1434_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_dec_ref(v___x_1435_);
v_mvarId_1363_ = v_val_1429_;
goto _start;
}
else
{
lean_dec(v_val_1429_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_declName_1362_);
return v___x_1435_;
}
}
}
else
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
lean_dec(v_val_1429_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_declName_1362_);
v_a_1437_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1439_ = v___x_1430_;
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1430_);
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
lean_object* v___x_1445_; lean_object* v___x_1446_; uint8_t v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
lean_dec(v_a_1428_);
v___x_1445_ = lean_unsigned_to_nat(100000u);
v___x_1446_ = lean_unsigned_to_nat(2u);
v___x_1447_ = 0;
v___x_1448_ = lean_box(0);
v___x_1449_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1449_, 0, v___x_1445_);
lean_ctor_set(v___x_1449_, 1, v___x_1446_);
lean_ctor_set(v___x_1449_, 2, v___x_1448_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*3, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*3 + 1, v___x_1426_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*3 + 2, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*3 + 3, v___x_1426_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*3 + 4, v___x_1426_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*3 + 5, v___x_1426_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*3 + 6, v___x_1447_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*3 + 7, v___x_1426_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*3 + 8, v___x_1426_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*3 + 9, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*3 + 10, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*3 + 11, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*3 + 12, v___x_1426_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*3 + 13, v___x_1426_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*3 + 14, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*3 + 15, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*3 + 16, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*3 + 17, v___x_1426_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*3 + 18, v___x_1426_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*3 + 19, v___x_1426_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*3 + 20, v___x_1426_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*3 + 21, v___x_1426_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*3 + 22, v___x_1426_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*3 + 23, v___x_1426_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*3 + 24, v___x_1426_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*3 + 25, v___x_1426_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*3 + 26, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*3 + 27, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*3 + 28, v_hasTrace_1382_);
v___x_1450_ = lean_unsigned_to_nat(0u);
v___x_1451_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__11));
v___x_1452_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__16, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__16_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__16);
v___x_1453_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1449_, v___x_1451_, v___x_1452_, v_a_1364_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v_a_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
lean_inc(v_a_1454_);
lean_dec_ref(v___x_1453_);
v___x_1455_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_mvarId_1363_);
v___x_1456_ = l_Lean_Meta_simpTargetStar(v_mvarId_1363_, v_a_1454_, v___x_1451_, v___x_1448_, v___x_1455_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; lean_object* v_fst_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1606_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_a_1457_);
lean_dec_ref(v___x_1456_);
v_fst_1458_ = lean_ctor_get(v_a_1457_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v_a_1457_);
if (v_isSharedCheck_1606_ == 0)
{
lean_object* v_unused_1607_; 
v_unused_1607_ = lean_ctor_get(v_a_1457_, 1);
lean_dec(v_unused_1607_);
v___x_1460_ = v_a_1457_;
v_isShared_1461_ = v_isSharedCheck_1606_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_fst_1458_);
lean_dec(v_a_1457_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1606_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
switch(lean_obj_tag(v_fst_1458_))
{
case 0:
{
lean_object* v___x_1462_; 
lean_del_object(v___x_1460_);
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v___x_1462_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1474_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1465_ = v___x_1462_;
v_isShared_1466_ = v_isSharedCheck_1474_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1462_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1474_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
uint8_t v___x_1467_; 
v___x_1467_ = lean_unbox(v_a_1463_);
lean_dec(v_a_1463_);
if (v___x_1467_ == 0)
{
lean_object* v___x_1468_; lean_object* v___x_1470_; 
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
v___x_1468_ = lean_box(0);
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 0, v___x_1468_);
v___x_1470_ = v___x_1465_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___x_1468_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
else
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
lean_del_object(v___x_1465_);
v___x_1472_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23);
v___x_1473_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_1472_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
return v___x_1473_;
}
}
}
else
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1482_; 
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
v_a_1475_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1477_ = v___x_1462_;
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1462_);
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
case 1:
{
lean_object* v___x_1483_; 
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_declName_1362_);
lean_inc(v_mvarId_1363_);
v___x_1483_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1363_, v_declName_1362_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; 
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_a_1484_);
lean_dec_ref(v___x_1483_);
if (lean_obj_tag(v_a_1484_) == 1)
{
lean_object* v_val_1485_; lean_object* v___x_1486_; 
lean_del_object(v___x_1460_);
lean_dec(v_mvarId_1363_);
v_val_1485_ = lean_ctor_get(v_a_1484_, 0);
lean_inc(v_val_1485_);
lean_dec_ref(v_a_1484_);
v___x_1486_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_a_1487_; uint8_t v___x_1488_; 
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
lean_inc(v_a_1487_);
lean_dec_ref(v___x_1486_);
v___x_1488_ = lean_unbox(v_a_1487_);
lean_dec(v_a_1487_);
if (v___x_1488_ == 0)
{
v_mvarId_1363_ = v_val_1485_;
goto _start;
}
else
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1490_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25);
v___x_1491_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_1490_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_dec_ref(v___x_1491_);
v_mvarId_1363_ = v_val_1485_;
goto _start;
}
else
{
lean_dec(v_val_1485_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_declName_1362_);
return v___x_1491_;
}
}
}
else
{
lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1500_; 
lean_dec(v_val_1485_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_declName_1362_);
v_a_1493_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1495_ = v___x_1486_;
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_dec(v___x_1486_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1498_; 
if (v_isShared_1496_ == 0)
{
v___x_1498_ = v___x_1495_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_a_1493_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
}
else
{
lean_object* v___x_1501_; 
lean_dec(v_a_1484_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_mvarId_1363_);
v___x_1501_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1573_; 
v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1504_ = v___x_1501_;
v_isShared_1505_ = v_isSharedCheck_1573_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1501_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1573_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
if (lean_obj_tag(v_a_1502_) == 1)
{
lean_object* v_val_1506_; lean_object* v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v___x_1528_; 
lean_del_object(v___x_1460_);
lean_dec(v_mvarId_1363_);
v_val_1506_ = lean_ctor_get(v_a_1502_, 0);
lean_inc(v_val_1506_);
lean_dec_ref(v_a_1502_);
v___x_1528_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; uint8_t v___x_1530_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_a_1529_);
lean_dec_ref(v___x_1528_);
v___x_1530_ = lean_unbox(v_a_1529_);
lean_dec(v_a_1529_);
if (v___x_1530_ == 0)
{
v___y_1508_ = v_a_1364_;
v___y_1509_ = v_a_1365_;
v___y_1510_ = v_a_1366_;
v___y_1511_ = v_a_1367_;
goto v___jp_1507_;
}
else
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1531_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27);
v___x_1532_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_1531_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_dec_ref(v___x_1532_);
v___y_1508_ = v_a_1364_;
v___y_1509_ = v_a_1365_;
v___y_1510_ = v_a_1366_;
v___y_1511_ = v_a_1367_;
goto v___jp_1507_;
}
else
{
lean_dec(v_val_1506_);
lean_del_object(v___x_1504_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_declName_1362_);
return v___x_1532_;
}
}
}
else
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1540_; 
lean_dec(v_val_1506_);
lean_del_object(v___x_1504_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_declName_1362_);
v_a_1533_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1535_ = v___x_1528_;
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1528_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1538_; 
if (v_isShared_1536_ == 0)
{
v___x_1538_ = v___x_1535_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_a_1533_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
v___jp_1507_:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; uint8_t v___x_1514_; 
v___x_1512_ = lean_array_get_size(v_val_1506_);
v___x_1513_ = lean_box(0);
v___x_1514_ = lean_nat_dec_lt(v___x_1450_, v___x_1512_);
if (v___x_1514_ == 0)
{
lean_object* v___x_1516_; 
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec(v_val_1506_);
lean_dec(v_declName_1362_);
if (v_isShared_1505_ == 0)
{
lean_ctor_set(v___x_1504_, 0, v___x_1513_);
v___x_1516_ = v___x_1504_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1513_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
else
{
uint8_t v___x_1518_; 
v___x_1518_ = lean_nat_dec_le(v___x_1512_, v___x_1512_);
if (v___x_1518_ == 0)
{
if (v___x_1514_ == 0)
{
lean_object* v___x_1520_; 
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec(v_val_1506_);
lean_dec(v_declName_1362_);
if (v_isShared_1505_ == 0)
{
lean_ctor_set(v___x_1504_, 0, v___x_1513_);
v___x_1520_ = v___x_1504_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1513_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
else
{
size_t v___x_1522_; size_t v___x_1523_; lean_object* v___x_1524_; 
lean_del_object(v___x_1504_);
v___x_1522_ = ((size_t)0ULL);
v___x_1523_ = lean_usize_of_nat(v___x_1512_);
v___x_1524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1362_, v_val_1506_, v___x_1522_, v___x_1523_, v___x_1513_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
lean_dec(v_val_1506_);
return v___x_1524_;
}
}
else
{
size_t v___x_1525_; size_t v___x_1526_; lean_object* v___x_1527_; 
lean_del_object(v___x_1504_);
v___x_1525_ = ((size_t)0ULL);
v___x_1526_ = lean_usize_of_nat(v___x_1512_);
v___x_1527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1362_, v_val_1506_, v___x_1525_, v___x_1526_, v___x_1513_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
lean_dec(v_val_1506_);
return v___x_1527_;
}
}
}
}
else
{
lean_object* v___x_1541_; 
lean_del_object(v___x_1504_);
lean_dec(v_a_1502_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_mvarId_1363_);
v___x_1541_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1363_, v___x_1426_, v___x_1426_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1542_);
lean_dec_ref(v___x_1541_);
if (lean_obj_tag(v_a_1542_) == 1)
{
lean_object* v_val_1543_; lean_object* v___x_1544_; 
lean_del_object(v___x_1460_);
lean_dec(v_mvarId_1363_);
v_val_1543_ = lean_ctor_get(v_a_1542_, 0);
lean_inc(v_val_1543_);
lean_dec_ref(v_a_1542_);
v___x_1544_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; uint8_t v___x_1546_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1545_);
lean_dec_ref(v___x_1544_);
v___x_1546_ = lean_unbox(v_a_1545_);
lean_dec(v_a_1545_);
if (v___x_1546_ == 0)
{
lean_object* v___x_1547_; 
v___x_1547_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_declName_1362_, v_val_1543_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
return v___x_1547_;
}
else
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29);
v___x_1549_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_1548_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v___x_1550_; 
lean_dec_ref(v___x_1549_);
v___x_1550_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_declName_1362_, v_val_1543_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
return v___x_1550_;
}
else
{
lean_dec(v_val_1543_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_declName_1362_);
return v___x_1549_;
}
}
}
else
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1558_; 
lean_dec(v_val_1543_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_declName_1362_);
v_a_1551_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1553_ = v___x_1544_;
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1544_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1556_; 
if (v_isShared_1554_ == 0)
{
v___x_1556_ = v___x_1553_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1551_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
}
else
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1562_; 
lean_dec(v_a_1542_);
lean_dec(v_declName_1362_);
v___x_1559_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31);
v___x_1560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1560_, 0, v_mvarId_1363_);
if (v_isShared_1461_ == 0)
{
lean_ctor_set_tag(v___x_1460_, 7);
lean_ctor_set(v___x_1460_, 1, v___x_1560_);
lean_ctor_set(v___x_1460_, 0, v___x_1559_);
v___x_1562_ = v___x_1460_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v___x_1559_);
lean_ctor_set(v_reuseFailAlloc_1564_, 1, v___x_1560_);
v___x_1562_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
lean_object* v___x_1563_; 
v___x_1563_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1562_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
return v___x_1563_;
}
}
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
lean_del_object(v___x_1460_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_1565_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v___x_1541_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1541_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1570_; 
if (v_isShared_1568_ == 0)
{
v___x_1570_ = v___x_1567_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1565_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
}
}
else
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
lean_del_object(v___x_1460_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_1574_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1501_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1501_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_del_object(v___x_1460_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_1582_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1483_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1483_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
default: 
{
lean_object* v_mvarId_1590_; lean_object* v___x_1591_; 
lean_del_object(v___x_1460_);
lean_dec(v_mvarId_1363_);
v_mvarId_1590_ = lean_ctor_get(v_fst_1458_, 0);
lean_inc(v_mvarId_1590_);
lean_dec_ref(v_fst_1458_);
v___x_1591_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v_a_1592_; uint8_t v___x_1593_; 
v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_a_1592_);
lean_dec_ref(v___x_1591_);
v___x_1593_ = lean_unbox(v_a_1592_);
lean_dec(v_a_1592_);
if (v___x_1593_ == 0)
{
v_mvarId_1363_ = v_mvarId_1590_;
goto _start;
}
else
{
lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1595_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33);
v___x_1596_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_1595_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_dec_ref(v___x_1596_);
v_mvarId_1363_ = v_mvarId_1590_;
goto _start;
}
else
{
lean_dec(v_mvarId_1590_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_declName_1362_);
return v___x_1596_;
}
}
}
else
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
lean_dec(v_mvarId_1590_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_declName_1362_);
v_a_1598_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1600_ = v___x_1591_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1591_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1598_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1615_; 
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_1608_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1610_ = v___x_1456_;
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1456_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1613_; 
if (v_isShared_1611_ == 0)
{
v___x_1613_ = v___x_1610_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_a_1608_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
else
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_1616_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1618_ = v___x_1453_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1453_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1616_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
}
else
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_1624_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1626_ = v___x_1427_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1427_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_1632_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1408_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1408_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
}
else
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_1640_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1642_ = v___x_1390_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1390_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1645_; 
if (v_isShared_1643_ == 0)
{
v___x_1645_ = v___x_1642_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_a_1640_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
else
{
lean_object* v___x_1648_; 
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v___x_1648_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; uint8_t v___x_1650_; 
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_a_1649_);
lean_dec_ref(v___x_1648_);
v___x_1650_ = lean_unbox(v_a_1649_);
lean_dec(v_a_1649_);
if (v___x_1650_ == 0)
{
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
goto v___jp_1375_;
}
else
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35);
v___x_1652_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_1651_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_dec_ref(v___x_1652_);
goto v___jp_1375_;
}
else
{
return v___x_1652_;
}
}
}
else
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
v_a_1653_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1648_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1648_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1653_);
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
else
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_1661_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1387_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1387_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
else
{
lean_object* v___x_1669_; 
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v___x_1669_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v_a_1670_; uint8_t v___x_1671_; 
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
lean_inc(v_a_1670_);
lean_dec_ref(v___x_1669_);
v___x_1671_ = lean_unbox(v_a_1670_);
lean_dec(v_a_1670_);
if (v___x_1671_ == 0)
{
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
goto v___jp_1378_;
}
else
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1672_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37);
v___x_1673_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_1672_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_dec_ref(v___x_1673_);
goto v___jp_1378_;
}
else
{
return v___x_1673_;
}
}
}
else
{
lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1681_; 
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
v_a_1674_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1676_ = v___x_1669_;
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1669_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1677_ == 0)
{
v___x_1679_ = v___x_1676_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_a_1674_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
}
}
else
{
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_1682_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v___x_1384_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1384_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1682_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
else
{
lean_object* v___x_1690_; 
v___x_1690_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; lean_object* v___f_1692_; lean_object* v___x_1693_; lean_object* v___y_1695_; lean_object* v___y_1696_; lean_object* v_a_1697_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v_a_1710_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v_a_1715_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v_a_1726_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v_a_1742_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v_a_1747_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; uint8_t v___x_2087_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
lean_inc(v_a_1691_);
lean_dec_ref(v___x_1690_);
lean_inc(v_mvarId_1363_);
v___f_1692_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1692_, 0, v_mvarId_1363_);
v___x_1693_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___closed__0));
v___x_2087_ = lean_unbox(v_a_1691_);
if (v___x_2087_ == 0)
{
lean_object* v___x_2088_; uint8_t v___x_2089_; 
v___x_2088_ = l_Lean_trace_profiler;
v___x_2089_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_options_1381_, v___x_2088_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; 
lean_dec_ref(v___f_1692_);
lean_dec(v_a_1691_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_mvarId_1363_);
v___x_2090_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; uint8_t v___x_2092_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_a_2091_);
lean_dec_ref(v___x_2090_);
v___x_2092_ = lean_unbox(v_a_2091_);
lean_dec(v_a_2091_);
if (v___x_2092_ == 0)
{
lean_object* v___x_2093_; 
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_mvarId_1363_);
v___x_2093_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_a_2094_; uint8_t v___x_2095_; 
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
lean_inc(v_a_2094_);
lean_dec_ref(v___x_2093_);
v___x_2095_ = lean_unbox(v_a_2094_);
lean_dec(v_a_2094_);
if (v___x_2095_ == 0)
{
lean_object* v___x_2096_; 
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_mvarId_1363_);
v___x_2096_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_a_2097_);
lean_dec_ref(v___x_2096_);
if (lean_obj_tag(v_a_2097_) == 1)
{
lean_object* v_val_2098_; lean_object* v___x_2099_; 
lean_dec(v_mvarId_1363_);
v_val_2098_ = lean_ctor_get(v_a_2097_, 0);
lean_inc(v_val_2098_);
lean_dec_ref(v_a_2097_);
v___x_2099_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; uint8_t v___x_2101_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_a_2100_);
lean_dec_ref(v___x_2099_);
v___x_2101_ = lean_unbox(v_a_2100_);
lean_dec(v_a_2100_);
if (v___x_2101_ == 0)
{
v_mvarId_1363_ = v_val_2098_;
goto _start;
}
else
{
lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2103_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6);
v___x_2104_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_2103_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_dec_ref(v___x_2104_);
v_mvarId_1363_ = v_val_2098_;
goto _start;
}
else
{
lean_dec(v_val_2098_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_declName_1362_);
return v___x_2104_;
}
}
}
else
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
lean_dec(v_val_2098_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_declName_1362_);
v_a_2106_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_2099_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2099_);
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
lean_object* v___x_2114_; 
lean_dec(v_a_2097_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_mvarId_1363_);
v___x_2114_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_a_2115_);
lean_dec_ref(v___x_2114_);
if (lean_obj_tag(v_a_2115_) == 1)
{
lean_object* v_val_2116_; lean_object* v___x_2117_; 
lean_dec(v_mvarId_1363_);
v_val_2116_ = lean_ctor_get(v_a_2115_, 0);
lean_inc(v_val_2116_);
lean_dec_ref(v_a_2115_);
v___x_2117_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v_a_2118_; uint8_t v___x_2119_; 
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
lean_inc(v_a_2118_);
lean_dec_ref(v___x_2117_);
v___x_2119_ = lean_unbox(v_a_2118_);
lean_dec(v_a_2118_);
if (v___x_2119_ == 0)
{
v_mvarId_1363_ = v_val_2116_;
goto _start;
}
else
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2121_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_2122_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_2121_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_dec_ref(v___x_2122_);
v_mvarId_1363_ = v_val_2116_;
goto _start;
}
else
{
lean_dec(v_val_2116_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_declName_1362_);
return v___x_2122_;
}
}
}
else
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2131_; 
lean_dec(v_val_2116_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_declName_1362_);
v_a_2124_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2126_ = v___x_2117_;
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2117_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2127_ == 0)
{
v___x_2129_ = v___x_2126_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_a_2124_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
else
{
lean_object* v___x_2132_; 
lean_dec(v_a_2115_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_mvarId_1363_);
v___x_2132_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1363_, v_hasTrace_1382_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
lean_dec_ref(v___x_2132_);
if (lean_obj_tag(v_a_2133_) == 1)
{
lean_object* v_val_2134_; lean_object* v___x_2135_; 
lean_dec(v_mvarId_1363_);
v_val_2134_ = lean_ctor_get(v_a_2133_, 0);
lean_inc(v_val_2134_);
lean_dec_ref(v_a_2133_);
v___x_2135_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; uint8_t v___x_2137_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2136_);
lean_dec_ref(v___x_2135_);
v___x_2137_ = lean_unbox(v_a_2136_);
lean_dec(v_a_2136_);
if (v___x_2137_ == 0)
{
v_mvarId_1363_ = v_val_2134_;
goto _start;
}
else
{
lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2139_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
v___x_2140_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_2139_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_dec_ref(v___x_2140_);
v_mvarId_1363_ = v_val_2134_;
goto _start;
}
else
{
lean_dec(v_val_2134_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_declName_1362_);
return v___x_2140_;
}
}
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2149_; 
lean_dec(v_val_2134_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_declName_1362_);
v_a_2142_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2144_ = v___x_2135_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2135_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2147_; 
if (v_isShared_2145_ == 0)
{
v___x_2147_ = v___x_2144_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_a_2142_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
else
{
lean_object* v___x_2150_; lean_object* v___x_2151_; uint8_t v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
lean_dec(v_a_2133_);
v___x_2150_ = lean_unsigned_to_nat(100000u);
v___x_2151_ = lean_unsigned_to_nat(2u);
v___x_2152_ = 0;
v___x_2153_ = lean_box(0);
v___x_2154_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_2154_, 0, v___x_2150_);
lean_ctor_set(v___x_2154_, 1, v___x_2151_);
lean_ctor_set(v___x_2154_, 2, v___x_2153_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*3, v___x_2089_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*3 + 1, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*3 + 2, v___x_2089_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*3 + 3, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*3 + 4, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*3 + 5, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*3 + 6, v___x_2152_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*3 + 7, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*3 + 8, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*3 + 9, v___x_2089_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*3 + 10, v___x_2089_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*3 + 11, v___x_2089_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*3 + 12, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*3 + 13, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*3 + 14, v___x_2089_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*3 + 15, v___x_2089_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*3 + 16, v___x_2089_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*3 + 17, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*3 + 18, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*3 + 19, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*3 + 20, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*3 + 21, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*3 + 22, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*3 + 23, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*3 + 24, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*3 + 25, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*3 + 26, v___x_2089_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*3 + 27, v___x_2089_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*3 + 28, v___x_2089_);
v___x_2155_ = lean_unsigned_to_nat(0u);
v___x_2156_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__11));
v___x_2157_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13);
v___x_2158_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15);
v___x_2159_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2159_, 0, v___x_2157_);
lean_ctor_set(v___x_2159_, 1, v___x_2158_);
lean_ctor_set_uint8(v___x_2159_, sizeof(void*)*2, v_hasTrace_1382_);
v___x_2160_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_2154_, v___x_2156_, v___x_2159_, v_a_1364_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v_a_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
lean_inc(v_a_2161_);
lean_dec_ref(v___x_2160_);
v___x_2162_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_mvarId_1363_);
v___x_2163_ = l_Lean_Meta_simpTargetStar(v_mvarId_1363_, v_a_2161_, v___x_2156_, v___x_2153_, v___x_2162_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; lean_object* v_fst_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2313_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_a_2164_);
lean_dec_ref(v___x_2163_);
v_fst_2165_ = lean_ctor_get(v_a_2164_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v_a_2164_);
if (v_isSharedCheck_2313_ == 0)
{
lean_object* v_unused_2314_; 
v_unused_2314_ = lean_ctor_get(v_a_2164_, 1);
lean_dec(v_unused_2314_);
v___x_2167_ = v_a_2164_;
v_isShared_2168_ = v_isSharedCheck_2313_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_fst_2165_);
lean_dec(v_a_2164_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2313_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
switch(lean_obj_tag(v_fst_2165_))
{
case 0:
{
lean_object* v___x_2169_; 
lean_del_object(v___x_2167_);
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v___x_2169_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2181_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2172_ = v___x_2169_;
v_isShared_2173_ = v_isSharedCheck_2181_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2169_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2181_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
uint8_t v___x_2174_; 
v___x_2174_ = lean_unbox(v_a_2170_);
lean_dec(v_a_2170_);
if (v___x_2174_ == 0)
{
lean_object* v___x_2175_; lean_object* v___x_2177_; 
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
v___x_2175_ = lean_box(0);
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 0, v___x_2175_);
v___x_2177_ = v___x_2172_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2175_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
else
{
lean_object* v___x_2179_; lean_object* v___x_2180_; 
lean_del_object(v___x_2172_);
v___x_2179_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23);
v___x_2180_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_2179_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
return v___x_2180_;
}
}
}
else
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
v_a_2182_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2169_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2169_);
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
case 1:
{
lean_object* v___x_2190_; 
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_declName_1362_);
lean_inc(v_mvarId_1363_);
v___x_2190_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1363_, v_declName_1362_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_a_2191_; 
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_a_2191_);
lean_dec_ref(v___x_2190_);
if (lean_obj_tag(v_a_2191_) == 1)
{
lean_object* v_val_2192_; lean_object* v___x_2193_; 
lean_del_object(v___x_2167_);
lean_dec(v_mvarId_1363_);
v_val_2192_ = lean_ctor_get(v_a_2191_, 0);
lean_inc(v_val_2192_);
lean_dec_ref(v_a_2191_);
v___x_2193_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2194_; uint8_t v___x_2195_; 
v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
lean_inc(v_a_2194_);
lean_dec_ref(v___x_2193_);
v___x_2195_ = lean_unbox(v_a_2194_);
lean_dec(v_a_2194_);
if (v___x_2195_ == 0)
{
v_mvarId_1363_ = v_val_2192_;
goto _start;
}
else
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2197_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25);
v___x_2198_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_2197_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_dec_ref(v___x_2198_);
v_mvarId_1363_ = v_val_2192_;
goto _start;
}
else
{
lean_dec(v_val_2192_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_declName_1362_);
return v___x_2198_;
}
}
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
lean_dec(v_val_2192_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_declName_1362_);
v_a_2200_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___x_2193_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2193_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2200_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
else
{
lean_object* v___x_2208_; 
lean_dec(v_a_2191_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_mvarId_1363_);
v___x_2208_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2280_; 
v_a_2209_ = lean_ctor_get(v___x_2208_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2211_ = v___x_2208_;
v_isShared_2212_ = v_isSharedCheck_2280_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___x_2208_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2280_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
if (lean_obj_tag(v_a_2209_) == 1)
{
lean_object* v_val_2213_; lean_object* v___y_2215_; lean_object* v___y_2216_; lean_object* v___y_2217_; lean_object* v___y_2218_; lean_object* v___x_2235_; 
lean_del_object(v___x_2167_);
lean_dec(v_mvarId_1363_);
v_val_2213_ = lean_ctor_get(v_a_2209_, 0);
lean_inc(v_val_2213_);
lean_dec_ref(v_a_2209_);
v___x_2235_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; uint8_t v___x_2237_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_a_2236_);
lean_dec_ref(v___x_2235_);
v___x_2237_ = lean_unbox(v_a_2236_);
lean_dec(v_a_2236_);
if (v___x_2237_ == 0)
{
v___y_2215_ = v_a_1364_;
v___y_2216_ = v_a_1365_;
v___y_2217_ = v_a_1366_;
v___y_2218_ = v_a_1367_;
goto v___jp_2214_;
}
else
{
lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2238_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27);
v___x_2239_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_2238_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_dec_ref(v___x_2239_);
v___y_2215_ = v_a_1364_;
v___y_2216_ = v_a_1365_;
v___y_2217_ = v_a_1366_;
v___y_2218_ = v_a_1367_;
goto v___jp_2214_;
}
else
{
lean_dec(v_val_2213_);
lean_del_object(v___x_2211_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_declName_1362_);
return v___x_2239_;
}
}
}
else
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2247_; 
lean_dec(v_val_2213_);
lean_del_object(v___x_2211_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_declName_1362_);
v_a_2240_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2242_ = v___x_2235_;
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2235_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2245_; 
if (v_isShared_2243_ == 0)
{
v___x_2245_ = v___x_2242_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_a_2240_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
v___jp_2214_:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; uint8_t v___x_2221_; 
v___x_2219_ = lean_array_get_size(v_val_2213_);
v___x_2220_ = lean_box(0);
v___x_2221_ = lean_nat_dec_lt(v___x_2155_, v___x_2219_);
if (v___x_2221_ == 0)
{
lean_object* v___x_2223_; 
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec(v_val_2213_);
lean_dec(v_declName_1362_);
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 0, v___x_2220_);
v___x_2223_ = v___x_2211_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v___x_2220_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
else
{
uint8_t v___x_2225_; 
v___x_2225_ = lean_nat_dec_le(v___x_2219_, v___x_2219_);
if (v___x_2225_ == 0)
{
if (v___x_2221_ == 0)
{
lean_object* v___x_2227_; 
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec(v_val_2213_);
lean_dec(v_declName_1362_);
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 0, v___x_2220_);
v___x_2227_ = v___x_2211_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2220_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
else
{
size_t v___x_2229_; size_t v___x_2230_; lean_object* v___x_2231_; 
lean_del_object(v___x_2211_);
v___x_2229_ = ((size_t)0ULL);
v___x_2230_ = lean_usize_of_nat(v___x_2219_);
v___x_2231_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1362_, v_val_2213_, v___x_2229_, v___x_2230_, v___x_2220_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
lean_dec(v_val_2213_);
return v___x_2231_;
}
}
else
{
size_t v___x_2232_; size_t v___x_2233_; lean_object* v___x_2234_; 
lean_del_object(v___x_2211_);
v___x_2232_ = ((size_t)0ULL);
v___x_2233_ = lean_usize_of_nat(v___x_2219_);
v___x_2234_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1362_, v_val_2213_, v___x_2232_, v___x_2233_, v___x_2220_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
lean_dec(v_val_2213_);
return v___x_2234_;
}
}
}
}
else
{
lean_object* v___x_2248_; 
lean_del_object(v___x_2211_);
lean_dec(v_a_2209_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_mvarId_1363_);
v___x_2248_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1363_, v_hasTrace_1382_, v_hasTrace_1382_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_2248_) == 0)
{
lean_object* v_a_2249_; 
v_a_2249_ = lean_ctor_get(v___x_2248_, 0);
lean_inc(v_a_2249_);
lean_dec_ref(v___x_2248_);
if (lean_obj_tag(v_a_2249_) == 1)
{
lean_object* v_val_2250_; lean_object* v___x_2251_; 
lean_del_object(v___x_2167_);
lean_dec(v_mvarId_1363_);
v_val_2250_ = lean_ctor_get(v_a_2249_, 0);
lean_inc(v_val_2250_);
lean_dec_ref(v_a_2249_);
v___x_2251_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v_a_2252_; uint8_t v___x_2253_; 
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_a_2252_);
lean_dec_ref(v___x_2251_);
v___x_2253_ = lean_unbox(v_a_2252_);
lean_dec(v_a_2252_);
if (v___x_2253_ == 0)
{
lean_object* v___x_2254_; 
v___x_2254_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_declName_1362_, v_val_2250_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
return v___x_2254_;
}
else
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29);
v___x_2256_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_2255_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v___x_2257_; 
lean_dec_ref(v___x_2256_);
v___x_2257_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_declName_1362_, v_val_2250_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
return v___x_2257_;
}
else
{
lean_dec(v_val_2250_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_declName_1362_);
return v___x_2256_;
}
}
}
else
{
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2265_; 
lean_dec(v_val_2250_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_declName_1362_);
v_a_2258_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2260_ = v___x_2251_;
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2251_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2263_; 
if (v_isShared_2261_ == 0)
{
v___x_2263_ = v___x_2260_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_a_2258_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
}
else
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2269_; 
lean_dec(v_a_2249_);
lean_dec(v_declName_1362_);
v___x_2266_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31);
v___x_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2267_, 0, v_mvarId_1363_);
if (v_isShared_2168_ == 0)
{
lean_ctor_set_tag(v___x_2167_, 7);
lean_ctor_set(v___x_2167_, 1, v___x_2267_);
lean_ctor_set(v___x_2167_, 0, v___x_2266_);
v___x_2269_ = v___x_2167_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v___x_2266_);
lean_ctor_set(v_reuseFailAlloc_2271_, 1, v___x_2267_);
v___x_2269_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
lean_object* v___x_2270_; 
v___x_2270_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_2269_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
return v___x_2270_;
}
}
}
else
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
lean_del_object(v___x_2167_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_2272_ = lean_ctor_get(v___x_2248_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2274_ = v___x_2248_;
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2248_);
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
}
}
else
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2288_; 
lean_del_object(v___x_2167_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_2281_ = lean_ctor_get(v___x_2208_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2283_ = v___x_2208_;
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2208_);
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
}
else
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2296_; 
lean_del_object(v___x_2167_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_2289_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2291_ = v___x_2190_;
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2190_);
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
default: 
{
lean_object* v_mvarId_2297_; lean_object* v___x_2298_; 
lean_del_object(v___x_2167_);
lean_dec(v_mvarId_1363_);
v_mvarId_2297_ = lean_ctor_get(v_fst_2165_, 0);
lean_inc(v_mvarId_2297_);
lean_dec_ref(v_fst_2165_);
v___x_2298_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_object* v_a_2299_; uint8_t v___x_2300_; 
v_a_2299_ = lean_ctor_get(v___x_2298_, 0);
lean_inc(v_a_2299_);
lean_dec_ref(v___x_2298_);
v___x_2300_ = lean_unbox(v_a_2299_);
lean_dec(v_a_2299_);
if (v___x_2300_ == 0)
{
v_mvarId_1363_ = v_mvarId_2297_;
goto _start;
}
else
{
lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2302_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33);
v___x_2303_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_2302_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_dec_ref(v___x_2303_);
v_mvarId_1363_ = v_mvarId_2297_;
goto _start;
}
else
{
lean_dec(v_mvarId_2297_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_declName_1362_);
return v___x_2303_;
}
}
}
else
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2312_; 
lean_dec(v_mvarId_2297_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_declName_1362_);
v_a_2305_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2307_ = v___x_2298_;
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2298_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2310_; 
if (v_isShared_2308_ == 0)
{
v___x_2310_ = v___x_2307_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2305_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_2315_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2317_ = v___x_2163_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2163_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2315_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
}
else
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2330_; 
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_2323_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2325_ = v___x_2160_;
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2160_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2328_; 
if (v_isShared_2326_ == 0)
{
v___x_2328_ = v___x_2325_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_a_2323_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
}
}
else
{
lean_object* v_a_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2338_; 
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_2331_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2333_ = v___x_2132_;
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_dec(v___x_2132_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2336_; 
if (v_isShared_2334_ == 0)
{
v___x_2336_ = v___x_2333_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2331_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
}
}
}
}
}
else
{
lean_object* v_a_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2346_; 
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_2339_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2341_ = v___x_2114_;
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_a_2339_);
lean_dec(v___x_2114_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2344_; 
if (v_isShared_2342_ == 0)
{
v___x_2344_ = v___x_2341_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_a_2339_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
}
}
}
else
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2354_; 
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_2347_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2349_ = v___x_2096_;
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2096_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2352_; 
if (v_isShared_2350_ == 0)
{
v___x_2352_ = v___x_2349_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_a_2347_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
}
else
{
lean_object* v___x_2355_; 
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v___x_2355_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v_a_2356_; uint8_t v___x_2357_; 
v_a_2356_ = lean_ctor_get(v___x_2355_, 0);
lean_inc(v_a_2356_);
lean_dec_ref(v___x_2355_);
v___x_2357_ = lean_unbox(v_a_2356_);
lean_dec(v_a_2356_);
if (v___x_2357_ == 0)
{
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
goto v___jp_1372_;
}
else
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2358_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35);
v___x_2359_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_2358_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_dec_ref(v___x_2359_);
goto v___jp_1372_;
}
else
{
return v___x_2359_;
}
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
v_a_2360_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2355_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2355_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_2368_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2093_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2093_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
else
{
lean_object* v___x_2376_; 
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v___x_2376_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_object* v_a_2377_; uint8_t v___x_2378_; 
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
lean_inc(v_a_2377_);
lean_dec_ref(v___x_2376_);
v___x_2378_ = lean_unbox(v_a_2377_);
lean_dec(v_a_2377_);
if (v___x_2378_ == 0)
{
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
goto v___jp_1369_;
}
else
{
lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2379_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37);
v___x_2380_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_2379_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
if (lean_obj_tag(v___x_2380_) == 0)
{
lean_dec_ref(v___x_2380_);
goto v___jp_1369_;
}
else
{
return v___x_2380_;
}
}
}
else
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
v_a_2381_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2376_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2376_);
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
}
else
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2396_; 
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_2389_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2391_ = v___x_2090_;
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2090_);
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
else
{
lean_inc_ref(v_options_1381_);
goto v___jp_1755_;
}
}
else
{
lean_inc_ref(v_options_1381_);
goto v___jp_1755_;
}
v___jp_1694_:
{
lean_object* v___x_1698_; double v___x_1699_; double v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; uint8_t v___x_1705_; lean_object* v___x_1706_; 
v___x_1698_ = lean_io_get_num_heartbeats();
v___x_1699_ = lean_float_of_nat(v___y_1696_);
v___x_1700_ = lean_float_of_nat(v___x_1698_);
v___x_1701_ = lean_box_float(v___x_1699_);
v___x_1702_ = lean_box_float(v___x_1700_);
v___x_1703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1701_);
lean_ctor_set(v___x_1703_, 1, v___x_1702_);
v___x_1704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1704_, 0, v_a_1697_);
lean_ctor_set(v___x_1704_, 1, v___x_1703_);
v___x_1705_ = lean_unbox(v_a_1691_);
lean_dec(v_a_1691_);
v___x_1706_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6(v_cls_1383_, v_hasTrace_1382_, v___x_1693_, v_options_1381_, v___x_1705_, v___y_1695_, v___f_1692_, v___x_1704_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
lean_dec_ref(v_options_1381_);
return v___x_1706_;
}
v___jp_1707_:
{
lean_object* v___x_1711_; 
v___x_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1711_, 0, v_a_1710_);
v___y_1695_ = v___y_1708_;
v___y_1696_ = v___y_1709_;
v_a_1697_ = v___x_1711_;
goto v___jp_1694_;
}
v___jp_1712_:
{
lean_object* v___x_1716_; 
v___x_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1716_, 0, v_a_1715_);
v___y_1695_ = v___y_1713_;
v___y_1696_ = v___y_1714_;
v_a_1697_ = v___x_1716_;
goto v___jp_1694_;
}
v___jp_1717_:
{
if (lean_obj_tag(v___y_1720_) == 0)
{
lean_object* v_a_1721_; 
v_a_1721_ = lean_ctor_get(v___y_1720_, 0);
lean_inc(v_a_1721_);
lean_dec_ref(v___y_1720_);
v___y_1708_ = v___y_1718_;
v___y_1709_ = v___y_1719_;
v_a_1710_ = v_a_1721_;
goto v___jp_1707_;
}
else
{
lean_object* v_a_1722_; 
v_a_1722_ = lean_ctor_get(v___y_1720_, 0);
lean_inc(v_a_1722_);
lean_dec_ref(v___y_1720_);
v___y_1713_ = v___y_1718_;
v___y_1714_ = v___y_1719_;
v_a_1715_ = v_a_1722_;
goto v___jp_1712_;
}
}
v___jp_1723_:
{
lean_object* v___x_1727_; double v___x_1728_; double v___x_1729_; double v___x_1730_; double v___x_1731_; double v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; uint8_t v___x_1737_; lean_object* v___x_1738_; 
v___x_1727_ = lean_io_mono_nanos_now();
v___x_1728_ = lean_float_of_nat(v___y_1724_);
v___x_1729_ = lean_float_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38);
v___x_1730_ = lean_float_div(v___x_1728_, v___x_1729_);
v___x_1731_ = lean_float_of_nat(v___x_1727_);
v___x_1732_ = lean_float_div(v___x_1731_, v___x_1729_);
v___x_1733_ = lean_box_float(v___x_1730_);
v___x_1734_ = lean_box_float(v___x_1732_);
v___x_1735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1733_);
lean_ctor_set(v___x_1735_, 1, v___x_1734_);
v___x_1736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1736_, 0, v_a_1726_);
lean_ctor_set(v___x_1736_, 1, v___x_1735_);
v___x_1737_ = lean_unbox(v_a_1691_);
lean_dec(v_a_1691_);
v___x_1738_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6(v_cls_1383_, v_hasTrace_1382_, v___x_1693_, v_options_1381_, v___x_1737_, v___y_1725_, v___f_1692_, v___x_1736_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
lean_dec_ref(v_options_1381_);
return v___x_1738_;
}
v___jp_1739_:
{
lean_object* v___x_1743_; 
v___x_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1743_, 0, v_a_1742_);
v___y_1724_ = v___y_1740_;
v___y_1725_ = v___y_1741_;
v_a_1726_ = v___x_1743_;
goto v___jp_1723_;
}
v___jp_1744_:
{
lean_object* v___x_1748_; 
v___x_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1748_, 0, v_a_1747_);
v___y_1724_ = v___y_1745_;
v___y_1725_ = v___y_1746_;
v_a_1726_ = v___x_1748_;
goto v___jp_1723_;
}
v___jp_1749_:
{
if (lean_obj_tag(v___y_1752_) == 0)
{
lean_object* v_a_1753_; 
v_a_1753_ = lean_ctor_get(v___y_1752_, 0);
lean_inc(v_a_1753_);
lean_dec_ref(v___y_1752_);
v___y_1745_ = v___y_1750_;
v___y_1746_ = v___y_1751_;
v_a_1747_ = v_a_1753_;
goto v___jp_1744_;
}
else
{
lean_object* v_a_1754_; 
v_a_1754_ = lean_ctor_get(v___y_1752_, 0);
lean_inc(v_a_1754_);
lean_dec_ref(v___y_1752_);
v___y_1740_ = v___y_1750_;
v___y_1741_ = v___y_1751_;
v_a_1742_ = v_a_1754_;
goto v___jp_1739_;
}
}
v___jp_1755_:
{
lean_object* v___x_1756_; 
v___x_1756_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg(v_a_1367_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_a_1757_; lean_object* v___x_1758_; uint8_t v___x_1759_; 
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
lean_inc(v_a_1757_);
lean_dec_ref(v___x_1756_);
v___x_1758_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1759_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_options_1381_, v___x_1758_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1760_ = lean_io_mono_nanos_now();
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_mvarId_1363_);
v___x_1761_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; uint8_t v___x_1763_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_a_1762_);
lean_dec_ref(v___x_1761_);
v___x_1763_ = lean_unbox(v_a_1762_);
lean_dec(v_a_1762_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; 
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_mvarId_1363_);
v___x_1764_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; uint8_t v___x_1766_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1765_);
lean_dec_ref(v___x_1764_);
v___x_1766_ = lean_unbox(v_a_1765_);
lean_dec(v_a_1765_);
if (v___x_1766_ == 0)
{
lean_object* v___x_1767_; 
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_mvarId_1363_);
v___x_1767_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v_a_1768_; 
v_a_1768_ = lean_ctor_get(v___x_1767_, 0);
lean_inc(v_a_1768_);
lean_dec_ref(v___x_1767_);
if (lean_obj_tag(v_a_1768_) == 1)
{
lean_object* v_val_1769_; lean_object* v___x_1770_; 
lean_dec(v_mvarId_1363_);
v_val_1769_ = lean_ctor_get(v_a_1768_, 0);
lean_inc(v_val_1769_);
lean_dec_ref(v_a_1768_);
v___x_1770_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; uint8_t v___x_1772_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref(v___x_1770_);
v___x_1772_ = lean_unbox(v_a_1771_);
lean_dec(v_a_1771_);
if (v___x_1772_ == 0)
{
lean_object* v___x_1773_; 
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
v___x_1773_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1362_, v_val_1769_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1750_ = v___x_1760_;
v___y_1751_ = v_a_1757_;
v___y_1752_ = v___x_1773_;
goto v___jp_1749_;
}
else
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6);
v___x_1775_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_1774_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v___x_1776_; 
lean_dec_ref(v___x_1775_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
v___x_1776_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1362_, v_val_1769_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1750_ = v___x_1760_;
v___y_1751_ = v_a_1757_;
v___y_1752_ = v___x_1776_;
goto v___jp_1749_;
}
else
{
lean_dec(v_val_1769_);
lean_dec(v_declName_1362_);
v___y_1750_ = v___x_1760_;
v___y_1751_ = v_a_1757_;
v___y_1752_ = v___x_1775_;
goto v___jp_1749_;
}
}
}
else
{
lean_object* v_a_1777_; 
lean_dec(v_val_1769_);
lean_dec(v_declName_1362_);
v_a_1777_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1777_);
lean_dec_ref(v___x_1770_);
v___y_1740_ = v___x_1760_;
v___y_1741_ = v_a_1757_;
v_a_1742_ = v_a_1777_;
goto v___jp_1739_;
}
}
else
{
lean_object* v___x_1778_; 
lean_dec(v_a_1768_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_mvarId_1363_);
v___x_1778_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v_a_1779_; 
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_a_1779_);
lean_dec_ref(v___x_1778_);
if (lean_obj_tag(v_a_1779_) == 1)
{
lean_object* v_val_1780_; lean_object* v___x_1781_; 
lean_dec(v_mvarId_1363_);
v_val_1780_ = lean_ctor_get(v_a_1779_, 0);
lean_inc(v_val_1780_);
lean_dec_ref(v_a_1779_);
v___x_1781_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v_a_1782_; uint8_t v___x_1783_; 
v_a_1782_ = lean_ctor_get(v___x_1781_, 0);
lean_inc(v_a_1782_);
lean_dec_ref(v___x_1781_);
v___x_1783_ = lean_unbox(v_a_1782_);
lean_dec(v_a_1782_);
if (v___x_1783_ == 0)
{
lean_object* v___x_1784_; 
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
v___x_1784_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1362_, v_val_1780_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1750_ = v___x_1760_;
v___y_1751_ = v_a_1757_;
v___y_1752_ = v___x_1784_;
goto v___jp_1749_;
}
else
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1786_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_1785_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v___x_1787_; 
lean_dec_ref(v___x_1786_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
v___x_1787_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1362_, v_val_1780_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1750_ = v___x_1760_;
v___y_1751_ = v_a_1757_;
v___y_1752_ = v___x_1787_;
goto v___jp_1749_;
}
else
{
lean_dec(v_val_1780_);
lean_dec(v_declName_1362_);
v___y_1750_ = v___x_1760_;
v___y_1751_ = v_a_1757_;
v___y_1752_ = v___x_1786_;
goto v___jp_1749_;
}
}
}
else
{
lean_object* v_a_1788_; 
lean_dec(v_val_1780_);
lean_dec(v_declName_1362_);
v_a_1788_ = lean_ctor_get(v___x_1781_, 0);
lean_inc(v_a_1788_);
lean_dec_ref(v___x_1781_);
v___y_1740_ = v___x_1760_;
v___y_1741_ = v_a_1757_;
v_a_1742_ = v_a_1788_;
goto v___jp_1739_;
}
}
else
{
lean_object* v___x_1789_; 
lean_dec(v_a_1779_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_mvarId_1363_);
v___x_1789_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1363_, v_hasTrace_1382_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v_a_1790_; 
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
lean_inc(v_a_1790_);
lean_dec_ref(v___x_1789_);
if (lean_obj_tag(v_a_1790_) == 1)
{
lean_object* v_val_1791_; lean_object* v___x_1792_; 
lean_dec(v_mvarId_1363_);
v_val_1791_ = lean_ctor_get(v_a_1790_, 0);
lean_inc(v_val_1791_);
lean_dec_ref(v_a_1790_);
v___x_1792_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_object* v_a_1793_; uint8_t v___x_1794_; 
v_a_1793_ = lean_ctor_get(v___x_1792_, 0);
lean_inc(v_a_1793_);
lean_dec_ref(v___x_1792_);
v___x_1794_ = lean_unbox(v_a_1793_);
lean_dec(v_a_1793_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; 
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
v___x_1795_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1362_, v_val_1791_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1750_ = v___x_1760_;
v___y_1751_ = v_a_1757_;
v___y_1752_ = v___x_1795_;
goto v___jp_1749_;
}
else
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1796_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
v___x_1797_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_1796_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v___x_1798_; 
lean_dec_ref(v___x_1797_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
v___x_1798_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1362_, v_val_1791_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1750_ = v___x_1760_;
v___y_1751_ = v_a_1757_;
v___y_1752_ = v___x_1798_;
goto v___jp_1749_;
}
else
{
lean_dec(v_val_1791_);
lean_dec(v_declName_1362_);
v___y_1750_ = v___x_1760_;
v___y_1751_ = v_a_1757_;
v___y_1752_ = v___x_1797_;
goto v___jp_1749_;
}
}
}
else
{
lean_object* v_a_1799_; 
lean_dec(v_val_1791_);
lean_dec(v_declName_1362_);
v_a_1799_ = lean_ctor_get(v___x_1792_, 0);
lean_inc(v_a_1799_);
lean_dec_ref(v___x_1792_);
v___y_1740_ = v___x_1760_;
v___y_1741_ = v_a_1757_;
v_a_1742_ = v_a_1799_;
goto v___jp_1739_;
}
}
else
{
lean_object* v___x_1800_; lean_object* v___x_1801_; uint8_t v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
lean_dec(v_a_1790_);
v___x_1800_ = lean_unsigned_to_nat(100000u);
v___x_1801_ = lean_unsigned_to_nat(2u);
v___x_1802_ = 0;
v___x_1803_ = lean_box(0);
v___x_1804_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1804_, 0, v___x_1800_);
lean_ctor_set(v___x_1804_, 1, v___x_1801_);
lean_ctor_set(v___x_1804_, 2, v___x_1803_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*3, v___x_1759_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*3 + 1, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*3 + 2, v___x_1759_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*3 + 3, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*3 + 4, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*3 + 5, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*3 + 6, v___x_1802_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*3 + 7, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*3 + 8, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*3 + 9, v___x_1759_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*3 + 10, v___x_1759_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*3 + 11, v___x_1759_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*3 + 12, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*3 + 13, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*3 + 14, v___x_1759_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*3 + 15, v___x_1759_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*3 + 16, v___x_1759_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*3 + 17, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*3 + 18, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*3 + 19, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*3 + 20, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*3 + 21, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*3 + 22, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*3 + 23, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*3 + 24, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*3 + 25, v_hasTrace_1382_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*3 + 26, v___x_1759_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*3 + 27, v___x_1759_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*3 + 28, v___x_1759_);
v___x_1805_ = lean_unsigned_to_nat(0u);
v___x_1806_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__11));
v___x_1807_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13);
v___x_1808_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15);
v___x_1809_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1809_, 0, v___x_1807_);
lean_ctor_set(v___x_1809_, 1, v___x_1808_);
lean_ctor_set_uint8(v___x_1809_, sizeof(void*)*2, v_hasTrace_1382_);
v___x_1810_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1804_, v___x_1806_, v___x_1809_, v_a_1364_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
lean_inc(v_a_1811_);
lean_dec_ref(v___x_1810_);
v___x_1812_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_mvarId_1363_);
v___x_1813_ = l_Lean_Meta_simpTargetStar(v_mvarId_1363_, v_a_1811_, v___x_1806_, v___x_1803_, v___x_1812_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_a_1814_; lean_object* v_fst_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1885_; 
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
lean_inc(v_a_1814_);
lean_dec_ref(v___x_1813_);
v_fst_1815_ = lean_ctor_get(v_a_1814_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v_a_1814_);
if (v_isSharedCheck_1885_ == 0)
{
lean_object* v_unused_1886_; 
v_unused_1886_ = lean_ctor_get(v_a_1814_, 1);
lean_dec(v_unused_1886_);
v___x_1817_ = v_a_1814_;
v_isShared_1818_ = v_isSharedCheck_1885_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_fst_1815_);
lean_dec(v_a_1814_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1885_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
switch(lean_obj_tag(v_fst_1815_))
{
case 0:
{
lean_object* v___x_1819_; 
lean_del_object(v___x_1817_);
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v___x_1819_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1820_; uint8_t v___x_1821_; 
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_a_1820_);
lean_dec_ref(v___x_1819_);
v___x_1821_ = lean_unbox(v_a_1820_);
lean_dec(v_a_1820_);
if (v___x_1821_ == 0)
{
lean_object* v___x_1822_; 
v___x_1822_ = lean_box(0);
v___y_1745_ = v___x_1760_;
v___y_1746_ = v_a_1757_;
v_a_1747_ = v___x_1822_;
goto v___jp_1744_;
}
else
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1823_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23);
v___x_1824_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_1823_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1750_ = v___x_1760_;
v___y_1751_ = v_a_1757_;
v___y_1752_ = v___x_1824_;
goto v___jp_1749_;
}
}
else
{
lean_object* v_a_1825_; 
v_a_1825_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_a_1825_);
lean_dec_ref(v___x_1819_);
v___y_1740_ = v___x_1760_;
v___y_1741_ = v_a_1757_;
v_a_1742_ = v_a_1825_;
goto v___jp_1739_;
}
}
case 1:
{
lean_object* v___x_1826_; 
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_declName_1362_);
lean_inc(v_mvarId_1363_);
v___x_1826_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1363_, v_declName_1362_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_a_1827_; 
v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
lean_inc(v_a_1827_);
lean_dec_ref(v___x_1826_);
if (lean_obj_tag(v_a_1827_) == 1)
{
lean_object* v_val_1828_; lean_object* v___x_1829_; 
lean_del_object(v___x_1817_);
lean_dec(v_mvarId_1363_);
v_val_1828_ = lean_ctor_get(v_a_1827_, 0);
lean_inc(v_val_1828_);
lean_dec_ref(v_a_1827_);
v___x_1829_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_a_1830_; uint8_t v___x_1831_; 
v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
lean_inc(v_a_1830_);
lean_dec_ref(v___x_1829_);
v___x_1831_ = lean_unbox(v_a_1830_);
lean_dec(v_a_1830_);
if (v___x_1831_ == 0)
{
lean_object* v___x_1832_; 
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
v___x_1832_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1362_, v_val_1828_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1750_ = v___x_1760_;
v___y_1751_ = v_a_1757_;
v___y_1752_ = v___x_1832_;
goto v___jp_1749_;
}
else
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1833_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25);
v___x_1834_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_1833_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v___x_1835_; 
lean_dec_ref(v___x_1834_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
v___x_1835_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1362_, v_val_1828_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1750_ = v___x_1760_;
v___y_1751_ = v_a_1757_;
v___y_1752_ = v___x_1835_;
goto v___jp_1749_;
}
else
{
lean_dec(v_val_1828_);
lean_dec(v_declName_1362_);
v___y_1750_ = v___x_1760_;
v___y_1751_ = v_a_1757_;
v___y_1752_ = v___x_1834_;
goto v___jp_1749_;
}
}
}
else
{
lean_object* v_a_1836_; 
lean_dec(v_val_1828_);
lean_dec(v_declName_1362_);
v_a_1836_ = lean_ctor_get(v___x_1829_, 0);
lean_inc(v_a_1836_);
lean_dec_ref(v___x_1829_);
v___y_1740_ = v___x_1760_;
v___y_1741_ = v_a_1757_;
v_a_1742_ = v_a_1836_;
goto v___jp_1739_;
}
}
else
{
lean_object* v___x_1837_; 
lean_dec(v_a_1827_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_mvarId_1363_);
v___x_1837_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
lean_inc(v_a_1838_);
lean_dec_ref(v___x_1837_);
if (lean_obj_tag(v_a_1838_) == 1)
{
lean_object* v_val_1839_; lean_object* v___x_1840_; 
lean_del_object(v___x_1817_);
lean_dec(v_mvarId_1363_);
v_val_1839_ = lean_ctor_get(v_a_1838_, 0);
lean_inc(v_val_1839_);
lean_dec_ref(v_a_1838_);
v___x_1840_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; uint8_t v___x_1842_; 
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
lean_inc(v_a_1841_);
lean_dec_ref(v___x_1840_);
v___x_1842_ = lean_unbox(v_a_1841_);
lean_dec(v_a_1841_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1843_ = lean_box(0);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
v___x_1844_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1839_, v___x_1805_, v_declName_1362_, v___x_1843_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
lean_dec(v_val_1839_);
v___y_1750_ = v___x_1760_;
v___y_1751_ = v_a_1757_;
v___y_1752_ = v___x_1844_;
goto v___jp_1749_;
}
else
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1845_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27);
v___x_1846_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_1845_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1848_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_a_1847_);
lean_dec_ref(v___x_1846_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
v___x_1848_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1839_, v___x_1805_, v_declName_1362_, v_a_1847_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
lean_dec(v_val_1839_);
v___y_1750_ = v___x_1760_;
v___y_1751_ = v_a_1757_;
v___y_1752_ = v___x_1848_;
goto v___jp_1749_;
}
else
{
lean_dec(v_val_1839_);
lean_dec(v_declName_1362_);
v___y_1750_ = v___x_1760_;
v___y_1751_ = v_a_1757_;
v___y_1752_ = v___x_1846_;
goto v___jp_1749_;
}
}
}
else
{
lean_object* v_a_1849_; 
lean_dec(v_val_1839_);
lean_dec(v_declName_1362_);
v_a_1849_ = lean_ctor_get(v___x_1840_, 0);
lean_inc(v_a_1849_);
lean_dec_ref(v___x_1840_);
v___y_1740_ = v___x_1760_;
v___y_1741_ = v_a_1757_;
v_a_1742_ = v_a_1849_;
goto v___jp_1739_;
}
}
else
{
lean_object* v___x_1850_; 
lean_dec(v_a_1838_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_mvarId_1363_);
v___x_1850_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1363_, v_hasTrace_1382_, v_hasTrace_1382_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1872_; 
v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1853_ = v___x_1850_;
v_isShared_1854_ = v_isSharedCheck_1872_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1850_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1872_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
if (lean_obj_tag(v_a_1851_) == 1)
{
lean_object* v_val_1855_; lean_object* v___x_1856_; 
lean_del_object(v___x_1853_);
lean_del_object(v___x_1817_);
lean_dec(v_mvarId_1363_);
v_val_1855_ = lean_ctor_get(v_a_1851_, 0);
lean_inc(v_val_1855_);
lean_dec_ref(v_a_1851_);
v___x_1856_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_a_1857_; uint8_t v___x_1858_; 
v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
lean_inc(v_a_1857_);
lean_dec_ref(v___x_1856_);
v___x_1858_ = lean_unbox(v_a_1857_);
lean_dec(v_a_1857_);
if (v___x_1858_ == 0)
{
lean_object* v___x_1859_; 
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
v___x_1859_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_declName_1362_, v_val_1855_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1750_ = v___x_1760_;
v___y_1751_ = v_a_1757_;
v___y_1752_ = v___x_1859_;
goto v___jp_1749_;
}
else
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1860_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29);
v___x_1861_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_1860_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_object* v___x_1862_; 
lean_dec_ref(v___x_1861_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
v___x_1862_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_declName_1362_, v_val_1855_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1750_ = v___x_1760_;
v___y_1751_ = v_a_1757_;
v___y_1752_ = v___x_1862_;
goto v___jp_1749_;
}
else
{
lean_dec(v_val_1855_);
lean_dec(v_declName_1362_);
v___y_1750_ = v___x_1760_;
v___y_1751_ = v_a_1757_;
v___y_1752_ = v___x_1861_;
goto v___jp_1749_;
}
}
}
else
{
lean_object* v_a_1863_; 
lean_dec(v_val_1855_);
lean_dec(v_declName_1362_);
v_a_1863_ = lean_ctor_get(v___x_1856_, 0);
lean_inc(v_a_1863_);
lean_dec_ref(v___x_1856_);
v___y_1740_ = v___x_1760_;
v___y_1741_ = v_a_1757_;
v_a_1742_ = v_a_1863_;
goto v___jp_1739_;
}
}
else
{
lean_object* v___x_1864_; lean_object* v___x_1866_; 
lean_dec(v_a_1851_);
lean_dec(v_declName_1362_);
v___x_1864_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31);
if (v_isShared_1854_ == 0)
{
lean_ctor_set_tag(v___x_1853_, 1);
lean_ctor_set(v___x_1853_, 0, v_mvarId_1363_);
v___x_1866_ = v___x_1853_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_mvarId_1363_);
v___x_1866_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
lean_object* v___x_1868_; 
if (v_isShared_1818_ == 0)
{
lean_ctor_set_tag(v___x_1817_, 7);
lean_ctor_set(v___x_1817_, 1, v___x_1866_);
lean_ctor_set(v___x_1817_, 0, v___x_1864_);
v___x_1868_ = v___x_1817_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1864_);
lean_ctor_set(v_reuseFailAlloc_1870_, 1, v___x_1866_);
v___x_1868_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
lean_object* v___x_1869_; 
v___x_1869_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1868_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1750_ = v___x_1760_;
v___y_1751_ = v_a_1757_;
v___y_1752_ = v___x_1869_;
goto v___jp_1749_;
}
}
}
}
}
else
{
lean_object* v_a_1873_; 
lean_del_object(v___x_1817_);
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_1873_ = lean_ctor_get(v___x_1850_, 0);
lean_inc(v_a_1873_);
lean_dec_ref(v___x_1850_);
v___y_1740_ = v___x_1760_;
v___y_1741_ = v_a_1757_;
v_a_1742_ = v_a_1873_;
goto v___jp_1739_;
}
}
}
else
{
lean_object* v_a_1874_; 
lean_del_object(v___x_1817_);
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_1874_ = lean_ctor_get(v___x_1837_, 0);
lean_inc(v_a_1874_);
lean_dec_ref(v___x_1837_);
v___y_1740_ = v___x_1760_;
v___y_1741_ = v_a_1757_;
v_a_1742_ = v_a_1874_;
goto v___jp_1739_;
}
}
}
else
{
lean_object* v_a_1875_; 
lean_del_object(v___x_1817_);
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_1875_ = lean_ctor_get(v___x_1826_, 0);
lean_inc(v_a_1875_);
lean_dec_ref(v___x_1826_);
v___y_1740_ = v___x_1760_;
v___y_1741_ = v_a_1757_;
v_a_1742_ = v_a_1875_;
goto v___jp_1739_;
}
}
default: 
{
lean_object* v_mvarId_1876_; lean_object* v___x_1877_; 
lean_del_object(v___x_1817_);
lean_dec(v_mvarId_1363_);
v_mvarId_1876_ = lean_ctor_get(v_fst_1815_, 0);
lean_inc(v_mvarId_1876_);
lean_dec_ref(v_fst_1815_);
v___x_1877_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_a_1878_; uint8_t v___x_1879_; 
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_a_1878_);
lean_dec_ref(v___x_1877_);
v___x_1879_ = lean_unbox(v_a_1878_);
lean_dec(v_a_1878_);
if (v___x_1879_ == 0)
{
lean_object* v___x_1880_; 
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
v___x_1880_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1362_, v_mvarId_1876_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1750_ = v___x_1760_;
v___y_1751_ = v_a_1757_;
v___y_1752_ = v___x_1880_;
goto v___jp_1749_;
}
else
{
lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1881_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33);
v___x_1882_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_1881_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v___x_1883_; 
lean_dec_ref(v___x_1882_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
v___x_1883_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1362_, v_mvarId_1876_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1750_ = v___x_1760_;
v___y_1751_ = v_a_1757_;
v___y_1752_ = v___x_1883_;
goto v___jp_1749_;
}
else
{
lean_dec(v_mvarId_1876_);
lean_dec(v_declName_1362_);
v___y_1750_ = v___x_1760_;
v___y_1751_ = v_a_1757_;
v___y_1752_ = v___x_1882_;
goto v___jp_1749_;
}
}
}
else
{
lean_object* v_a_1884_; 
lean_dec(v_mvarId_1876_);
lean_dec(v_declName_1362_);
v_a_1884_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_a_1884_);
lean_dec_ref(v___x_1877_);
v___y_1740_ = v___x_1760_;
v___y_1741_ = v_a_1757_;
v_a_1742_ = v_a_1884_;
goto v___jp_1739_;
}
}
}
}
}
else
{
lean_object* v_a_1887_; 
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_1887_ = lean_ctor_get(v___x_1813_, 0);
lean_inc(v_a_1887_);
lean_dec_ref(v___x_1813_);
v___y_1740_ = v___x_1760_;
v___y_1741_ = v_a_1757_;
v_a_1742_ = v_a_1887_;
goto v___jp_1739_;
}
}
else
{
lean_object* v_a_1888_; 
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_1888_ = lean_ctor_get(v___x_1810_, 0);
lean_inc(v_a_1888_);
lean_dec_ref(v___x_1810_);
v___y_1740_ = v___x_1760_;
v___y_1741_ = v_a_1757_;
v_a_1742_ = v_a_1888_;
goto v___jp_1739_;
}
}
}
else
{
lean_object* v_a_1889_; 
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_1889_ = lean_ctor_get(v___x_1789_, 0);
lean_inc(v_a_1889_);
lean_dec_ref(v___x_1789_);
v___y_1740_ = v___x_1760_;
v___y_1741_ = v_a_1757_;
v_a_1742_ = v_a_1889_;
goto v___jp_1739_;
}
}
}
else
{
lean_object* v_a_1890_; 
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_1890_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_a_1890_);
lean_dec_ref(v___x_1778_);
v___y_1740_ = v___x_1760_;
v___y_1741_ = v_a_1757_;
v_a_1742_ = v_a_1890_;
goto v___jp_1739_;
}
}
}
else
{
lean_object* v_a_1891_; 
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_1891_ = lean_ctor_get(v___x_1767_, 0);
lean_inc(v_a_1891_);
lean_dec_ref(v___x_1767_);
v___y_1740_ = v___x_1760_;
v___y_1741_ = v_a_1757_;
v_a_1742_ = v_a_1891_;
goto v___jp_1739_;
}
}
else
{
lean_object* v___x_1892_; 
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v___x_1892_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; uint8_t v___x_1894_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_a_1893_);
lean_dec_ref(v___x_1892_);
v___x_1894_ = lean_unbox(v_a_1893_);
lean_dec(v_a_1893_);
if (v___x_1894_ == 0)
{
lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1895_ = lean_box(0);
v___x_1896_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1895_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1750_ = v___x_1760_;
v___y_1751_ = v_a_1757_;
v___y_1752_ = v___x_1896_;
goto v___jp_1749_;
}
else
{
lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1897_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35);
v___x_1898_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_1897_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v___x_1900_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
lean_inc(v_a_1899_);
lean_dec_ref(v___x_1898_);
v___x_1900_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1899_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1750_ = v___x_1760_;
v___y_1751_ = v_a_1757_;
v___y_1752_ = v___x_1900_;
goto v___jp_1749_;
}
else
{
v___y_1750_ = v___x_1760_;
v___y_1751_ = v_a_1757_;
v___y_1752_ = v___x_1898_;
goto v___jp_1749_;
}
}
}
else
{
lean_object* v_a_1901_; 
v_a_1901_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_a_1901_);
lean_dec_ref(v___x_1892_);
v___y_1740_ = v___x_1760_;
v___y_1741_ = v_a_1757_;
v_a_1742_ = v_a_1901_;
goto v___jp_1739_;
}
}
}
else
{
lean_object* v_a_1902_; 
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_1902_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1902_);
lean_dec_ref(v___x_1764_);
v___y_1740_ = v___x_1760_;
v___y_1741_ = v_a_1757_;
v_a_1742_ = v_a_1902_;
goto v___jp_1739_;
}
}
else
{
lean_object* v___x_1903_; 
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v___x_1903_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_object* v_a_1904_; uint8_t v___x_1905_; 
v_a_1904_ = lean_ctor_get(v___x_1903_, 0);
lean_inc(v_a_1904_);
lean_dec_ref(v___x_1903_);
v___x_1905_ = lean_unbox(v_a_1904_);
lean_dec(v_a_1904_);
if (v___x_1905_ == 0)
{
lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1906_ = lean_box(0);
v___x_1907_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1906_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1750_ = v___x_1760_;
v___y_1751_ = v_a_1757_;
v___y_1752_ = v___x_1907_;
goto v___jp_1749_;
}
else
{
lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1908_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37);
v___x_1909_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_1908_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v_a_1910_; lean_object* v___x_1911_; 
v_a_1910_ = lean_ctor_get(v___x_1909_, 0);
lean_inc(v_a_1910_);
lean_dec_ref(v___x_1909_);
v___x_1911_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1910_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1750_ = v___x_1760_;
v___y_1751_ = v_a_1757_;
v___y_1752_ = v___x_1911_;
goto v___jp_1749_;
}
else
{
v___y_1750_ = v___x_1760_;
v___y_1751_ = v_a_1757_;
v___y_1752_ = v___x_1909_;
goto v___jp_1749_;
}
}
}
else
{
lean_object* v_a_1912_; 
v_a_1912_ = lean_ctor_get(v___x_1903_, 0);
lean_inc(v_a_1912_);
lean_dec_ref(v___x_1903_);
v___y_1740_ = v___x_1760_;
v___y_1741_ = v_a_1757_;
v_a_1742_ = v_a_1912_;
goto v___jp_1739_;
}
}
}
else
{
lean_object* v_a_1913_; 
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_1913_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_a_1913_);
lean_dec_ref(v___x_1761_);
v___y_1740_ = v___x_1760_;
v___y_1741_ = v_a_1757_;
v_a_1742_ = v_a_1913_;
goto v___jp_1739_;
}
}
else
{
lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1914_ = lean_io_get_num_heartbeats();
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_mvarId_1363_);
v___x_1915_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; uint8_t v___x_1917_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_1916_);
lean_dec_ref(v___x_1915_);
v___x_1917_ = lean_unbox(v_a_1916_);
lean_dec(v_a_1916_);
if (v___x_1917_ == 0)
{
lean_object* v___x_1918_; 
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_mvarId_1363_);
v___x_1918_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; uint8_t v___x_1920_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_a_1919_);
lean_dec_ref(v___x_1918_);
v___x_1920_ = lean_unbox(v_a_1919_);
if (v___x_1920_ == 0)
{
lean_object* v___x_1921_; 
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_mvarId_1363_);
v___x_1921_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v_a_1922_; 
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_a_1922_);
lean_dec_ref(v___x_1921_);
if (lean_obj_tag(v_a_1922_) == 1)
{
lean_object* v_val_1923_; lean_object* v___x_1924_; 
lean_dec(v_a_1919_);
lean_dec(v_mvarId_1363_);
v_val_1923_ = lean_ctor_get(v_a_1922_, 0);
lean_inc(v_val_1923_);
lean_dec_ref(v_a_1922_);
v___x_1924_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_a_1925_; uint8_t v___x_1926_; 
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc(v_a_1925_);
lean_dec_ref(v___x_1924_);
v___x_1926_ = lean_unbox(v_a_1925_);
lean_dec(v_a_1925_);
if (v___x_1926_ == 0)
{
lean_object* v___x_1927_; 
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
v___x_1927_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1362_, v_val_1923_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1718_ = v_a_1757_;
v___y_1719_ = v___x_1914_;
v___y_1720_ = v___x_1927_;
goto v___jp_1717_;
}
else
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6);
v___x_1929_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_1928_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v___x_1930_; 
lean_dec_ref(v___x_1929_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
v___x_1930_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1362_, v_val_1923_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1718_ = v_a_1757_;
v___y_1719_ = v___x_1914_;
v___y_1720_ = v___x_1930_;
goto v___jp_1717_;
}
else
{
lean_dec(v_val_1923_);
lean_dec(v_declName_1362_);
v___y_1718_ = v_a_1757_;
v___y_1719_ = v___x_1914_;
v___y_1720_ = v___x_1929_;
goto v___jp_1717_;
}
}
}
else
{
lean_object* v_a_1931_; 
lean_dec(v_val_1923_);
lean_dec(v_declName_1362_);
v_a_1931_ = lean_ctor_get(v___x_1924_, 0);
lean_inc(v_a_1931_);
lean_dec_ref(v___x_1924_);
v___y_1713_ = v_a_1757_;
v___y_1714_ = v___x_1914_;
v_a_1715_ = v_a_1931_;
goto v___jp_1712_;
}
}
else
{
lean_object* v___x_1932_; 
lean_dec(v_a_1922_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_mvarId_1363_);
v___x_1932_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
lean_dec_ref(v___x_1932_);
if (lean_obj_tag(v_a_1933_) == 1)
{
lean_object* v_val_1934_; lean_object* v___x_1935_; 
lean_dec(v_a_1919_);
lean_dec(v_mvarId_1363_);
v_val_1934_ = lean_ctor_get(v_a_1933_, 0);
lean_inc(v_val_1934_);
lean_dec_ref(v_a_1933_);
v___x_1935_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; uint8_t v___x_1937_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_a_1936_);
lean_dec_ref(v___x_1935_);
v___x_1937_ = lean_unbox(v_a_1936_);
lean_dec(v_a_1936_);
if (v___x_1937_ == 0)
{
lean_object* v___x_1938_; 
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
v___x_1938_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1362_, v_val_1934_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1718_ = v_a_1757_;
v___y_1719_ = v___x_1914_;
v___y_1720_ = v___x_1938_;
goto v___jp_1717_;
}
else
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1940_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_1939_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1940_) == 0)
{
lean_object* v___x_1941_; 
lean_dec_ref(v___x_1940_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
v___x_1941_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1362_, v_val_1934_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1718_ = v_a_1757_;
v___y_1719_ = v___x_1914_;
v___y_1720_ = v___x_1941_;
goto v___jp_1717_;
}
else
{
lean_dec(v_val_1934_);
lean_dec(v_declName_1362_);
v___y_1718_ = v_a_1757_;
v___y_1719_ = v___x_1914_;
v___y_1720_ = v___x_1940_;
goto v___jp_1717_;
}
}
}
else
{
lean_object* v_a_1942_; 
lean_dec(v_val_1934_);
lean_dec(v_declName_1362_);
v_a_1942_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_a_1942_);
lean_dec_ref(v___x_1935_);
v___y_1713_ = v_a_1757_;
v___y_1714_ = v___x_1914_;
v_a_1715_ = v_a_1942_;
goto v___jp_1712_;
}
}
else
{
lean_object* v___x_1943_; 
lean_dec(v_a_1933_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_mvarId_1363_);
v___x_1943_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1363_, v___x_1759_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v_a_1944_; 
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
lean_inc(v_a_1944_);
lean_dec_ref(v___x_1943_);
if (lean_obj_tag(v_a_1944_) == 1)
{
lean_object* v_val_1945_; lean_object* v___x_1946_; 
lean_dec(v_a_1919_);
lean_dec(v_mvarId_1363_);
v_val_1945_ = lean_ctor_get(v_a_1944_, 0);
lean_inc(v_val_1945_);
lean_dec_ref(v_a_1944_);
v___x_1946_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; uint8_t v___x_1948_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1947_);
lean_dec_ref(v___x_1946_);
v___x_1948_ = lean_unbox(v_a_1947_);
lean_dec(v_a_1947_);
if (v___x_1948_ == 0)
{
lean_object* v___x_1949_; 
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
v___x_1949_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1362_, v_val_1945_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1718_ = v_a_1757_;
v___y_1719_ = v___x_1914_;
v___y_1720_ = v___x_1949_;
goto v___jp_1717_;
}
else
{
lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1950_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
v___x_1951_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_1950_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v___x_1952_; 
lean_dec_ref(v___x_1951_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
v___x_1952_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1362_, v_val_1945_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1718_ = v_a_1757_;
v___y_1719_ = v___x_1914_;
v___y_1720_ = v___x_1952_;
goto v___jp_1717_;
}
else
{
lean_dec(v_val_1945_);
lean_dec(v_declName_1362_);
v___y_1718_ = v_a_1757_;
v___y_1719_ = v___x_1914_;
v___y_1720_ = v___x_1951_;
goto v___jp_1717_;
}
}
}
else
{
lean_object* v_a_1953_; 
lean_dec(v_val_1945_);
lean_dec(v_declName_1362_);
v_a_1953_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1953_);
lean_dec_ref(v___x_1946_);
v___y_1713_ = v_a_1757_;
v___y_1714_ = v___x_1914_;
v_a_1715_ = v_a_1953_;
goto v___jp_1712_;
}
}
else
{
lean_object* v___x_1954_; lean_object* v___x_1955_; uint8_t v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; uint8_t v___x_1959_; uint8_t v___x_1960_; uint8_t v___x_1961_; uint8_t v___x_1962_; uint8_t v___x_1963_; uint8_t v___x_1964_; uint8_t v___x_1965_; uint8_t v___x_1966_; uint8_t v___x_1967_; uint8_t v___x_1968_; uint8_t v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
lean_dec(v_a_1944_);
v___x_1954_ = lean_unsigned_to_nat(100000u);
v___x_1955_ = lean_unsigned_to_nat(2u);
v___x_1956_ = 0;
v___x_1957_ = lean_box(0);
v___x_1958_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1958_, 0, v___x_1954_);
lean_ctor_set(v___x_1958_, 1, v___x_1955_);
lean_ctor_set(v___x_1958_, 2, v___x_1957_);
v___x_1959_ = lean_unbox(v_a_1919_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*3, v___x_1959_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*3 + 1, v___x_1759_);
v___x_1960_ = lean_unbox(v_a_1919_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*3 + 2, v___x_1960_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*3 + 3, v___x_1759_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*3 + 4, v___x_1759_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*3 + 5, v___x_1759_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*3 + 6, v___x_1956_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*3 + 7, v___x_1759_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*3 + 8, v___x_1759_);
v___x_1961_ = lean_unbox(v_a_1919_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*3 + 9, v___x_1961_);
v___x_1962_ = lean_unbox(v_a_1919_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*3 + 10, v___x_1962_);
v___x_1963_ = lean_unbox(v_a_1919_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*3 + 11, v___x_1963_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*3 + 12, v___x_1759_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*3 + 13, v___x_1759_);
v___x_1964_ = lean_unbox(v_a_1919_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*3 + 14, v___x_1964_);
v___x_1965_ = lean_unbox(v_a_1919_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*3 + 15, v___x_1965_);
v___x_1966_ = lean_unbox(v_a_1919_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*3 + 16, v___x_1966_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*3 + 17, v___x_1759_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*3 + 18, v___x_1759_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*3 + 19, v___x_1759_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*3 + 20, v___x_1759_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*3 + 21, v___x_1759_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*3 + 22, v___x_1759_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*3 + 23, v___x_1759_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*3 + 24, v___x_1759_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*3 + 25, v___x_1759_);
v___x_1967_ = lean_unbox(v_a_1919_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*3 + 26, v___x_1967_);
v___x_1968_ = lean_unbox(v_a_1919_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*3 + 27, v___x_1968_);
v___x_1969_ = lean_unbox(v_a_1919_);
lean_dec(v_a_1919_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*3 + 28, v___x_1969_);
v___x_1970_ = lean_unsigned_to_nat(0u);
v___x_1971_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__11));
v___x_1972_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13);
v___x_1973_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15);
v___x_1974_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1974_, 0, v___x_1972_);
lean_ctor_set(v___x_1974_, 1, v___x_1973_);
lean_ctor_set_uint8(v___x_1974_, sizeof(void*)*2, v___x_1759_);
v___x_1975_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1958_, v___x_1971_, v___x_1974_, v_a_1364_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v_a_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v_a_1976_ = lean_ctor_get(v___x_1975_, 0);
lean_inc(v_a_1976_);
lean_dec_ref(v___x_1975_);
v___x_1977_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_mvarId_1363_);
v___x_1978_ = l_Lean_Meta_simpTargetStar(v_mvarId_1363_, v_a_1976_, v___x_1971_, v___x_1957_, v___x_1977_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; lean_object* v_fst_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_2050_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_a_1979_);
lean_dec_ref(v___x_1978_);
v_fst_1980_ = lean_ctor_get(v_a_1979_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v_a_1979_);
if (v_isSharedCheck_2050_ == 0)
{
lean_object* v_unused_2051_; 
v_unused_2051_ = lean_ctor_get(v_a_1979_, 1);
lean_dec(v_unused_2051_);
v___x_1982_ = v_a_1979_;
v_isShared_1983_ = v_isSharedCheck_2050_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_fst_1980_);
lean_dec(v_a_1979_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_2050_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
switch(lean_obj_tag(v_fst_1980_))
{
case 0:
{
lean_object* v___x_1984_; 
lean_del_object(v___x_1982_);
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v___x_1984_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_a_1985_; uint8_t v___x_1986_; 
v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
lean_inc(v_a_1985_);
lean_dec_ref(v___x_1984_);
v___x_1986_ = lean_unbox(v_a_1985_);
lean_dec(v_a_1985_);
if (v___x_1986_ == 0)
{
lean_object* v___x_1987_; 
v___x_1987_ = lean_box(0);
v___y_1708_ = v_a_1757_;
v___y_1709_ = v___x_1914_;
v_a_1710_ = v___x_1987_;
goto v___jp_1707_;
}
else
{
lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1988_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23);
v___x_1989_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_1988_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1718_ = v_a_1757_;
v___y_1719_ = v___x_1914_;
v___y_1720_ = v___x_1989_;
goto v___jp_1717_;
}
}
else
{
lean_object* v_a_1990_; 
v_a_1990_ = lean_ctor_get(v___x_1984_, 0);
lean_inc(v_a_1990_);
lean_dec_ref(v___x_1984_);
v___y_1713_ = v_a_1757_;
v___y_1714_ = v___x_1914_;
v_a_1715_ = v_a_1990_;
goto v___jp_1712_;
}
}
case 1:
{
lean_object* v___x_1991_; 
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_declName_1362_);
lean_inc(v_mvarId_1363_);
v___x_1991_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1363_, v_declName_1362_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_a_1992_);
lean_dec_ref(v___x_1991_);
if (lean_obj_tag(v_a_1992_) == 1)
{
lean_object* v_val_1993_; lean_object* v___x_1994_; 
lean_del_object(v___x_1982_);
lean_dec(v_mvarId_1363_);
v_val_1993_ = lean_ctor_get(v_a_1992_, 0);
lean_inc(v_val_1993_);
lean_dec_ref(v_a_1992_);
v___x_1994_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v_a_1995_; uint8_t v___x_1996_; 
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
lean_inc(v_a_1995_);
lean_dec_ref(v___x_1994_);
v___x_1996_ = lean_unbox(v_a_1995_);
lean_dec(v_a_1995_);
if (v___x_1996_ == 0)
{
lean_object* v___x_1997_; 
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
v___x_1997_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1362_, v_val_1993_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1718_ = v_a_1757_;
v___y_1719_ = v___x_1914_;
v___y_1720_ = v___x_1997_;
goto v___jp_1717_;
}
else
{
lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1998_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25);
v___x_1999_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_1998_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v___x_2000_; 
lean_dec_ref(v___x_1999_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
v___x_2000_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1362_, v_val_1993_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1718_ = v_a_1757_;
v___y_1719_ = v___x_1914_;
v___y_1720_ = v___x_2000_;
goto v___jp_1717_;
}
else
{
lean_dec(v_val_1993_);
lean_dec(v_declName_1362_);
v___y_1718_ = v_a_1757_;
v___y_1719_ = v___x_1914_;
v___y_1720_ = v___x_1999_;
goto v___jp_1717_;
}
}
}
else
{
lean_object* v_a_2001_; 
lean_dec(v_val_1993_);
lean_dec(v_declName_1362_);
v_a_2001_ = lean_ctor_get(v___x_1994_, 0);
lean_inc(v_a_2001_);
lean_dec_ref(v___x_1994_);
v___y_1713_ = v_a_1757_;
v___y_1714_ = v___x_1914_;
v_a_1715_ = v_a_2001_;
goto v___jp_1712_;
}
}
else
{
lean_object* v___x_2002_; 
lean_dec(v_a_1992_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_mvarId_1363_);
v___x_2002_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_a_2003_);
lean_dec_ref(v___x_2002_);
if (lean_obj_tag(v_a_2003_) == 1)
{
lean_object* v_val_2004_; lean_object* v___x_2005_; 
lean_del_object(v___x_1982_);
lean_dec(v_mvarId_1363_);
v_val_2004_ = lean_ctor_get(v_a_2003_, 0);
lean_inc(v_val_2004_);
lean_dec_ref(v_a_2003_);
v___x_2005_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_object* v_a_2006_; uint8_t v___x_2007_; 
v_a_2006_ = lean_ctor_get(v___x_2005_, 0);
lean_inc(v_a_2006_);
lean_dec_ref(v___x_2005_);
v___x_2007_ = lean_unbox(v_a_2006_);
lean_dec(v_a_2006_);
if (v___x_2007_ == 0)
{
lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2008_ = lean_box(0);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
v___x_2009_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_2004_, v___x_1970_, v_declName_1362_, v___x_2008_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
lean_dec(v_val_2004_);
v___y_1718_ = v_a_1757_;
v___y_1719_ = v___x_1914_;
v___y_1720_ = v___x_2009_;
goto v___jp_1717_;
}
else
{
lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2010_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27);
v___x_2011_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_2010_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v_a_2012_; lean_object* v___x_2013_; 
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_a_2012_);
lean_dec_ref(v___x_2011_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
v___x_2013_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_2004_, v___x_1970_, v_declName_1362_, v_a_2012_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
lean_dec(v_val_2004_);
v___y_1718_ = v_a_1757_;
v___y_1719_ = v___x_1914_;
v___y_1720_ = v___x_2013_;
goto v___jp_1717_;
}
else
{
lean_dec(v_val_2004_);
lean_dec(v_declName_1362_);
v___y_1718_ = v_a_1757_;
v___y_1719_ = v___x_1914_;
v___y_1720_ = v___x_2011_;
goto v___jp_1717_;
}
}
}
else
{
lean_object* v_a_2014_; 
lean_dec(v_val_2004_);
lean_dec(v_declName_1362_);
v_a_2014_ = lean_ctor_get(v___x_2005_, 0);
lean_inc(v_a_2014_);
lean_dec_ref(v___x_2005_);
v___y_1713_ = v_a_1757_;
v___y_1714_ = v___x_1914_;
v_a_1715_ = v_a_2014_;
goto v___jp_1712_;
}
}
else
{
lean_object* v___x_2015_; 
lean_dec(v_a_2003_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_mvarId_1363_);
v___x_2015_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1363_, v___x_1759_, v___x_1759_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2037_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2018_ = v___x_2015_;
v_isShared_2019_ = v_isSharedCheck_2037_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_2015_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2037_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
if (lean_obj_tag(v_a_2016_) == 1)
{
lean_object* v_val_2020_; lean_object* v___x_2021_; 
lean_del_object(v___x_2018_);
lean_del_object(v___x_1982_);
lean_dec(v_mvarId_1363_);
v_val_2020_ = lean_ctor_get(v_a_2016_, 0);
lean_inc(v_val_2020_);
lean_dec_ref(v_a_2016_);
v___x_2021_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; uint8_t v___x_2023_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_a_2022_);
lean_dec_ref(v___x_2021_);
v___x_2023_ = lean_unbox(v_a_2022_);
lean_dec(v_a_2022_);
if (v___x_2023_ == 0)
{
lean_object* v___x_2024_; 
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
v___x_2024_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_declName_1362_, v_val_2020_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1718_ = v_a_1757_;
v___y_1719_ = v___x_1914_;
v___y_1720_ = v___x_2024_;
goto v___jp_1717_;
}
else
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2025_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29);
v___x_2026_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_2025_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v___x_2027_; 
lean_dec_ref(v___x_2026_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
v___x_2027_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_declName_1362_, v_val_2020_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1718_ = v_a_1757_;
v___y_1719_ = v___x_1914_;
v___y_1720_ = v___x_2027_;
goto v___jp_1717_;
}
else
{
lean_dec(v_val_2020_);
lean_dec(v_declName_1362_);
v___y_1718_ = v_a_1757_;
v___y_1719_ = v___x_1914_;
v___y_1720_ = v___x_2026_;
goto v___jp_1717_;
}
}
}
else
{
lean_object* v_a_2028_; 
lean_dec(v_val_2020_);
lean_dec(v_declName_1362_);
v_a_2028_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_a_2028_);
lean_dec_ref(v___x_2021_);
v___y_1713_ = v_a_1757_;
v___y_1714_ = v___x_1914_;
v_a_1715_ = v_a_2028_;
goto v___jp_1712_;
}
}
else
{
lean_object* v___x_2029_; lean_object* v___x_2031_; 
lean_dec(v_a_2016_);
lean_dec(v_declName_1362_);
v___x_2029_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31);
if (v_isShared_2019_ == 0)
{
lean_ctor_set_tag(v___x_2018_, 1);
lean_ctor_set(v___x_2018_, 0, v_mvarId_1363_);
v___x_2031_ = v___x_2018_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_mvarId_1363_);
v___x_2031_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
lean_object* v___x_2033_; 
if (v_isShared_1983_ == 0)
{
lean_ctor_set_tag(v___x_1982_, 7);
lean_ctor_set(v___x_1982_, 1, v___x_2031_);
lean_ctor_set(v___x_1982_, 0, v___x_2029_);
v___x_2033_ = v___x_1982_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2029_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v___x_2031_);
v___x_2033_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
lean_object* v___x_2034_; 
v___x_2034_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_2033_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1718_ = v_a_1757_;
v___y_1719_ = v___x_1914_;
v___y_1720_ = v___x_2034_;
goto v___jp_1717_;
}
}
}
}
}
else
{
lean_object* v_a_2038_; 
lean_del_object(v___x_1982_);
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_2038_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_a_2038_);
lean_dec_ref(v___x_2015_);
v___y_1713_ = v_a_1757_;
v___y_1714_ = v___x_1914_;
v_a_1715_ = v_a_2038_;
goto v___jp_1712_;
}
}
}
else
{
lean_object* v_a_2039_; 
lean_del_object(v___x_1982_);
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_2039_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_a_2039_);
lean_dec_ref(v___x_2002_);
v___y_1713_ = v_a_1757_;
v___y_1714_ = v___x_1914_;
v_a_1715_ = v_a_2039_;
goto v___jp_1712_;
}
}
}
else
{
lean_object* v_a_2040_; 
lean_del_object(v___x_1982_);
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_2040_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_a_2040_);
lean_dec_ref(v___x_1991_);
v___y_1713_ = v_a_1757_;
v___y_1714_ = v___x_1914_;
v_a_1715_ = v_a_2040_;
goto v___jp_1712_;
}
}
default: 
{
lean_object* v_mvarId_2041_; lean_object* v___x_2042_; 
lean_del_object(v___x_1982_);
lean_dec(v_mvarId_1363_);
v_mvarId_2041_ = lean_ctor_get(v_fst_1980_, 0);
lean_inc(v_mvarId_2041_);
lean_dec_ref(v_fst_1980_);
v___x_2042_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v_a_2043_; uint8_t v___x_2044_; 
v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
lean_inc(v_a_2043_);
lean_dec_ref(v___x_2042_);
v___x_2044_ = lean_unbox(v_a_2043_);
lean_dec(v_a_2043_);
if (v___x_2044_ == 0)
{
lean_object* v___x_2045_; 
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
v___x_2045_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1362_, v_mvarId_2041_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1718_ = v_a_1757_;
v___y_1719_ = v___x_1914_;
v___y_1720_ = v___x_2045_;
goto v___jp_1717_;
}
else
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33);
v___x_2047_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_2046_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v___x_2048_; 
lean_dec_ref(v___x_2047_);
lean_inc(v_a_1367_);
lean_inc_ref(v_a_1366_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
v___x_2048_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1362_, v_mvarId_2041_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1718_ = v_a_1757_;
v___y_1719_ = v___x_1914_;
v___y_1720_ = v___x_2048_;
goto v___jp_1717_;
}
else
{
lean_dec(v_mvarId_2041_);
lean_dec(v_declName_1362_);
v___y_1718_ = v_a_1757_;
v___y_1719_ = v___x_1914_;
v___y_1720_ = v___x_2047_;
goto v___jp_1717_;
}
}
}
else
{
lean_object* v_a_2049_; 
lean_dec(v_mvarId_2041_);
lean_dec(v_declName_1362_);
v_a_2049_ = lean_ctor_get(v___x_2042_, 0);
lean_inc(v_a_2049_);
lean_dec_ref(v___x_2042_);
v___y_1713_ = v_a_1757_;
v___y_1714_ = v___x_1914_;
v_a_1715_ = v_a_2049_;
goto v___jp_1712_;
}
}
}
}
}
else
{
lean_object* v_a_2052_; 
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_2052_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_a_2052_);
lean_dec_ref(v___x_1978_);
v___y_1713_ = v_a_1757_;
v___y_1714_ = v___x_1914_;
v_a_1715_ = v_a_2052_;
goto v___jp_1712_;
}
}
else
{
lean_object* v_a_2053_; 
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_2053_ = lean_ctor_get(v___x_1975_, 0);
lean_inc(v_a_2053_);
lean_dec_ref(v___x_1975_);
v___y_1713_ = v_a_1757_;
v___y_1714_ = v___x_1914_;
v_a_1715_ = v_a_2053_;
goto v___jp_1712_;
}
}
}
else
{
lean_object* v_a_2054_; 
lean_dec(v_a_1919_);
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_2054_ = lean_ctor_get(v___x_1943_, 0);
lean_inc(v_a_2054_);
lean_dec_ref(v___x_1943_);
v___y_1713_ = v_a_1757_;
v___y_1714_ = v___x_1914_;
v_a_1715_ = v_a_2054_;
goto v___jp_1712_;
}
}
}
else
{
lean_object* v_a_2055_; 
lean_dec(v_a_1919_);
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_2055_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_2055_);
lean_dec_ref(v___x_1932_);
v___y_1713_ = v_a_1757_;
v___y_1714_ = v___x_1914_;
v_a_1715_ = v_a_2055_;
goto v___jp_1712_;
}
}
}
else
{
lean_object* v_a_2056_; 
lean_dec(v_a_1919_);
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_2056_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_a_2056_);
lean_dec_ref(v___x_1921_);
v___y_1713_ = v_a_1757_;
v___y_1714_ = v___x_1914_;
v_a_1715_ = v_a_2056_;
goto v___jp_1712_;
}
}
else
{
lean_object* v___x_2057_; 
lean_dec(v_a_1919_);
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v___x_2057_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v_a_2058_; uint8_t v___x_2059_; 
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
lean_inc(v_a_2058_);
lean_dec_ref(v___x_2057_);
v___x_2059_ = lean_unbox(v_a_2058_);
lean_dec(v_a_2058_);
if (v___x_2059_ == 0)
{
lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2060_ = lean_box(0);
v___x_2061_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_2060_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1718_ = v_a_1757_;
v___y_1719_ = v___x_1914_;
v___y_1720_ = v___x_2061_;
goto v___jp_1717_;
}
else
{
lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2062_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35);
v___x_2063_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_2062_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_a_2064_; lean_object* v___x_2065_; 
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2064_);
lean_dec_ref(v___x_2063_);
v___x_2065_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_2064_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1718_ = v_a_1757_;
v___y_1719_ = v___x_1914_;
v___y_1720_ = v___x_2065_;
goto v___jp_1717_;
}
else
{
v___y_1718_ = v_a_1757_;
v___y_1719_ = v___x_1914_;
v___y_1720_ = v___x_2063_;
goto v___jp_1717_;
}
}
}
else
{
lean_object* v_a_2066_; 
v_a_2066_ = lean_ctor_get(v___x_2057_, 0);
lean_inc(v_a_2066_);
lean_dec_ref(v___x_2057_);
v___y_1713_ = v_a_1757_;
v___y_1714_ = v___x_1914_;
v_a_1715_ = v_a_2066_;
goto v___jp_1712_;
}
}
}
else
{
lean_object* v_a_2067_; 
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_2067_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_a_2067_);
lean_dec_ref(v___x_1918_);
v___y_1713_ = v_a_1757_;
v___y_1714_ = v___x_1914_;
v_a_1715_ = v_a_2067_;
goto v___jp_1712_;
}
}
else
{
lean_object* v___x_2068_; 
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v___x_2068_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1383_, v_a_1366_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_object* v_a_2069_; uint8_t v___x_2070_; 
v_a_2069_ = lean_ctor_get(v___x_2068_, 0);
lean_inc(v_a_2069_);
lean_dec_ref(v___x_2068_);
v___x_2070_ = lean_unbox(v_a_2069_);
lean_dec(v_a_2069_);
if (v___x_2070_ == 0)
{
lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2071_ = lean_box(0);
v___x_2072_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_2071_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1718_ = v_a_1757_;
v___y_1719_ = v___x_1914_;
v___y_1720_ = v___x_2072_;
goto v___jp_1717_;
}
else
{
lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2073_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37);
v___x_2074_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1383_, v___x_2073_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; lean_object* v___x_2076_; 
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_a_2075_);
lean_dec_ref(v___x_2074_);
v___x_2076_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_2075_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
v___y_1718_ = v_a_1757_;
v___y_1719_ = v___x_1914_;
v___y_1720_ = v___x_2076_;
goto v___jp_1717_;
}
else
{
v___y_1718_ = v_a_1757_;
v___y_1719_ = v___x_1914_;
v___y_1720_ = v___x_2074_;
goto v___jp_1717_;
}
}
}
else
{
lean_object* v_a_2077_; 
v_a_2077_ = lean_ctor_get(v___x_2068_, 0);
lean_inc(v_a_2077_);
lean_dec_ref(v___x_2068_);
v___y_1713_ = v_a_1757_;
v___y_1714_ = v___x_1914_;
v_a_1715_ = v_a_2077_;
goto v___jp_1712_;
}
}
}
else
{
lean_object* v_a_2078_; 
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_2078_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_2078_);
lean_dec_ref(v___x_1915_);
v___y_1713_ = v_a_1757_;
v___y_1714_ = v___x_1914_;
v_a_1715_ = v_a_2078_;
goto v___jp_1712_;
}
}
}
else
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2086_; 
lean_dec_ref(v___f_1692_);
lean_dec(v_a_1691_);
lean_dec_ref(v_options_1381_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_2079_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2081_ = v___x_1756_;
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_1756_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2084_; 
if (v_isShared_2082_ == 0)
{
v___x_2084_ = v___x_2081_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_a_2079_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
}
}
else
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2404_; 
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_mvarId_1363_);
lean_dec(v_declName_1362_);
v_a_2397_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2399_ = v___x_1690_;
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_1690_);
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
v___jp_1369_:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = lean_box(0);
v___x_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1370_);
return v___x_1371_;
}
v___jp_1372_:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = lean_box(0);
v___x_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1373_);
return v___x_1374_;
}
v___jp_1375_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = lean_box(0);
v___x_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1376_);
return v___x_1377_;
}
v___jp_1378_:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1379_ = lean_box(0);
v___x_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1379_);
return v___x_1380_;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(lean_object* v_declName_2405_, lean_object* v_as_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
if (lean_obj_tag(v_as_2406_) == 0)
{
lean_object* v___x_2412_; lean_object* v___x_2413_; 
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v_declName_2405_);
v___x_2412_ = lean_box(0);
v___x_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2412_);
return v___x_2413_;
}
else
{
lean_object* v_head_2414_; lean_object* v_tail_2415_; lean_object* v___x_2416_; 
v_head_2414_ = lean_ctor_get(v_as_2406_, 0);
lean_inc(v_head_2414_);
v_tail_2415_ = lean_ctor_get(v_as_2406_, 1);
lean_inc(v_tail_2415_);
lean_dec_ref(v_as_2406_);
lean_inc(v___y_2410_);
lean_inc_ref(v___y_2409_);
lean_inc(v___y_2408_);
lean_inc_ref(v___y_2407_);
lean_inc(v_declName_2405_);
v___x_2416_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2405_, v_head_2414_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_dec_ref(v___x_2416_);
v_as_2406_ = v_tail_2415_;
goto _start;
}
else
{
lean_dec(v_tail_2415_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v_declName_2405_);
return v___x_2416_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___boxed(lean_object* v_declName_2418_, lean_object* v_as_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_){
_start:
{
lean_object* v_res_2425_; 
v_res_2425_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_declName_2418_, v_as_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
return v_res_2425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___boxed(lean_object* v_declName_2426_, lean_object* v_as_2427_, lean_object* v_i_2428_, lean_object* v_stop_2429_, lean_object* v_b_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
size_t v_i_boxed_2436_; size_t v_stop_boxed_2437_; lean_object* v_res_2438_; 
v_i_boxed_2436_ = lean_unbox_usize(v_i_2428_);
lean_dec(v_i_2428_);
v_stop_boxed_2437_ = lean_unbox_usize(v_stop_2429_);
lean_dec(v_stop_2429_);
v_res_2438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_2426_, v_as_2427_, v_i_boxed_2436_, v_stop_boxed_2437_, v_b_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_);
lean_dec_ref(v_as_2427_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5___boxed(lean_object* v_val_2439_, lean_object* v___x_2440_, lean_object* v_declName_2441_, lean_object* v_____r_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_2439_, v___x_2440_, v_declName_2441_, v_____r_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
lean_dec(v___x_2440_);
lean_dec_ref(v_val_2439_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___boxed(lean_object* v_declName_2449_, lean_object* v_mvarId_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2449_, v_mvarId_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__8(lean_object* v_00_u03b1_2457_, lean_object* v_x_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_){
_start:
{
lean_object* v___x_2464_; 
v___x_2464_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__8___redArg(v_x_2458_);
return v___x_2464_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__8___boxed(lean_object* v_00_u03b1_2465_, lean_object* v_x_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
lean_object* v_res_2472_; 
v_res_2472_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__8(v_00_u03b1_2465_, v_x_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
return v_res_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(lean_object* v_constName_2473_, uint8_t v_skipRealize_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v___x_2477_; lean_object* v_env_2478_; uint8_t v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2477_ = lean_st_ref_get(v___y_2475_);
v_env_2478_ = lean_ctor_get(v___x_2477_, 0);
lean_inc_ref(v_env_2478_);
lean_dec(v___x_2477_);
v___x_2479_ = l_Lean_Environment_contains(v_env_2478_, v_constName_2473_, v_skipRealize_2474_);
v___x_2480_ = lean_box(v___x_2479_);
v___x_2481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2480_);
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg___boxed(lean_object* v_constName_2482_, lean_object* v_skipRealize_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_){
_start:
{
uint8_t v_skipRealize_boxed_2486_; lean_object* v_res_2487_; 
v_skipRealize_boxed_2486_ = lean_unbox(v_skipRealize_2483_);
v_res_2487_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(v_constName_2482_, v_skipRealize_boxed_2486_, v___y_2484_);
lean_dec(v___y_2484_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0(lean_object* v_constName_2488_, uint8_t v_skipRealize_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
lean_object* v___x_2495_; 
v___x_2495_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(v_constName_2488_, v_skipRealize_2489_, v___y_2493_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___boxed(lean_object* v_constName_2496_, lean_object* v_skipRealize_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
uint8_t v_skipRealize_boxed_2503_; lean_object* v_res_2504_; 
v_skipRealize_boxed_2503_ = lean_unbox(v_skipRealize_2497_);
v_res_2504_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0(v_constName_2496_, v_skipRealize_boxed_2503_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0(lean_object* v_snd_2505_, lean_object* v___x_2506_, lean_object* v___x_2507_, lean_object* v_snd_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
lean_object* v___x_2514_; 
lean_inc(v___y_2512_);
lean_inc_ref(v___y_2511_);
lean_inc(v___y_2510_);
lean_inc_ref(v___y_2509_);
lean_inc_ref(v_snd_2505_);
v___x_2514_ = l_Lean_Meta_mkCongrArg(v_snd_2505_, v___x_2506_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v_a_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_a_2515_);
lean_dec_ref(v___x_2514_);
v___x_2516_ = l_Lean_Expr_app___override(v_snd_2505_, v___x_2507_);
v___x_2517_ = l_Lean_MVarId_replaceTargetEq(v_snd_2508_, v___x_2516_, v_a_2515_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
return v___x_2517_;
}
else
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2525_; 
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v_snd_2508_);
lean_dec_ref(v___x_2507_);
lean_dec_ref(v_snd_2505_);
v_a_2518_ = lean_ctor_get(v___x_2514_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2520_ = v___x_2514_;
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2514_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
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
return v___x_2523_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0___boxed(lean_object* v_snd_2526_, lean_object* v___x_2527_, lean_object* v___x_2528_, lean_object* v_snd_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
lean_object* v_res_2535_; 
v_res_2535_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0(v_snd_2526_, v___x_2527_, v___x_2528_, v_snd_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
return v_res_2535_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2541_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__3));
v___x_2542_ = l_Lean_stringToMessageData(v___x_2541_);
return v___x_2542_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6(void){
_start:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2544_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__5));
v___x_2545_ = l_Lean_stringToMessageData(v___x_2544_);
return v___x_2545_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8(void){
_start:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2547_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__7));
v___x_2548_ = l_Lean_stringToMessageData(v___x_2547_);
return v___x_2548_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10(void){
_start:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2550_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__9));
v___x_2551_ = l_Lean_stringToMessageData(v___x_2550_);
return v___x_2551_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12(void){
_start:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2553_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__11));
v___x_2554_ = l_Lean_stringToMessageData(v___x_2553_);
return v___x_2554_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14(void){
_start:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2556_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__13));
v___x_2557_ = l_Lean_stringToMessageData(v___x_2556_);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1(lean_object* v_mvarId_2558_, lean_object* v_cls_2559_, lean_object* v___x_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_){
_start:
{
lean_object* v___x_2566_; 
lean_inc(v_mvarId_2558_);
v___x_2566_ = l_Lean_MVarId_getType(v_mvarId_2558_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; lean_object* v___x_2568_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
lean_inc(v_a_2567_);
lean_dec_ref(v___x_2566_);
lean_inc(v___y_2564_);
lean_inc_ref(v___y_2563_);
lean_inc(v___y_2562_);
lean_inc_ref(v___y_2561_);
v___x_2568_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS(v_a_2567_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v_a_2569_; lean_object* v_fst_2570_; lean_object* v_snd_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2721_; 
v_a_2569_ = lean_ctor_get(v___x_2568_, 0);
lean_inc(v_a_2569_);
lean_dec_ref(v___x_2568_);
v_fst_2570_ = lean_ctor_get(v_a_2569_, 0);
v_snd_2571_ = lean_ctor_get(v_a_2569_, 1);
v_isSharedCheck_2721_ = !lean_is_exclusive(v_a_2569_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2573_ = v_a_2569_;
v_isShared_2574_ = v_isSharedCheck_2721_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_snd_2571_);
lean_inc(v_fst_2570_);
lean_dec(v_a_2569_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2721_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; uint8_t v___x_2579_; lean_object* v___x_2580_; lean_object* v_a_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2720_; 
v___x_2575_ = l_Lean_Expr_getAppFn(v_fst_2570_);
v___x_2576_ = l_Lean_Expr_constName_x21(v___x_2575_);
v___x_2577_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__0));
v___x_2578_ = l_Lean_Name_str___override(v___x_2576_, v___x_2577_);
v___x_2579_ = 1;
lean_inc(v___x_2578_);
v___x_2580_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(v___x_2578_, v___x_2579_, v___y_2564_);
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2583_ = v___x_2580_;
v_isShared_2584_ = v_isSharedCheck_2720_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_a_2581_);
lean_dec(v___x_2580_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2720_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v_nargs_2585_; lean_object* v___x_2586_; lean_object* v_dummy_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___y_2593_; lean_object* v___y_2594_; uint8_t v___y_2595_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v___y_2636_; uint8_t v___x_2703_; 
v_nargs_2585_ = l_Lean_Expr_getAppNumArgs(v_fst_2570_);
v___x_2586_ = l_Lean_Expr_constLevels_x21(v___x_2575_);
lean_dec_ref(v___x_2575_);
v_dummy_2587_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0);
lean_inc(v_nargs_2585_);
v___x_2588_ = lean_mk_array(v_nargs_2585_, v_dummy_2587_);
v___x_2589_ = lean_unsigned_to_nat(1u);
v___x_2590_ = lean_nat_sub(v_nargs_2585_, v___x_2589_);
lean_dec(v_nargs_2585_);
v___x_2591_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_fst_2570_, v___x_2588_, v___x_2590_);
v___x_2703_ = lean_unbox(v_a_2581_);
lean_dec(v_a_2581_);
if (v___x_2703_ == 0)
{
lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v_a_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2719_; 
lean_dec_ref(v___x_2591_);
lean_dec(v___x_2586_);
lean_del_object(v___x_2583_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
lean_dec_ref(v___x_2560_);
lean_dec(v_cls_2559_);
v___x_2704_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12);
v___x_2705_ = l_Lean_MessageData_ofName(v___x_2578_);
v___x_2706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2704_);
lean_ctor_set(v___x_2706_, 1, v___x_2705_);
v___x_2707_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14);
v___x_2708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2706_);
lean_ctor_set(v___x_2708_, 1, v___x_2707_);
v___x_2709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2709_, 0, v_mvarId_2558_);
v___x_2710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2708_);
lean_ctor_set(v___x_2710_, 1, v___x_2709_);
v___x_2711_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_2710_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_);
lean_dec(v___y_2564_);
lean_dec_ref(v___y_2563_);
lean_dec(v___y_2562_);
lean_dec_ref(v___y_2561_);
v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2714_ = v___x_2711_;
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_a_2712_);
lean_dec(v___x_2711_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v___x_2717_; 
if (v_isShared_2715_ == 0)
{
v___x_2717_ = v___x_2714_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_a_2712_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
return v___x_2717_;
}
}
}
else
{
v___y_2633_ = v___y_2561_;
v___y_2634_ = v___y_2562_;
v___y_2635_ = v___y_2563_;
v___y_2636_ = v___y_2564_;
goto v___jp_2632_;
}
v___jp_2592_:
{
lean_object* v___x_2601_; 
lean_inc(v___y_2600_);
lean_inc_ref(v___y_2599_);
lean_inc(v___y_2598_);
lean_inc_ref(v___y_2597_);
lean_inc_ref(v___y_2596_);
v___x_2601_ = lean_infer_type(v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v_a_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
lean_inc(v_a_2602_);
lean_dec_ref(v___x_2601_);
v___x_2603_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__2));
lean_inc(v___y_2600_);
lean_inc_ref(v___y_2599_);
lean_inc(v___y_2598_);
lean_inc_ref(v___y_2597_);
v___x_2604_ = l_Lean_MVarId_define(v_mvarId_2558_, v___x_2603_, v_a_2602_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v_a_2605_; lean_object* v___x_2606_; 
v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_a_2605_);
lean_dec_ref(v___x_2604_);
lean_inc(v___y_2600_);
lean_inc_ref(v___y_2599_);
lean_inc(v___y_2598_);
lean_inc_ref(v___y_2597_);
v___x_2606_ = l_Lean_Meta_intro1Core(v_a_2605_, v___y_2595_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v_a_2607_; lean_object* v_fst_2608_; lean_object* v_snd_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___f_2614_; lean_object* v___x_2615_; 
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_a_2607_);
lean_dec_ref(v___x_2606_);
v_fst_2608_ = lean_ctor_get(v_a_2607_, 0);
lean_inc(v_fst_2608_);
v_snd_2609_ = lean_ctor_get(v_a_2607_, 1);
lean_inc(v_snd_2609_);
lean_dec(v_a_2607_);
v___x_2610_ = l_Lean_Expr_appFn_x21(v___y_2593_);
lean_dec_ref(v___y_2593_);
v___x_2611_ = l_Lean_mkFVar(v_fst_2608_);
v___x_2612_ = l_Lean_Expr_app___override(v___x_2610_, v___x_2611_);
v___x_2613_ = l_Lean_mkAppN(v___y_2594_, v___x_2591_);
lean_dec_ref(v___x_2591_);
lean_inc(v_snd_2609_);
v___f_2614_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2614_, 0, v_snd_2571_);
lean_closure_set(v___f_2614_, 1, v___x_2613_);
lean_closure_set(v___f_2614_, 2, v___x_2612_);
lean_closure_set(v___f_2614_, 3, v_snd_2609_);
v___x_2615_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_snd_2609_, v___f_2614_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_);
return v___x_2615_;
}
else
{
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2623_; 
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
lean_dec_ref(v___y_2594_);
lean_dec_ref(v___y_2593_);
lean_dec_ref(v___x_2591_);
lean_dec(v_snd_2571_);
v_a_2616_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2618_ = v___x_2606_;
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2606_);
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
else
{
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
lean_dec_ref(v___y_2594_);
lean_dec_ref(v___y_2593_);
lean_dec_ref(v___x_2591_);
lean_dec(v_snd_2571_);
return v___x_2604_;
}
}
else
{
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2631_; 
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec_ref(v___y_2594_);
lean_dec_ref(v___y_2593_);
lean_dec_ref(v___x_2591_);
lean_dec(v_snd_2571_);
lean_dec(v_mvarId_2558_);
v_a_2624_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2626_ = v___x_2601_;
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v___x_2601_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2629_; 
if (v_isShared_2627_ == 0)
{
v___x_2629_ = v___x_2626_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_a_2624_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
}
v___jp_2632_:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; 
lean_inc(v___x_2578_);
v___x_2637_ = l_Lean_mkConst(v___x_2578_, v___x_2586_);
lean_inc(v___y_2636_);
lean_inc_ref(v___y_2635_);
lean_inc(v___y_2634_);
lean_inc_ref(v___y_2633_);
lean_inc_ref(v___x_2637_);
v___x_2638_ = lean_infer_type(v___x_2637_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v_a_2639_; lean_object* v___x_2640_; 
v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
lean_inc(v_a_2639_);
lean_dec_ref(v___x_2638_);
lean_inc(v___y_2636_);
lean_inc_ref(v___y_2635_);
lean_inc(v___y_2634_);
lean_inc_ref(v___y_2633_);
v___x_2640_ = l_Lean_Meta_instantiateForall(v_a_2639_, v___x_2591_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v_a_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; uint8_t v___x_2644_; 
v_a_2641_ = lean_ctor_get(v___x_2640_, 0);
lean_inc(v_a_2641_);
lean_dec_ref(v___x_2640_);
v___x_2642_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__1));
v___x_2643_ = lean_unsigned_to_nat(3u);
v___x_2644_ = l_Lean_Expr_isAppOfArity(v_a_2641_, v___x_2642_, v___x_2643_);
if (v___x_2644_ == 0)
{
lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2648_; 
lean_dec(v_a_2641_);
lean_dec_ref(v___x_2637_);
lean_dec_ref(v___x_2591_);
lean_dec(v_snd_2571_);
lean_dec_ref(v___x_2560_);
lean_dec(v_cls_2559_);
v___x_2645_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4);
v___x_2646_ = l_Lean_MessageData_ofName(v___x_2578_);
if (v_isShared_2574_ == 0)
{
lean_ctor_set_tag(v___x_2573_, 7);
lean_ctor_set(v___x_2573_, 1, v___x_2646_);
lean_ctor_set(v___x_2573_, 0, v___x_2645_);
v___x_2648_ = v___x_2573_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v___x_2645_);
lean_ctor_set(v_reuseFailAlloc_2656_, 1, v___x_2646_);
v___x_2648_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2652_; 
v___x_2649_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6);
v___x_2650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2648_);
lean_ctor_set(v___x_2650_, 1, v___x_2649_);
if (v_isShared_2584_ == 0)
{
lean_ctor_set_tag(v___x_2583_, 1);
lean_ctor_set(v___x_2583_, 0, v_mvarId_2558_);
v___x_2652_ = v___x_2583_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_mvarId_2558_);
v___x_2652_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2650_);
lean_ctor_set(v___x_2653_, 1, v___x_2652_);
v___x_2654_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_2653_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
return v___x_2654_;
}
}
}
else
{
lean_object* v___x_2657_; lean_object* v_a_2658_; lean_object* v___x_2659_; lean_object* v_nargs_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; uint8_t v___x_2667_; 
lean_del_object(v___x_2583_);
lean_dec(v___x_2578_);
lean_inc(v_cls_2559_);
v___x_2657_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_2559_, v___y_2635_);
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
lean_inc(v_a_2658_);
lean_dec_ref(v___x_2657_);
v___x_2659_ = l_Lean_Expr_appArg_x21(v_a_2641_);
lean_dec(v_a_2641_);
v_nargs_2660_ = l_Lean_Expr_getAppNumArgs(v___x_2659_);
lean_inc(v_nargs_2660_);
v___x_2661_ = lean_mk_array(v_nargs_2660_, v_dummy_2587_);
v___x_2662_ = lean_nat_sub(v_nargs_2660_, v___x_2589_);
lean_dec(v_nargs_2660_);
lean_inc_ref(v___x_2659_);
v___x_2663_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_2659_, v___x_2661_, v___x_2662_);
v___x_2664_ = lean_array_get_size(v___x_2663_);
v___x_2665_ = lean_nat_sub(v___x_2664_, v___x_2589_);
v___x_2666_ = lean_array_get(v___x_2560_, v___x_2663_, v___x_2665_);
lean_dec(v___x_2665_);
lean_dec_ref(v___x_2663_);
v___x_2667_ = lean_unbox(v_a_2658_);
lean_dec(v_a_2658_);
if (v___x_2667_ == 0)
{
lean_del_object(v___x_2573_);
lean_dec(v_cls_2559_);
v___y_2593_ = v___x_2659_;
v___y_2594_ = v___x_2637_;
v___y_2595_ = v___x_2644_;
v___y_2596_ = v___x_2666_;
v___y_2597_ = v___y_2633_;
v___y_2598_ = v___y_2634_;
v___y_2599_ = v___y_2635_;
v___y_2600_ = v___y_2636_;
goto v___jp_2592_;
}
else
{
lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2672_; 
v___x_2668_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8);
v___x_2669_ = lean_unsigned_to_nat(30u);
lean_inc(v___x_2666_);
v___x_2670_ = l_Lean_inlineExpr(v___x_2666_, v___x_2669_);
if (v_isShared_2574_ == 0)
{
lean_ctor_set_tag(v___x_2573_, 7);
lean_ctor_set(v___x_2573_, 1, v___x_2670_);
lean_ctor_set(v___x_2573_, 0, v___x_2668_);
v___x_2672_ = v___x_2573_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v___x_2668_);
lean_ctor_set(v_reuseFailAlloc_2686_, 1, v___x_2670_);
v___x_2672_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2673_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10);
v___x_2674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2672_);
lean_ctor_set(v___x_2674_, 1, v___x_2673_);
lean_inc_ref(v___x_2659_);
v___x_2675_ = l_Lean_indentExpr(v___x_2659_);
v___x_2676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2674_);
lean_ctor_set(v___x_2676_, 1, v___x_2675_);
v___x_2677_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_2559_, v___x_2676_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_dec_ref(v___x_2677_);
v___y_2593_ = v___x_2659_;
v___y_2594_ = v___x_2637_;
v___y_2595_ = v___x_2644_;
v___y_2596_ = v___x_2666_;
v___y_2597_ = v___y_2633_;
v___y_2598_ = v___y_2634_;
v___y_2599_ = v___y_2635_;
v___y_2600_ = v___y_2636_;
goto v___jp_2592_;
}
else
{
lean_object* v_a_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2685_; 
lean_dec(v___x_2666_);
lean_dec_ref(v___x_2659_);
lean_dec_ref(v___x_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec_ref(v___x_2591_);
lean_dec(v_snd_2571_);
lean_dec(v_mvarId_2558_);
v_a_2678_ = lean_ctor_get(v___x_2677_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2680_ = v___x_2677_;
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_a_2678_);
lean_dec(v___x_2677_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2683_; 
if (v_isShared_2681_ == 0)
{
v___x_2683_ = v___x_2680_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_a_2678_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2694_; 
lean_dec_ref(v___x_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec_ref(v___x_2591_);
lean_del_object(v___x_2583_);
lean_dec(v___x_2578_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
lean_dec_ref(v___x_2560_);
lean_dec(v_cls_2559_);
lean_dec(v_mvarId_2558_);
v_a_2687_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2689_ = v___x_2640_;
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_a_2687_);
lean_dec(v___x_2640_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2692_; 
if (v_isShared_2690_ == 0)
{
v___x_2692_ = v___x_2689_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_a_2687_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
}
else
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2702_; 
lean_dec_ref(v___x_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec_ref(v___x_2591_);
lean_del_object(v___x_2583_);
lean_dec(v___x_2578_);
lean_del_object(v___x_2573_);
lean_dec(v_snd_2571_);
lean_dec_ref(v___x_2560_);
lean_dec(v_cls_2559_);
lean_dec(v_mvarId_2558_);
v_a_2695_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2697_ = v___x_2638_;
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2638_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
if (v_isShared_2698_ == 0)
{
v___x_2700_ = v___x_2697_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_a_2695_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2729_; 
lean_dec(v___y_2564_);
lean_dec_ref(v___y_2563_);
lean_dec(v___y_2562_);
lean_dec_ref(v___y_2561_);
lean_dec_ref(v___x_2560_);
lean_dec(v_cls_2559_);
lean_dec(v_mvarId_2558_);
v_a_2722_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2724_ = v___x_2568_;
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2568_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2727_; 
if (v_isShared_2725_ == 0)
{
v___x_2727_ = v___x_2724_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_a_2722_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
else
{
lean_object* v_a_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2737_; 
lean_dec(v___y_2564_);
lean_dec_ref(v___y_2563_);
lean_dec(v___y_2562_);
lean_dec_ref(v___y_2561_);
lean_dec_ref(v___x_2560_);
lean_dec(v_cls_2559_);
lean_dec(v_mvarId_2558_);
v_a_2730_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2732_ = v___x_2566_;
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_a_2730_);
lean_dec(v___x_2566_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2735_; 
if (v_isShared_2733_ == 0)
{
v___x_2735_ = v___x_2732_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_a_2730_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___boxed(lean_object* v_mvarId_2738_, lean_object* v_cls_2739_, lean_object* v___x_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_){
_start:
{
lean_object* v_res_2746_; 
v_res_2746_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1(v_mvarId_2738_, v_cls_2739_, v___x_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
return v_res_2746_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2748_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__0));
v___x_2749_ = l_Lean_stringToMessageData(v___x_2748_);
return v___x_2749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2(lean_object* v_mvarId_2750_, lean_object* v_x_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_){
_start:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2757_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1);
v___x_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2758_, 0, v_mvarId_2750_);
v___x_2759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2757_);
lean_ctor_set(v___x_2759_, 1, v___x_2758_);
v___x_2760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2759_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___boxed(lean_object* v_mvarId_2761_, lean_object* v_x_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2(v_mvarId_2761_, v_x_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2765_);
lean_dec(v___y_2764_);
lean_dec_ref(v___y_2763_);
lean_dec_ref(v_x_2762_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(lean_object* v_declName_2769_, lean_object* v_mvarId_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_){
_start:
{
lean_object* v_options_2776_; uint8_t v_hasTrace_2777_; lean_object* v___x_2778_; lean_object* v_cls_2779_; lean_object* v___f_2780_; 
v_options_2776_ = lean_ctor_get(v_a_2773_, 2);
v_hasTrace_2777_ = lean_ctor_get_uint8(v_options_2776_, sizeof(void*)*1);
v___x_2778_ = l_Lean_instInhabitedExpr;
v_cls_2779_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4));
lean_inc(v_mvarId_2770_);
v___f_2780_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___boxed), 8, 3);
lean_closure_set(v___f_2780_, 0, v_mvarId_2770_);
lean_closure_set(v___f_2780_, 1, v_cls_2779_);
lean_closure_set(v___f_2780_, 2, v___x_2778_);
if (v_hasTrace_2777_ == 0)
{
lean_object* v___x_2781_; 
lean_inc(v_a_2774_);
lean_inc_ref(v_a_2773_);
lean_inc(v_a_2772_);
lean_inc_ref(v_a_2771_);
v___x_2781_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2770_, v___f_2780_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_);
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v_a_2782_; lean_object* v___x_2783_; 
v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
lean_inc(v_a_2782_);
lean_dec_ref(v___x_2781_);
v___x_2783_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2769_, v_a_2782_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_);
return v___x_2783_;
}
else
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2791_; 
lean_dec(v_a_2774_);
lean_dec_ref(v_a_2773_);
lean_dec(v_a_2772_);
lean_dec_ref(v_a_2771_);
lean_dec(v_declName_2769_);
v_a_2784_ = lean_ctor_get(v___x_2781_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2786_ = v___x_2781_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2781_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
if (v_isShared_2787_ == 0)
{
v___x_2789_ = v___x_2786_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
}
else
{
lean_object* v___x_2792_; lean_object* v_a_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2887_; 
v___x_2792_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_2779_, v_a_2773_);
v_a_2793_ = lean_ctor_get(v___x_2792_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2795_ = v___x_2792_;
v_isShared_2796_ = v_isSharedCheck_2887_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v___x_2792_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2887_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___f_2797_; lean_object* v___x_2798_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v_a_2802_; lean_object* v___y_2816_; lean_object* v___y_2817_; lean_object* v_a_2818_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v_a_2825_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v_a_2838_; uint8_t v___x_2873_; 
lean_inc(v_mvarId_2770_);
v___f_2797_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2797_, 0, v_mvarId_2770_);
v___x_2798_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___closed__0));
v___x_2873_ = lean_unbox(v_a_2793_);
if (v___x_2873_ == 0)
{
lean_object* v___x_2874_; uint8_t v___x_2875_; 
v___x_2874_ = l_Lean_trace_profiler;
v___x_2875_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_options_2776_, v___x_2874_);
if (v___x_2875_ == 0)
{
lean_object* v___x_2876_; 
lean_dec_ref(v___f_2797_);
lean_del_object(v___x_2795_);
lean_dec(v_a_2793_);
lean_inc(v_a_2774_);
lean_inc_ref(v_a_2773_);
lean_inc(v_a_2772_);
lean_inc_ref(v_a_2771_);
v___x_2876_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2770_, v___f_2780_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_);
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_object* v_a_2877_; lean_object* v___x_2878_; 
v_a_2877_ = lean_ctor_get(v___x_2876_, 0);
lean_inc(v_a_2877_);
lean_dec_ref(v___x_2876_);
v___x_2878_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2769_, v_a_2877_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_);
return v___x_2878_;
}
else
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2886_; 
lean_dec(v_a_2774_);
lean_dec_ref(v_a_2773_);
lean_dec(v_a_2772_);
lean_dec_ref(v_a_2771_);
lean_dec(v_declName_2769_);
v_a_2879_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2881_ = v___x_2876_;
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2876_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2884_; 
if (v_isShared_2882_ == 0)
{
v___x_2884_ = v___x_2881_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2879_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
}
else
{
lean_inc_ref(v_options_2776_);
goto v___jp_2840_;
}
}
else
{
lean_inc_ref(v_options_2776_);
goto v___jp_2840_;
}
v___jp_2799_:
{
lean_object* v___x_2803_; double v___x_2804_; double v___x_2805_; double v___x_2806_; double v___x_2807_; double v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; uint8_t v___x_2813_; lean_object* v___x_2814_; 
v___x_2803_ = lean_io_mono_nanos_now();
v___x_2804_ = lean_float_of_nat(v___y_2801_);
v___x_2805_ = lean_float_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38);
v___x_2806_ = lean_float_div(v___x_2804_, v___x_2805_);
v___x_2807_ = lean_float_of_nat(v___x_2803_);
v___x_2808_ = lean_float_div(v___x_2807_, v___x_2805_);
v___x_2809_ = lean_box_float(v___x_2806_);
v___x_2810_ = lean_box_float(v___x_2808_);
v___x_2811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2811_, 0, v___x_2809_);
lean_ctor_set(v___x_2811_, 1, v___x_2810_);
v___x_2812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2812_, 0, v_a_2802_);
lean_ctor_set(v___x_2812_, 1, v___x_2811_);
v___x_2813_ = lean_unbox(v_a_2793_);
lean_dec(v_a_2793_);
v___x_2814_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6(v_cls_2779_, v_hasTrace_2777_, v___x_2798_, v_options_2776_, v___x_2813_, v___y_2800_, v___f_2797_, v___x_2812_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_);
lean_dec_ref(v_options_2776_);
return v___x_2814_;
}
v___jp_2815_:
{
lean_object* v___x_2820_; 
if (v_isShared_2796_ == 0)
{
lean_ctor_set(v___x_2795_, 0, v_a_2818_);
v___x_2820_ = v___x_2795_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2818_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
v___y_2800_ = v___y_2816_;
v___y_2801_ = v___y_2817_;
v_a_2802_ = v___x_2820_;
goto v___jp_2799_;
}
}
v___jp_2822_:
{
lean_object* v___x_2826_; double v___x_2827_; double v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; uint8_t v___x_2833_; lean_object* v___x_2834_; 
v___x_2826_ = lean_io_get_num_heartbeats();
v___x_2827_ = lean_float_of_nat(v___y_2824_);
v___x_2828_ = lean_float_of_nat(v___x_2826_);
v___x_2829_ = lean_box_float(v___x_2827_);
v___x_2830_ = lean_box_float(v___x_2828_);
v___x_2831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2829_);
lean_ctor_set(v___x_2831_, 1, v___x_2830_);
v___x_2832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2832_, 0, v_a_2825_);
lean_ctor_set(v___x_2832_, 1, v___x_2831_);
v___x_2833_ = lean_unbox(v_a_2793_);
lean_dec(v_a_2793_);
v___x_2834_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6(v_cls_2779_, v_hasTrace_2777_, v___x_2798_, v_options_2776_, v___x_2833_, v___y_2823_, v___f_2797_, v___x_2832_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_);
lean_dec_ref(v_options_2776_);
return v___x_2834_;
}
v___jp_2835_:
{
lean_object* v___x_2839_; 
v___x_2839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2839_, 0, v_a_2838_);
v___y_2823_ = v___y_2836_;
v___y_2824_ = v___y_2837_;
v_a_2825_ = v___x_2839_;
goto v___jp_2822_;
}
v___jp_2840_:
{
lean_object* v___x_2841_; lean_object* v_a_2842_; lean_object* v___x_2843_; uint8_t v___x_2844_; 
v___x_2841_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg(v_a_2774_);
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_a_2842_);
lean_dec_ref(v___x_2841_);
v___x_2843_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2844_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_options_2776_, v___x_2843_);
if (v___x_2844_ == 0)
{
lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2845_ = lean_io_mono_nanos_now();
lean_inc(v_a_2774_);
lean_inc_ref(v_a_2773_);
lean_inc(v_a_2772_);
lean_inc_ref(v_a_2771_);
v___x_2846_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2770_, v___f_2780_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; lean_object* v___x_2848_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2847_);
lean_dec_ref(v___x_2846_);
lean_inc(v_a_2774_);
lean_inc_ref(v_a_2773_);
lean_inc(v_a_2772_);
lean_inc_ref(v_a_2771_);
v___x_2848_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2769_, v_a_2847_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_);
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2856_; 
lean_del_object(v___x_2795_);
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2851_ = v___x_2848_;
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2848_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
if (v_isShared_2852_ == 0)
{
lean_ctor_set_tag(v___x_2851_, 1);
v___x_2854_ = v___x_2851_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2849_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
v___y_2800_ = v_a_2842_;
v___y_2801_ = v___x_2845_;
v_a_2802_ = v___x_2854_;
goto v___jp_2799_;
}
}
}
else
{
lean_object* v_a_2857_; 
v_a_2857_ = lean_ctor_get(v___x_2848_, 0);
lean_inc(v_a_2857_);
lean_dec_ref(v___x_2848_);
v___y_2816_ = v_a_2842_;
v___y_2817_ = v___x_2845_;
v_a_2818_ = v_a_2857_;
goto v___jp_2815_;
}
}
else
{
lean_object* v_a_2858_; 
lean_dec(v_declName_2769_);
v_a_2858_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2858_);
lean_dec_ref(v___x_2846_);
v___y_2816_ = v_a_2842_;
v___y_2817_ = v___x_2845_;
v_a_2818_ = v_a_2858_;
goto v___jp_2815_;
}
}
else
{
lean_object* v___x_2859_; lean_object* v___x_2860_; 
lean_del_object(v___x_2795_);
v___x_2859_ = lean_io_get_num_heartbeats();
lean_inc(v_a_2774_);
lean_inc_ref(v_a_2773_);
lean_inc(v_a_2772_);
lean_inc_ref(v_a_2771_);
v___x_2860_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2770_, v___f_2780_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v_a_2861_; lean_object* v___x_2862_; 
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
lean_inc(v_a_2861_);
lean_dec_ref(v___x_2860_);
lean_inc(v_a_2774_);
lean_inc_ref(v_a_2773_);
lean_inc(v_a_2772_);
lean_inc_ref(v_a_2771_);
v___x_2862_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2769_, v_a_2861_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2870_; 
v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2865_ = v___x_2862_;
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___x_2862_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2868_; 
if (v_isShared_2866_ == 0)
{
lean_ctor_set_tag(v___x_2865_, 1);
v___x_2868_ = v___x_2865_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_a_2863_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
v___y_2823_ = v_a_2842_;
v___y_2824_ = v___x_2859_;
v_a_2825_ = v___x_2868_;
goto v___jp_2822_;
}
}
}
else
{
lean_object* v_a_2871_; 
v_a_2871_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_a_2871_);
lean_dec_ref(v___x_2862_);
v___y_2836_ = v_a_2842_;
v___y_2837_ = v___x_2859_;
v_a_2838_ = v_a_2871_;
goto v___jp_2835_;
}
}
else
{
lean_object* v_a_2872_; 
lean_dec(v_declName_2769_);
v_a_2872_ = lean_ctor_get(v___x_2860_, 0);
lean_inc(v_a_2872_);
lean_dec_ref(v___x_2860_);
v___y_2836_ = v_a_2842_;
v___y_2837_ = v___x_2859_;
v_a_2838_ = v_a_2872_;
goto v___jp_2835_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___boxed(lean_object* v_declName_2888_, lean_object* v_mvarId_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_){
_start:
{
lean_object* v_res_2895_; 
v_res_2895_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(v_declName_2888_, v_mvarId_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(lean_object* v_e_2896_, lean_object* v___y_2897_){
_start:
{
uint8_t v___x_2899_; 
v___x_2899_ = l_Lean_Expr_hasMVar(v_e_2896_);
if (v___x_2899_ == 0)
{
lean_object* v___x_2900_; 
v___x_2900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2900_, 0, v_e_2896_);
return v___x_2900_;
}
else
{
lean_object* v___x_2901_; lean_object* v_mctx_2902_; lean_object* v___x_2903_; lean_object* v_fst_2904_; lean_object* v_snd_2905_; lean_object* v___x_2906_; lean_object* v_cache_2907_; lean_object* v_zetaDeltaFVarIds_2908_; lean_object* v_postponed_2909_; lean_object* v_diag_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2919_; 
v___x_2901_ = lean_st_ref_get(v___y_2897_);
v_mctx_2902_ = lean_ctor_get(v___x_2901_, 0);
lean_inc_ref(v_mctx_2902_);
lean_dec(v___x_2901_);
v___x_2903_ = l_Lean_instantiateMVarsCore(v_mctx_2902_, v_e_2896_);
v_fst_2904_ = lean_ctor_get(v___x_2903_, 0);
lean_inc(v_fst_2904_);
v_snd_2905_ = lean_ctor_get(v___x_2903_, 1);
lean_inc(v_snd_2905_);
lean_dec_ref(v___x_2903_);
v___x_2906_ = lean_st_ref_take(v___y_2897_);
v_cache_2907_ = lean_ctor_get(v___x_2906_, 1);
v_zetaDeltaFVarIds_2908_ = lean_ctor_get(v___x_2906_, 2);
v_postponed_2909_ = lean_ctor_get(v___x_2906_, 3);
v_diag_2910_ = lean_ctor_get(v___x_2906_, 4);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_2919_ == 0)
{
lean_object* v_unused_2920_; 
v_unused_2920_ = lean_ctor_get(v___x_2906_, 0);
lean_dec(v_unused_2920_);
v___x_2912_ = v___x_2906_;
v_isShared_2913_ = v_isSharedCheck_2919_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_diag_2910_);
lean_inc(v_postponed_2909_);
lean_inc(v_zetaDeltaFVarIds_2908_);
lean_inc(v_cache_2907_);
lean_dec(v___x_2906_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2919_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2915_; 
if (v_isShared_2913_ == 0)
{
lean_ctor_set(v___x_2912_, 0, v_snd_2905_);
v___x_2915_ = v___x_2912_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_snd_2905_);
lean_ctor_set(v_reuseFailAlloc_2918_, 1, v_cache_2907_);
lean_ctor_set(v_reuseFailAlloc_2918_, 2, v_zetaDeltaFVarIds_2908_);
lean_ctor_set(v_reuseFailAlloc_2918_, 3, v_postponed_2909_);
lean_ctor_set(v_reuseFailAlloc_2918_, 4, v_diag_2910_);
v___x_2915_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2916_ = lean_st_ref_set(v___y_2897_, v___x_2915_);
v___x_2917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2917_, 0, v_fst_2904_);
return v___x_2917_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg___boxed(lean_object* v_e_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_){
_start:
{
lean_object* v_res_2924_; 
v_res_2924_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_e_2921_, v___y_2922_);
lean_dec(v___y_2922_);
return v_res_2924_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0(lean_object* v_e_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
lean_object* v___x_2931_; 
v___x_2931_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_e_2925_, v___y_2927_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___boxed(lean_object* v_e_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
lean_object* v_res_2938_; 
v_res_2938_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0(v_e_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(lean_object* v_k_2939_, uint8_t v_allowLevelAssignments_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_){
_start:
{
lean_object* v___x_2946_; 
v___x_2946_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2940_, v_k_2939_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_object* v_a_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2954_; 
v_a_2947_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2949_ = v___x_2946_;
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_a_2947_);
lean_dec(v___x_2946_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2952_; 
if (v_isShared_2950_ == 0)
{
v___x_2952_ = v___x_2949_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_a_2947_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
return v___x_2952_;
}
}
}
else
{
lean_object* v_a_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2962_; 
v_a_2955_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2957_ = v___x_2946_;
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_a_2955_);
lean_dec(v___x_2946_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2960_; 
if (v_isShared_2958_ == 0)
{
v___x_2960_ = v___x_2957_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_a_2955_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
return v___x_2960_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg___boxed(lean_object* v_k_2963_, lean_object* v_allowLevelAssignments_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2970_; lean_object* v_res_2971_; 
v_allowLevelAssignments_boxed_2970_ = lean_unbox(v_allowLevelAssignments_2964_);
v_res_2971_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(v_k_2963_, v_allowLevelAssignments_boxed_2970_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_);
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1(lean_object* v_00_u03b1_2972_, lean_object* v_k_2973_, uint8_t v_allowLevelAssignments_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_){
_start:
{
lean_object* v___x_2980_; 
v___x_2980_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(v_k_2973_, v_allowLevelAssignments_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_);
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___boxed(lean_object* v_00_u03b1_2981_, lean_object* v_k_2982_, lean_object* v_allowLevelAssignments_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2989_; lean_object* v_res_2990_; 
v_allowLevelAssignments_boxed_2989_ = lean_unbox(v_allowLevelAssignments_2983_);
v_res_2990_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1(v_00_u03b1_2981_, v_k_2982_, v_allowLevelAssignments_boxed_2989_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__0(lean_object* v___x_2991_, lean_object* v_e_2992_){
_start:
{
lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2993_ = l_Lean_indentD(v_e_2992_);
v___x_2994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2994_, 0, v___x_2991_);
lean_ctor_set(v___x_2994_, 1, v___x_2993_);
return v___x_2994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1(lean_object* v_type_2995_, lean_object* v___x_2996_, lean_object* v_declName_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_){
_start:
{
lean_object* v___x_3003_; 
lean_inc_ref(v___y_2998_);
v___x_3003_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_2995_, v___x_2996_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v_a_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_a_3004_);
lean_dec_ref(v___x_3003_);
v___x_3005_ = l_Lean_Expr_mvarId_x21(v_a_3004_);
lean_inc(v___y_3001_);
lean_inc_ref(v___y_3000_);
lean_inc(v___y_2999_);
lean_inc_ref(v___y_2998_);
v___x_3006_ = l_Lean_MVarId_intros(v___x_3005_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; lean_object* v_snd_3008_; lean_object* v___x_3009_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc(v_a_3007_);
lean_dec_ref(v___x_3006_);
v_snd_3008_ = lean_ctor_get(v_a_3007_, 1);
lean_inc(v_snd_3008_);
lean_dec(v_a_3007_);
lean_inc(v___y_3001_);
lean_inc_ref(v___y_3000_);
lean_inc(v___y_2999_);
lean_inc_ref(v___y_2998_);
lean_inc(v_snd_3008_);
v___x_3009_ = l_Lean_Elab_Eqns_tryURefl(v_snd_3008_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v_a_3010_; uint8_t v___x_3011_; 
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
lean_inc(v_a_3010_);
lean_dec_ref(v___x_3009_);
v___x_3011_ = lean_unbox(v_a_3010_);
lean_dec(v_a_3010_);
if (v___x_3011_ == 0)
{
lean_object* v___x_3012_; 
lean_inc(v___y_3001_);
lean_inc_ref(v___y_3000_);
lean_inc(v___y_2999_);
lean_inc_ref(v___y_2998_);
v___x_3012_ = l_Lean_Elab_Eqns_deltaLHS(v_snd_3008_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v_a_3013_; lean_object* v___x_3014_; 
v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
lean_inc(v_a_3013_);
lean_dec_ref(v___x_3012_);
lean_inc(v___y_2999_);
v___x_3014_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(v_declName_2997_, v_a_3013_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v___x_3015_; 
lean_dec_ref(v___x_3014_);
v___x_3015_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_a_3004_, v___y_2999_);
lean_dec(v___y_2999_);
return v___x_3015_;
}
else
{
lean_object* v_a_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3023_; 
lean_dec(v_a_3004_);
lean_dec(v___y_2999_);
v_a_3016_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3018_ = v___x_3014_;
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_a_3016_);
lean_dec(v___x_3014_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3021_; 
if (v_isShared_3019_ == 0)
{
v___x_3021_ = v___x_3018_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_a_3016_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
}
}
else
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3031_; 
lean_dec(v_a_3004_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
lean_dec(v_declName_2997_);
v_a_3024_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_3026_ = v___x_3012_;
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_3012_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3029_; 
if (v_isShared_3027_ == 0)
{
v___x_3029_ = v___x_3026_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_a_3024_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
return v___x_3029_;
}
}
}
}
else
{
lean_object* v___x_3032_; 
lean_dec(v_snd_3008_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec_ref(v___y_2998_);
lean_dec(v_declName_2997_);
v___x_3032_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_a_3004_, v___y_2999_);
lean_dec(v___y_2999_);
return v___x_3032_;
}
}
else
{
lean_object* v_a_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3040_; 
lean_dec(v_snd_3008_);
lean_dec(v_a_3004_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
lean_dec(v_declName_2997_);
v_a_3033_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3040_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_3035_ = v___x_3009_;
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_a_3033_);
lean_dec(v___x_3009_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3038_; 
if (v_isShared_3036_ == 0)
{
v___x_3038_ = v___x_3035_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_a_3033_);
v___x_3038_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
return v___x_3038_;
}
}
}
}
else
{
lean_object* v_a_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3048_; 
lean_dec(v_a_3004_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
lean_dec(v_declName_2997_);
v_a_3041_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3048_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3048_ == 0)
{
v___x_3043_ = v___x_3006_;
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_a_3041_);
lean_dec(v___x_3006_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3046_; 
if (v_isShared_3044_ == 0)
{
v___x_3046_ = v___x_3043_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_a_3041_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
}
else
{
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
lean_dec(v_declName_2997_);
return v___x_3003_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1___boxed(lean_object* v_type_3049_, lean_object* v___x_3050_, lean_object* v_declName_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_){
_start:
{
lean_object* v_res_3057_; 
v_res_3057_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1(v_type_3049_, v___x_3050_, v_declName_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_);
return v_res_3057_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3059_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__0));
v___x_3060_ = l_Lean_stringToMessageData(v___x_3059_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2(lean_object* v_type_3061_, lean_object* v_x_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_){
_start:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3068_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1);
v___x_3069_ = l_Lean_indentExpr(v_type_3061_);
v___x_3070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3068_);
lean_ctor_set(v___x_3070_, 1, v___x_3069_);
v___x_3071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3070_);
return v___x_3071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___boxed(lean_object* v_type_3072_, lean_object* v_x_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_){
_start:
{
lean_object* v_res_3079_; 
v_res_3079_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2(v_type_3072_, v_x_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec_ref(v_x_3073_);
return v_res_3079_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2(lean_object* v_e_3080_){
_start:
{
if (lean_obj_tag(v_e_3080_) == 0)
{
uint8_t v___x_3081_; 
v___x_3081_ = 2;
return v___x_3081_;
}
else
{
uint8_t v___x_3082_; 
v___x_3082_ = 0;
return v___x_3082_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2___boxed(lean_object* v_e_3083_){
_start:
{
uint8_t v_res_3084_; lean_object* v_r_3085_; 
v_res_3084_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2(v_e_3083_);
lean_dec_ref(v_e_3083_);
v_r_3085_ = lean_box(v_res_3084_);
return v_r_3085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(lean_object* v_cls_3086_, uint8_t v_collapsed_3087_, lean_object* v_tag_3088_, lean_object* v_opts_3089_, uint8_t v_clsEnabled_3090_, lean_object* v_oldTraces_3091_, lean_object* v_msg_3092_, lean_object* v_resStartStop_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_){
_start:
{
lean_object* v_fst_3099_; lean_object* v_snd_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3198_; 
v_fst_3099_ = lean_ctor_get(v_resStartStop_3093_, 0);
v_snd_3100_ = lean_ctor_get(v_resStartStop_3093_, 1);
v_isSharedCheck_3198_ = !lean_is_exclusive(v_resStartStop_3093_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3102_ = v_resStartStop_3093_;
v_isShared_3103_ = v_isSharedCheck_3198_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_snd_3100_);
lean_inc(v_fst_3099_);
lean_dec(v_resStartStop_3093_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3198_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v_data_3107_; lean_object* v_fst_3118_; lean_object* v_snd_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3197_; 
v_fst_3118_ = lean_ctor_get(v_snd_3100_, 0);
v_snd_3119_ = lean_ctor_get(v_snd_3100_, 1);
v_isSharedCheck_3197_ = !lean_is_exclusive(v_snd_3100_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3121_ = v_snd_3100_;
v_isShared_3122_ = v_isSharedCheck_3197_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_snd_3119_);
lean_inc(v_fst_3118_);
lean_dec(v_snd_3100_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3197_;
goto v_resetjp_3120_;
}
v___jp_3104_:
{
lean_object* v___x_3108_; 
v___x_3108_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__7(v_oldTraces_3091_, v_data_3107_, v___y_3106_, v___y_3105_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
lean_dec(v___y_3097_);
lean_dec(v___y_3095_);
lean_dec_ref(v___y_3094_);
if (lean_obj_tag(v___x_3108_) == 0)
{
lean_object* v___x_3109_; 
lean_dec_ref(v___x_3108_);
v___x_3109_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__8___redArg(v_fst_3099_);
return v___x_3109_;
}
else
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3117_; 
lean_dec(v_fst_3099_);
v_a_3110_ = lean_ctor_get(v___x_3108_, 0);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3112_ = v___x_3108_;
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_3108_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3115_; 
if (v_isShared_3113_ == 0)
{
v___x_3115_ = v___x_3112_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_a_3110_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
}
}
v_resetjp_3120_:
{
lean_object* v___x_3123_; uint8_t v___x_3124_; lean_object* v___y_3126_; lean_object* v_a_3127_; uint8_t v___y_3151_; double v___y_3182_; 
v___x_3123_ = l_Lean_trace_profiler;
v___x_3124_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_opts_3089_, v___x_3123_);
if (v___x_3124_ == 0)
{
v___y_3151_ = v___x_3124_;
goto v___jp_3150_;
}
else
{
lean_object* v___x_3187_; uint8_t v___x_3188_; 
v___x_3187_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3188_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_opts_3089_, v___x_3187_);
if (v___x_3188_ == 0)
{
lean_object* v___x_3189_; lean_object* v___x_3190_; double v___x_3191_; double v___x_3192_; double v___x_3193_; 
v___x_3189_ = l_Lean_trace_profiler_threshold;
v___x_3190_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__9(v_opts_3089_, v___x_3189_);
v___x_3191_ = lean_float_of_nat(v___x_3190_);
v___x_3192_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__5);
v___x_3193_ = lean_float_div(v___x_3191_, v___x_3192_);
v___y_3182_ = v___x_3193_;
goto v___jp_3181_;
}
else
{
lean_object* v___x_3194_; lean_object* v___x_3195_; double v___x_3196_; 
v___x_3194_ = l_Lean_trace_profiler_threshold;
v___x_3195_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__9(v_opts_3089_, v___x_3194_);
v___x_3196_ = lean_float_of_nat(v___x_3195_);
v___y_3182_ = v___x_3196_;
goto v___jp_3181_;
}
}
v___jp_3125_:
{
uint8_t v_result_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3133_; 
v_result_3128_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2(v_fst_3099_);
v___x_3129_ = l_Lean_TraceResult_toEmoji(v_result_3128_);
v___x_3130_ = l_Lean_stringToMessageData(v___x_3129_);
v___x_3131_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__1);
if (v_isShared_3122_ == 0)
{
lean_ctor_set_tag(v___x_3121_, 7);
lean_ctor_set(v___x_3121_, 1, v___x_3131_);
lean_ctor_set(v___x_3121_, 0, v___x_3130_);
v___x_3133_ = v___x_3121_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v___x_3130_);
lean_ctor_set(v_reuseFailAlloc_3144_, 1, v___x_3131_);
v___x_3133_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
lean_object* v_m_3135_; 
if (v_isShared_3103_ == 0)
{
lean_ctor_set_tag(v___x_3102_, 7);
lean_ctor_set(v___x_3102_, 1, v_a_3127_);
lean_ctor_set(v___x_3102_, 0, v___x_3133_);
v_m_3135_ = v___x_3102_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v___x_3133_);
lean_ctor_set(v_reuseFailAlloc_3143_, 1, v_a_3127_);
v_m_3135_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; double v___x_3138_; lean_object* v_data_3139_; 
v___x_3136_ = lean_box(v_result_3128_);
v___x_3137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3136_);
v___x_3138_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__2);
lean_inc_ref(v_tag_3088_);
lean_inc_ref(v___x_3137_);
lean_inc(v_cls_3086_);
v_data_3139_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3139_, 0, v_cls_3086_);
lean_ctor_set(v_data_3139_, 1, v___x_3137_);
lean_ctor_set(v_data_3139_, 2, v_tag_3088_);
lean_ctor_set_float(v_data_3139_, sizeof(void*)*3, v___x_3138_);
lean_ctor_set_float(v_data_3139_, sizeof(void*)*3 + 8, v___x_3138_);
lean_ctor_set_uint8(v_data_3139_, sizeof(void*)*3 + 16, v_collapsed_3087_);
if (v___x_3124_ == 0)
{
lean_dec_ref(v___x_3137_);
lean_dec(v_snd_3119_);
lean_dec(v_fst_3118_);
lean_dec_ref(v_tag_3088_);
lean_dec(v_cls_3086_);
v___y_3105_ = v_m_3135_;
v___y_3106_ = v___y_3126_;
v_data_3107_ = v_data_3139_;
goto v___jp_3104_;
}
else
{
lean_object* v_data_3140_; double v___x_3141_; double v___x_3142_; 
lean_dec_ref(v_data_3139_);
v_data_3140_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3140_, 0, v_cls_3086_);
lean_ctor_set(v_data_3140_, 1, v___x_3137_);
lean_ctor_set(v_data_3140_, 2, v_tag_3088_);
v___x_3141_ = lean_unbox_float(v_fst_3118_);
lean_dec(v_fst_3118_);
lean_ctor_set_float(v_data_3140_, sizeof(void*)*3, v___x_3141_);
v___x_3142_ = lean_unbox_float(v_snd_3119_);
lean_dec(v_snd_3119_);
lean_ctor_set_float(v_data_3140_, sizeof(void*)*3 + 8, v___x_3142_);
lean_ctor_set_uint8(v_data_3140_, sizeof(void*)*3 + 16, v_collapsed_3087_);
v___y_3105_ = v_m_3135_;
v___y_3106_ = v___y_3126_;
v_data_3107_ = v_data_3140_;
goto v___jp_3104_;
}
}
}
}
v___jp_3145_:
{
lean_object* v_ref_3146_; lean_object* v___x_3147_; 
v_ref_3146_ = lean_ctor_get(v___y_3096_, 5);
lean_inc(v___y_3097_);
lean_inc_ref(v___y_3096_);
lean_inc(v___y_3095_);
lean_inc_ref(v___y_3094_);
lean_inc(v_fst_3099_);
v___x_3147_ = lean_apply_6(v_msg_3092_, v_fst_3099_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, lean_box(0));
if (lean_obj_tag(v___x_3147_) == 0)
{
lean_object* v_a_3148_; 
v_a_3148_ = lean_ctor_get(v___x_3147_, 0);
lean_inc(v_a_3148_);
lean_dec_ref(v___x_3147_);
lean_inc(v_ref_3146_);
v___y_3126_ = v_ref_3146_;
v_a_3127_ = v_a_3148_;
goto v___jp_3125_;
}
else
{
lean_object* v___x_3149_; 
lean_dec_ref(v___x_3147_);
v___x_3149_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__4);
lean_inc(v_ref_3146_);
v___y_3126_ = v_ref_3146_;
v_a_3127_ = v___x_3149_;
goto v___jp_3125_;
}
}
v___jp_3150_:
{
if (v_clsEnabled_3090_ == 0)
{
if (v___y_3151_ == 0)
{
lean_object* v___x_3152_; lean_object* v_traceState_3153_; lean_object* v_env_3154_; lean_object* v_nextMacroScope_3155_; lean_object* v_ngen_3156_; lean_object* v_auxDeclNGen_3157_; lean_object* v_cache_3158_; lean_object* v_messages_3159_; lean_object* v_infoState_3160_; lean_object* v_snapshotTasks_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3180_; 
lean_del_object(v___x_3121_);
lean_dec(v_snd_3119_);
lean_dec(v_fst_3118_);
lean_del_object(v___x_3102_);
lean_dec_ref(v___y_3096_);
lean_dec(v___y_3095_);
lean_dec_ref(v___y_3094_);
lean_dec_ref(v_msg_3092_);
lean_dec_ref(v_tag_3088_);
lean_dec(v_cls_3086_);
v___x_3152_ = lean_st_ref_take(v___y_3097_);
v_traceState_3153_ = lean_ctor_get(v___x_3152_, 4);
v_env_3154_ = lean_ctor_get(v___x_3152_, 0);
v_nextMacroScope_3155_ = lean_ctor_get(v___x_3152_, 1);
v_ngen_3156_ = lean_ctor_get(v___x_3152_, 2);
v_auxDeclNGen_3157_ = lean_ctor_get(v___x_3152_, 3);
v_cache_3158_ = lean_ctor_get(v___x_3152_, 5);
v_messages_3159_ = lean_ctor_get(v___x_3152_, 6);
v_infoState_3160_ = lean_ctor_get(v___x_3152_, 7);
v_snapshotTasks_3161_ = lean_ctor_get(v___x_3152_, 8);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3163_ = v___x_3152_;
v_isShared_3164_ = v_isSharedCheck_3180_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_snapshotTasks_3161_);
lean_inc(v_infoState_3160_);
lean_inc(v_messages_3159_);
lean_inc(v_cache_3158_);
lean_inc(v_traceState_3153_);
lean_inc(v_auxDeclNGen_3157_);
lean_inc(v_ngen_3156_);
lean_inc(v_nextMacroScope_3155_);
lean_inc(v_env_3154_);
lean_dec(v___x_3152_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3180_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
uint64_t v_tid_3165_; lean_object* v_traces_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3179_; 
v_tid_3165_ = lean_ctor_get_uint64(v_traceState_3153_, sizeof(void*)*1);
v_traces_3166_ = lean_ctor_get(v_traceState_3153_, 0);
v_isSharedCheck_3179_ = !lean_is_exclusive(v_traceState_3153_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3168_ = v_traceState_3153_;
v_isShared_3169_ = v_isSharedCheck_3179_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_traces_3166_);
lean_dec(v_traceState_3153_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3179_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v___x_3170_; lean_object* v___x_3172_; 
v___x_3170_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3091_, v_traces_3166_);
lean_dec_ref(v_traces_3166_);
if (v_isShared_3169_ == 0)
{
lean_ctor_set(v___x_3168_, 0, v___x_3170_);
v___x_3172_ = v___x_3168_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v___x_3170_);
lean_ctor_set_uint64(v_reuseFailAlloc_3178_, sizeof(void*)*1, v_tid_3165_);
v___x_3172_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
lean_object* v___x_3174_; 
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 4, v___x_3172_);
v___x_3174_ = v___x_3163_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_env_3154_);
lean_ctor_set(v_reuseFailAlloc_3177_, 1, v_nextMacroScope_3155_);
lean_ctor_set(v_reuseFailAlloc_3177_, 2, v_ngen_3156_);
lean_ctor_set(v_reuseFailAlloc_3177_, 3, v_auxDeclNGen_3157_);
lean_ctor_set(v_reuseFailAlloc_3177_, 4, v___x_3172_);
lean_ctor_set(v_reuseFailAlloc_3177_, 5, v_cache_3158_);
lean_ctor_set(v_reuseFailAlloc_3177_, 6, v_messages_3159_);
lean_ctor_set(v_reuseFailAlloc_3177_, 7, v_infoState_3160_);
lean_ctor_set(v_reuseFailAlloc_3177_, 8, v_snapshotTasks_3161_);
v___x_3174_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
lean_object* v___x_3175_; lean_object* v___x_3176_; 
v___x_3175_ = lean_st_ref_set(v___y_3097_, v___x_3174_);
lean_dec(v___y_3097_);
v___x_3176_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__8___redArg(v_fst_3099_);
return v___x_3176_;
}
}
}
}
}
else
{
goto v___jp_3145_;
}
}
else
{
goto v___jp_3145_;
}
}
v___jp_3181_:
{
double v___x_3183_; double v___x_3184_; double v___x_3185_; uint8_t v___x_3186_; 
v___x_3183_ = lean_unbox_float(v_snd_3119_);
v___x_3184_ = lean_unbox_float(v_fst_3118_);
v___x_3185_ = lean_float_sub(v___x_3183_, v___x_3184_);
v___x_3186_ = lean_float_decLt(v___y_3182_, v___x_3185_);
v___y_3151_ = v___x_3186_;
goto v___jp_3150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2___boxed(lean_object* v_cls_3199_, lean_object* v_collapsed_3200_, lean_object* v_tag_3201_, lean_object* v_opts_3202_, lean_object* v_clsEnabled_3203_, lean_object* v_oldTraces_3204_, lean_object* v_msg_3205_, lean_object* v_resStartStop_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_){
_start:
{
uint8_t v_collapsed_boxed_3212_; uint8_t v_clsEnabled_boxed_3213_; lean_object* v_res_3214_; 
v_collapsed_boxed_3212_ = lean_unbox(v_collapsed_3200_);
v_clsEnabled_boxed_3213_ = lean_unbox(v_clsEnabled_3203_);
v_res_3214_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(v_cls_3199_, v_collapsed_boxed_3212_, v_tag_3201_, v_opts_3202_, v_clsEnabled_boxed_3213_, v_oldTraces_3204_, v_msg_3205_, v_resStartStop_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
lean_dec_ref(v_opts_3202_);
return v_res_3214_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1(void){
_start:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; 
v___x_3216_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__0));
v___x_3217_ = l_Lean_stringToMessageData(v___x_3216_);
return v___x_3217_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3(void){
_start:
{
lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3219_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__2));
v___x_3220_ = l_Lean_stringToMessageData(v___x_3219_);
return v___x_3220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof(lean_object* v_declName_3221_, lean_object* v_type_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_){
_start:
{
lean_object* v_options_3228_; uint8_t v_hasTrace_3229_; uint8_t v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___f_3236_; lean_object* v___x_3237_; lean_object* v___f_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; 
v_options_3228_ = lean_ctor_get(v_a_3225_, 2);
v_hasTrace_3229_ = lean_ctor_get_uint8(v_options_3228_, sizeof(void*)*1);
v___x_3230_ = 0;
lean_inc(v_declName_3221_);
v___x_3231_ = l_Lean_MessageData_ofConstName(v_declName_3221_, v___x_3230_);
v___x_3232_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1);
v___x_3233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3232_);
lean_ctor_set(v___x_3233_, 1, v___x_3231_);
v___x_3234_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3);
v___x_3235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3235_, 0, v___x_3233_);
lean_ctor_set(v___x_3235_, 1, v___x_3234_);
v___f_3236_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__0), 2, 1);
lean_closure_set(v___f_3236_, 0, v___x_3235_);
v___x_3237_ = lean_box(0);
lean_inc_ref(v_type_3222_);
v___f_3238_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1___boxed), 8, 3);
lean_closure_set(v___f_3238_, 0, v_type_3222_);
lean_closure_set(v___f_3238_, 1, v___x_3237_);
lean_closure_set(v___f_3238_, 2, v_declName_3221_);
v___x_3239_ = lean_box(v___x_3230_);
v___x_3240_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___boxed), 8, 3);
lean_closure_set(v___x_3240_, 0, lean_box(0));
lean_closure_set(v___x_3240_, 1, v___f_3238_);
lean_closure_set(v___x_3240_, 2, v___x_3239_);
if (v_hasTrace_3229_ == 0)
{
lean_object* v___x_3241_; 
lean_dec_ref(v_type_3222_);
v___x_3241_ = l_Lean_Meta_mapErrorImp___redArg(v___x_3240_, v___f_3236_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_object* v_a_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3249_; 
v_a_3242_ = lean_ctor_get(v___x_3241_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3241_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3244_ = v___x_3241_;
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_a_3242_);
lean_dec(v___x_3241_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3247_; 
if (v_isShared_3245_ == 0)
{
v___x_3247_ = v___x_3244_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_a_3242_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
}
else
{
lean_object* v_a_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3257_; 
v_a_3250_ = lean_ctor_get(v___x_3241_, 0);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_3241_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3252_ = v___x_3241_;
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_a_3250_);
lean_dec(v___x_3241_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
lean_object* v___x_3255_; 
if (v_isShared_3253_ == 0)
{
v___x_3255_ = v___x_3252_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_a_3250_);
v___x_3255_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
return v___x_3255_;
}
}
}
}
else
{
lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v_a_3260_; lean_object* v___f_3261_; lean_object* v___x_3262_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v_a_3266_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v_a_3282_; uint8_t v___x_3333_; 
v___x_3258_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4));
v___x_3259_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v___x_3258_, v_a_3225_);
v_a_3260_ = lean_ctor_get(v___x_3259_, 0);
lean_inc(v_a_3260_);
lean_dec_ref(v___x_3259_);
v___f_3261_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___boxed), 7, 1);
lean_closure_set(v___f_3261_, 0, v_type_3222_);
v___x_3262_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___closed__0));
v___x_3333_ = lean_unbox(v_a_3260_);
if (v___x_3333_ == 0)
{
lean_object* v___x_3334_; uint8_t v___x_3335_; 
v___x_3334_ = l_Lean_trace_profiler;
v___x_3335_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_options_3228_, v___x_3334_);
if (v___x_3335_ == 0)
{
lean_object* v___x_3336_; 
lean_dec_ref(v___f_3261_);
lean_dec(v_a_3260_);
v___x_3336_ = l_Lean_Meta_mapErrorImp___redArg(v___x_3240_, v___f_3236_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_);
if (lean_obj_tag(v___x_3336_) == 0)
{
lean_object* v_a_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3344_; 
v_a_3337_ = lean_ctor_get(v___x_3336_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3336_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3339_ = v___x_3336_;
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_a_3337_);
lean_dec(v___x_3336_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3342_; 
if (v_isShared_3340_ == 0)
{
v___x_3342_ = v___x_3339_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v_a_3337_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
}
}
}
else
{
lean_object* v_a_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3352_; 
v_a_3345_ = lean_ctor_get(v___x_3336_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3336_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3347_ = v___x_3336_;
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_a_3345_);
lean_dec(v___x_3336_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3350_; 
if (v_isShared_3348_ == 0)
{
v___x_3350_ = v___x_3347_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_a_3345_);
v___x_3350_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
return v___x_3350_;
}
}
}
}
else
{
lean_inc_ref(v_options_3228_);
goto v___jp_3292_;
}
}
else
{
lean_inc_ref(v_options_3228_);
goto v___jp_3292_;
}
v___jp_3263_:
{
lean_object* v___x_3267_; double v___x_3268_; double v___x_3269_; double v___x_3270_; double v___x_3271_; double v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; uint8_t v___x_3277_; lean_object* v___x_3278_; 
v___x_3267_ = lean_io_mono_nanos_now();
v___x_3268_ = lean_float_of_nat(v___y_3264_);
v___x_3269_ = lean_float_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38);
v___x_3270_ = lean_float_div(v___x_3268_, v___x_3269_);
v___x_3271_ = lean_float_of_nat(v___x_3267_);
v___x_3272_ = lean_float_div(v___x_3271_, v___x_3269_);
v___x_3273_ = lean_box_float(v___x_3270_);
v___x_3274_ = lean_box_float(v___x_3272_);
v___x_3275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3275_, 0, v___x_3273_);
lean_ctor_set(v___x_3275_, 1, v___x_3274_);
v___x_3276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3276_, 0, v_a_3266_);
lean_ctor_set(v___x_3276_, 1, v___x_3275_);
v___x_3277_ = lean_unbox(v_a_3260_);
lean_dec(v_a_3260_);
v___x_3278_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(v___x_3258_, v_hasTrace_3229_, v___x_3262_, v_options_3228_, v___x_3277_, v___y_3265_, v___f_3261_, v___x_3276_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_);
lean_dec_ref(v_options_3228_);
return v___x_3278_;
}
v___jp_3279_:
{
lean_object* v___x_3283_; double v___x_3284_; double v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; uint8_t v___x_3290_; lean_object* v___x_3291_; 
v___x_3283_ = lean_io_get_num_heartbeats();
v___x_3284_ = lean_float_of_nat(v___y_3280_);
v___x_3285_ = lean_float_of_nat(v___x_3283_);
v___x_3286_ = lean_box_float(v___x_3284_);
v___x_3287_ = lean_box_float(v___x_3285_);
v___x_3288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3286_);
lean_ctor_set(v___x_3288_, 1, v___x_3287_);
v___x_3289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3289_, 0, v_a_3282_);
lean_ctor_set(v___x_3289_, 1, v___x_3288_);
v___x_3290_ = lean_unbox(v_a_3260_);
lean_dec(v_a_3260_);
v___x_3291_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(v___x_3258_, v_hasTrace_3229_, v___x_3262_, v_options_3228_, v___x_3290_, v___y_3281_, v___f_3261_, v___x_3289_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_);
lean_dec_ref(v_options_3228_);
return v___x_3291_;
}
v___jp_3292_:
{
lean_object* v___x_3293_; lean_object* v_a_3294_; lean_object* v___x_3295_; uint8_t v___x_3296_; 
v___x_3293_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg(v_a_3226_);
v_a_3294_ = lean_ctor_get(v___x_3293_, 0);
lean_inc(v_a_3294_);
lean_dec_ref(v___x_3293_);
v___x_3295_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3296_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_options_3228_, v___x_3295_);
if (v___x_3296_ == 0)
{
lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3297_ = lean_io_mono_nanos_now();
lean_inc(v_a_3226_);
lean_inc_ref(v_a_3225_);
lean_inc(v_a_3224_);
lean_inc_ref(v_a_3223_);
v___x_3298_ = l_Lean_Meta_mapErrorImp___redArg(v___x_3240_, v___f_3236_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_);
if (lean_obj_tag(v___x_3298_) == 0)
{
lean_object* v_a_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3306_; 
v_a_3299_ = lean_ctor_get(v___x_3298_, 0);
v_isSharedCheck_3306_ = !lean_is_exclusive(v___x_3298_);
if (v_isSharedCheck_3306_ == 0)
{
v___x_3301_ = v___x_3298_;
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_a_3299_);
lean_dec(v___x_3298_);
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
v___x_3304_ = v___x_3301_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v_a_3299_);
v___x_3304_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
v___y_3264_ = v___x_3297_;
v___y_3265_ = v_a_3294_;
v_a_3266_ = v___x_3304_;
goto v___jp_3263_;
}
}
}
else
{
lean_object* v_a_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3314_; 
v_a_3307_ = lean_ctor_get(v___x_3298_, 0);
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3298_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3309_ = v___x_3298_;
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_a_3307_);
lean_dec(v___x_3298_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3312_; 
if (v_isShared_3310_ == 0)
{
lean_ctor_set_tag(v___x_3309_, 0);
v___x_3312_ = v___x_3309_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v_a_3307_);
v___x_3312_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
v___y_3264_ = v___x_3297_;
v___y_3265_ = v_a_3294_;
v_a_3266_ = v___x_3312_;
goto v___jp_3263_;
}
}
}
}
else
{
lean_object* v___x_3315_; lean_object* v___x_3316_; 
v___x_3315_ = lean_io_get_num_heartbeats();
lean_inc(v_a_3226_);
lean_inc_ref(v_a_3225_);
lean_inc(v_a_3224_);
lean_inc_ref(v_a_3223_);
v___x_3316_ = l_Lean_Meta_mapErrorImp___redArg(v___x_3240_, v___f_3236_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_);
if (lean_obj_tag(v___x_3316_) == 0)
{
lean_object* v_a_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3324_; 
v_a_3317_ = lean_ctor_get(v___x_3316_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3316_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3319_ = v___x_3316_;
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_a_3317_);
lean_dec(v___x_3316_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3322_; 
if (v_isShared_3320_ == 0)
{
lean_ctor_set_tag(v___x_3319_, 1);
v___x_3322_ = v___x_3319_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_a_3317_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
v___y_3280_ = v___x_3315_;
v___y_3281_ = v_a_3294_;
v_a_3282_ = v___x_3322_;
goto v___jp_3279_;
}
}
}
else
{
lean_object* v_a_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3332_; 
v_a_3325_ = lean_ctor_get(v___x_3316_, 0);
v_isSharedCheck_3332_ = !lean_is_exclusive(v___x_3316_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3327_ = v___x_3316_;
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_a_3325_);
lean_dec(v___x_3316_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3330_; 
if (v_isShared_3328_ == 0)
{
lean_ctor_set_tag(v___x_3327_, 0);
v___x_3330_ = v___x_3327_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v_a_3325_);
v___x_3330_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
v___y_3280_ = v___x_3315_;
v___y_3281_ = v_a_3294_;
v_a_3282_ = v___x_3330_;
goto v___jp_3279_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___boxed(lean_object* v_declName_3353_, lean_object* v_type_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_){
_start:
{
lean_object* v_res_3360_; 
v_res_3360_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof(v_declName_3353_, v_type_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_);
return v_res_3360_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_(lean_object* v_env_3361_, lean_object* v_n_3362_, lean_object* v_x_3363_){
_start:
{
uint8_t v___x_3364_; lean_object* v___x_3365_; 
v___x_3364_ = 0;
v___x_3365_ = l_Lean_Environment_find_x3f(v_env_3361_, v_n_3362_, v___x_3364_);
if (lean_obj_tag(v___x_3365_) == 0)
{
return v___x_3364_;
}
else
{
lean_object* v_val_3366_; uint8_t v___x_3367_; 
v_val_3366_ = lean_ctor_get(v___x_3365_, 0);
lean_inc(v_val_3366_);
lean_dec_ref(v___x_3365_);
v___x_3367_ = l_Lean_ConstantInfo_hasValue(v_val_3366_, v___x_3364_);
lean_dec(v_val_3366_);
return v___x_3367_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2____boxed(lean_object* v_env_3368_, lean_object* v_n_3369_, lean_object* v_x_3370_){
_start:
{
uint8_t v_res_3371_; lean_object* v_r_3372_; 
v_res_3371_ = l_Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_(v_env_3368_, v_n_3369_, v_x_3370_);
lean_dec_ref(v_x_3370_);
v_r_3372_ = lean_box(v_res_3371_);
return v_r_3372_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_3373_, lean_object* v_x_3374_){
_start:
{
if (lean_obj_tag(v_x_3374_) == 0)
{
lean_object* v_k_3375_; lean_object* v_v_3376_; lean_object* v_l_3377_; lean_object* v_r_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; 
v_k_3375_ = lean_ctor_get(v_x_3374_, 1);
v_v_3376_ = lean_ctor_get(v_x_3374_, 2);
v_l_3377_ = lean_ctor_get(v_x_3374_, 3);
v_r_3378_ = lean_ctor_get(v_x_3374_, 4);
v___x_3379_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0(v_init_3373_, v_l_3377_);
lean_inc(v_v_3376_);
lean_inc(v_k_3375_);
v___x_3380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3380_, 0, v_k_3375_);
lean_ctor_set(v___x_3380_, 1, v_v_3376_);
v___x_3381_ = lean_array_push(v___x_3379_, v___x_3380_);
v_init_3373_ = v___x_3381_;
v_x_3374_ = v_r_3378_;
goto _start;
}
else
{
return v_init_3373_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_3383_, lean_object* v_x_3384_){
_start:
{
lean_object* v_res_3385_; 
v_res_3385_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0(v_init_3383_, v_x_3384_);
lean_dec(v_x_3384_);
return v_res_3385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_(lean_object* v_env_3388_, lean_object* v_s_3389_, uint8_t v_x_3390_){
_start:
{
lean_object* v___f_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; 
v___f_3391_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2____boxed), 3, 1);
lean_closure_set(v___f_3391_, 0, v_env_3388_);
v___x_3392_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v___f_3391_, v_s_3389_);
v___x_3393_ = ((lean_object*)(l_Lean_Elab_Structural_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_));
v___x_3394_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0(v___x_3393_, v___x_3392_);
lean_dec(v___x_3392_);
return v___x_3394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2____boxed(lean_object* v_env_3395_, lean_object* v_s_3396_, lean_object* v_x_3397_){
_start:
{
uint8_t v_x_232__boxed_3398_; lean_object* v_res_3399_; 
v_x_232__boxed_3398_ = lean_unbox(v_x_3397_);
v_res_3399_ = l_Lean_Elab_Structural_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_(v_env_3395_, v_s_3396_, v_x_232__boxed_3398_);
return v_res_3399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___f_3412_ = ((lean_object*)(l_Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_));
v___x_3413_ = ((lean_object*)(l_Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_));
v___x_3414_ = ((lean_object*)(l_Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_));
v___x_3415_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_3413_, v___x_3414_, v___f_3412_);
return v___x_3415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2____boxed(lean_object* v_a_3416_){
_start:
{
lean_object* v_res_3417_; 
v_res_3417_ = l_Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_();
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__spec__0(lean_object* v_init_3418_, lean_object* v_t_3419_){
_start:
{
lean_object* v___x_3420_; 
v___x_3420_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0(v_init_3418_, v_t_3419_);
return v___x_3420_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_3421_, lean_object* v_t_3422_){
_start:
{
lean_object* v_res_3423_; 
v_res_3423_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__spec__0(v_init_3421_, v_t_3422_);
lean_dec(v_t_3422_);
return v_res_3423_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__0(void){
_start:
{
lean_object* v___x_3424_; 
v___x_3424_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3424_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1(void){
_start:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___x_3425_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__0, &l_Lean_Elab_Structural_registerEqnsInfo___closed__0_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__0);
v___x_3426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3425_);
return v___x_3426_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__2(void){
_start:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3427_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__1, &l_Lean_Elab_Structural_registerEqnsInfo___closed__1_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1);
v___x_3428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3428_, 0, v___x_3427_);
lean_ctor_set(v___x_3428_, 1, v___x_3427_);
return v___x_3428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_registerEqnsInfo(lean_object* v_preDef_3429_, lean_object* v_declNames_3430_, lean_object* v_recArgPos_3431_, lean_object* v_fixedParamPerms_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_){
_start:
{
lean_object* v_levelParams_3436_; lean_object* v_declName_3437_; lean_object* v_type_3438_; lean_object* v_value_3439_; lean_object* v___x_3440_; 
v_levelParams_3436_ = lean_ctor_get(v_preDef_3429_, 1);
lean_inc(v_levelParams_3436_);
v_declName_3437_ = lean_ctor_get(v_preDef_3429_, 3);
lean_inc(v_declName_3437_);
v_type_3438_ = lean_ctor_get(v_preDef_3429_, 6);
lean_inc_ref(v_type_3438_);
v_value_3439_ = lean_ctor_get(v_preDef_3429_, 7);
lean_inc_ref(v_value_3439_);
lean_dec_ref(v_preDef_3429_);
lean_inc(v_declName_3437_);
v___x_3440_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_3437_, v_a_3433_, v_a_3434_);
if (lean_obj_tag(v___x_3440_) == 0)
{
lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3470_; 
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3440_);
if (v_isSharedCheck_3470_ == 0)
{
lean_object* v_unused_3471_; 
v_unused_3471_ = lean_ctor_get(v___x_3440_, 0);
lean_dec(v_unused_3471_);
v___x_3442_ = v___x_3440_;
v_isShared_3443_ = v_isSharedCheck_3470_;
goto v_resetjp_3441_;
}
else
{
lean_dec(v___x_3440_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3470_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3444_; lean_object* v_env_3445_; lean_object* v_nextMacroScope_3446_; lean_object* v_ngen_3447_; lean_object* v_auxDeclNGen_3448_; lean_object* v_traceState_3449_; lean_object* v_messages_3450_; lean_object* v_infoState_3451_; lean_object* v_snapshotTasks_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3468_; 
v___x_3444_ = lean_st_ref_take(v_a_3434_);
v_env_3445_ = lean_ctor_get(v___x_3444_, 0);
v_nextMacroScope_3446_ = lean_ctor_get(v___x_3444_, 1);
v_ngen_3447_ = lean_ctor_get(v___x_3444_, 2);
v_auxDeclNGen_3448_ = lean_ctor_get(v___x_3444_, 3);
v_traceState_3449_ = lean_ctor_get(v___x_3444_, 4);
v_messages_3450_ = lean_ctor_get(v___x_3444_, 6);
v_infoState_3451_ = lean_ctor_get(v___x_3444_, 7);
v_snapshotTasks_3452_ = lean_ctor_get(v___x_3444_, 8);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3468_ == 0)
{
lean_object* v_unused_3469_; 
v_unused_3469_ = lean_ctor_get(v___x_3444_, 5);
lean_dec(v_unused_3469_);
v___x_3454_ = v___x_3444_;
v_isShared_3455_ = v_isSharedCheck_3468_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_snapshotTasks_3452_);
lean_inc(v_infoState_3451_);
lean_inc(v_messages_3450_);
lean_inc(v_traceState_3449_);
lean_inc(v_auxDeclNGen_3448_);
lean_inc(v_ngen_3447_);
lean_inc(v_nextMacroScope_3446_);
lean_inc(v_env_3445_);
lean_dec(v___x_3444_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3468_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3461_; 
v___x_3456_ = l_Lean_Elab_Structural_eqnInfoExt;
lean_inc(v_declName_3437_);
v___x_3457_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3457_, 0, v_declName_3437_);
lean_ctor_set(v___x_3457_, 1, v_levelParams_3436_);
lean_ctor_set(v___x_3457_, 2, v_type_3438_);
lean_ctor_set(v___x_3457_, 3, v_value_3439_);
lean_ctor_set(v___x_3457_, 4, v_recArgPos_3431_);
lean_ctor_set(v___x_3457_, 5, v_declNames_3430_);
lean_ctor_set(v___x_3457_, 6, v_fixedParamPerms_3432_);
v___x_3458_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3456_, v_env_3445_, v_declName_3437_, v___x_3457_);
v___x_3459_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__2, &l_Lean_Elab_Structural_registerEqnsInfo___closed__2_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__2);
if (v_isShared_3455_ == 0)
{
lean_ctor_set(v___x_3454_, 5, v___x_3459_);
lean_ctor_set(v___x_3454_, 0, v___x_3458_);
v___x_3461_ = v___x_3454_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v___x_3458_);
lean_ctor_set(v_reuseFailAlloc_3467_, 1, v_nextMacroScope_3446_);
lean_ctor_set(v_reuseFailAlloc_3467_, 2, v_ngen_3447_);
lean_ctor_set(v_reuseFailAlloc_3467_, 3, v_auxDeclNGen_3448_);
lean_ctor_set(v_reuseFailAlloc_3467_, 4, v_traceState_3449_);
lean_ctor_set(v_reuseFailAlloc_3467_, 5, v___x_3459_);
lean_ctor_set(v_reuseFailAlloc_3467_, 6, v_messages_3450_);
lean_ctor_set(v_reuseFailAlloc_3467_, 7, v_infoState_3451_);
lean_ctor_set(v_reuseFailAlloc_3467_, 8, v_snapshotTasks_3452_);
v___x_3461_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3465_; 
v___x_3462_ = lean_st_ref_set(v_a_3434_, v___x_3461_);
v___x_3463_ = lean_box(0);
if (v_isShared_3443_ == 0)
{
lean_ctor_set(v___x_3442_, 0, v___x_3463_);
v___x_3465_ = v___x_3442_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v___x_3463_);
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
else
{
lean_dec_ref(v_value_3439_);
lean_dec_ref(v_type_3438_);
lean_dec(v_declName_3437_);
lean_dec(v_levelParams_3436_);
lean_dec_ref(v_fixedParamPerms_3432_);
lean_dec(v_recArgPos_3431_);
lean_dec_ref(v_declNames_3430_);
return v___x_3440_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_registerEqnsInfo___boxed(lean_object* v_preDef_3472_, lean_object* v_declNames_3473_, lean_object* v_recArgPos_3474_, lean_object* v_fixedParamPerms_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_){
_start:
{
lean_object* v_res_3479_; 
v_res_3479_ = l_Lean_Elab_Structural_registerEqnsInfo(v_preDef_3472_, v_declNames_3473_, v_recArgPos_3474_, v_fixedParamPerms_3475_, v_a_3476_, v_a_3477_);
lean_dec(v_a_3477_);
lean_dec_ref(v_a_3476_);
return v_res_3479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(lean_object* v_e_3480_, lean_object* v_k_3481_, uint8_t v_cleanupAnnotations_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_){
_start:
{
lean_object* v___f_3488_; uint8_t v___x_3489_; uint8_t v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; 
v___f_3488_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3488_, 0, v_k_3481_);
v___x_3489_ = 1;
v___x_3490_ = 0;
v___x_3491_ = lean_box(0);
v___x_3492_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3480_, v___x_3489_, v___x_3490_, v___x_3489_, v___x_3490_, v___x_3491_, v___f_3488_, v_cleanupAnnotations_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3500_; 
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3495_ = v___x_3492_;
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_a_3493_);
lean_dec(v___x_3492_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v___x_3498_; 
if (v_isShared_3496_ == 0)
{
v___x_3498_ = v___x_3495_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v_a_3493_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
}
}
}
else
{
lean_object* v_a_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3508_; 
v_a_3501_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3508_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3503_ = v___x_3492_;
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_a_3501_);
lean_dec(v___x_3492_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3506_; 
if (v_isShared_3504_ == 0)
{
v___x_3506_ = v___x_3503_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_a_3501_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg___boxed(lean_object* v_e_3509_, lean_object* v_k_3510_, lean_object* v_cleanupAnnotations_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3517_; lean_object* v_res_3518_; 
v_cleanupAnnotations_boxed_3517_ = lean_unbox(v_cleanupAnnotations_3511_);
v_res_3518_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(v_e_3509_, v_k_3510_, v_cleanupAnnotations_boxed_3517_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_);
return v_res_3518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3(lean_object* v_00_u03b1_3519_, lean_object* v_e_3520_, lean_object* v_k_3521_, uint8_t v_cleanupAnnotations_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_){
_start:
{
lean_object* v___x_3528_; 
v___x_3528_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(v_e_3520_, v_k_3521_, v_cleanupAnnotations_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_);
return v___x_3528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___boxed(lean_object* v_00_u03b1_3529_, lean_object* v_e_3530_, lean_object* v_k_3531_, lean_object* v_cleanupAnnotations_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3538_; lean_object* v_res_3539_; 
v_cleanupAnnotations_boxed_3538_ = lean_unbox(v_cleanupAnnotations_3532_);
v_res_3539_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3(v_00_u03b1_3529_, v_e_3530_, v_k_3531_, v_cleanupAnnotations_boxed_3538_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_);
return v_res_3539_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(lean_object* v___y_3540_, uint8_t v_isExporting_3541_, lean_object* v___x_3542_, lean_object* v___y_3543_, lean_object* v___x_3544_, lean_object* v_a_x3f_3545_){
_start:
{
lean_object* v___x_3547_; lean_object* v_env_3548_; lean_object* v_nextMacroScope_3549_; lean_object* v_ngen_3550_; lean_object* v_auxDeclNGen_3551_; lean_object* v_traceState_3552_; lean_object* v_messages_3553_; lean_object* v_infoState_3554_; lean_object* v_snapshotTasks_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3580_; 
v___x_3547_ = lean_st_ref_take(v___y_3540_);
v_env_3548_ = lean_ctor_get(v___x_3547_, 0);
v_nextMacroScope_3549_ = lean_ctor_get(v___x_3547_, 1);
v_ngen_3550_ = lean_ctor_get(v___x_3547_, 2);
v_auxDeclNGen_3551_ = lean_ctor_get(v___x_3547_, 3);
v_traceState_3552_ = lean_ctor_get(v___x_3547_, 4);
v_messages_3553_ = lean_ctor_get(v___x_3547_, 6);
v_infoState_3554_ = lean_ctor_get(v___x_3547_, 7);
v_snapshotTasks_3555_ = lean_ctor_get(v___x_3547_, 8);
v_isSharedCheck_3580_ = !lean_is_exclusive(v___x_3547_);
if (v_isSharedCheck_3580_ == 0)
{
lean_object* v_unused_3581_; 
v_unused_3581_ = lean_ctor_get(v___x_3547_, 5);
lean_dec(v_unused_3581_);
v___x_3557_ = v___x_3547_;
v_isShared_3558_ = v_isSharedCheck_3580_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_snapshotTasks_3555_);
lean_inc(v_infoState_3554_);
lean_inc(v_messages_3553_);
lean_inc(v_traceState_3552_);
lean_inc(v_auxDeclNGen_3551_);
lean_inc(v_ngen_3550_);
lean_inc(v_nextMacroScope_3549_);
lean_inc(v_env_3548_);
lean_dec(v___x_3547_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3580_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v___x_3559_; lean_object* v___x_3561_; 
v___x_3559_ = l_Lean_Environment_setExporting(v_env_3548_, v_isExporting_3541_);
if (v_isShared_3558_ == 0)
{
lean_ctor_set(v___x_3557_, 5, v___x_3542_);
lean_ctor_set(v___x_3557_, 0, v___x_3559_);
v___x_3561_ = v___x_3557_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___x_3559_);
lean_ctor_set(v_reuseFailAlloc_3579_, 1, v_nextMacroScope_3549_);
lean_ctor_set(v_reuseFailAlloc_3579_, 2, v_ngen_3550_);
lean_ctor_set(v_reuseFailAlloc_3579_, 3, v_auxDeclNGen_3551_);
lean_ctor_set(v_reuseFailAlloc_3579_, 4, v_traceState_3552_);
lean_ctor_set(v_reuseFailAlloc_3579_, 5, v___x_3542_);
lean_ctor_set(v_reuseFailAlloc_3579_, 6, v_messages_3553_);
lean_ctor_set(v_reuseFailAlloc_3579_, 7, v_infoState_3554_);
lean_ctor_set(v_reuseFailAlloc_3579_, 8, v_snapshotTasks_3555_);
v___x_3561_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v_mctx_3564_; lean_object* v_zetaDeltaFVarIds_3565_; lean_object* v_postponed_3566_; lean_object* v_diag_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3577_; 
v___x_3562_ = lean_st_ref_set(v___y_3540_, v___x_3561_);
v___x_3563_ = lean_st_ref_take(v___y_3543_);
v_mctx_3564_ = lean_ctor_get(v___x_3563_, 0);
v_zetaDeltaFVarIds_3565_ = lean_ctor_get(v___x_3563_, 2);
v_postponed_3566_ = lean_ctor_get(v___x_3563_, 3);
v_diag_3567_ = lean_ctor_get(v___x_3563_, 4);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3563_);
if (v_isSharedCheck_3577_ == 0)
{
lean_object* v_unused_3578_; 
v_unused_3578_ = lean_ctor_get(v___x_3563_, 1);
lean_dec(v_unused_3578_);
v___x_3569_ = v___x_3563_;
v_isShared_3570_ = v_isSharedCheck_3577_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_diag_3567_);
lean_inc(v_postponed_3566_);
lean_inc(v_zetaDeltaFVarIds_3565_);
lean_inc(v_mctx_3564_);
lean_dec(v___x_3563_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3577_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3572_; 
if (v_isShared_3570_ == 0)
{
lean_ctor_set(v___x_3569_, 1, v___x_3544_);
v___x_3572_ = v___x_3569_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_mctx_3564_);
lean_ctor_set(v_reuseFailAlloc_3576_, 1, v___x_3544_);
lean_ctor_set(v_reuseFailAlloc_3576_, 2, v_zetaDeltaFVarIds_3565_);
lean_ctor_set(v_reuseFailAlloc_3576_, 3, v_postponed_3566_);
lean_ctor_set(v_reuseFailAlloc_3576_, 4, v_diag_3567_);
v___x_3572_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3573_ = lean_st_ref_set(v___y_3543_, v___x_3572_);
v___x_3574_ = lean_box(0);
v___x_3575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3575_, 0, v___x_3574_);
return v___x_3575_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_3582_, lean_object* v_isExporting_3583_, lean_object* v___x_3584_, lean_object* v___y_3585_, lean_object* v___x_3586_, lean_object* v_a_x3f_3587_, lean_object* v___y_3588_){
_start:
{
uint8_t v_isExporting_boxed_3589_; lean_object* v_res_3590_; 
v_isExporting_boxed_3589_ = lean_unbox(v_isExporting_3583_);
v_res_3590_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(v___y_3582_, v_isExporting_boxed_3589_, v___x_3584_, v___y_3585_, v___x_3586_, v_a_x3f_3587_);
lean_dec(v_a_x3f_3587_);
lean_dec(v___y_3585_);
lean_dec(v___y_3582_);
return v_res_3590_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3591_; lean_object* v___x_3592_; 
v___x_3591_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__1, &l_Lean_Elab_Structural_registerEqnsInfo___closed__1_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1);
v___x_3592_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3592_, 0, v___x_3591_);
lean_ctor_set(v___x_3592_, 1, v___x_3591_);
lean_ctor_set(v___x_3592_, 2, v___x_3591_);
lean_ctor_set(v___x_3592_, 3, v___x_3591_);
lean_ctor_set(v___x_3592_, 4, v___x_3591_);
lean_ctor_set(v___x_3592_, 5, v___x_3591_);
return v___x_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(lean_object* v_x_3593_, uint8_t v_isExporting_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_){
_start:
{
lean_object* v___x_3600_; lean_object* v_env_3601_; uint8_t v_isExporting_3602_; lean_object* v___x_3603_; lean_object* v_env_3604_; lean_object* v_nextMacroScope_3605_; lean_object* v_ngen_3606_; lean_object* v_auxDeclNGen_3607_; lean_object* v_traceState_3608_; lean_object* v_messages_3609_; lean_object* v_infoState_3610_; lean_object* v_snapshotTasks_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3665_; 
v___x_3600_ = lean_st_ref_get(v___y_3598_);
v_env_3601_ = lean_ctor_get(v___x_3600_, 0);
lean_inc_ref(v_env_3601_);
lean_dec(v___x_3600_);
v_isExporting_3602_ = lean_ctor_get_uint8(v_env_3601_, sizeof(void*)*8);
lean_dec_ref(v_env_3601_);
v___x_3603_ = lean_st_ref_take(v___y_3598_);
v_env_3604_ = lean_ctor_get(v___x_3603_, 0);
v_nextMacroScope_3605_ = lean_ctor_get(v___x_3603_, 1);
v_ngen_3606_ = lean_ctor_get(v___x_3603_, 2);
v_auxDeclNGen_3607_ = lean_ctor_get(v___x_3603_, 3);
v_traceState_3608_ = lean_ctor_get(v___x_3603_, 4);
v_messages_3609_ = lean_ctor_get(v___x_3603_, 6);
v_infoState_3610_ = lean_ctor_get(v___x_3603_, 7);
v_snapshotTasks_3611_ = lean_ctor_get(v___x_3603_, 8);
v_isSharedCheck_3665_ = !lean_is_exclusive(v___x_3603_);
if (v_isSharedCheck_3665_ == 0)
{
lean_object* v_unused_3666_; 
v_unused_3666_ = lean_ctor_get(v___x_3603_, 5);
lean_dec(v_unused_3666_);
v___x_3613_ = v___x_3603_;
v_isShared_3614_ = v_isSharedCheck_3665_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_snapshotTasks_3611_);
lean_inc(v_infoState_3610_);
lean_inc(v_messages_3609_);
lean_inc(v_traceState_3608_);
lean_inc(v_auxDeclNGen_3607_);
lean_inc(v_ngen_3606_);
lean_inc(v_nextMacroScope_3605_);
lean_inc(v_env_3604_);
lean_dec(v___x_3603_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3665_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3618_; 
v___x_3615_ = l_Lean_Environment_setExporting(v_env_3604_, v_isExporting_3594_);
v___x_3616_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__2, &l_Lean_Elab_Structural_registerEqnsInfo___closed__2_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__2);
if (v_isShared_3614_ == 0)
{
lean_ctor_set(v___x_3613_, 5, v___x_3616_);
lean_ctor_set(v___x_3613_, 0, v___x_3615_);
v___x_3618_ = v___x_3613_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v___x_3615_);
lean_ctor_set(v_reuseFailAlloc_3664_, 1, v_nextMacroScope_3605_);
lean_ctor_set(v_reuseFailAlloc_3664_, 2, v_ngen_3606_);
lean_ctor_set(v_reuseFailAlloc_3664_, 3, v_auxDeclNGen_3607_);
lean_ctor_set(v_reuseFailAlloc_3664_, 4, v_traceState_3608_);
lean_ctor_set(v_reuseFailAlloc_3664_, 5, v___x_3616_);
lean_ctor_set(v_reuseFailAlloc_3664_, 6, v_messages_3609_);
lean_ctor_set(v_reuseFailAlloc_3664_, 7, v_infoState_3610_);
lean_ctor_set(v_reuseFailAlloc_3664_, 8, v_snapshotTasks_3611_);
v___x_3618_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v_mctx_3621_; lean_object* v_zetaDeltaFVarIds_3622_; lean_object* v_postponed_3623_; lean_object* v_diag_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3662_; 
v___x_3619_ = lean_st_ref_set(v___y_3598_, v___x_3618_);
v___x_3620_ = lean_st_ref_take(v___y_3596_);
v_mctx_3621_ = lean_ctor_get(v___x_3620_, 0);
v_zetaDeltaFVarIds_3622_ = lean_ctor_get(v___x_3620_, 2);
v_postponed_3623_ = lean_ctor_get(v___x_3620_, 3);
v_diag_3624_ = lean_ctor_get(v___x_3620_, 4);
v_isSharedCheck_3662_ = !lean_is_exclusive(v___x_3620_);
if (v_isSharedCheck_3662_ == 0)
{
lean_object* v_unused_3663_; 
v_unused_3663_ = lean_ctor_get(v___x_3620_, 1);
lean_dec(v_unused_3663_);
v___x_3626_ = v___x_3620_;
v_isShared_3627_ = v_isSharedCheck_3662_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_diag_3624_);
lean_inc(v_postponed_3623_);
lean_inc(v_zetaDeltaFVarIds_3622_);
lean_inc(v_mctx_3621_);
lean_dec(v___x_3620_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3662_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3628_; lean_object* v___x_3630_; 
v___x_3628_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0);
if (v_isShared_3627_ == 0)
{
lean_ctor_set(v___x_3626_, 1, v___x_3628_);
v___x_3630_ = v___x_3626_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_mctx_3621_);
lean_ctor_set(v_reuseFailAlloc_3661_, 1, v___x_3628_);
lean_ctor_set(v_reuseFailAlloc_3661_, 2, v_zetaDeltaFVarIds_3622_);
lean_ctor_set(v_reuseFailAlloc_3661_, 3, v_postponed_3623_);
lean_ctor_set(v_reuseFailAlloc_3661_, 4, v_diag_3624_);
v___x_3630_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
lean_object* v___x_3631_; lean_object* v_r_3632_; 
v___x_3631_ = lean_st_ref_set(v___y_3596_, v___x_3630_);
lean_inc(v___y_3598_);
lean_inc(v___y_3596_);
v_r_3632_ = lean_apply_5(v_x_3593_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, lean_box(0));
if (lean_obj_tag(v_r_3632_) == 0)
{
lean_object* v_a_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3649_; 
v_a_3633_ = lean_ctor_get(v_r_3632_, 0);
v_isSharedCheck_3649_ = !lean_is_exclusive(v_r_3632_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3635_ = v_r_3632_;
v_isShared_3636_ = v_isSharedCheck_3649_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v_r_3632_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3649_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___x_3638_; 
lean_inc(v_a_3633_);
if (v_isShared_3636_ == 0)
{
lean_ctor_set_tag(v___x_3635_, 1);
v___x_3638_ = v___x_3635_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_a_3633_);
v___x_3638_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
lean_object* v___x_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3646_; 
v___x_3639_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(v___y_3598_, v_isExporting_3602_, v___x_3616_, v___y_3596_, v___x_3628_, v___x_3638_);
lean_dec_ref(v___x_3638_);
lean_dec(v___y_3596_);
lean_dec(v___y_3598_);
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
lean_ctor_set(v___x_3641_, 0, v_a_3633_);
v___x_3644_ = v___x_3641_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v_a_3633_);
v___x_3644_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
return v___x_3644_;
}
}
}
}
}
else
{
lean_object* v_a_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3659_; 
v_a_3650_ = lean_ctor_get(v_r_3632_, 0);
lean_inc(v_a_3650_);
lean_dec_ref(v_r_3632_);
v___x_3651_ = lean_box(0);
v___x_3652_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(v___y_3598_, v_isExporting_3602_, v___x_3616_, v___y_3596_, v___x_3628_, v___x_3651_);
lean_dec(v___y_3596_);
lean_dec(v___y_3598_);
v_isSharedCheck_3659_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3659_ == 0)
{
lean_object* v_unused_3660_; 
v_unused_3660_ = lean_ctor_get(v___x_3652_, 0);
lean_dec(v_unused_3660_);
v___x_3654_ = v___x_3652_;
v_isShared_3655_ = v_isSharedCheck_3659_;
goto v_resetjp_3653_;
}
else
{
lean_dec(v___x_3652_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3659_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v___x_3657_; 
if (v_isShared_3655_ == 0)
{
lean_ctor_set_tag(v___x_3654_, 1);
lean_ctor_set(v___x_3654_, 0, v_a_3650_);
v___x_3657_ = v___x_3654_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v_a_3650_);
v___x_3657_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
return v___x_3657_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___boxed(lean_object* v_x_3667_, lean_object* v_isExporting_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_){
_start:
{
uint8_t v_isExporting_boxed_3674_; lean_object* v_res_3675_; 
v_isExporting_boxed_3674_ = lean_unbox(v_isExporting_3668_);
v_res_3675_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(v_x_3667_, v_isExporting_boxed_3674_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_);
return v_res_3675_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(lean_object* v_x_3676_, uint8_t v_when_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_){
_start:
{
if (v_when_3677_ == 0)
{
lean_object* v___x_3683_; 
v___x_3683_ = lean_apply_5(v_x_3676_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_, lean_box(0));
return v___x_3683_;
}
else
{
uint8_t v___x_3684_; lean_object* v___x_3685_; 
v___x_3684_ = 0;
v___x_3685_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(v_x_3676_, v___x_3684_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_);
return v___x_3685_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg___boxed(lean_object* v_x_3686_, lean_object* v_when_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_){
_start:
{
uint8_t v_when_boxed_3693_; lean_object* v_res_3694_; 
v_when_boxed_3693_ = lean_unbox(v_when_3687_);
v_res_3694_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(v_x_3686_, v_when_boxed_3693_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_);
return v_res_3694_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__0(lean_object* v_a_3695_, lean_object* v_a_3696_){
_start:
{
if (lean_obj_tag(v_a_3695_) == 0)
{
lean_object* v___x_3697_; 
v___x_3697_ = l_List_reverse___redArg(v_a_3696_);
return v___x_3697_;
}
else
{
lean_object* v_head_3698_; lean_object* v_tail_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3708_; 
v_head_3698_ = lean_ctor_get(v_a_3695_, 0);
v_tail_3699_ = lean_ctor_get(v_a_3695_, 1);
v_isSharedCheck_3708_ = !lean_is_exclusive(v_a_3695_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3701_ = v_a_3695_;
v_isShared_3702_ = v_isSharedCheck_3708_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_tail_3699_);
lean_inc(v_head_3698_);
lean_dec(v_a_3695_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3708_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3703_; lean_object* v___x_3705_; 
v___x_3703_ = l_Lean_mkLevelParam(v_head_3698_);
if (v_isShared_3702_ == 0)
{
lean_ctor_set(v___x_3701_, 1, v_a_3696_);
lean_ctor_set(v___x_3701_, 0, v___x_3703_);
v___x_3705_ = v___x_3701_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v___x_3703_);
lean_ctor_set(v_reuseFailAlloc_3707_, 1, v_a_3696_);
v___x_3705_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
v_a_3695_ = v_tail_3699_;
v_a_3696_ = v___x_3705_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0(lean_object* v_levelParams_3709_, lean_object* v_declName_3710_, lean_object* v_name_3711_, lean_object* v_xs_3712_, lean_object* v_body_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_){
_start:
{
lean_object* v___x_3719_; lean_object* v_us_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3719_ = lean_box(0);
lean_inc(v_levelParams_3709_);
v_us_3720_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__0(v_levelParams_3709_, v___x_3719_);
lean_inc(v_declName_3710_);
v___x_3721_ = l_Lean_mkConst(v_declName_3710_, v_us_3720_);
v___x_3722_ = l_Lean_mkAppN(v___x_3721_, v_xs_3712_);
lean_inc(v___y_3717_);
lean_inc_ref(v___y_3716_);
lean_inc(v___y_3715_);
lean_inc_ref(v___y_3714_);
v___x_3723_ = l_Lean_Meta_mkEq(v___x_3722_, v_body_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_);
if (lean_obj_tag(v___x_3723_) == 0)
{
lean_object* v_a_3724_; lean_object* v___x_3725_; uint8_t v___x_3726_; lean_object* v___x_3727_; 
v_a_3724_ = lean_ctor_get(v___x_3723_, 0);
lean_inc(v_a_3724_);
lean_dec_ref(v___x_3723_);
lean_inc(v_a_3724_);
v___x_3725_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___boxed), 7, 2);
lean_closure_set(v___x_3725_, 0, v_declName_3710_);
lean_closure_set(v___x_3725_, 1, v_a_3724_);
v___x_3726_ = 1;
lean_inc(v___y_3717_);
lean_inc_ref(v___y_3716_);
lean_inc(v___y_3715_);
lean_inc_ref(v___y_3714_);
v___x_3727_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(v___x_3725_, v___x_3726_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_);
if (lean_obj_tag(v___x_3727_) == 0)
{
lean_object* v_a_3728_; uint8_t v___x_3729_; uint8_t v___x_3730_; lean_object* v___x_3731_; 
v_a_3728_ = lean_ctor_get(v___x_3727_, 0);
lean_inc(v_a_3728_);
lean_dec_ref(v___x_3727_);
v___x_3729_ = 0;
v___x_3730_ = 1;
v___x_3731_ = l_Lean_Meta_mkForallFVars(v_xs_3712_, v_a_3724_, v___x_3729_, v___x_3726_, v___x_3726_, v___x_3730_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_);
if (lean_obj_tag(v___x_3731_) == 0)
{
lean_object* v_a_3732_; lean_object* v___x_3733_; 
v_a_3732_ = lean_ctor_get(v___x_3731_, 0);
lean_inc(v_a_3732_);
lean_dec_ref(v___x_3731_);
lean_inc(v___y_3717_);
lean_inc_ref(v___y_3716_);
lean_inc(v___y_3715_);
lean_inc_ref(v___y_3714_);
v___x_3733_ = l_Lean_Meta_letToHave(v_a_3732_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_);
if (lean_obj_tag(v___x_3733_) == 0)
{
lean_object* v_a_3734_; lean_object* v___x_3735_; 
v_a_3734_ = lean_ctor_get(v___x_3733_, 0);
lean_inc(v_a_3734_);
lean_dec_ref(v___x_3733_);
v___x_3735_ = l_Lean_Meta_mkLambdaFVars(v_xs_3712_, v_a_3728_, v___x_3729_, v___x_3726_, v___x_3729_, v___x_3726_, v___x_3730_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_);
if (lean_obj_tag(v___x_3735_) == 0)
{
lean_object* v_a_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; 
v_a_3736_ = lean_ctor_get(v___x_3735_, 0);
lean_inc(v_a_3736_);
lean_dec_ref(v___x_3735_);
lean_inc(v_name_3711_);
v___x_3737_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3737_, 0, v_name_3711_);
lean_ctor_set(v___x_3737_, 1, v_levelParams_3709_);
lean_ctor_set(v___x_3737_, 2, v_a_3734_);
lean_inc(v_name_3711_);
v___x_3738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3738_, 0, v_name_3711_);
lean_ctor_set(v___x_3738_, 1, v___x_3719_);
v___x_3739_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3737_);
lean_ctor_set(v___x_3739_, 1, v_a_3736_);
lean_ctor_set(v___x_3739_, 2, v___x_3738_);
v___x_3740_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3739_);
lean_inc(v___y_3717_);
lean_inc_ref(v___y_3716_);
v___x_3741_ = l_Lean_addDecl(v___x_3740_, v___x_3729_, v___y_3716_, v___y_3717_);
if (lean_obj_tag(v___x_3741_) == 0)
{
lean_object* v___x_3742_; 
lean_dec_ref(v___x_3741_);
v___x_3742_ = l_Lean_inferDefEqAttr(v_name_3711_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_);
return v___x_3742_;
}
else
{
lean_dec(v___y_3717_);
lean_dec_ref(v___y_3716_);
lean_dec(v___y_3715_);
lean_dec_ref(v___y_3714_);
lean_dec(v_name_3711_);
return v___x_3741_;
}
}
else
{
lean_object* v_a_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3750_; 
lean_dec(v_a_3734_);
lean_dec(v___y_3717_);
lean_dec_ref(v___y_3716_);
lean_dec(v___y_3715_);
lean_dec_ref(v___y_3714_);
lean_dec(v_name_3711_);
lean_dec(v_levelParams_3709_);
v_a_3743_ = lean_ctor_get(v___x_3735_, 0);
v_isSharedCheck_3750_ = !lean_is_exclusive(v___x_3735_);
if (v_isSharedCheck_3750_ == 0)
{
v___x_3745_ = v___x_3735_;
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_a_3743_);
lean_dec(v___x_3735_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___x_3748_; 
if (v_isShared_3746_ == 0)
{
v___x_3748_ = v___x_3745_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v_a_3743_);
v___x_3748_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
return v___x_3748_;
}
}
}
}
else
{
lean_object* v_a_3751_; lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_3758_; 
lean_dec(v_a_3728_);
lean_dec(v___y_3717_);
lean_dec_ref(v___y_3716_);
lean_dec(v___y_3715_);
lean_dec_ref(v___y_3714_);
lean_dec(v_name_3711_);
lean_dec(v_levelParams_3709_);
v_a_3751_ = lean_ctor_get(v___x_3733_, 0);
v_isSharedCheck_3758_ = !lean_is_exclusive(v___x_3733_);
if (v_isSharedCheck_3758_ == 0)
{
v___x_3753_ = v___x_3733_;
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
else
{
lean_inc(v_a_3751_);
lean_dec(v___x_3733_);
v___x_3753_ = lean_box(0);
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
v_resetjp_3752_:
{
lean_object* v___x_3756_; 
if (v_isShared_3754_ == 0)
{
v___x_3756_ = v___x_3753_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v_a_3751_);
v___x_3756_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
return v___x_3756_;
}
}
}
}
else
{
lean_object* v_a_3759_; lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3766_; 
lean_dec(v_a_3728_);
lean_dec(v___y_3717_);
lean_dec_ref(v___y_3716_);
lean_dec(v___y_3715_);
lean_dec_ref(v___y_3714_);
lean_dec(v_name_3711_);
lean_dec(v_levelParams_3709_);
v_a_3759_ = lean_ctor_get(v___x_3731_, 0);
v_isSharedCheck_3766_ = !lean_is_exclusive(v___x_3731_);
if (v_isSharedCheck_3766_ == 0)
{
v___x_3761_ = v___x_3731_;
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
else
{
lean_inc(v_a_3759_);
lean_dec(v___x_3731_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
lean_object* v___x_3764_; 
if (v_isShared_3762_ == 0)
{
v___x_3764_ = v___x_3761_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v_a_3759_);
v___x_3764_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
return v___x_3764_;
}
}
}
}
else
{
lean_object* v_a_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3774_; 
lean_dec(v_a_3724_);
lean_dec(v___y_3717_);
lean_dec_ref(v___y_3716_);
lean_dec(v___y_3715_);
lean_dec_ref(v___y_3714_);
lean_dec(v_name_3711_);
lean_dec(v_levelParams_3709_);
v_a_3767_ = lean_ctor_get(v___x_3727_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3727_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3769_ = v___x_3727_;
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_a_3767_);
lean_dec(v___x_3727_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v___x_3772_; 
if (v_isShared_3770_ == 0)
{
v___x_3772_ = v___x_3769_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v_a_3767_);
v___x_3772_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
return v___x_3772_;
}
}
}
}
else
{
lean_object* v_a_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3782_; 
lean_dec(v___y_3717_);
lean_dec_ref(v___y_3716_);
lean_dec(v___y_3715_);
lean_dec_ref(v___y_3714_);
lean_dec(v_name_3711_);
lean_dec(v_declName_3710_);
lean_dec(v_levelParams_3709_);
v_a_3775_ = lean_ctor_get(v___x_3723_, 0);
v_isSharedCheck_3782_ = !lean_is_exclusive(v___x_3723_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3777_ = v___x_3723_;
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_a_3775_);
lean_dec(v___x_3723_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
lean_object* v___x_3780_; 
if (v_isShared_3778_ == 0)
{
v___x_3780_ = v___x_3777_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_a_3775_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
return v___x_3780_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0___boxed(lean_object* v_levelParams_3783_, lean_object* v_declName_3784_, lean_object* v_name_3785_, lean_object* v_xs_3786_, lean_object* v_body_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_){
_start:
{
lean_object* v_res_3793_; 
v_res_3793_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0(v_levelParams_3783_, v_declName_3784_, v_name_3785_, v_xs_3786_, v_body_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
lean_dec_ref(v_xs_3786_);
return v_res_3793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3(lean_object* v_o_3794_, lean_object* v_k_3795_, uint8_t v_v_3796_){
_start:
{
lean_object* v_map_3797_; uint8_t v_hasTrace_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3812_; 
v_map_3797_ = lean_ctor_get(v_o_3794_, 0);
v_hasTrace_3798_ = lean_ctor_get_uint8(v_o_3794_, sizeof(void*)*1);
v_isSharedCheck_3812_ = !lean_is_exclusive(v_o_3794_);
if (v_isSharedCheck_3812_ == 0)
{
v___x_3800_ = v_o_3794_;
v_isShared_3801_ = v_isSharedCheck_3812_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_map_3797_);
lean_dec(v_o_3794_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3812_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
lean_object* v___x_3802_; lean_object* v___x_3803_; 
v___x_3802_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3802_, 0, v_v_3796_);
lean_inc(v_k_3795_);
v___x_3803_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_3795_, v___x_3802_, v_map_3797_);
if (v_hasTrace_3798_ == 0)
{
lean_object* v___x_3804_; uint8_t v___x_3805_; lean_object* v___x_3807_; 
v___x_3804_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___closed__1));
v___x_3805_ = l_Lean_Name_isPrefixOf(v___x_3804_, v_k_3795_);
lean_dec(v_k_3795_);
if (v_isShared_3801_ == 0)
{
lean_ctor_set(v___x_3800_, 0, v___x_3803_);
v___x_3807_ = v___x_3800_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v___x_3803_);
v___x_3807_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
lean_ctor_set_uint8(v___x_3807_, sizeof(void*)*1, v___x_3805_);
return v___x_3807_;
}
}
else
{
lean_object* v___x_3810_; 
lean_dec(v_k_3795_);
if (v_isShared_3801_ == 0)
{
lean_ctor_set(v___x_3800_, 0, v___x_3803_);
v___x_3810_ = v___x_3800_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v___x_3803_);
lean_ctor_set_uint8(v_reuseFailAlloc_3811_, sizeof(void*)*1, v_hasTrace_3798_);
v___x_3810_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
return v___x_3810_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3___boxed(lean_object* v_o_3813_, lean_object* v_k_3814_, lean_object* v_v_3815_){
_start:
{
uint8_t v_v_boxed_3816_; lean_object* v_res_3817_; 
v_v_boxed_3816_ = lean_unbox(v_v_3815_);
v_res_3817_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3(v_o_3813_, v_k_3814_, v_v_boxed_3816_);
return v_res_3817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2(lean_object* v_opts_3818_, lean_object* v_opt_3819_, uint8_t v_val_3820_){
_start:
{
lean_object* v_name_3821_; lean_object* v___x_3822_; 
v_name_3821_ = lean_ctor_get(v_opt_3819_, 0);
lean_inc(v_name_3821_);
lean_dec_ref(v_opt_3819_);
v___x_3822_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3(v_opts_3818_, v_name_3821_, v_val_3820_);
return v___x_3822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2___boxed(lean_object* v_opts_3823_, lean_object* v_opt_3824_, lean_object* v_val_3825_){
_start:
{
uint8_t v_val_boxed_3826_; lean_object* v_res_3827_; 
v_val_boxed_3826_ = lean_unbox(v_val_3825_);
v_res_3827_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2(v_opts_3823_, v_opt_3824_, v_val_boxed_3826_);
return v_res_3827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize(lean_object* v_declName_3828_, lean_object* v_info_3829_, lean_object* v_name_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_){
_start:
{
lean_object* v___x_3836_; lean_object* v_levelParams_3837_; lean_object* v_value_3838_; lean_object* v_fileName_3839_; lean_object* v_fileMap_3840_; lean_object* v_options_3841_; lean_object* v_currRecDepth_3842_; lean_object* v_ref_3843_; lean_object* v_currNamespace_3844_; lean_object* v_openDecls_3845_; lean_object* v_initHeartbeats_3846_; lean_object* v_maxHeartbeats_3847_; lean_object* v_quotContext_3848_; lean_object* v_currMacroScope_3849_; lean_object* v_cancelTk_x3f_3850_; uint8_t v_suppressElabErrors_3851_; lean_object* v_inheritedTraceOptions_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3907_; 
v___x_3836_ = lean_st_ref_get(v_a_3834_);
v_levelParams_3837_ = lean_ctor_get(v_info_3829_, 1);
lean_inc(v_levelParams_3837_);
v_value_3838_ = lean_ctor_get(v_info_3829_, 3);
lean_inc_ref(v_value_3838_);
lean_dec_ref(v_info_3829_);
v_fileName_3839_ = lean_ctor_get(v_a_3833_, 0);
v_fileMap_3840_ = lean_ctor_get(v_a_3833_, 1);
v_options_3841_ = lean_ctor_get(v_a_3833_, 2);
v_currRecDepth_3842_ = lean_ctor_get(v_a_3833_, 3);
v_ref_3843_ = lean_ctor_get(v_a_3833_, 5);
v_currNamespace_3844_ = lean_ctor_get(v_a_3833_, 6);
v_openDecls_3845_ = lean_ctor_get(v_a_3833_, 7);
v_initHeartbeats_3846_ = lean_ctor_get(v_a_3833_, 8);
v_maxHeartbeats_3847_ = lean_ctor_get(v_a_3833_, 9);
v_quotContext_3848_ = lean_ctor_get(v_a_3833_, 10);
v_currMacroScope_3849_ = lean_ctor_get(v_a_3833_, 11);
v_cancelTk_x3f_3850_ = lean_ctor_get(v_a_3833_, 12);
v_suppressElabErrors_3851_ = lean_ctor_get_uint8(v_a_3833_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3852_ = lean_ctor_get(v_a_3833_, 13);
v_isSharedCheck_3907_ = !lean_is_exclusive(v_a_3833_);
if (v_isSharedCheck_3907_ == 0)
{
lean_object* v_unused_3908_; 
v_unused_3908_ = lean_ctor_get(v_a_3833_, 4);
lean_dec(v_unused_3908_);
v___x_3854_ = v_a_3833_;
v_isShared_3855_ = v_isSharedCheck_3907_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_inheritedTraceOptions_3852_);
lean_inc(v_cancelTk_x3f_3850_);
lean_inc(v_currMacroScope_3849_);
lean_inc(v_quotContext_3848_);
lean_inc(v_maxHeartbeats_3847_);
lean_inc(v_initHeartbeats_3846_);
lean_inc(v_openDecls_3845_);
lean_inc(v_currNamespace_3844_);
lean_inc(v_ref_3843_);
lean_inc(v_currRecDepth_3842_);
lean_inc(v_options_3841_);
lean_inc(v_fileMap_3840_);
lean_inc(v_fileName_3839_);
lean_dec(v_a_3833_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3907_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v_env_3856_; lean_object* v___f_3857_; uint8_t v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; uint8_t v___x_3862_; lean_object* v_fileName_3864_; lean_object* v_fileMap_3865_; lean_object* v_currRecDepth_3866_; lean_object* v_ref_3867_; lean_object* v_currNamespace_3868_; lean_object* v_openDecls_3869_; lean_object* v_initHeartbeats_3870_; lean_object* v_maxHeartbeats_3871_; lean_object* v_quotContext_3872_; lean_object* v_currMacroScope_3873_; lean_object* v_cancelTk_x3f_3874_; uint8_t v_suppressElabErrors_3875_; lean_object* v_inheritedTraceOptions_3876_; lean_object* v___y_3877_; uint8_t v___y_3885_; uint8_t v___x_3906_; 
v_env_3856_ = lean_ctor_get(v___x_3836_, 0);
lean_inc_ref(v_env_3856_);
lean_dec(v___x_3836_);
v___f_3857_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3857_, 0, v_levelParams_3837_);
lean_closure_set(v___f_3857_, 1, v_declName_3828_);
lean_closure_set(v___f_3857_, 2, v_name_3830_);
v___x_3858_ = 0;
v___x_3859_ = l_Lean_Meta_tactic_hygienic;
v___x_3860_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2(v_options_3841_, v___x_3859_, v___x_3858_);
v___x_3861_ = l_Lean_diagnostics;
v___x_3862_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v___x_3860_, v___x_3861_);
v___x_3906_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3856_);
lean_dec_ref(v_env_3856_);
if (v___x_3906_ == 0)
{
if (v___x_3862_ == 0)
{
v_fileName_3864_ = v_fileName_3839_;
v_fileMap_3865_ = v_fileMap_3840_;
v_currRecDepth_3866_ = v_currRecDepth_3842_;
v_ref_3867_ = v_ref_3843_;
v_currNamespace_3868_ = v_currNamespace_3844_;
v_openDecls_3869_ = v_openDecls_3845_;
v_initHeartbeats_3870_ = v_initHeartbeats_3846_;
v_maxHeartbeats_3871_ = v_maxHeartbeats_3847_;
v_quotContext_3872_ = v_quotContext_3848_;
v_currMacroScope_3873_ = v_currMacroScope_3849_;
v_cancelTk_x3f_3874_ = v_cancelTk_x3f_3850_;
v_suppressElabErrors_3875_ = v_suppressElabErrors_3851_;
v_inheritedTraceOptions_3876_ = v_inheritedTraceOptions_3852_;
v___y_3877_ = v_a_3834_;
goto v___jp_3863_;
}
else
{
v___y_3885_ = v___x_3906_;
goto v___jp_3884_;
}
}
else
{
v___y_3885_ = v___x_3862_;
goto v___jp_3884_;
}
v___jp_3863_:
{
lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3881_; 
v___x_3878_ = l_Lean_maxRecDepth;
v___x_3879_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__9(v___x_3860_, v___x_3878_);
if (v_isShared_3855_ == 0)
{
lean_ctor_set(v___x_3854_, 13, v_inheritedTraceOptions_3876_);
lean_ctor_set(v___x_3854_, 12, v_cancelTk_x3f_3874_);
lean_ctor_set(v___x_3854_, 11, v_currMacroScope_3873_);
lean_ctor_set(v___x_3854_, 10, v_quotContext_3872_);
lean_ctor_set(v___x_3854_, 9, v_maxHeartbeats_3871_);
lean_ctor_set(v___x_3854_, 8, v_initHeartbeats_3870_);
lean_ctor_set(v___x_3854_, 7, v_openDecls_3869_);
lean_ctor_set(v___x_3854_, 6, v_currNamespace_3868_);
lean_ctor_set(v___x_3854_, 5, v_ref_3867_);
lean_ctor_set(v___x_3854_, 4, v___x_3879_);
lean_ctor_set(v___x_3854_, 3, v_currRecDepth_3866_);
lean_ctor_set(v___x_3854_, 2, v___x_3860_);
lean_ctor_set(v___x_3854_, 1, v_fileMap_3865_);
lean_ctor_set(v___x_3854_, 0, v_fileName_3864_);
v___x_3881_ = v___x_3854_;
goto v_reusejp_3880_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v_fileName_3864_);
lean_ctor_set(v_reuseFailAlloc_3883_, 1, v_fileMap_3865_);
lean_ctor_set(v_reuseFailAlloc_3883_, 2, v___x_3860_);
lean_ctor_set(v_reuseFailAlloc_3883_, 3, v_currRecDepth_3866_);
lean_ctor_set(v_reuseFailAlloc_3883_, 4, v___x_3879_);
lean_ctor_set(v_reuseFailAlloc_3883_, 5, v_ref_3867_);
lean_ctor_set(v_reuseFailAlloc_3883_, 6, v_currNamespace_3868_);
lean_ctor_set(v_reuseFailAlloc_3883_, 7, v_openDecls_3869_);
lean_ctor_set(v_reuseFailAlloc_3883_, 8, v_initHeartbeats_3870_);
lean_ctor_set(v_reuseFailAlloc_3883_, 9, v_maxHeartbeats_3871_);
lean_ctor_set(v_reuseFailAlloc_3883_, 10, v_quotContext_3872_);
lean_ctor_set(v_reuseFailAlloc_3883_, 11, v_currMacroScope_3873_);
lean_ctor_set(v_reuseFailAlloc_3883_, 12, v_cancelTk_x3f_3874_);
lean_ctor_set(v_reuseFailAlloc_3883_, 13, v_inheritedTraceOptions_3876_);
v___x_3881_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3880_;
}
v_reusejp_3880_:
{
lean_object* v___x_3882_; 
lean_ctor_set_uint8(v___x_3881_, sizeof(void*)*14, v___x_3862_);
lean_ctor_set_uint8(v___x_3881_, sizeof(void*)*14 + 1, v_suppressElabErrors_3875_);
v___x_3882_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(v_value_3838_, v___f_3857_, v___x_3858_, v_a_3831_, v_a_3832_, v___x_3881_, v___y_3877_);
return v___x_3882_;
}
}
v___jp_3884_:
{
if (v___y_3885_ == 0)
{
lean_object* v___x_3886_; lean_object* v_env_3887_; lean_object* v_nextMacroScope_3888_; lean_object* v_ngen_3889_; lean_object* v_auxDeclNGen_3890_; lean_object* v_traceState_3891_; lean_object* v_messages_3892_; lean_object* v_infoState_3893_; lean_object* v_snapshotTasks_3894_; lean_object* v___x_3896_; uint8_t v_isShared_3897_; uint8_t v_isSharedCheck_3904_; 
v___x_3886_ = lean_st_ref_take(v_a_3834_);
v_env_3887_ = lean_ctor_get(v___x_3886_, 0);
v_nextMacroScope_3888_ = lean_ctor_get(v___x_3886_, 1);
v_ngen_3889_ = lean_ctor_get(v___x_3886_, 2);
v_auxDeclNGen_3890_ = lean_ctor_get(v___x_3886_, 3);
v_traceState_3891_ = lean_ctor_get(v___x_3886_, 4);
v_messages_3892_ = lean_ctor_get(v___x_3886_, 6);
v_infoState_3893_ = lean_ctor_get(v___x_3886_, 7);
v_snapshotTasks_3894_ = lean_ctor_get(v___x_3886_, 8);
v_isSharedCheck_3904_ = !lean_is_exclusive(v___x_3886_);
if (v_isSharedCheck_3904_ == 0)
{
lean_object* v_unused_3905_; 
v_unused_3905_ = lean_ctor_get(v___x_3886_, 5);
lean_dec(v_unused_3905_);
v___x_3896_ = v___x_3886_;
v_isShared_3897_ = v_isSharedCheck_3904_;
goto v_resetjp_3895_;
}
else
{
lean_inc(v_snapshotTasks_3894_);
lean_inc(v_infoState_3893_);
lean_inc(v_messages_3892_);
lean_inc(v_traceState_3891_);
lean_inc(v_auxDeclNGen_3890_);
lean_inc(v_ngen_3889_);
lean_inc(v_nextMacroScope_3888_);
lean_inc(v_env_3887_);
lean_dec(v___x_3886_);
v___x_3896_ = lean_box(0);
v_isShared_3897_ = v_isSharedCheck_3904_;
goto v_resetjp_3895_;
}
v_resetjp_3895_:
{
lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3901_; 
v___x_3898_ = l_Lean_Kernel_enableDiag(v_env_3887_, v___x_3862_);
v___x_3899_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__2, &l_Lean_Elab_Structural_registerEqnsInfo___closed__2_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__2);
if (v_isShared_3897_ == 0)
{
lean_ctor_set(v___x_3896_, 5, v___x_3899_);
lean_ctor_set(v___x_3896_, 0, v___x_3898_);
v___x_3901_ = v___x_3896_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3903_; 
v_reuseFailAlloc_3903_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3903_, 0, v___x_3898_);
lean_ctor_set(v_reuseFailAlloc_3903_, 1, v_nextMacroScope_3888_);
lean_ctor_set(v_reuseFailAlloc_3903_, 2, v_ngen_3889_);
lean_ctor_set(v_reuseFailAlloc_3903_, 3, v_auxDeclNGen_3890_);
lean_ctor_set(v_reuseFailAlloc_3903_, 4, v_traceState_3891_);
lean_ctor_set(v_reuseFailAlloc_3903_, 5, v___x_3899_);
lean_ctor_set(v_reuseFailAlloc_3903_, 6, v_messages_3892_);
lean_ctor_set(v_reuseFailAlloc_3903_, 7, v_infoState_3893_);
lean_ctor_set(v_reuseFailAlloc_3903_, 8, v_snapshotTasks_3894_);
v___x_3901_ = v_reuseFailAlloc_3903_;
goto v_reusejp_3900_;
}
v_reusejp_3900_:
{
lean_object* v___x_3902_; 
v___x_3902_ = lean_st_ref_set(v_a_3834_, v___x_3901_);
v_fileName_3864_ = v_fileName_3839_;
v_fileMap_3865_ = v_fileMap_3840_;
v_currRecDepth_3866_ = v_currRecDepth_3842_;
v_ref_3867_ = v_ref_3843_;
v_currNamespace_3868_ = v_currNamespace_3844_;
v_openDecls_3869_ = v_openDecls_3845_;
v_initHeartbeats_3870_ = v_initHeartbeats_3846_;
v_maxHeartbeats_3871_ = v_maxHeartbeats_3847_;
v_quotContext_3872_ = v_quotContext_3848_;
v_currMacroScope_3873_ = v_currMacroScope_3849_;
v_cancelTk_x3f_3874_ = v_cancelTk_x3f_3850_;
v_suppressElabErrors_3875_ = v_suppressElabErrors_3851_;
v_inheritedTraceOptions_3876_ = v_inheritedTraceOptions_3852_;
v___y_3877_ = v_a_3834_;
goto v___jp_3863_;
}
}
}
else
{
v_fileName_3864_ = v_fileName_3839_;
v_fileMap_3865_ = v_fileMap_3840_;
v_currRecDepth_3866_ = v_currRecDepth_3842_;
v_ref_3867_ = v_ref_3843_;
v_currNamespace_3868_ = v_currNamespace_3844_;
v_openDecls_3869_ = v_openDecls_3845_;
v_initHeartbeats_3870_ = v_initHeartbeats_3846_;
v_maxHeartbeats_3871_ = v_maxHeartbeats_3847_;
v_quotContext_3872_ = v_quotContext_3848_;
v_currMacroScope_3873_ = v_currMacroScope_3849_;
v_cancelTk_x3f_3874_ = v_cancelTk_x3f_3850_;
v_suppressElabErrors_3875_ = v_suppressElabErrors_3851_;
v_inheritedTraceOptions_3876_ = v_inheritedTraceOptions_3852_;
v___y_3877_ = v_a_3834_;
goto v___jp_3863_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___boxed(lean_object* v_declName_3909_, lean_object* v_info_3910_, lean_object* v_name_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_, lean_object* v_a_3915_, lean_object* v_a_3916_){
_start:
{
lean_object* v_res_3917_; 
v_res_3917_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize(v_declName_3909_, v_info_3910_, v_name_3911_, v_a_3912_, v_a_3913_, v_a_3914_, v_a_3915_);
return v_res_3917_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1(lean_object* v_00_u03b1_3918_, lean_object* v_x_3919_, uint8_t v_isExporting_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_){
_start:
{
lean_object* v___x_3926_; 
v___x_3926_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(v_x_3919_, v_isExporting_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_);
return v___x_3926_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___boxed(lean_object* v_00_u03b1_3927_, lean_object* v_x_3928_, lean_object* v_isExporting_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_){
_start:
{
uint8_t v_isExporting_boxed_3935_; lean_object* v_res_3936_; 
v_isExporting_boxed_3935_ = lean_unbox(v_isExporting_3929_);
v_res_3936_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1(v_00_u03b1_3927_, v_x_3928_, v_isExporting_boxed_3935_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_);
return v_res_3936_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1(lean_object* v_00_u03b1_3937_, lean_object* v_x_3938_, uint8_t v_when_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_){
_start:
{
lean_object* v___x_3945_; 
v___x_3945_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(v_x_3938_, v_when_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_);
return v___x_3945_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___boxed(lean_object* v_00_u03b1_3946_, lean_object* v_x_3947_, lean_object* v_when_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_){
_start:
{
uint8_t v_when_boxed_3954_; lean_object* v_res_3955_; 
v_when_boxed_3954_ = lean_unbox(v_when_3948_);
v_res_3955_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1(v_00_u03b1_3946_, v_x_3947_, v_when_boxed_3954_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_);
return v_res_3955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq(lean_object* v_declName_3956_, lean_object* v_info_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_){
_start:
{
lean_object* v___x_3963_; lean_object* v_env_3964_; lean_object* v_declName_3965_; lean_object* v_declNames_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; 
v___x_3963_ = lean_st_ref_get(v_a_3961_);
v_env_3964_ = lean_ctor_get(v___x_3963_, 0);
lean_inc_ref(v_env_3964_);
lean_dec(v___x_3963_);
v_declName_3965_ = lean_ctor_get(v_info_3957_, 0);
v_declNames_3966_ = lean_ctor_get(v_info_3957_, 5);
v___x_3967_ = lean_box(0);
v___x_3968_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc(v_declName_3965_);
v___x_3969_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3964_, v_declName_3965_, v___x_3968_);
v___x_3970_ = lean_unsigned_to_nat(0u);
v___x_3971_ = lean_array_get(v___x_3967_, v_declNames_3966_, v___x_3970_);
lean_inc(v___x_3969_);
v___x_3972_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___boxed), 8, 3);
lean_closure_set(v___x_3972_, 0, v_declName_3956_);
lean_closure_set(v___x_3972_, 1, v_info_3957_);
lean_closure_set(v___x_3972_, 2, v___x_3969_);
lean_inc(v___x_3969_);
v___x_3973_ = l_Lean_Meta_realizeConst(v___x_3971_, v___x_3969_, v___x_3972_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_);
if (lean_obj_tag(v___x_3973_) == 0)
{
lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_3980_; 
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3973_);
if (v_isSharedCheck_3980_ == 0)
{
lean_object* v_unused_3981_; 
v_unused_3981_ = lean_ctor_get(v___x_3973_, 0);
lean_dec(v_unused_3981_);
v___x_3975_ = v___x_3973_;
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
else
{
lean_dec(v___x_3973_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v___x_3978_; 
if (v_isShared_3976_ == 0)
{
lean_ctor_set(v___x_3975_, 0, v___x_3969_);
v___x_3978_ = v___x_3975_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v___x_3969_);
v___x_3978_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
return v___x_3978_;
}
}
}
else
{
lean_object* v_a_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3989_; 
lean_dec(v___x_3969_);
v_a_3982_ = lean_ctor_get(v___x_3973_, 0);
v_isSharedCheck_3989_ = !lean_is_exclusive(v___x_3973_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3984_ = v___x_3973_;
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_a_3982_);
lean_dec(v___x_3973_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___x_3987_; 
if (v_isShared_3985_ == 0)
{
v___x_3987_ = v___x_3984_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v_a_3982_);
v___x_3987_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
return v___x_3987_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq___boxed(lean_object* v_declName_3990_, lean_object* v_info_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_){
_start:
{
lean_object* v_res_3997_; 
v_res_3997_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq(v_declName_3990_, v_info_3991_, v_a_3992_, v_a_3993_, v_a_3994_, v_a_3995_);
return v_res_3997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f(lean_object* v_declName_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_){
_start:
{
lean_object* v___x_4004_; lean_object* v_env_4005_; lean_object* v___x_4006_; lean_object* v_toEnvExtension_4007_; lean_object* v_asyncMode_4008_; lean_object* v___x_4009_; uint8_t v___x_4010_; lean_object* v___x_4011_; 
v___x_4004_ = lean_st_ref_get(v_a_4002_);
v_env_4005_ = lean_ctor_get(v___x_4004_, 0);
lean_inc_ref(v_env_4005_);
lean_dec(v___x_4004_);
v___x_4006_ = l_Lean_Elab_Structural_eqnInfoExt;
v_toEnvExtension_4007_ = lean_ctor_get(v___x_4006_, 0);
lean_inc_ref(v_toEnvExtension_4007_);
v_asyncMode_4008_ = lean_ctor_get(v_toEnvExtension_4007_, 2);
lean_inc(v_asyncMode_4008_);
lean_dec_ref(v_toEnvExtension_4007_);
v___x_4009_ = l_Lean_Elab_Structural_instInhabitedEqnInfo_default;
v___x_4010_ = 0;
lean_inc(v_declName_3998_);
v___x_4011_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_4009_, v___x_4006_, v_env_4005_, v_declName_3998_, v_asyncMode_4008_, v___x_4010_);
lean_dec(v_asyncMode_4008_);
if (lean_obj_tag(v___x_4011_) == 1)
{
lean_object* v_val_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4036_; 
v_val_4012_ = lean_ctor_get(v___x_4011_, 0);
v_isSharedCheck_4036_ = !lean_is_exclusive(v___x_4011_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_4014_ = v___x_4011_;
v_isShared_4015_ = v_isSharedCheck_4036_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_val_4012_);
lean_dec(v___x_4011_);
v___x_4014_ = lean_box(0);
v_isShared_4015_ = v_isSharedCheck_4036_;
goto v_resetjp_4013_;
}
v_resetjp_4013_:
{
lean_object* v___x_4016_; 
v___x_4016_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq(v_declName_3998_, v_val_4012_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_);
if (lean_obj_tag(v___x_4016_) == 0)
{
lean_object* v_a_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4027_; 
v_a_4017_ = lean_ctor_get(v___x_4016_, 0);
v_isSharedCheck_4027_ = !lean_is_exclusive(v___x_4016_);
if (v_isSharedCheck_4027_ == 0)
{
v___x_4019_ = v___x_4016_;
v_isShared_4020_ = v_isSharedCheck_4027_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_a_4017_);
lean_dec(v___x_4016_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4027_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v___x_4022_; 
if (v_isShared_4015_ == 0)
{
lean_ctor_set(v___x_4014_, 0, v_a_4017_);
v___x_4022_ = v___x_4014_;
goto v_reusejp_4021_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v_a_4017_);
v___x_4022_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4021_;
}
v_reusejp_4021_:
{
lean_object* v___x_4024_; 
if (v_isShared_4020_ == 0)
{
lean_ctor_set(v___x_4019_, 0, v___x_4022_);
v___x_4024_ = v___x_4019_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4025_; 
v_reuseFailAlloc_4025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4025_, 0, v___x_4022_);
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
else
{
lean_object* v_a_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4035_; 
lean_del_object(v___x_4014_);
v_a_4028_ = lean_ctor_get(v___x_4016_, 0);
v_isSharedCheck_4035_ = !lean_is_exclusive(v___x_4016_);
if (v_isSharedCheck_4035_ == 0)
{
v___x_4030_ = v___x_4016_;
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_a_4028_);
lean_dec(v___x_4016_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v___x_4033_; 
if (v_isShared_4031_ == 0)
{
v___x_4033_ = v___x_4030_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v_a_4028_);
v___x_4033_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
return v___x_4033_;
}
}
}
}
}
else
{
lean_object* v___x_4037_; lean_object* v___x_4038_; 
lean_dec(v___x_4011_);
lean_dec(v_a_4002_);
lean_dec_ref(v_a_4001_);
lean_dec(v_a_4000_);
lean_dec_ref(v_a_3999_);
lean_dec(v_declName_3998_);
v___x_4037_ = lean_box(0);
v___x_4038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4038_, 0, v___x_4037_);
return v___x_4038_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f___boxed(lean_object* v_declName_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_){
_start:
{
lean_object* v_res_4045_; 
v_res_4045_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f(v_declName_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_);
return v_res_4045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(lean_object* v_declName_4046_, lean_object* v_a_4047_){
_start:
{
lean_object* v___x_4049_; lean_object* v_env_4050_; lean_object* v___x_4051_; lean_object* v_toEnvExtension_4052_; lean_object* v_asyncMode_4053_; lean_object* v___x_4054_; uint8_t v___x_4055_; lean_object* v___x_4056_; 
v___x_4049_ = lean_st_ref_get(v_a_4047_);
v_env_4050_ = lean_ctor_get(v___x_4049_, 0);
lean_inc_ref(v_env_4050_);
lean_dec(v___x_4049_);
v___x_4051_ = l_Lean_Elab_Structural_eqnInfoExt;
v_toEnvExtension_4052_ = lean_ctor_get(v___x_4051_, 0);
lean_inc_ref(v_toEnvExtension_4052_);
v_asyncMode_4053_ = lean_ctor_get(v_toEnvExtension_4052_, 2);
lean_inc(v_asyncMode_4053_);
lean_dec_ref(v_toEnvExtension_4052_);
v___x_4054_ = l_Lean_Elab_Structural_instInhabitedEqnInfo_default;
v___x_4055_ = 0;
v___x_4056_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_4054_, v___x_4051_, v_env_4050_, v_declName_4046_, v_asyncMode_4053_, v___x_4055_);
lean_dec(v_asyncMode_4053_);
if (lean_obj_tag(v___x_4056_) == 1)
{
lean_object* v_val_4057_; lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4066_; 
v_val_4057_ = lean_ctor_get(v___x_4056_, 0);
v_isSharedCheck_4066_ = !lean_is_exclusive(v___x_4056_);
if (v_isSharedCheck_4066_ == 0)
{
v___x_4059_ = v___x_4056_;
v_isShared_4060_ = v_isSharedCheck_4066_;
goto v_resetjp_4058_;
}
else
{
lean_inc(v_val_4057_);
lean_dec(v___x_4056_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4066_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
lean_object* v_recArgPos_4061_; lean_object* v___x_4063_; 
v_recArgPos_4061_ = lean_ctor_get(v_val_4057_, 4);
lean_inc(v_recArgPos_4061_);
lean_dec(v_val_4057_);
if (v_isShared_4060_ == 0)
{
lean_ctor_set(v___x_4059_, 0, v_recArgPos_4061_);
v___x_4063_ = v___x_4059_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v_recArgPos_4061_);
v___x_4063_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
lean_object* v___x_4064_; 
v___x_4064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4064_, 0, v___x_4063_);
return v___x_4064_;
}
}
}
else
{
lean_object* v___x_4067_; lean_object* v___x_4068_; 
lean_dec(v___x_4056_);
v___x_4067_ = lean_box(0);
v___x_4068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4068_, 0, v___x_4067_);
return v___x_4068_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg___boxed(lean_object* v_declName_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_){
_start:
{
lean_object* v_res_4072_; 
v_res_4072_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(v_declName_4069_, v_a_4070_);
lean_dec(v_a_4070_);
return v_res_4072_;
}
}
LEAN_EXPORT lean_object* lean_get_structural_rec_arg_pos(lean_object* v_declName_4073_, lean_object* v_a_4074_, lean_object* v_a_4075_){
_start:
{
lean_object* v___x_4077_; 
lean_dec_ref(v_a_4074_);
v___x_4077_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(v_declName_4073_, v_a_4075_);
lean_dec(v_a_4075_);
return v___x_4077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___boxed(lean_object* v_declName_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_, lean_object* v_a_4081_){
_start:
{
lean_object* v_res_4082_; 
v_res_4082_ = lean_get_structural_rec_arg_pos(v_declName_4078_, v_a_4079_, v_a_4080_);
return v_res_4082_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; 
v___x_4140_ = lean_unsigned_to_nat(2295916746u);
v___x_4141_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__22_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_4142_ = l_Lean_Name_num___override(v___x_4141_, v___x_4140_);
return v___x_4142_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; 
v___x_4144_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__24_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_4145_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_4146_ = l_Lean_Name_str___override(v___x_4145_, v___x_4144_);
return v___x_4146_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; 
v___x_4148_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__26_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_4149_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_4150_ = l_Lean_Name_str___override(v___x_4149_, v___x_4148_);
return v___x_4150_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; 
v___x_4151_ = lean_unsigned_to_nat(2u);
v___x_4152_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_4153_ = l_Lean_Name_num___override(v___x_4152_, v___x_4151_);
return v___x_4153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4155_; lean_object* v___x_4156_; 
v___x_4155_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_4156_ = l_Lean_Meta_registerGetUnfoldEqnFn(v___x_4155_);
if (lean_obj_tag(v___x_4156_) == 0)
{
lean_object* v___x_4157_; uint8_t v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; 
lean_dec_ref(v___x_4156_);
v___x_4157_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4));
v___x_4158_ = 0;
v___x_4159_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_4160_ = l_Lean_registerTraceClass(v___x_4157_, v___x_4158_, v___x_4159_);
return v___x_4160_;
}
else
{
return v___x_4156_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2____boxed(lean_object* v_a_4161_){
_start:
{
lean_object* v_res_4162_; 
v_res_4162_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_();
return v_res_4162_;
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
res = l_Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_();
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
