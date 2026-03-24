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
lean_object* l_Lean_Meta_delta_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(lean_object* v_cls_765_, lean_object* v___y_766_){
_start:
{
lean_object* v_options_768_; uint8_t v_hasTrace_769_; 
v_options_768_ = lean_ctor_get(v___y_766_, 2);
v_hasTrace_769_ = lean_ctor_get_uint8(v_options_768_, sizeof(void*)*1);
if (v_hasTrace_769_ == 0)
{
lean_object* v___x_770_; lean_object* v___x_771_; 
lean_dec(v_cls_765_);
v___x_770_ = lean_box(v_hasTrace_769_);
v___x_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
return v___x_771_;
}
else
{
lean_object* v_inheritedTraceOptions_772_; lean_object* v___x_773_; lean_object* v___x_774_; uint8_t v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v_inheritedTraceOptions_772_ = lean_ctor_get(v___y_766_, 13);
v___x_773_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___closed__1));
v___x_774_ = l_Lean_Name_append(v___x_773_, v_cls_765_);
v___x_775_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_772_, v_options_768_, v___x_774_);
lean_dec(v___x_774_);
v___x_776_ = lean_box(v___x_775_);
v___x_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_777_, 0, v___x_776_);
return v___x_777_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___boxed(lean_object* v_cls_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_778_, v___y_779_);
lean_dec_ref(v___y_779_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(lean_object* v_cls_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_782_, v___y_785_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___boxed(lean_object* v_cls_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
return v_res_795_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_796_ = lean_unsigned_to_nat(32u);
v___x_797_ = lean_mk_empty_array_with_capacity(v___x_796_);
v___x_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
return v___x_798_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_799_ = ((size_t)5ULL);
v___x_800_ = lean_unsigned_to_nat(0u);
v___x_801_ = lean_unsigned_to_nat(32u);
v___x_802_ = lean_mk_empty_array_with_capacity(v___x_801_);
v___x_803_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__0);
v___x_804_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_804_, 0, v___x_803_);
lean_ctor_set(v___x_804_, 1, v___x_802_);
lean_ctor_set(v___x_804_, 2, v___x_800_);
lean_ctor_set(v___x_804_, 3, v___x_800_);
lean_ctor_set_usize(v___x_804_, 4, v___x_799_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg(lean_object* v___y_805_){
_start:
{
lean_object* v___x_807_; lean_object* v_traceState_808_; lean_object* v_traces_809_; lean_object* v___x_810_; lean_object* v_traceState_811_; lean_object* v_env_812_; lean_object* v_nextMacroScope_813_; lean_object* v_ngen_814_; lean_object* v_auxDeclNGen_815_; lean_object* v_cache_816_; lean_object* v_messages_817_; lean_object* v_infoState_818_; lean_object* v_snapshotTasks_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_838_; 
v___x_807_ = lean_st_ref_get(v___y_805_);
v_traceState_808_ = lean_ctor_get(v___x_807_, 4);
lean_inc_ref(v_traceState_808_);
lean_dec(v___x_807_);
v_traces_809_ = lean_ctor_get(v_traceState_808_, 0);
lean_inc_ref(v_traces_809_);
lean_dec_ref(v_traceState_808_);
v___x_810_ = lean_st_ref_take(v___y_805_);
v_traceState_811_ = lean_ctor_get(v___x_810_, 4);
v_env_812_ = lean_ctor_get(v___x_810_, 0);
v_nextMacroScope_813_ = lean_ctor_get(v___x_810_, 1);
v_ngen_814_ = lean_ctor_get(v___x_810_, 2);
v_auxDeclNGen_815_ = lean_ctor_get(v___x_810_, 3);
v_cache_816_ = lean_ctor_get(v___x_810_, 5);
v_messages_817_ = lean_ctor_get(v___x_810_, 6);
v_infoState_818_ = lean_ctor_get(v___x_810_, 7);
v_snapshotTasks_819_ = lean_ctor_get(v___x_810_, 8);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_838_ == 0)
{
v___x_821_ = v___x_810_;
v_isShared_822_ = v_isSharedCheck_838_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_snapshotTasks_819_);
lean_inc(v_infoState_818_);
lean_inc(v_messages_817_);
lean_inc(v_cache_816_);
lean_inc(v_traceState_811_);
lean_inc(v_auxDeclNGen_815_);
lean_inc(v_ngen_814_);
lean_inc(v_nextMacroScope_813_);
lean_inc(v_env_812_);
lean_dec(v___x_810_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_838_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
uint64_t v_tid_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_836_; 
v_tid_823_ = lean_ctor_get_uint64(v_traceState_811_, sizeof(void*)*1);
v_isSharedCheck_836_ = !lean_is_exclusive(v_traceState_811_);
if (v_isSharedCheck_836_ == 0)
{
lean_object* v_unused_837_; 
v_unused_837_ = lean_ctor_get(v_traceState_811_, 0);
lean_dec(v_unused_837_);
v___x_825_ = v_traceState_811_;
v_isShared_826_ = v_isSharedCheck_836_;
goto v_resetjp_824_;
}
else
{
lean_dec(v_traceState_811_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_836_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_827_; lean_object* v___x_829_; 
v___x_827_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___closed__1);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v___x_827_);
v___x_829_ = v___x_825_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_827_);
lean_ctor_set_uint64(v_reuseFailAlloc_835_, sizeof(void*)*1, v_tid_823_);
v___x_829_ = v_reuseFailAlloc_835_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
lean_object* v___x_831_; 
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 4, v___x_829_);
v___x_831_ = v___x_821_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_env_812_);
lean_ctor_set(v_reuseFailAlloc_834_, 1, v_nextMacroScope_813_);
lean_ctor_set(v_reuseFailAlloc_834_, 2, v_ngen_814_);
lean_ctor_set(v_reuseFailAlloc_834_, 3, v_auxDeclNGen_815_);
lean_ctor_set(v_reuseFailAlloc_834_, 4, v___x_829_);
lean_ctor_set(v_reuseFailAlloc_834_, 5, v_cache_816_);
lean_ctor_set(v_reuseFailAlloc_834_, 6, v_messages_817_);
lean_ctor_set(v_reuseFailAlloc_834_, 7, v_infoState_818_);
lean_ctor_set(v_reuseFailAlloc_834_, 8, v_snapshotTasks_819_);
v___x_831_ = v_reuseFailAlloc_834_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_832_ = lean_st_ref_set(v___y_805_, v___x_831_);
v___x_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_833_, 0, v_traces_809_);
return v___x_833_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg___boxed(lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg(v___y_839_);
lean_dec(v___y_839_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg(v___y_845_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___boxed(lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v___y_848_, v___y_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
return v_res_853_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(lean_object* v_opts_854_, lean_object* v_opt_855_){
_start:
{
lean_object* v_name_856_; lean_object* v_defValue_857_; lean_object* v_map_858_; lean_object* v___x_859_; 
v_name_856_ = lean_ctor_get(v_opt_855_, 0);
v_defValue_857_ = lean_ctor_get(v_opt_855_, 1);
v_map_858_ = lean_ctor_get(v_opts_854_, 0);
v___x_859_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_858_, v_name_856_);
if (lean_obj_tag(v___x_859_) == 0)
{
uint8_t v___x_860_; 
v___x_860_ = lean_unbox(v_defValue_857_);
return v___x_860_;
}
else
{
lean_object* v_val_861_; 
v_val_861_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_val_861_);
lean_dec_ref(v___x_859_);
if (lean_obj_tag(v_val_861_) == 1)
{
uint8_t v_v_862_; 
v_v_862_ = lean_ctor_get_uint8(v_val_861_, 0);
lean_dec_ref(v_val_861_);
return v_v_862_;
}
else
{
uint8_t v___x_863_; 
lean_dec(v_val_861_);
v___x_863_ = lean_unbox(v_defValue_857_);
return v___x_863_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___boxed(lean_object* v_opts_864_, lean_object* v_opt_865_){
_start:
{
uint8_t v_res_866_; lean_object* v_r_867_; 
v_res_866_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_opts_864_, v_opt_865_);
lean_dec_ref(v_opt_865_);
lean_dec_ref(v_opts_864_);
v_r_867_ = lean_box(v_res_866_);
return v_r_867_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1(void){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__0));
v___x_870_ = l_Lean_stringToMessageData(v___x_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0(lean_object* v_mvarId_871_, lean_object* v_x_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_878_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1);
v___x_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_879_, 0, v_mvarId_871_);
v___x_880_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_878_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___boxed(lean_object* v_mvarId_882_, lean_object* v_x_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0(v_mvarId_882_, v_x_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec_ref(v_x_883_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(lean_object* v_____r_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_896_ = lean_box(0);
v___x_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
return v___x_897_;
}
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__9(lean_object* v_opts_905_, lean_object* v_opt_906_){
_start:
{
lean_object* v_name_907_; lean_object* v_defValue_908_; lean_object* v_map_909_; lean_object* v___x_910_; 
v_name_907_ = lean_ctor_get(v_opt_906_, 0);
v_defValue_908_ = lean_ctor_get(v_opt_906_, 1);
v_map_909_ = lean_ctor_get(v_opts_905_, 0);
v___x_910_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_909_, v_name_907_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_inc(v_defValue_908_);
return v_defValue_908_;
}
else
{
lean_object* v_val_911_; 
v_val_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_val_911_);
lean_dec_ref(v___x_910_);
if (lean_obj_tag(v_val_911_) == 3)
{
lean_object* v_v_912_; 
v_v_912_ = lean_ctor_get(v_val_911_, 0);
lean_inc(v_v_912_);
lean_dec_ref(v_val_911_);
return v_v_912_;
}
else
{
lean_dec(v_val_911_);
lean_inc(v_defValue_908_);
return v_defValue_908_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__9___boxed(lean_object* v_opts_913_, lean_object* v_opt_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__9(v_opts_913_, v_opt_914_);
lean_dec_ref(v_opt_914_);
lean_dec_ref(v_opts_913_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__8___redArg(lean_object* v_x_916_){
_start:
{
if (lean_obj_tag(v_x_916_) == 0)
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
v_a_918_ = lean_ctor_get(v_x_916_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v_x_916_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v_x_916_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v_x_916_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_923_; 
if (v_isShared_921_ == 0)
{
lean_ctor_set_tag(v___x_920_, 1);
v___x_923_ = v___x_920_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_918_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
else
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
v_a_926_ = lean_ctor_get(v_x_916_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v_x_916_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v_x_916_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v_x_916_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
lean_ctor_set_tag(v___x_928_, 0);
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__8___redArg___boxed(lean_object* v_x_934_, lean_object* v___y_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__8___redArg(v_x_934_);
return v_res_936_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__6(lean_object* v_e_937_){
_start:
{
if (lean_obj_tag(v_e_937_) == 0)
{
uint8_t v___x_938_; 
v___x_938_ = 2;
return v___x_938_;
}
else
{
uint8_t v___x_939_; 
v___x_939_ = 0;
return v___x_939_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__6___boxed(lean_object* v_e_940_){
_start:
{
uint8_t v_res_941_; lean_object* v_r_942_; 
v_res_941_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__6(v_e_940_);
lean_dec_ref(v_e_940_);
v_r_942_ = lean_box(v_res_941_);
return v_r_942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__7_spec__8(size_t v_sz_943_, size_t v_i_944_, lean_object* v_bs_945_){
_start:
{
uint8_t v___x_946_; 
v___x_946_ = lean_usize_dec_lt(v_i_944_, v_sz_943_);
if (v___x_946_ == 0)
{
return v_bs_945_;
}
else
{
lean_object* v_v_947_; lean_object* v_msg_948_; lean_object* v___x_949_; lean_object* v_bs_x27_950_; size_t v___x_951_; size_t v___x_952_; lean_object* v___x_953_; 
v_v_947_ = lean_array_uget_borrowed(v_bs_945_, v_i_944_);
v_msg_948_ = lean_ctor_get(v_v_947_, 1);
lean_inc_ref(v_msg_948_);
v___x_949_ = lean_unsigned_to_nat(0u);
v_bs_x27_950_ = lean_array_uset(v_bs_945_, v_i_944_, v___x_949_);
v___x_951_ = ((size_t)1ULL);
v___x_952_ = lean_usize_add(v_i_944_, v___x_951_);
v___x_953_ = lean_array_uset(v_bs_x27_950_, v_i_944_, v_msg_948_);
v_i_944_ = v___x_952_;
v_bs_945_ = v___x_953_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__7_spec__8___boxed(lean_object* v_sz_955_, lean_object* v_i_956_, lean_object* v_bs_957_){
_start:
{
size_t v_sz_boxed_958_; size_t v_i_boxed_959_; lean_object* v_res_960_; 
v_sz_boxed_958_ = lean_unbox_usize(v_sz_955_);
lean_dec(v_sz_955_);
v_i_boxed_959_ = lean_unbox_usize(v_i_956_);
lean_dec(v_i_956_);
v_res_960_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__7_spec__8(v_sz_boxed_958_, v_i_boxed_959_, v_bs_957_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__7(lean_object* v_oldTraces_961_, lean_object* v_data_962_, lean_object* v_ref_963_, lean_object* v_msg_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v_fileName_970_; lean_object* v_fileMap_971_; lean_object* v_options_972_; lean_object* v_currRecDepth_973_; lean_object* v_maxRecDepth_974_; lean_object* v_ref_975_; lean_object* v_currNamespace_976_; lean_object* v_openDecls_977_; lean_object* v_initHeartbeats_978_; lean_object* v_maxHeartbeats_979_; lean_object* v_quotContext_980_; lean_object* v_currMacroScope_981_; uint8_t v_diag_982_; lean_object* v_cancelTk_x3f_983_; uint8_t v_suppressElabErrors_984_; lean_object* v_inheritedTraceOptions_985_; lean_object* v___x_986_; lean_object* v_traceState_987_; lean_object* v_traces_988_; lean_object* v_ref_989_; lean_object* v___x_990_; lean_object* v___x_991_; size_t v_sz_992_; size_t v___x_993_; lean_object* v___x_994_; lean_object* v_msg_995_; lean_object* v___x_996_; lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1034_; 
v_fileName_970_ = lean_ctor_get(v___y_967_, 0);
v_fileMap_971_ = lean_ctor_get(v___y_967_, 1);
v_options_972_ = lean_ctor_get(v___y_967_, 2);
v_currRecDepth_973_ = lean_ctor_get(v___y_967_, 3);
v_maxRecDepth_974_ = lean_ctor_get(v___y_967_, 4);
v_ref_975_ = lean_ctor_get(v___y_967_, 5);
v_currNamespace_976_ = lean_ctor_get(v___y_967_, 6);
v_openDecls_977_ = lean_ctor_get(v___y_967_, 7);
v_initHeartbeats_978_ = lean_ctor_get(v___y_967_, 8);
v_maxHeartbeats_979_ = lean_ctor_get(v___y_967_, 9);
v_quotContext_980_ = lean_ctor_get(v___y_967_, 10);
v_currMacroScope_981_ = lean_ctor_get(v___y_967_, 11);
v_diag_982_ = lean_ctor_get_uint8(v___y_967_, sizeof(void*)*14);
v_cancelTk_x3f_983_ = lean_ctor_get(v___y_967_, 12);
v_suppressElabErrors_984_ = lean_ctor_get_uint8(v___y_967_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_985_ = lean_ctor_get(v___y_967_, 13);
v___x_986_ = lean_st_ref_get(v___y_968_);
v_traceState_987_ = lean_ctor_get(v___x_986_, 4);
lean_inc_ref(v_traceState_987_);
lean_dec(v___x_986_);
v_traces_988_ = lean_ctor_get(v_traceState_987_, 0);
lean_inc_ref(v_traces_988_);
lean_dec_ref(v_traceState_987_);
v_ref_989_ = l_Lean_replaceRef(v_ref_963_, v_ref_975_);
lean_inc_ref(v_inheritedTraceOptions_985_);
lean_inc(v_cancelTk_x3f_983_);
lean_inc(v_currMacroScope_981_);
lean_inc(v_quotContext_980_);
lean_inc(v_maxHeartbeats_979_);
lean_inc(v_initHeartbeats_978_);
lean_inc(v_openDecls_977_);
lean_inc(v_currNamespace_976_);
lean_inc(v_maxRecDepth_974_);
lean_inc(v_currRecDepth_973_);
lean_inc_ref(v_options_972_);
lean_inc_ref(v_fileMap_971_);
lean_inc_ref(v_fileName_970_);
v___x_990_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_990_, 0, v_fileName_970_);
lean_ctor_set(v___x_990_, 1, v_fileMap_971_);
lean_ctor_set(v___x_990_, 2, v_options_972_);
lean_ctor_set(v___x_990_, 3, v_currRecDepth_973_);
lean_ctor_set(v___x_990_, 4, v_maxRecDepth_974_);
lean_ctor_set(v___x_990_, 5, v_ref_989_);
lean_ctor_set(v___x_990_, 6, v_currNamespace_976_);
lean_ctor_set(v___x_990_, 7, v_openDecls_977_);
lean_ctor_set(v___x_990_, 8, v_initHeartbeats_978_);
lean_ctor_set(v___x_990_, 9, v_maxHeartbeats_979_);
lean_ctor_set(v___x_990_, 10, v_quotContext_980_);
lean_ctor_set(v___x_990_, 11, v_currMacroScope_981_);
lean_ctor_set(v___x_990_, 12, v_cancelTk_x3f_983_);
lean_ctor_set(v___x_990_, 13, v_inheritedTraceOptions_985_);
lean_ctor_set_uint8(v___x_990_, sizeof(void*)*14, v_diag_982_);
lean_ctor_set_uint8(v___x_990_, sizeof(void*)*14 + 1, v_suppressElabErrors_984_);
v___x_991_ = l_Lean_PersistentArray_toArray___redArg(v_traces_988_);
lean_dec_ref(v_traces_988_);
v_sz_992_ = lean_array_size(v___x_991_);
v___x_993_ = ((size_t)0ULL);
v___x_994_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__7_spec__8(v_sz_992_, v___x_993_, v___x_991_);
v_msg_995_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_995_, 0, v_data_962_);
lean_ctor_set(v_msg_995_, 1, v_msg_964_);
lean_ctor_set(v_msg_995_, 2, v___x_994_);
v___x_996_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(v_msg_995_, v___y_965_, v___y_966_, v___x_990_, v___y_968_);
lean_dec_ref(v___x_990_);
v_a_997_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_999_ = v___x_996_;
v_isShared_1000_ = v_isSharedCheck_1034_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_996_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1034_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1001_; lean_object* v_traceState_1002_; lean_object* v_env_1003_; lean_object* v_nextMacroScope_1004_; lean_object* v_ngen_1005_; lean_object* v_auxDeclNGen_1006_; lean_object* v_cache_1007_; lean_object* v_messages_1008_; lean_object* v_infoState_1009_; lean_object* v_snapshotTasks_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1033_; 
v___x_1001_ = lean_st_ref_take(v___y_968_);
v_traceState_1002_ = lean_ctor_get(v___x_1001_, 4);
v_env_1003_ = lean_ctor_get(v___x_1001_, 0);
v_nextMacroScope_1004_ = lean_ctor_get(v___x_1001_, 1);
v_ngen_1005_ = lean_ctor_get(v___x_1001_, 2);
v_auxDeclNGen_1006_ = lean_ctor_get(v___x_1001_, 3);
v_cache_1007_ = lean_ctor_get(v___x_1001_, 5);
v_messages_1008_ = lean_ctor_get(v___x_1001_, 6);
v_infoState_1009_ = lean_ctor_get(v___x_1001_, 7);
v_snapshotTasks_1010_ = lean_ctor_get(v___x_1001_, 8);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1012_ = v___x_1001_;
v_isShared_1013_ = v_isSharedCheck_1033_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_snapshotTasks_1010_);
lean_inc(v_infoState_1009_);
lean_inc(v_messages_1008_);
lean_inc(v_cache_1007_);
lean_inc(v_traceState_1002_);
lean_inc(v_auxDeclNGen_1006_);
lean_inc(v_ngen_1005_);
lean_inc(v_nextMacroScope_1004_);
lean_inc(v_env_1003_);
lean_dec(v___x_1001_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1033_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
uint64_t v_tid_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1031_; 
v_tid_1014_ = lean_ctor_get_uint64(v_traceState_1002_, sizeof(void*)*1);
v_isSharedCheck_1031_ = !lean_is_exclusive(v_traceState_1002_);
if (v_isSharedCheck_1031_ == 0)
{
lean_object* v_unused_1032_; 
v_unused_1032_ = lean_ctor_get(v_traceState_1002_, 0);
lean_dec(v_unused_1032_);
v___x_1016_ = v_traceState_1002_;
v_isShared_1017_ = v_isSharedCheck_1031_;
goto v_resetjp_1015_;
}
else
{
lean_dec(v_traceState_1002_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1031_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1021_; 
v___x_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1018_, 0, v_ref_963_);
lean_ctor_set(v___x_1018_, 1, v_a_997_);
v___x_1019_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_961_, v___x_1018_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 0, v___x_1019_);
v___x_1021_ = v___x_1016_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1019_);
lean_ctor_set_uint64(v_reuseFailAlloc_1030_, sizeof(void*)*1, v_tid_1014_);
v___x_1021_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
lean_object* v___x_1023_; 
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 4, v___x_1021_);
v___x_1023_ = v___x_1012_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_env_1003_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_nextMacroScope_1004_);
lean_ctor_set(v_reuseFailAlloc_1029_, 2, v_ngen_1005_);
lean_ctor_set(v_reuseFailAlloc_1029_, 3, v_auxDeclNGen_1006_);
lean_ctor_set(v_reuseFailAlloc_1029_, 4, v___x_1021_);
lean_ctor_set(v_reuseFailAlloc_1029_, 5, v_cache_1007_);
lean_ctor_set(v_reuseFailAlloc_1029_, 6, v_messages_1008_);
lean_ctor_set(v_reuseFailAlloc_1029_, 7, v_infoState_1009_);
lean_ctor_set(v_reuseFailAlloc_1029_, 8, v_snapshotTasks_1010_);
v___x_1023_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1027_; 
v___x_1024_ = lean_st_ref_set(v___y_968_, v___x_1023_);
v___x_1025_ = lean_box(0);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v___x_1025_);
v___x_1027_ = v___x_999_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1025_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__7___boxed(lean_object* v_oldTraces_1035_, lean_object* v_data_1036_, lean_object* v_ref_1037_, lean_object* v_msg_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__7(v_oldTraces_1035_, v_data_1036_, v_ref_1037_, v_msg_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
return v_res_1044_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__1(void){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__0));
v___x_1047_ = l_Lean_stringToMessageData(v___x_1046_);
return v___x_1047_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__2(void){
_start:
{
lean_object* v___x_1048_; double v___x_1049_; 
v___x_1048_ = lean_unsigned_to_nat(0u);
v___x_1049_ = lean_float_of_nat(v___x_1048_);
return v___x_1049_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__4(void){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__3));
v___x_1052_ = l_Lean_stringToMessageData(v___x_1051_);
return v___x_1052_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__5(void){
_start:
{
lean_object* v___x_1053_; double v___x_1054_; 
v___x_1053_ = lean_unsigned_to_nat(1000u);
v___x_1054_ = lean_float_of_nat(v___x_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6(lean_object* v_cls_1055_, uint8_t v_collapsed_1056_, lean_object* v_tag_1057_, lean_object* v_opts_1058_, uint8_t v_clsEnabled_1059_, lean_object* v_oldTraces_1060_, lean_object* v_msg_1061_, lean_object* v_resStartStop_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v_fst_1068_; lean_object* v_snd_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1159_; 
v_fst_1068_ = lean_ctor_get(v_resStartStop_1062_, 0);
v_snd_1069_ = lean_ctor_get(v_resStartStop_1062_, 1);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_resStartStop_1062_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1071_ = v_resStartStop_1062_;
v_isShared_1072_ = v_isSharedCheck_1159_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_snd_1069_);
lean_inc(v_fst_1068_);
lean_dec(v_resStartStop_1062_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1159_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v_data_1076_; lean_object* v_fst_1079_; lean_object* v_snd_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1158_; 
v_fst_1079_ = lean_ctor_get(v_snd_1069_, 0);
v_snd_1080_ = lean_ctor_get(v_snd_1069_, 1);
v_isSharedCheck_1158_ = !lean_is_exclusive(v_snd_1069_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1082_ = v_snd_1069_;
v_isShared_1083_ = v_isSharedCheck_1158_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_snd_1080_);
lean_inc(v_fst_1079_);
lean_dec(v_snd_1069_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1158_;
goto v_resetjp_1081_;
}
v___jp_1073_:
{
lean_object* v___x_1077_; 
lean_inc(v___y_1075_);
v___x_1077_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__7(v_oldTraces_1060_, v_data_1076_, v___y_1075_, v___y_1074_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v___x_1078_; 
lean_dec_ref(v___x_1077_);
v___x_1078_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__8___redArg(v_fst_1068_);
return v___x_1078_;
}
else
{
lean_dec(v_fst_1068_);
return v___x_1077_;
}
}
v_resetjp_1081_:
{
lean_object* v___x_1084_; uint8_t v___x_1085_; lean_object* v___y_1087_; lean_object* v_a_1088_; uint8_t v___y_1112_; double v___y_1143_; 
v___x_1084_ = l_Lean_trace_profiler;
v___x_1085_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_opts_1058_, v___x_1084_);
if (v___x_1085_ == 0)
{
v___y_1112_ = v___x_1085_;
goto v___jp_1111_;
}
else
{
lean_object* v___x_1148_; uint8_t v___x_1149_; 
v___x_1148_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1149_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_opts_1058_, v___x_1148_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; lean_object* v___x_1151_; double v___x_1152_; double v___x_1153_; double v___x_1154_; 
v___x_1150_ = l_Lean_trace_profiler_threshold;
v___x_1151_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__9(v_opts_1058_, v___x_1150_);
v___x_1152_ = lean_float_of_nat(v___x_1151_);
v___x_1153_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__5);
v___x_1154_ = lean_float_div(v___x_1152_, v___x_1153_);
v___y_1143_ = v___x_1154_;
goto v___jp_1142_;
}
else
{
lean_object* v___x_1155_; lean_object* v___x_1156_; double v___x_1157_; 
v___x_1155_ = l_Lean_trace_profiler_threshold;
v___x_1156_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__9(v_opts_1058_, v___x_1155_);
v___x_1157_ = lean_float_of_nat(v___x_1156_);
v___y_1143_ = v___x_1157_;
goto v___jp_1142_;
}
}
v___jp_1086_:
{
uint8_t v_result_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1094_; 
v_result_1089_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__6(v_fst_1068_);
v___x_1090_ = l_Lean_TraceResult_toEmoji(v_result_1089_);
v___x_1091_ = l_Lean_stringToMessageData(v___x_1090_);
v___x_1092_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__1);
if (v_isShared_1083_ == 0)
{
lean_ctor_set_tag(v___x_1082_, 7);
lean_ctor_set(v___x_1082_, 1, v___x_1092_);
lean_ctor_set(v___x_1082_, 0, v___x_1091_);
v___x_1094_ = v___x_1082_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1091_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v___x_1092_);
v___x_1094_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
lean_object* v_m_1096_; 
if (v_isShared_1072_ == 0)
{
lean_ctor_set_tag(v___x_1071_, 7);
lean_ctor_set(v___x_1071_, 1, v_a_1088_);
lean_ctor_set(v___x_1071_, 0, v___x_1094_);
v_m_1096_ = v___x_1071_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1094_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v_a_1088_);
v_m_1096_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; double v___x_1099_; lean_object* v_data_1100_; 
v___x_1097_ = lean_box(v_result_1089_);
v___x_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
v___x_1099_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__2);
lean_inc_ref(v_tag_1057_);
lean_inc_ref(v___x_1098_);
lean_inc(v_cls_1055_);
v_data_1100_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1100_, 0, v_cls_1055_);
lean_ctor_set(v_data_1100_, 1, v___x_1098_);
lean_ctor_set(v_data_1100_, 2, v_tag_1057_);
lean_ctor_set_float(v_data_1100_, sizeof(void*)*3, v___x_1099_);
lean_ctor_set_float(v_data_1100_, sizeof(void*)*3 + 8, v___x_1099_);
lean_ctor_set_uint8(v_data_1100_, sizeof(void*)*3 + 16, v_collapsed_1056_);
if (v___x_1085_ == 0)
{
lean_dec_ref(v___x_1098_);
lean_dec(v_snd_1080_);
lean_dec(v_fst_1079_);
lean_dec_ref(v_tag_1057_);
lean_dec(v_cls_1055_);
v___y_1074_ = v_m_1096_;
v___y_1075_ = v___y_1087_;
v_data_1076_ = v_data_1100_;
goto v___jp_1073_;
}
else
{
lean_object* v_data_1101_; double v___x_1102_; double v___x_1103_; 
lean_dec_ref(v_data_1100_);
v_data_1101_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1101_, 0, v_cls_1055_);
lean_ctor_set(v_data_1101_, 1, v___x_1098_);
lean_ctor_set(v_data_1101_, 2, v_tag_1057_);
v___x_1102_ = lean_unbox_float(v_fst_1079_);
lean_dec(v_fst_1079_);
lean_ctor_set_float(v_data_1101_, sizeof(void*)*3, v___x_1102_);
v___x_1103_ = lean_unbox_float(v_snd_1080_);
lean_dec(v_snd_1080_);
lean_ctor_set_float(v_data_1101_, sizeof(void*)*3 + 8, v___x_1103_);
lean_ctor_set_uint8(v_data_1101_, sizeof(void*)*3 + 16, v_collapsed_1056_);
v___y_1074_ = v_m_1096_;
v___y_1075_ = v___y_1087_;
v_data_1076_ = v_data_1101_;
goto v___jp_1073_;
}
}
}
}
v___jp_1106_:
{
lean_object* v_ref_1107_; lean_object* v___x_1108_; 
v_ref_1107_ = lean_ctor_get(v___y_1065_, 5);
lean_inc(v___y_1066_);
lean_inc_ref(v___y_1065_);
lean_inc(v___y_1064_);
lean_inc_ref(v___y_1063_);
lean_inc(v_fst_1068_);
v___x_1108_ = lean_apply_6(v_msg_1061_, v_fst_1068_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, lean_box(0));
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v_a_1109_; 
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
lean_inc(v_a_1109_);
lean_dec_ref(v___x_1108_);
v___y_1087_ = v_ref_1107_;
v_a_1088_ = v_a_1109_;
goto v___jp_1086_;
}
else
{
lean_object* v___x_1110_; 
lean_dec_ref(v___x_1108_);
v___x_1110_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__4);
v___y_1087_ = v_ref_1107_;
v_a_1088_ = v___x_1110_;
goto v___jp_1086_;
}
}
v___jp_1111_:
{
if (v_clsEnabled_1059_ == 0)
{
if (v___y_1112_ == 0)
{
lean_object* v___x_1113_; lean_object* v_traceState_1114_; lean_object* v_env_1115_; lean_object* v_nextMacroScope_1116_; lean_object* v_ngen_1117_; lean_object* v_auxDeclNGen_1118_; lean_object* v_cache_1119_; lean_object* v_messages_1120_; lean_object* v_infoState_1121_; lean_object* v_snapshotTasks_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1141_; 
lean_del_object(v___x_1082_);
lean_dec(v_snd_1080_);
lean_dec(v_fst_1079_);
lean_del_object(v___x_1071_);
lean_dec_ref(v_msg_1061_);
lean_dec_ref(v_tag_1057_);
lean_dec(v_cls_1055_);
v___x_1113_ = lean_st_ref_take(v___y_1066_);
v_traceState_1114_ = lean_ctor_get(v___x_1113_, 4);
v_env_1115_ = lean_ctor_get(v___x_1113_, 0);
v_nextMacroScope_1116_ = lean_ctor_get(v___x_1113_, 1);
v_ngen_1117_ = lean_ctor_get(v___x_1113_, 2);
v_auxDeclNGen_1118_ = lean_ctor_get(v___x_1113_, 3);
v_cache_1119_ = lean_ctor_get(v___x_1113_, 5);
v_messages_1120_ = lean_ctor_get(v___x_1113_, 6);
v_infoState_1121_ = lean_ctor_get(v___x_1113_, 7);
v_snapshotTasks_1122_ = lean_ctor_get(v___x_1113_, 8);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1124_ = v___x_1113_;
v_isShared_1125_ = v_isSharedCheck_1141_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_snapshotTasks_1122_);
lean_inc(v_infoState_1121_);
lean_inc(v_messages_1120_);
lean_inc(v_cache_1119_);
lean_inc(v_traceState_1114_);
lean_inc(v_auxDeclNGen_1118_);
lean_inc(v_ngen_1117_);
lean_inc(v_nextMacroScope_1116_);
lean_inc(v_env_1115_);
lean_dec(v___x_1113_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1141_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
uint64_t v_tid_1126_; lean_object* v_traces_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1140_; 
v_tid_1126_ = lean_ctor_get_uint64(v_traceState_1114_, sizeof(void*)*1);
v_traces_1127_ = lean_ctor_get(v_traceState_1114_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v_traceState_1114_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1129_ = v_traceState_1114_;
v_isShared_1130_ = v_isSharedCheck_1140_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_traces_1127_);
lean_dec(v_traceState_1114_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1140_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1131_; lean_object* v___x_1133_; 
v___x_1131_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1060_, v_traces_1127_);
lean_dec_ref(v_traces_1127_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 0, v___x_1131_);
v___x_1133_ = v___x_1129_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1131_);
lean_ctor_set_uint64(v_reuseFailAlloc_1139_, sizeof(void*)*1, v_tid_1126_);
v___x_1133_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
lean_object* v___x_1135_; 
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 4, v___x_1133_);
v___x_1135_ = v___x_1124_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_env_1115_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v_nextMacroScope_1116_);
lean_ctor_set(v_reuseFailAlloc_1138_, 2, v_ngen_1117_);
lean_ctor_set(v_reuseFailAlloc_1138_, 3, v_auxDeclNGen_1118_);
lean_ctor_set(v_reuseFailAlloc_1138_, 4, v___x_1133_);
lean_ctor_set(v_reuseFailAlloc_1138_, 5, v_cache_1119_);
lean_ctor_set(v_reuseFailAlloc_1138_, 6, v_messages_1120_);
lean_ctor_set(v_reuseFailAlloc_1138_, 7, v_infoState_1121_);
lean_ctor_set(v_reuseFailAlloc_1138_, 8, v_snapshotTasks_1122_);
v___x_1135_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = lean_st_ref_set(v___y_1066_, v___x_1135_);
v___x_1137_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__8___redArg(v_fst_1068_);
return v___x_1137_;
}
}
}
}
}
else
{
goto v___jp_1106_;
}
}
else
{
goto v___jp_1106_;
}
}
v___jp_1142_:
{
double v___x_1144_; double v___x_1145_; double v___x_1146_; uint8_t v___x_1147_; 
v___x_1144_ = lean_unbox_float(v_snd_1080_);
v___x_1145_ = lean_unbox_float(v_fst_1079_);
v___x_1146_ = lean_float_sub(v___x_1144_, v___x_1145_);
v___x_1147_ = lean_float_decLt(v___y_1143_, v___x_1146_);
v___y_1112_ = v___x_1147_;
goto v___jp_1111_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___boxed(lean_object* v_cls_1160_, lean_object* v_collapsed_1161_, lean_object* v_tag_1162_, lean_object* v_opts_1163_, lean_object* v_clsEnabled_1164_, lean_object* v_oldTraces_1165_, lean_object* v_msg_1166_, lean_object* v_resStartStop_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
uint8_t v_collapsed_boxed_1173_; uint8_t v_clsEnabled_boxed_1174_; lean_object* v_res_1175_; 
v_collapsed_boxed_1173_ = lean_unbox(v_collapsed_1161_);
v_clsEnabled_boxed_1174_ = lean_unbox(v_clsEnabled_1164_);
v_res_1175_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6(v_cls_1160_, v_collapsed_boxed_1173_, v_tag_1162_, v_opts_1163_, v_clsEnabled_boxed_1174_, v_oldTraces_1165_, v_msg_1166_, v_resStartStop_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec_ref(v_opts_1163_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(lean_object* v_cls_1179_, lean_object* v_msg_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v_ref_1186_; lean_object* v___x_1187_; lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1232_; 
v_ref_1186_ = lean_ctor_get(v___y_1183_, 5);
v___x_1187_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(v_msg_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1190_ = v___x_1187_;
v_isShared_1191_ = v_isSharedCheck_1232_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1187_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1232_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1192_; lean_object* v_traceState_1193_; lean_object* v_env_1194_; lean_object* v_nextMacroScope_1195_; lean_object* v_ngen_1196_; lean_object* v_auxDeclNGen_1197_; lean_object* v_cache_1198_; lean_object* v_messages_1199_; lean_object* v_infoState_1200_; lean_object* v_snapshotTasks_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1231_; 
v___x_1192_ = lean_st_ref_take(v___y_1184_);
v_traceState_1193_ = lean_ctor_get(v___x_1192_, 4);
v_env_1194_ = lean_ctor_get(v___x_1192_, 0);
v_nextMacroScope_1195_ = lean_ctor_get(v___x_1192_, 1);
v_ngen_1196_ = lean_ctor_get(v___x_1192_, 2);
v_auxDeclNGen_1197_ = lean_ctor_get(v___x_1192_, 3);
v_cache_1198_ = lean_ctor_get(v___x_1192_, 5);
v_messages_1199_ = lean_ctor_get(v___x_1192_, 6);
v_infoState_1200_ = lean_ctor_get(v___x_1192_, 7);
v_snapshotTasks_1201_ = lean_ctor_get(v___x_1192_, 8);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1203_ = v___x_1192_;
v_isShared_1204_ = v_isSharedCheck_1231_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_snapshotTasks_1201_);
lean_inc(v_infoState_1200_);
lean_inc(v_messages_1199_);
lean_inc(v_cache_1198_);
lean_inc(v_traceState_1193_);
lean_inc(v_auxDeclNGen_1197_);
lean_inc(v_ngen_1196_);
lean_inc(v_nextMacroScope_1195_);
lean_inc(v_env_1194_);
lean_dec(v___x_1192_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1231_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
uint64_t v_tid_1205_; lean_object* v_traces_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1230_; 
v_tid_1205_ = lean_ctor_get_uint64(v_traceState_1193_, sizeof(void*)*1);
v_traces_1206_ = lean_ctor_get(v_traceState_1193_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_traceState_1193_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1208_ = v_traceState_1193_;
v_isShared_1209_ = v_isSharedCheck_1230_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_traces_1206_);
lean_dec(v_traceState_1193_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1230_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1210_; double v___x_1211_; uint8_t v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1220_; 
v___x_1210_ = lean_box(0);
v___x_1211_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__2);
v___x_1212_ = 0;
v___x_1213_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___closed__0));
v___x_1214_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1214_, 0, v_cls_1179_);
lean_ctor_set(v___x_1214_, 1, v___x_1210_);
lean_ctor_set(v___x_1214_, 2, v___x_1213_);
lean_ctor_set_float(v___x_1214_, sizeof(void*)*3, v___x_1211_);
lean_ctor_set_float(v___x_1214_, sizeof(void*)*3 + 8, v___x_1211_);
lean_ctor_set_uint8(v___x_1214_, sizeof(void*)*3 + 16, v___x_1212_);
v___x_1215_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___closed__1));
v___x_1216_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1214_);
lean_ctor_set(v___x_1216_, 1, v_a_1188_);
lean_ctor_set(v___x_1216_, 2, v___x_1215_);
lean_inc(v_ref_1186_);
v___x_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1217_, 0, v_ref_1186_);
lean_ctor_set(v___x_1217_, 1, v___x_1216_);
v___x_1218_ = l_Lean_PersistentArray_push___redArg(v_traces_1206_, v___x_1217_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v___x_1218_);
v___x_1220_ = v___x_1208_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1218_);
lean_ctor_set_uint64(v_reuseFailAlloc_1229_, sizeof(void*)*1, v_tid_1205_);
v___x_1220_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1222_; 
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 4, v___x_1220_);
v___x_1222_ = v___x_1203_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_env_1194_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v_nextMacroScope_1195_);
lean_ctor_set(v_reuseFailAlloc_1228_, 2, v_ngen_1196_);
lean_ctor_set(v_reuseFailAlloc_1228_, 3, v_auxDeclNGen_1197_);
lean_ctor_set(v_reuseFailAlloc_1228_, 4, v___x_1220_);
lean_ctor_set(v_reuseFailAlloc_1228_, 5, v_cache_1198_);
lean_ctor_set(v_reuseFailAlloc_1228_, 6, v_messages_1199_);
lean_ctor_set(v_reuseFailAlloc_1228_, 7, v_infoState_1200_);
lean_ctor_set(v_reuseFailAlloc_1228_, 8, v_snapshotTasks_1201_);
v___x_1222_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1226_; 
v___x_1223_ = lean_st_ref_set(v___y_1184_, v___x_1222_);
v___x_1224_ = lean_box(0);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 0, v___x_1224_);
v___x_1226_ = v___x_1190_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1224_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___boxed(lean_object* v_cls_1233_, lean_object* v_msg_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1233_, v_msg_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
return v_res_1240_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6(void){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5));
v___x_1252_ = l_Lean_stringToMessageData(v___x_1251_);
return v___x_1252_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8(void){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1254_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7));
v___x_1255_ = l_Lean_stringToMessageData(v___x_1254_);
return v___x_1255_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10(void){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9));
v___x_1258_ = l_Lean_stringToMessageData(v___x_1257_);
return v___x_1258_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__14(void){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1261_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15(void){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__14, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__14_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__14);
v___x_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
return v___x_1263_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12(void){
_start:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1264_ = lean_box(0);
v___x_1265_ = lean_unsigned_to_nat(16u);
v___x_1266_ = lean_mk_array(v___x_1265_, v___x_1264_);
return v___x_1266_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13(void){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1267_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
v___x_1268_ = lean_unsigned_to_nat(0u);
v___x_1269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1268_);
lean_ctor_set(v___x_1269_, 1, v___x_1267_);
return v___x_1269_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__16(void){
_start:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; lean_object* v___x_1273_; 
v___x_1270_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15);
v___x_1271_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13);
v___x_1272_ = 1;
v___x_1273_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1273_, 0, v___x_1271_);
lean_ctor_set(v___x_1273_, 1, v___x_1270_);
lean_ctor_set_uint8(v___x_1273_, sizeof(void*)*2, v___x_1272_);
return v___x_1273_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__18(void){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1274_ = lean_unsigned_to_nat(32u);
v___x_1275_ = lean_mk_empty_array_with_capacity(v___x_1274_);
v___x_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
return v___x_1276_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19(void){
_start:
{
size_t v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1277_ = ((size_t)5ULL);
v___x_1278_ = lean_unsigned_to_nat(0u);
v___x_1279_ = lean_unsigned_to_nat(32u);
v___x_1280_ = lean_mk_empty_array_with_capacity(v___x_1279_);
v___x_1281_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__18, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__18);
v___x_1282_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
lean_ctor_set(v___x_1282_, 1, v___x_1280_);
lean_ctor_set(v___x_1282_, 2, v___x_1278_);
lean_ctor_set(v___x_1282_, 3, v___x_1278_);
lean_ctor_set_usize(v___x_1282_, 4, v___x_1277_);
return v___x_1282_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20(void){
_start:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1283_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19);
v___x_1284_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15);
v___x_1285_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1284_);
lean_ctor_set(v___x_1285_, 1, v___x_1284_);
lean_ctor_set(v___x_1285_, 2, v___x_1284_);
lean_ctor_set(v___x_1285_, 3, v___x_1283_);
return v___x_1285_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17(void){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1286_ = lean_unsigned_to_nat(0u);
v___x_1287_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15);
v___x_1288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1287_);
lean_ctor_set(v___x_1288_, 1, v___x_1286_);
return v___x_1288_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21(void){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1289_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20);
v___x_1290_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17);
v___x_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
lean_ctor_set(v___x_1291_, 1, v___x_1289_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(lean_object* v_declName_1298_, lean_object* v_as_1299_, size_t v_i_1300_, size_t v_stop_1301_, lean_object* v_b_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
uint8_t v___x_1308_; 
v___x_1308_ = lean_usize_dec_eq(v_i_1300_, v_stop_1301_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = lean_array_uget_borrowed(v_as_1299_, v_i_1300_);
lean_inc(v___x_1309_);
lean_inc(v_declName_1298_);
v___x_1310_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1298_, v___x_1309_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; size_t v___x_1312_; size_t v___x_1313_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_a_1311_);
lean_dec_ref(v___x_1310_);
v___x_1312_ = ((size_t)1ULL);
v___x_1313_ = lean_usize_add(v_i_1300_, v___x_1312_);
v_i_1300_ = v___x_1313_;
v_b_1302_ = v_a_1311_;
goto _start;
}
else
{
lean_dec(v_declName_1298_);
return v___x_1310_;
}
}
else
{
lean_object* v___x_1315_; 
lean_dec(v_declName_1298_);
v___x_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1315_, 0, v_b_1302_);
return v___x_1315_;
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27(void){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__26));
v___x_1318_ = l_Lean_stringToMessageData(v___x_1317_);
return v___x_1318_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29(void){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__28));
v___x_1321_ = l_Lean_stringToMessageData(v___x_1320_);
return v___x_1321_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31(void){
_start:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1323_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__30));
v___x_1324_ = l_Lean_stringToMessageData(v___x_1323_);
return v___x_1324_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33(void){
_start:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__32));
v___x_1327_ = l_Lean_stringToMessageData(v___x_1326_);
return v___x_1327_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35(void){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__34));
v___x_1330_ = l_Lean_stringToMessageData(v___x_1329_);
return v___x_1330_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37(void){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__36));
v___x_1333_ = l_Lean_stringToMessageData(v___x_1332_);
return v___x_1333_;
}
}
static double _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38(void){
_start:
{
lean_object* v___x_1334_; double v___x_1335_; 
v___x_1334_ = lean_unsigned_to_nat(1000000000u);
v___x_1335_ = lean_float_of_nat(v___x_1334_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(lean_object* v_val_1336_, lean_object* v___x_1337_, lean_object* v_declName_1338_, lean_object* v_____r_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; uint8_t v___x_1347_; 
v___x_1345_ = lean_array_get_size(v_val_1336_);
v___x_1346_ = lean_box(0);
v___x_1347_ = lean_nat_dec_lt(v___x_1337_, v___x_1345_);
if (v___x_1347_ == 0)
{
lean_object* v___x_1348_; 
lean_dec(v_declName_1338_);
v___x_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1346_);
return v___x_1348_;
}
else
{
uint8_t v___x_1349_; 
v___x_1349_ = lean_nat_dec_le(v___x_1345_, v___x_1345_);
if (v___x_1349_ == 0)
{
if (v___x_1347_ == 0)
{
lean_object* v___x_1350_; 
lean_dec(v_declName_1338_);
v___x_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1346_);
return v___x_1350_;
}
else
{
size_t v___x_1351_; size_t v___x_1352_; lean_object* v___x_1353_; 
v___x_1351_ = ((size_t)0ULL);
v___x_1352_ = lean_usize_of_nat(v___x_1345_);
v___x_1353_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1338_, v_val_1336_, v___x_1351_, v___x_1352_, v___x_1346_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
return v___x_1353_;
}
}
else
{
size_t v___x_1354_; size_t v___x_1355_; lean_object* v___x_1356_; 
v___x_1354_ = ((size_t)0ULL);
v___x_1355_ = lean_usize_of_nat(v___x_1345_);
v___x_1356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1338_, v_val_1336_, v___x_1354_, v___x_1355_, v___x_1346_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
return v___x_1356_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(lean_object* v_declName_1357_, lean_object* v_mvarId_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_){
_start:
{
lean_object* v_options_1376_; uint8_t v_hasTrace_1377_; lean_object* v_cls_1378_; 
v_options_1376_ = lean_ctor_get(v_a_1361_, 2);
v_hasTrace_1377_ = lean_ctor_get_uint8(v_options_1376_, sizeof(void*)*1);
v_cls_1378_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4));
if (v_hasTrace_1377_ == 0)
{
lean_object* v___x_1379_; 
lean_inc_ref(v_a_1361_);
lean_inc(v_mvarId_1358_);
v___x_1379_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; uint8_t v___x_1381_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc(v_a_1380_);
lean_dec_ref(v___x_1379_);
v___x_1381_ = lean_unbox(v_a_1380_);
lean_dec(v_a_1380_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; 
lean_inc(v_mvarId_1358_);
v___x_1382_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_a_1383_; uint8_t v___x_1384_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_a_1383_);
lean_dec_ref(v___x_1382_);
v___x_1384_ = lean_unbox(v_a_1383_);
lean_dec(v_a_1383_);
if (v___x_1384_ == 0)
{
lean_object* v___x_1385_; 
lean_inc(v_mvarId_1358_);
v___x_1385_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_a_1386_);
lean_dec_ref(v___x_1385_);
if (lean_obj_tag(v_a_1386_) == 1)
{
lean_object* v_val_1387_; lean_object* v___x_1388_; 
lean_dec(v_mvarId_1358_);
v_val_1387_ = lean_ctor_get(v_a_1386_, 0);
lean_inc(v_val_1387_);
lean_dec_ref(v_a_1386_);
v___x_1388_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; uint8_t v___x_1390_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_a_1389_);
lean_dec_ref(v___x_1388_);
v___x_1390_ = lean_unbox(v_a_1389_);
lean_dec(v_a_1389_);
if (v___x_1390_ == 0)
{
v_mvarId_1358_ = v_val_1387_;
goto _start;
}
else
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1392_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6);
v___x_1393_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_1392_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_dec_ref(v___x_1393_);
v_mvarId_1358_ = v_val_1387_;
goto _start;
}
else
{
lean_dec(v_val_1387_);
lean_dec(v_declName_1357_);
return v___x_1393_;
}
}
}
else
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1402_; 
lean_dec(v_val_1387_);
lean_dec(v_declName_1357_);
v_a_1395_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1397_ = v___x_1388_;
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1388_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1400_; 
if (v_isShared_1398_ == 0)
{
v___x_1400_ = v___x_1397_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_a_1395_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
}
else
{
lean_object* v___x_1403_; 
lean_dec(v_a_1386_);
lean_inc(v_mvarId_1358_);
v___x_1403_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v_a_1404_; 
v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
lean_inc(v_a_1404_);
lean_dec_ref(v___x_1403_);
if (lean_obj_tag(v_a_1404_) == 1)
{
lean_object* v_val_1405_; lean_object* v___x_1406_; 
lean_dec(v_mvarId_1358_);
v_val_1405_ = lean_ctor_get(v_a_1404_, 0);
lean_inc(v_val_1405_);
lean_dec_ref(v_a_1404_);
v___x_1406_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v_a_1407_; uint8_t v___x_1408_; 
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_a_1407_);
lean_dec_ref(v___x_1406_);
v___x_1408_ = lean_unbox(v_a_1407_);
lean_dec(v_a_1407_);
if (v___x_1408_ == 0)
{
v_mvarId_1358_ = v_val_1405_;
goto _start;
}
else
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1410_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1411_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_1410_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_dec_ref(v___x_1411_);
v_mvarId_1358_ = v_val_1405_;
goto _start;
}
else
{
lean_dec(v_val_1405_);
lean_dec(v_declName_1357_);
return v___x_1411_;
}
}
}
else
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
lean_dec(v_val_1405_);
lean_dec(v_declName_1357_);
v_a_1413_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1406_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1406_);
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
else
{
uint8_t v___x_1421_; lean_object* v___x_1422_; 
lean_dec(v_a_1404_);
v___x_1421_ = 1;
lean_inc(v_mvarId_1358_);
v___x_1422_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1358_, v___x_1421_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1423_);
lean_dec_ref(v___x_1422_);
if (lean_obj_tag(v_a_1423_) == 1)
{
lean_object* v_val_1424_; lean_object* v___x_1425_; 
lean_dec(v_mvarId_1358_);
v_val_1424_ = lean_ctor_get(v_a_1423_, 0);
lean_inc(v_val_1424_);
lean_dec_ref(v_a_1423_);
v___x_1425_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1426_; uint8_t v___x_1427_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_a_1426_);
lean_dec_ref(v___x_1425_);
v___x_1427_ = lean_unbox(v_a_1426_);
lean_dec(v_a_1426_);
if (v___x_1427_ == 0)
{
v_mvarId_1358_ = v_val_1424_;
goto _start;
}
else
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1429_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
v___x_1430_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_1429_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_dec_ref(v___x_1430_);
v_mvarId_1358_ = v_val_1424_;
goto _start;
}
else
{
lean_dec(v_val_1424_);
lean_dec(v_declName_1357_);
return v___x_1430_;
}
}
}
else
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1439_; 
lean_dec(v_val_1424_);
lean_dec(v_declName_1357_);
v_a_1432_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1434_ = v___x_1425_;
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1425_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1437_; 
if (v_isShared_1435_ == 0)
{
v___x_1437_ = v___x_1434_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_a_1432_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
else
{
lean_object* v___x_1440_; lean_object* v___x_1441_; uint8_t v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
lean_dec(v_a_1423_);
v___x_1440_ = lean_unsigned_to_nat(100000u);
v___x_1441_ = lean_unsigned_to_nat(2u);
v___x_1442_ = 0;
v___x_1443_ = lean_box(0);
v___x_1444_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1444_, 0, v___x_1440_);
lean_ctor_set(v___x_1444_, 1, v___x_1441_);
lean_ctor_set(v___x_1444_, 2, v___x_1443_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*3, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*3 + 1, v___x_1421_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*3 + 2, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*3 + 3, v___x_1421_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*3 + 4, v___x_1421_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*3 + 5, v___x_1421_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*3 + 6, v___x_1442_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*3 + 7, v___x_1421_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*3 + 8, v___x_1421_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*3 + 9, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*3 + 10, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*3 + 11, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*3 + 12, v___x_1421_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*3 + 13, v___x_1421_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*3 + 14, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*3 + 15, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*3 + 16, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*3 + 17, v___x_1421_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*3 + 18, v___x_1421_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*3 + 19, v___x_1421_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*3 + 20, v___x_1421_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*3 + 21, v___x_1421_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*3 + 22, v___x_1421_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*3 + 23, v___x_1421_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*3 + 24, v___x_1421_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*3 + 25, v___x_1421_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*3 + 26, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*3 + 27, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*3 + 28, v_hasTrace_1377_);
v___x_1445_ = lean_unsigned_to_nat(0u);
v___x_1446_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__11));
v___x_1447_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__16, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__16_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__16);
v___x_1448_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1444_, v___x_1446_, v___x_1447_, v_a_1359_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_a_1449_);
lean_dec_ref(v___x_1448_);
v___x_1450_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21);
lean_inc(v_mvarId_1358_);
v___x_1451_ = l_Lean_Meta_simpTargetStar(v_mvarId_1358_, v_a_1449_, v___x_1446_, v___x_1443_, v___x_1450_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_a_1452_; lean_object* v_fst_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1601_; 
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_a_1452_);
lean_dec_ref(v___x_1451_);
v_fst_1453_ = lean_ctor_get(v_a_1452_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v_a_1452_);
if (v_isSharedCheck_1601_ == 0)
{
lean_object* v_unused_1602_; 
v_unused_1602_ = lean_ctor_get(v_a_1452_, 1);
lean_dec(v_unused_1602_);
v___x_1455_ = v_a_1452_;
v_isShared_1456_ = v_isSharedCheck_1601_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_fst_1453_);
lean_dec(v_a_1452_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1601_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
switch(lean_obj_tag(v_fst_1453_))
{
case 0:
{
lean_object* v___x_1457_; 
lean_del_object(v___x_1455_);
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v___x_1457_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1469_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1460_ = v___x_1457_;
v_isShared_1461_ = v_isSharedCheck_1469_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1457_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1469_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
uint8_t v___x_1462_; 
v___x_1462_ = lean_unbox(v_a_1458_);
lean_dec(v_a_1458_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; lean_object* v___x_1465_; 
v___x_1463_ = lean_box(0);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 0, v___x_1463_);
v___x_1465_ = v___x_1460_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1463_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
else
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
lean_del_object(v___x_1460_);
v___x_1467_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23);
v___x_1468_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_1467_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
return v___x_1468_;
}
}
}
else
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
v_a_1470_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1457_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1457_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
case 1:
{
lean_object* v___x_1478_; 
lean_inc(v_declName_1357_);
lean_inc(v_mvarId_1358_);
v___x_1478_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1358_, v_declName_1357_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v_a_1479_; 
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_a_1479_);
lean_dec_ref(v___x_1478_);
if (lean_obj_tag(v_a_1479_) == 1)
{
lean_object* v_val_1480_; lean_object* v___x_1481_; 
lean_del_object(v___x_1455_);
lean_dec(v_mvarId_1358_);
v_val_1480_ = lean_ctor_get(v_a_1479_, 0);
lean_inc(v_val_1480_);
lean_dec_ref(v_a_1479_);
v___x_1481_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v_a_1482_; uint8_t v___x_1483_; 
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
lean_inc(v_a_1482_);
lean_dec_ref(v___x_1481_);
v___x_1483_ = lean_unbox(v_a_1482_);
lean_dec(v_a_1482_);
if (v___x_1483_ == 0)
{
v_mvarId_1358_ = v_val_1480_;
goto _start;
}
else
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25);
v___x_1486_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_1485_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_dec_ref(v___x_1486_);
v_mvarId_1358_ = v_val_1480_;
goto _start;
}
else
{
lean_dec(v_val_1480_);
lean_dec(v_declName_1357_);
return v___x_1486_;
}
}
}
else
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1495_; 
lean_dec(v_val_1480_);
lean_dec(v_declName_1357_);
v_a_1488_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1490_ = v___x_1481_;
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1481_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1493_; 
if (v_isShared_1491_ == 0)
{
v___x_1493_ = v___x_1490_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_a_1488_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
else
{
lean_object* v___x_1496_; 
lean_dec(v_a_1479_);
lean_inc(v_mvarId_1358_);
v___x_1496_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1568_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1499_ = v___x_1496_;
v_isShared_1500_ = v_isSharedCheck_1568_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1496_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1568_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
if (lean_obj_tag(v_a_1497_) == 1)
{
lean_object* v_val_1501_; lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___x_1523_; 
lean_del_object(v___x_1455_);
lean_dec(v_mvarId_1358_);
v_val_1501_ = lean_ctor_get(v_a_1497_, 0);
lean_inc(v_val_1501_);
lean_dec_ref(v_a_1497_);
v___x_1523_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_a_1524_; uint8_t v___x_1525_; 
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_a_1524_);
lean_dec_ref(v___x_1523_);
v___x_1525_ = lean_unbox(v_a_1524_);
lean_dec(v_a_1524_);
if (v___x_1525_ == 0)
{
v___y_1503_ = v_a_1359_;
v___y_1504_ = v_a_1360_;
v___y_1505_ = v_a_1361_;
v___y_1506_ = v_a_1362_;
goto v___jp_1502_;
}
else
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27);
v___x_1527_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_1526_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_dec_ref(v___x_1527_);
v___y_1503_ = v_a_1359_;
v___y_1504_ = v_a_1360_;
v___y_1505_ = v_a_1361_;
v___y_1506_ = v_a_1362_;
goto v___jp_1502_;
}
else
{
lean_dec(v_val_1501_);
lean_del_object(v___x_1499_);
lean_dec(v_declName_1357_);
return v___x_1527_;
}
}
}
else
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1535_; 
lean_dec(v_val_1501_);
lean_del_object(v___x_1499_);
lean_dec(v_declName_1357_);
v_a_1528_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1530_ = v___x_1523_;
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1523_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1533_; 
if (v_isShared_1531_ == 0)
{
v___x_1533_ = v___x_1530_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_a_1528_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
v___jp_1502_:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; uint8_t v___x_1509_; 
v___x_1507_ = lean_array_get_size(v_val_1501_);
v___x_1508_ = lean_box(0);
v___x_1509_ = lean_nat_dec_lt(v___x_1445_, v___x_1507_);
if (v___x_1509_ == 0)
{
lean_object* v___x_1511_; 
lean_dec(v_val_1501_);
lean_dec(v_declName_1357_);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 0, v___x_1508_);
v___x_1511_ = v___x_1499_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___x_1508_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
else
{
uint8_t v___x_1513_; 
v___x_1513_ = lean_nat_dec_le(v___x_1507_, v___x_1507_);
if (v___x_1513_ == 0)
{
if (v___x_1509_ == 0)
{
lean_object* v___x_1515_; 
lean_dec(v_val_1501_);
lean_dec(v_declName_1357_);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 0, v___x_1508_);
v___x_1515_ = v___x_1499_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1508_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
else
{
size_t v___x_1517_; size_t v___x_1518_; lean_object* v___x_1519_; 
lean_del_object(v___x_1499_);
v___x_1517_ = ((size_t)0ULL);
v___x_1518_ = lean_usize_of_nat(v___x_1507_);
v___x_1519_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1357_, v_val_1501_, v___x_1517_, v___x_1518_, v___x_1508_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
lean_dec(v_val_1501_);
return v___x_1519_;
}
}
else
{
size_t v___x_1520_; size_t v___x_1521_; lean_object* v___x_1522_; 
lean_del_object(v___x_1499_);
v___x_1520_ = ((size_t)0ULL);
v___x_1521_ = lean_usize_of_nat(v___x_1507_);
v___x_1522_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1357_, v_val_1501_, v___x_1520_, v___x_1521_, v___x_1508_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
lean_dec(v_val_1501_);
return v___x_1522_;
}
}
}
}
else
{
lean_object* v___x_1536_; 
lean_del_object(v___x_1499_);
lean_dec(v_a_1497_);
lean_inc(v_mvarId_1358_);
v___x_1536_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1358_, v___x_1421_, v___x_1421_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_a_1537_);
lean_dec_ref(v___x_1536_);
if (lean_obj_tag(v_a_1537_) == 1)
{
lean_object* v_val_1538_; lean_object* v___x_1539_; 
lean_del_object(v___x_1455_);
lean_dec(v_mvarId_1358_);
v_val_1538_ = lean_ctor_get(v_a_1537_, 0);
lean_inc(v_val_1538_);
lean_dec_ref(v_a_1537_);
v___x_1539_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; uint8_t v___x_1541_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
lean_inc(v_a_1540_);
lean_dec_ref(v___x_1539_);
v___x_1541_ = lean_unbox(v_a_1540_);
lean_dec(v_a_1540_);
if (v___x_1541_ == 0)
{
lean_object* v___x_1542_; 
v___x_1542_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_declName_1357_, v_val_1538_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
return v___x_1542_;
}
else
{
lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1543_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29);
v___x_1544_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_1543_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v___x_1545_; 
lean_dec_ref(v___x_1544_);
v___x_1545_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_declName_1357_, v_val_1538_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
return v___x_1545_;
}
else
{
lean_dec(v_val_1538_);
lean_dec(v_declName_1357_);
return v___x_1544_;
}
}
}
else
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
lean_dec(v_val_1538_);
lean_dec(v_declName_1357_);
v_a_1546_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1548_ = v___x_1539_;
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1539_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1551_; 
if (v_isShared_1549_ == 0)
{
v___x_1551_ = v___x_1548_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_a_1546_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
else
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1557_; 
lean_dec(v_a_1537_);
lean_dec(v_declName_1357_);
v___x_1554_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31);
v___x_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1555_, 0, v_mvarId_1358_);
if (v_isShared_1456_ == 0)
{
lean_ctor_set_tag(v___x_1455_, 7);
lean_ctor_set(v___x_1455_, 1, v___x_1555_);
lean_ctor_set(v___x_1455_, 0, v___x_1554_);
v___x_1557_ = v___x_1455_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1554_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v___x_1555_);
v___x_1557_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
lean_object* v___x_1558_; 
v___x_1558_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1557_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
return v___x_1558_;
}
}
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
lean_del_object(v___x_1455_);
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_1560_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1536_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1536_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
}
}
else
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
lean_del_object(v___x_1455_);
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_1569_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___x_1496_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1496_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
}
else
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
lean_del_object(v___x_1455_);
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_1577_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1478_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1478_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
default: 
{
lean_object* v_mvarId_1585_; lean_object* v___x_1586_; 
lean_del_object(v___x_1455_);
lean_dec(v_mvarId_1358_);
v_mvarId_1585_ = lean_ctor_get(v_fst_1453_, 0);
lean_inc(v_mvarId_1585_);
lean_dec_ref(v_fst_1453_);
v___x_1586_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; uint8_t v___x_1588_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1587_);
lean_dec_ref(v___x_1586_);
v___x_1588_ = lean_unbox(v_a_1587_);
lean_dec(v_a_1587_);
if (v___x_1588_ == 0)
{
v_mvarId_1358_ = v_mvarId_1585_;
goto _start;
}
else
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33);
v___x_1591_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_1590_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_dec_ref(v___x_1591_);
v_mvarId_1358_ = v_mvarId_1585_;
goto _start;
}
else
{
lean_dec(v_mvarId_1585_);
lean_dec(v_declName_1357_);
return v___x_1591_;
}
}
}
else
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
lean_dec(v_mvarId_1585_);
lean_dec(v_declName_1357_);
v_a_1593_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1586_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1586_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_1603_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1451_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1451_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
else
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_1611_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1448_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1448_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_1619_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1422_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1422_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
}
else
{
lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1634_; 
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_1627_ = lean_ctor_get(v___x_1403_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1629_ = v___x_1403_;
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1403_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1632_; 
if (v_isShared_1630_ == 0)
{
v___x_1632_ = v___x_1629_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_a_1627_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
}
}
else
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1642_; 
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_1635_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1637_ = v___x_1385_;
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1385_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1640_; 
if (v_isShared_1638_ == 0)
{
v___x_1640_ = v___x_1637_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_a_1635_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
}
else
{
lean_object* v___x_1643_; 
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v___x_1643_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_a_1644_; uint8_t v___x_1645_; 
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
lean_inc(v_a_1644_);
lean_dec_ref(v___x_1643_);
v___x_1645_ = lean_unbox(v_a_1644_);
lean_dec(v_a_1644_);
if (v___x_1645_ == 0)
{
goto v___jp_1370_;
}
else
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1646_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35);
v___x_1647_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_1646_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_dec_ref(v___x_1647_);
goto v___jp_1370_;
}
else
{
return v___x_1647_;
}
}
}
else
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1655_; 
v_a_1648_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1650_ = v___x_1643_;
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1643_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_a_1648_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_1656_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1382_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1382_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
else
{
lean_object* v___x_1664_; 
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v___x_1664_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v_a_1665_; uint8_t v___x_1666_; 
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
lean_inc(v_a_1665_);
lean_dec_ref(v___x_1664_);
v___x_1666_ = lean_unbox(v_a_1665_);
lean_dec(v_a_1665_);
if (v___x_1666_ == 0)
{
goto v___jp_1373_;
}
else
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1667_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37);
v___x_1668_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_1667_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_dec_ref(v___x_1668_);
goto v___jp_1373_;
}
else
{
return v___x_1668_;
}
}
}
else
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
v_a_1669_ = lean_ctor_get(v___x_1664_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1671_ = v___x_1664_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1664_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_a_1669_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
}
}
else
{
lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1684_; 
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_1677_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1679_ = v___x_1379_;
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_a_1677_);
lean_dec(v___x_1379_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1682_; 
if (v_isShared_1680_ == 0)
{
v___x_1682_ = v___x_1679_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1677_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
}
else
{
lean_object* v___x_1685_; 
v___x_1685_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v_a_1686_; lean_object* v___f_1687_; lean_object* v___x_1688_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v_a_1692_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v_a_1705_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v_a_1710_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v_a_1721_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v_a_1737_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v_a_1742_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; uint8_t v___x_2082_; 
v_a_1686_ = lean_ctor_get(v___x_1685_, 0);
lean_inc(v_a_1686_);
lean_dec_ref(v___x_1685_);
lean_inc(v_mvarId_1358_);
v___f_1687_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1687_, 0, v_mvarId_1358_);
v___x_1688_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___closed__0));
v___x_2082_ = lean_unbox(v_a_1686_);
if (v___x_2082_ == 0)
{
lean_object* v___x_2083_; uint8_t v___x_2084_; 
v___x_2083_ = l_Lean_trace_profiler;
v___x_2084_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_options_1376_, v___x_2083_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2085_; 
lean_dec_ref(v___f_1687_);
lean_dec(v_a_1686_);
lean_inc_ref(v_a_1361_);
lean_inc(v_mvarId_1358_);
v___x_2085_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; uint8_t v___x_2087_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_a_2086_);
lean_dec_ref(v___x_2085_);
v___x_2087_ = lean_unbox(v_a_2086_);
lean_dec(v_a_2086_);
if (v___x_2087_ == 0)
{
lean_object* v___x_2088_; 
lean_inc(v_mvarId_1358_);
v___x_2088_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_a_2089_; uint8_t v___x_2090_; 
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_a_2089_);
lean_dec_ref(v___x_2088_);
v___x_2090_ = lean_unbox(v_a_2089_);
lean_dec(v_a_2089_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2091_; 
lean_inc(v_mvarId_1358_);
v___x_2091_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_a_2092_);
lean_dec_ref(v___x_2091_);
if (lean_obj_tag(v_a_2092_) == 1)
{
lean_object* v_val_2093_; lean_object* v___x_2094_; 
lean_dec(v_mvarId_1358_);
v_val_2093_ = lean_ctor_get(v_a_2092_, 0);
lean_inc(v_val_2093_);
lean_dec_ref(v_a_2092_);
v___x_2094_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; uint8_t v___x_2096_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2095_);
lean_dec_ref(v___x_2094_);
v___x_2096_ = lean_unbox(v_a_2095_);
lean_dec(v_a_2095_);
if (v___x_2096_ == 0)
{
v_mvarId_1358_ = v_val_2093_;
goto _start;
}
else
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2098_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6);
v___x_2099_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_2098_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_dec_ref(v___x_2099_);
v_mvarId_1358_ = v_val_2093_;
goto _start;
}
else
{
lean_dec(v_val_2093_);
lean_dec(v_declName_1357_);
return v___x_2099_;
}
}
}
else
{
lean_object* v_a_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2108_; 
lean_dec(v_val_2093_);
lean_dec(v_declName_1357_);
v_a_2101_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2103_ = v___x_2094_;
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_a_2101_);
lean_dec(v___x_2094_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2106_; 
if (v_isShared_2104_ == 0)
{
v___x_2106_ = v___x_2103_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_a_2101_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
}
else
{
lean_object* v___x_2109_; 
lean_dec(v_a_2092_);
lean_inc(v_mvarId_1358_);
v___x_2109_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_a_2110_; 
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
lean_inc(v_a_2110_);
lean_dec_ref(v___x_2109_);
if (lean_obj_tag(v_a_2110_) == 1)
{
lean_object* v_val_2111_; lean_object* v___x_2112_; 
lean_dec(v_mvarId_1358_);
v_val_2111_ = lean_ctor_get(v_a_2110_, 0);
lean_inc(v_val_2111_);
lean_dec_ref(v_a_2110_);
v___x_2112_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; uint8_t v___x_2114_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
lean_inc(v_a_2113_);
lean_dec_ref(v___x_2112_);
v___x_2114_ = lean_unbox(v_a_2113_);
lean_dec(v_a_2113_);
if (v___x_2114_ == 0)
{
v_mvarId_1358_ = v_val_2111_;
goto _start;
}
else
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2116_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_2117_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_2116_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_dec_ref(v___x_2117_);
v_mvarId_1358_ = v_val_2111_;
goto _start;
}
else
{
lean_dec(v_val_2111_);
lean_dec(v_declName_1357_);
return v___x_2117_;
}
}
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
lean_dec(v_val_2111_);
lean_dec(v_declName_1357_);
v_a_2119_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2112_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2112_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2122_ == 0)
{
v___x_2124_ = v___x_2121_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_a_2119_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
}
else
{
lean_object* v___x_2127_; 
lean_dec(v_a_2110_);
lean_inc(v_mvarId_1358_);
v___x_2127_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1358_, v_hasTrace_1377_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v_a_2128_; 
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
lean_inc(v_a_2128_);
lean_dec_ref(v___x_2127_);
if (lean_obj_tag(v_a_2128_) == 1)
{
lean_object* v_val_2129_; lean_object* v___x_2130_; 
lean_dec(v_mvarId_1358_);
v_val_2129_ = lean_ctor_get(v_a_2128_, 0);
lean_inc(v_val_2129_);
lean_dec_ref(v_a_2128_);
v___x_2130_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; uint8_t v___x_2132_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref(v___x_2130_);
v___x_2132_ = lean_unbox(v_a_2131_);
lean_dec(v_a_2131_);
if (v___x_2132_ == 0)
{
v_mvarId_1358_ = v_val_2129_;
goto _start;
}
else
{
lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2134_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
v___x_2135_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_2134_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_dec_ref(v___x_2135_);
v_mvarId_1358_ = v_val_2129_;
goto _start;
}
else
{
lean_dec(v_val_2129_);
lean_dec(v_declName_1357_);
return v___x_2135_;
}
}
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_dec(v_val_2129_);
lean_dec(v_declName_1357_);
v_a_2137_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2130_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2130_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
else
{
lean_object* v___x_2145_; lean_object* v___x_2146_; uint8_t v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
lean_dec(v_a_2128_);
v___x_2145_ = lean_unsigned_to_nat(100000u);
v___x_2146_ = lean_unsigned_to_nat(2u);
v___x_2147_ = 0;
v___x_2148_ = lean_box(0);
v___x_2149_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_2149_, 0, v___x_2145_);
lean_ctor_set(v___x_2149_, 1, v___x_2146_);
lean_ctor_set(v___x_2149_, 2, v___x_2148_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*3, v___x_2084_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*3 + 1, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*3 + 2, v___x_2084_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*3 + 3, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*3 + 4, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*3 + 5, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*3 + 6, v___x_2147_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*3 + 7, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*3 + 8, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*3 + 9, v___x_2084_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*3 + 10, v___x_2084_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*3 + 11, v___x_2084_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*3 + 12, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*3 + 13, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*3 + 14, v___x_2084_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*3 + 15, v___x_2084_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*3 + 16, v___x_2084_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*3 + 17, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*3 + 18, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*3 + 19, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*3 + 20, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*3 + 21, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*3 + 22, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*3 + 23, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*3 + 24, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*3 + 25, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*3 + 26, v___x_2084_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*3 + 27, v___x_2084_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*3 + 28, v___x_2084_);
v___x_2150_ = lean_unsigned_to_nat(0u);
v___x_2151_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__11));
v___x_2152_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13);
v___x_2153_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15);
v___x_2154_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2154_, 0, v___x_2152_);
lean_ctor_set(v___x_2154_, 1, v___x_2153_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*2, v_hasTrace_1377_);
v___x_2155_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_2149_, v___x_2151_, v___x_2154_, v_a_1359_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v_a_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
lean_inc(v_a_2156_);
lean_dec_ref(v___x_2155_);
v___x_2157_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21);
lean_inc(v_mvarId_1358_);
v___x_2158_ = l_Lean_Meta_simpTargetStar(v_mvarId_1358_, v_a_2156_, v___x_2151_, v___x_2148_, v___x_2157_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_object* v_a_2159_; lean_object* v_fst_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2308_; 
v_a_2159_ = lean_ctor_get(v___x_2158_, 0);
lean_inc(v_a_2159_);
lean_dec_ref(v___x_2158_);
v_fst_2160_ = lean_ctor_get(v_a_2159_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v_a_2159_);
if (v_isSharedCheck_2308_ == 0)
{
lean_object* v_unused_2309_; 
v_unused_2309_ = lean_ctor_get(v_a_2159_, 1);
lean_dec(v_unused_2309_);
v___x_2162_ = v_a_2159_;
v_isShared_2163_ = v_isSharedCheck_2308_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_fst_2160_);
lean_dec(v_a_2159_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2308_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
switch(lean_obj_tag(v_fst_2160_))
{
case 0:
{
lean_object* v___x_2164_; 
lean_del_object(v___x_2162_);
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v___x_2164_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2176_; 
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2167_ = v___x_2164_;
v_isShared_2168_ = v_isSharedCheck_2176_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2164_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2176_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
uint8_t v___x_2169_; 
v___x_2169_ = lean_unbox(v_a_2165_);
lean_dec(v_a_2165_);
if (v___x_2169_ == 0)
{
lean_object* v___x_2170_; lean_object* v___x_2172_; 
v___x_2170_ = lean_box(0);
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 0, v___x_2170_);
v___x_2172_ = v___x_2167_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2170_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
else
{
lean_object* v___x_2174_; lean_object* v___x_2175_; 
lean_del_object(v___x_2167_);
v___x_2174_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23);
v___x_2175_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_2174_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
return v___x_2175_;
}
}
}
else
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2184_; 
v_a_2177_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2179_ = v___x_2164_;
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2164_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2182_; 
if (v_isShared_2180_ == 0)
{
v___x_2182_ = v___x_2179_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_a_2177_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
}
case 1:
{
lean_object* v___x_2185_; 
lean_inc(v_declName_1357_);
lean_inc(v_mvarId_1358_);
v___x_2185_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1358_, v_declName_1357_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v_a_2186_; 
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
lean_inc(v_a_2186_);
lean_dec_ref(v___x_2185_);
if (lean_obj_tag(v_a_2186_) == 1)
{
lean_object* v_val_2187_; lean_object* v___x_2188_; 
lean_del_object(v___x_2162_);
lean_dec(v_mvarId_1358_);
v_val_2187_ = lean_ctor_get(v_a_2186_, 0);
lean_inc(v_val_2187_);
lean_dec_ref(v_a_2186_);
v___x_2188_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v_a_2189_; uint8_t v___x_2190_; 
v_a_2189_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_a_2189_);
lean_dec_ref(v___x_2188_);
v___x_2190_ = lean_unbox(v_a_2189_);
lean_dec(v_a_2189_);
if (v___x_2190_ == 0)
{
v_mvarId_1358_ = v_val_2187_;
goto _start;
}
else
{
lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2192_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25);
v___x_2193_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_2192_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_dec_ref(v___x_2193_);
v_mvarId_1358_ = v_val_2187_;
goto _start;
}
else
{
lean_dec(v_val_2187_);
lean_dec(v_declName_1357_);
return v___x_2193_;
}
}
}
else
{
lean_object* v_a_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2202_; 
lean_dec(v_val_2187_);
lean_dec(v_declName_1357_);
v_a_2195_ = lean_ctor_get(v___x_2188_, 0);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2197_ = v___x_2188_;
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_a_2195_);
lean_dec(v___x_2188_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___x_2200_; 
if (v_isShared_2198_ == 0)
{
v___x_2200_ = v___x_2197_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_a_2195_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
}
else
{
lean_object* v___x_2203_; 
lean_dec(v_a_2186_);
lean_inc(v_mvarId_1358_);
v___x_2203_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2275_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2206_ = v___x_2203_;
v_isShared_2207_ = v_isSharedCheck_2275_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2203_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2275_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
if (lean_obj_tag(v_a_2204_) == 1)
{
lean_object* v_val_2208_; lean_object* v___y_2210_; lean_object* v___y_2211_; lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v___x_2230_; 
lean_del_object(v___x_2162_);
lean_dec(v_mvarId_1358_);
v_val_2208_ = lean_ctor_get(v_a_2204_, 0);
lean_inc(v_val_2208_);
lean_dec_ref(v_a_2204_);
v___x_2230_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v_a_2231_; uint8_t v___x_2232_; 
v_a_2231_ = lean_ctor_get(v___x_2230_, 0);
lean_inc(v_a_2231_);
lean_dec_ref(v___x_2230_);
v___x_2232_ = lean_unbox(v_a_2231_);
lean_dec(v_a_2231_);
if (v___x_2232_ == 0)
{
v___y_2210_ = v_a_1359_;
v___y_2211_ = v_a_1360_;
v___y_2212_ = v_a_1361_;
v___y_2213_ = v_a_1362_;
goto v___jp_2209_;
}
else
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27);
v___x_2234_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_2233_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_dec_ref(v___x_2234_);
v___y_2210_ = v_a_1359_;
v___y_2211_ = v_a_1360_;
v___y_2212_ = v_a_1361_;
v___y_2213_ = v_a_1362_;
goto v___jp_2209_;
}
else
{
lean_dec(v_val_2208_);
lean_del_object(v___x_2206_);
lean_dec(v_declName_1357_);
return v___x_2234_;
}
}
}
else
{
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2242_; 
lean_dec(v_val_2208_);
lean_del_object(v___x_2206_);
lean_dec(v_declName_1357_);
v_a_2235_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2237_ = v___x_2230_;
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___x_2230_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2240_; 
if (v_isShared_2238_ == 0)
{
v___x_2240_ = v___x_2237_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2235_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
v___jp_2209_:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; uint8_t v___x_2216_; 
v___x_2214_ = lean_array_get_size(v_val_2208_);
v___x_2215_ = lean_box(0);
v___x_2216_ = lean_nat_dec_lt(v___x_2150_, v___x_2214_);
if (v___x_2216_ == 0)
{
lean_object* v___x_2218_; 
lean_dec(v_val_2208_);
lean_dec(v_declName_1357_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 0, v___x_2215_);
v___x_2218_ = v___x_2206_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v___x_2215_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
else
{
uint8_t v___x_2220_; 
v___x_2220_ = lean_nat_dec_le(v___x_2214_, v___x_2214_);
if (v___x_2220_ == 0)
{
if (v___x_2216_ == 0)
{
lean_object* v___x_2222_; 
lean_dec(v_val_2208_);
lean_dec(v_declName_1357_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 0, v___x_2215_);
v___x_2222_ = v___x_2206_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2215_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
else
{
size_t v___x_2224_; size_t v___x_2225_; lean_object* v___x_2226_; 
lean_del_object(v___x_2206_);
v___x_2224_ = ((size_t)0ULL);
v___x_2225_ = lean_usize_of_nat(v___x_2214_);
v___x_2226_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1357_, v_val_2208_, v___x_2224_, v___x_2225_, v___x_2215_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
lean_dec(v_val_2208_);
return v___x_2226_;
}
}
else
{
size_t v___x_2227_; size_t v___x_2228_; lean_object* v___x_2229_; 
lean_del_object(v___x_2206_);
v___x_2227_ = ((size_t)0ULL);
v___x_2228_ = lean_usize_of_nat(v___x_2214_);
v___x_2229_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1357_, v_val_2208_, v___x_2227_, v___x_2228_, v___x_2215_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
lean_dec(v_val_2208_);
return v___x_2229_;
}
}
}
}
else
{
lean_object* v___x_2243_; 
lean_del_object(v___x_2206_);
lean_dec(v_a_2204_);
lean_inc(v_mvarId_1358_);
v___x_2243_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1358_, v_hasTrace_1377_, v_hasTrace_1377_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_object* v_a_2244_; 
v_a_2244_ = lean_ctor_get(v___x_2243_, 0);
lean_inc(v_a_2244_);
lean_dec_ref(v___x_2243_);
if (lean_obj_tag(v_a_2244_) == 1)
{
lean_object* v_val_2245_; lean_object* v___x_2246_; 
lean_del_object(v___x_2162_);
lean_dec(v_mvarId_1358_);
v_val_2245_ = lean_ctor_get(v_a_2244_, 0);
lean_inc(v_val_2245_);
lean_dec_ref(v_a_2244_);
v___x_2246_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v_a_2247_; uint8_t v___x_2248_; 
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
lean_inc(v_a_2247_);
lean_dec_ref(v___x_2246_);
v___x_2248_ = lean_unbox(v_a_2247_);
lean_dec(v_a_2247_);
if (v___x_2248_ == 0)
{
lean_object* v___x_2249_; 
v___x_2249_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_declName_1357_, v_val_2245_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
return v___x_2249_;
}
else
{
lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2250_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29);
v___x_2251_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_2250_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v___x_2252_; 
lean_dec_ref(v___x_2251_);
v___x_2252_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_declName_1357_, v_val_2245_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
return v___x_2252_;
}
else
{
lean_dec(v_val_2245_);
lean_dec(v_declName_1357_);
return v___x_2251_;
}
}
}
else
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2260_; 
lean_dec(v_val_2245_);
lean_dec(v_declName_1357_);
v_a_2253_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2255_ = v___x_2246_;
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2246_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2258_; 
if (v_isShared_2256_ == 0)
{
v___x_2258_ = v___x_2255_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_a_2253_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
}
else
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2264_; 
lean_dec(v_a_2244_);
lean_dec(v_declName_1357_);
v___x_2261_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31);
v___x_2262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2262_, 0, v_mvarId_1358_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set_tag(v___x_2162_, 7);
lean_ctor_set(v___x_2162_, 1, v___x_2262_);
lean_ctor_set(v___x_2162_, 0, v___x_2261_);
v___x_2264_ = v___x_2162_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v___x_2261_);
lean_ctor_set(v_reuseFailAlloc_2266_, 1, v___x_2262_);
v___x_2264_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
lean_object* v___x_2265_; 
v___x_2265_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_2264_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
return v___x_2265_;
}
}
}
else
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2274_; 
lean_del_object(v___x_2162_);
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_2267_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2269_ = v___x_2243_;
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2243_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2272_; 
if (v_isShared_2270_ == 0)
{
v___x_2272_ = v___x_2269_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_a_2267_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
}
}
}
else
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2283_; 
lean_del_object(v___x_2162_);
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_2276_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2203_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2203_);
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
}
else
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2291_; 
lean_del_object(v___x_2162_);
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_2284_ = lean_ctor_get(v___x_2185_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2286_ = v___x_2185_;
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2185_);
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
default: 
{
lean_object* v_mvarId_2292_; lean_object* v___x_2293_; 
lean_del_object(v___x_2162_);
lean_dec(v_mvarId_1358_);
v_mvarId_2292_ = lean_ctor_get(v_fst_2160_, 0);
lean_inc(v_mvarId_2292_);
lean_dec_ref(v_fst_2160_);
v___x_2293_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; uint8_t v___x_2295_; 
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
lean_inc(v_a_2294_);
lean_dec_ref(v___x_2293_);
v___x_2295_ = lean_unbox(v_a_2294_);
lean_dec(v_a_2294_);
if (v___x_2295_ == 0)
{
v_mvarId_1358_ = v_mvarId_2292_;
goto _start;
}
else
{
lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2297_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33);
v___x_2298_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_2297_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_dec_ref(v___x_2298_);
v_mvarId_1358_ = v_mvarId_2292_;
goto _start;
}
else
{
lean_dec(v_mvarId_2292_);
lean_dec(v_declName_1357_);
return v___x_2298_;
}
}
}
else
{
lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2307_; 
lean_dec(v_mvarId_2292_);
lean_dec(v_declName_1357_);
v_a_2300_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2302_ = v___x_2293_;
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___x_2293_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2305_; 
if (v_isShared_2303_ == 0)
{
v___x_2305_ = v___x_2302_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_a_2300_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_2310_ = lean_ctor_get(v___x_2158_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2158_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2158_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2310_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_2318_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2155_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2155_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2318_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
}
else
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2333_; 
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_2326_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2328_ = v___x_2127_;
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2127_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2331_; 
if (v_isShared_2329_ == 0)
{
v___x_2331_ = v___x_2328_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2326_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
}
}
else
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_2334_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2109_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2109_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2334_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
}
else
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2349_; 
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_2342_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2344_ = v___x_2091_;
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2091_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2347_; 
if (v_isShared_2345_ == 0)
{
v___x_2347_ = v___x_2344_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2342_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
}
else
{
lean_object* v___x_2350_; 
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v___x_2350_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_a_2351_; uint8_t v___x_2352_; 
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
lean_inc(v_a_2351_);
lean_dec_ref(v___x_2350_);
v___x_2352_ = lean_unbox(v_a_2351_);
lean_dec(v_a_2351_);
if (v___x_2352_ == 0)
{
goto v___jp_1367_;
}
else
{
lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2353_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35);
v___x_2354_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_2353_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_2354_) == 0)
{
lean_dec_ref(v___x_2354_);
goto v___jp_1367_;
}
else
{
return v___x_2354_;
}
}
}
else
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
v_a_2355_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___x_2350_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2350_);
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
}
else
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2370_; 
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_2363_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2365_ = v___x_2088_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2088_);
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
else
{
lean_object* v___x_2371_; 
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v___x_2371_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_object* v_a_2372_; uint8_t v___x_2373_; 
v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
lean_inc(v_a_2372_);
lean_dec_ref(v___x_2371_);
v___x_2373_ = lean_unbox(v_a_2372_);
lean_dec(v_a_2372_);
if (v___x_2373_ == 0)
{
goto v___jp_1364_;
}
else
{
lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2374_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37);
v___x_2375_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_2374_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_2375_) == 0)
{
lean_dec_ref(v___x_2375_);
goto v___jp_1364_;
}
else
{
return v___x_2375_;
}
}
}
else
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2383_; 
v_a_2376_ = lean_ctor_get(v___x_2371_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2378_ = v___x_2371_;
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2371_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2381_; 
if (v_isShared_2379_ == 0)
{
v___x_2381_ = v___x_2378_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_a_2376_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
}
}
else
{
lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2391_; 
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_2384_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2386_ = v___x_2085_;
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2085_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2389_; 
if (v_isShared_2387_ == 0)
{
v___x_2389_ = v___x_2386_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2384_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
else
{
goto v___jp_1750_;
}
}
else
{
goto v___jp_1750_;
}
v___jp_1689_:
{
lean_object* v___x_1693_; double v___x_1694_; double v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; uint8_t v___x_1700_; lean_object* v___x_1701_; 
v___x_1693_ = lean_io_get_num_heartbeats();
v___x_1694_ = lean_float_of_nat(v___y_1690_);
v___x_1695_ = lean_float_of_nat(v___x_1693_);
v___x_1696_ = lean_box_float(v___x_1694_);
v___x_1697_ = lean_box_float(v___x_1695_);
v___x_1698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1696_);
lean_ctor_set(v___x_1698_, 1, v___x_1697_);
v___x_1699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1699_, 0, v_a_1692_);
lean_ctor_set(v___x_1699_, 1, v___x_1698_);
v___x_1700_ = lean_unbox(v_a_1686_);
lean_dec(v_a_1686_);
v___x_1701_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6(v_cls_1378_, v_hasTrace_1377_, v___x_1688_, v_options_1376_, v___x_1700_, v___y_1691_, v___f_1687_, v___x_1699_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
return v___x_1701_;
}
v___jp_1702_:
{
lean_object* v___x_1706_; 
v___x_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1706_, 0, v_a_1705_);
v___y_1690_ = v___y_1703_;
v___y_1691_ = v___y_1704_;
v_a_1692_ = v___x_1706_;
goto v___jp_1689_;
}
v___jp_1707_:
{
lean_object* v___x_1711_; 
v___x_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1711_, 0, v_a_1710_);
v___y_1690_ = v___y_1708_;
v___y_1691_ = v___y_1709_;
v_a_1692_ = v___x_1711_;
goto v___jp_1689_;
}
v___jp_1712_:
{
if (lean_obj_tag(v___y_1715_) == 0)
{
lean_object* v_a_1716_; 
v_a_1716_ = lean_ctor_get(v___y_1715_, 0);
lean_inc(v_a_1716_);
lean_dec_ref(v___y_1715_);
v___y_1703_ = v___y_1713_;
v___y_1704_ = v___y_1714_;
v_a_1705_ = v_a_1716_;
goto v___jp_1702_;
}
else
{
lean_object* v_a_1717_; 
v_a_1717_ = lean_ctor_get(v___y_1715_, 0);
lean_inc(v_a_1717_);
lean_dec_ref(v___y_1715_);
v___y_1708_ = v___y_1713_;
v___y_1709_ = v___y_1714_;
v_a_1710_ = v_a_1717_;
goto v___jp_1707_;
}
}
v___jp_1718_:
{
lean_object* v___x_1722_; double v___x_1723_; double v___x_1724_; double v___x_1725_; double v___x_1726_; double v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; uint8_t v___x_1732_; lean_object* v___x_1733_; 
v___x_1722_ = lean_io_mono_nanos_now();
v___x_1723_ = lean_float_of_nat(v___y_1720_);
v___x_1724_ = lean_float_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38);
v___x_1725_ = lean_float_div(v___x_1723_, v___x_1724_);
v___x_1726_ = lean_float_of_nat(v___x_1722_);
v___x_1727_ = lean_float_div(v___x_1726_, v___x_1724_);
v___x_1728_ = lean_box_float(v___x_1725_);
v___x_1729_ = lean_box_float(v___x_1727_);
v___x_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1728_);
lean_ctor_set(v___x_1730_, 1, v___x_1729_);
v___x_1731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1731_, 0, v_a_1721_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
v___x_1732_ = lean_unbox(v_a_1686_);
lean_dec(v_a_1686_);
v___x_1733_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6(v_cls_1378_, v_hasTrace_1377_, v___x_1688_, v_options_1376_, v___x_1732_, v___y_1719_, v___f_1687_, v___x_1731_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
return v___x_1733_;
}
v___jp_1734_:
{
lean_object* v___x_1738_; 
v___x_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1738_, 0, v_a_1737_);
v___y_1719_ = v___y_1735_;
v___y_1720_ = v___y_1736_;
v_a_1721_ = v___x_1738_;
goto v___jp_1718_;
}
v___jp_1739_:
{
lean_object* v___x_1743_; 
v___x_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1743_, 0, v_a_1742_);
v___y_1719_ = v___y_1740_;
v___y_1720_ = v___y_1741_;
v_a_1721_ = v___x_1743_;
goto v___jp_1718_;
}
v___jp_1744_:
{
if (lean_obj_tag(v___y_1747_) == 0)
{
lean_object* v_a_1748_; 
v_a_1748_ = lean_ctor_get(v___y_1747_, 0);
lean_inc(v_a_1748_);
lean_dec_ref(v___y_1747_);
v___y_1740_ = v___y_1745_;
v___y_1741_ = v___y_1746_;
v_a_1742_ = v_a_1748_;
goto v___jp_1739_;
}
else
{
lean_object* v_a_1749_; 
v_a_1749_ = lean_ctor_get(v___y_1747_, 0);
lean_inc(v_a_1749_);
lean_dec_ref(v___y_1747_);
v___y_1735_ = v___y_1745_;
v___y_1736_ = v___y_1746_;
v_a_1737_ = v_a_1749_;
goto v___jp_1734_;
}
}
v___jp_1750_:
{
lean_object* v___x_1751_; 
v___x_1751_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg(v_a_1362_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v_a_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; 
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_a_1752_);
lean_dec_ref(v___x_1751_);
v___x_1753_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1754_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_options_1376_, v___x_1753_);
if (v___x_1754_ == 0)
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1755_ = lean_io_mono_nanos_now();
lean_inc_ref(v_a_1361_);
lean_inc(v_mvarId_1358_);
v___x_1756_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_a_1757_; uint8_t v___x_1758_; 
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
lean_inc(v_a_1757_);
lean_dec_ref(v___x_1756_);
v___x_1758_ = lean_unbox(v_a_1757_);
lean_dec(v_a_1757_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; 
lean_inc(v_mvarId_1358_);
v___x_1759_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v_a_1760_; uint8_t v___x_1761_; 
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
lean_inc(v_a_1760_);
lean_dec_ref(v___x_1759_);
v___x_1761_ = lean_unbox(v_a_1760_);
lean_dec(v_a_1760_);
if (v___x_1761_ == 0)
{
lean_object* v___x_1762_; 
lean_inc(v_mvarId_1358_);
v___x_1762_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
lean_inc(v_a_1763_);
lean_dec_ref(v___x_1762_);
if (lean_obj_tag(v_a_1763_) == 1)
{
lean_object* v_val_1764_; lean_object* v___x_1765_; 
lean_dec(v_mvarId_1358_);
v_val_1764_ = lean_ctor_get(v_a_1763_, 0);
lean_inc(v_val_1764_);
lean_dec_ref(v_a_1763_);
v___x_1765_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; uint8_t v___x_1767_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
lean_inc(v_a_1766_);
lean_dec_ref(v___x_1765_);
v___x_1767_ = lean_unbox(v_a_1766_);
lean_dec(v_a_1766_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; 
v___x_1768_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1357_, v_val_1764_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
v___y_1745_ = v_a_1752_;
v___y_1746_ = v___x_1755_;
v___y_1747_ = v___x_1768_;
goto v___jp_1744_;
}
else
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1769_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6);
v___x_1770_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_1769_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v___x_1771_; 
lean_dec_ref(v___x_1770_);
v___x_1771_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1357_, v_val_1764_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
v___y_1745_ = v_a_1752_;
v___y_1746_ = v___x_1755_;
v___y_1747_ = v___x_1771_;
goto v___jp_1744_;
}
else
{
lean_dec(v_val_1764_);
lean_dec(v_declName_1357_);
v___y_1745_ = v_a_1752_;
v___y_1746_ = v___x_1755_;
v___y_1747_ = v___x_1770_;
goto v___jp_1744_;
}
}
}
else
{
lean_object* v_a_1772_; 
lean_dec(v_val_1764_);
lean_dec(v_declName_1357_);
v_a_1772_ = lean_ctor_get(v___x_1765_, 0);
lean_inc(v_a_1772_);
lean_dec_ref(v___x_1765_);
v___y_1735_ = v_a_1752_;
v___y_1736_ = v___x_1755_;
v_a_1737_ = v_a_1772_;
goto v___jp_1734_;
}
}
else
{
lean_object* v___x_1773_; 
lean_dec(v_a_1763_);
lean_inc(v_mvarId_1358_);
v___x_1773_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
lean_inc(v_a_1774_);
lean_dec_ref(v___x_1773_);
if (lean_obj_tag(v_a_1774_) == 1)
{
lean_object* v_val_1775_; lean_object* v___x_1776_; 
lean_dec(v_mvarId_1358_);
v_val_1775_ = lean_ctor_get(v_a_1774_, 0);
lean_inc(v_val_1775_);
lean_dec_ref(v_a_1774_);
v___x_1776_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; uint8_t v___x_1778_; 
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_a_1777_);
lean_dec_ref(v___x_1776_);
v___x_1778_ = lean_unbox(v_a_1777_);
lean_dec(v_a_1777_);
if (v___x_1778_ == 0)
{
lean_object* v___x_1779_; 
v___x_1779_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1357_, v_val_1775_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
v___y_1745_ = v_a_1752_;
v___y_1746_ = v___x_1755_;
v___y_1747_ = v___x_1779_;
goto v___jp_1744_;
}
else
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1780_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1781_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_1780_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v___x_1782_; 
lean_dec_ref(v___x_1781_);
v___x_1782_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1357_, v_val_1775_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
v___y_1745_ = v_a_1752_;
v___y_1746_ = v___x_1755_;
v___y_1747_ = v___x_1782_;
goto v___jp_1744_;
}
else
{
lean_dec(v_val_1775_);
lean_dec(v_declName_1357_);
v___y_1745_ = v_a_1752_;
v___y_1746_ = v___x_1755_;
v___y_1747_ = v___x_1781_;
goto v___jp_1744_;
}
}
}
else
{
lean_object* v_a_1783_; 
lean_dec(v_val_1775_);
lean_dec(v_declName_1357_);
v_a_1783_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_a_1783_);
lean_dec_ref(v___x_1776_);
v___y_1735_ = v_a_1752_;
v___y_1736_ = v___x_1755_;
v_a_1737_ = v_a_1783_;
goto v___jp_1734_;
}
}
else
{
lean_object* v___x_1784_; 
lean_dec(v_a_1774_);
lean_inc(v_mvarId_1358_);
v___x_1784_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1358_, v_hasTrace_1377_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_a_1785_);
lean_dec_ref(v___x_1784_);
if (lean_obj_tag(v_a_1785_) == 1)
{
lean_object* v_val_1786_; lean_object* v___x_1787_; 
lean_dec(v_mvarId_1358_);
v_val_1786_ = lean_ctor_get(v_a_1785_, 0);
lean_inc(v_val_1786_);
lean_dec_ref(v_a_1785_);
v___x_1787_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_a_1788_; uint8_t v___x_1789_; 
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_a_1788_);
lean_dec_ref(v___x_1787_);
v___x_1789_ = lean_unbox(v_a_1788_);
lean_dec(v_a_1788_);
if (v___x_1789_ == 0)
{
lean_object* v___x_1790_; 
v___x_1790_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1357_, v_val_1786_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
v___y_1745_ = v_a_1752_;
v___y_1746_ = v___x_1755_;
v___y_1747_ = v___x_1790_;
goto v___jp_1744_;
}
else
{
lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1791_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
v___x_1792_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_1791_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_object* v___x_1793_; 
lean_dec_ref(v___x_1792_);
v___x_1793_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1357_, v_val_1786_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
v___y_1745_ = v_a_1752_;
v___y_1746_ = v___x_1755_;
v___y_1747_ = v___x_1793_;
goto v___jp_1744_;
}
else
{
lean_dec(v_val_1786_);
lean_dec(v_declName_1357_);
v___y_1745_ = v_a_1752_;
v___y_1746_ = v___x_1755_;
v___y_1747_ = v___x_1792_;
goto v___jp_1744_;
}
}
}
else
{
lean_object* v_a_1794_; 
lean_dec(v_val_1786_);
lean_dec(v_declName_1357_);
v_a_1794_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_a_1794_);
lean_dec_ref(v___x_1787_);
v___y_1735_ = v_a_1752_;
v___y_1736_ = v___x_1755_;
v_a_1737_ = v_a_1794_;
goto v___jp_1734_;
}
}
else
{
lean_object* v___x_1795_; lean_object* v___x_1796_; uint8_t v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
lean_dec(v_a_1785_);
v___x_1795_ = lean_unsigned_to_nat(100000u);
v___x_1796_ = lean_unsigned_to_nat(2u);
v___x_1797_ = 0;
v___x_1798_ = lean_box(0);
v___x_1799_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1799_, 0, v___x_1795_);
lean_ctor_set(v___x_1799_, 1, v___x_1796_);
lean_ctor_set(v___x_1799_, 2, v___x_1798_);
lean_ctor_set_uint8(v___x_1799_, sizeof(void*)*3, v___x_1754_);
lean_ctor_set_uint8(v___x_1799_, sizeof(void*)*3 + 1, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_1799_, sizeof(void*)*3 + 2, v___x_1754_);
lean_ctor_set_uint8(v___x_1799_, sizeof(void*)*3 + 3, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_1799_, sizeof(void*)*3 + 4, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_1799_, sizeof(void*)*3 + 5, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_1799_, sizeof(void*)*3 + 6, v___x_1797_);
lean_ctor_set_uint8(v___x_1799_, sizeof(void*)*3 + 7, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_1799_, sizeof(void*)*3 + 8, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_1799_, sizeof(void*)*3 + 9, v___x_1754_);
lean_ctor_set_uint8(v___x_1799_, sizeof(void*)*3 + 10, v___x_1754_);
lean_ctor_set_uint8(v___x_1799_, sizeof(void*)*3 + 11, v___x_1754_);
lean_ctor_set_uint8(v___x_1799_, sizeof(void*)*3 + 12, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_1799_, sizeof(void*)*3 + 13, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_1799_, sizeof(void*)*3 + 14, v___x_1754_);
lean_ctor_set_uint8(v___x_1799_, sizeof(void*)*3 + 15, v___x_1754_);
lean_ctor_set_uint8(v___x_1799_, sizeof(void*)*3 + 16, v___x_1754_);
lean_ctor_set_uint8(v___x_1799_, sizeof(void*)*3 + 17, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_1799_, sizeof(void*)*3 + 18, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_1799_, sizeof(void*)*3 + 19, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_1799_, sizeof(void*)*3 + 20, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_1799_, sizeof(void*)*3 + 21, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_1799_, sizeof(void*)*3 + 22, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_1799_, sizeof(void*)*3 + 23, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_1799_, sizeof(void*)*3 + 24, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_1799_, sizeof(void*)*3 + 25, v_hasTrace_1377_);
lean_ctor_set_uint8(v___x_1799_, sizeof(void*)*3 + 26, v___x_1754_);
lean_ctor_set_uint8(v___x_1799_, sizeof(void*)*3 + 27, v___x_1754_);
lean_ctor_set_uint8(v___x_1799_, sizeof(void*)*3 + 28, v___x_1754_);
v___x_1800_ = lean_unsigned_to_nat(0u);
v___x_1801_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__11));
v___x_1802_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13);
v___x_1803_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15);
v___x_1804_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1804_, 0, v___x_1802_);
lean_ctor_set(v___x_1804_, 1, v___x_1803_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*2, v_hasTrace_1377_);
v___x_1805_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1799_, v___x_1801_, v___x_1804_, v_a_1359_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_a_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_a_1806_);
lean_dec_ref(v___x_1805_);
v___x_1807_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21);
lean_inc(v_mvarId_1358_);
v___x_1808_ = l_Lean_Meta_simpTargetStar(v_mvarId_1358_, v_a_1806_, v___x_1801_, v___x_1798_, v___x_1807_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v_fst_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1880_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_a_1809_);
lean_dec_ref(v___x_1808_);
v_fst_1810_ = lean_ctor_get(v_a_1809_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v_a_1809_);
if (v_isSharedCheck_1880_ == 0)
{
lean_object* v_unused_1881_; 
v_unused_1881_ = lean_ctor_get(v_a_1809_, 1);
lean_dec(v_unused_1881_);
v___x_1812_ = v_a_1809_;
v_isShared_1813_ = v_isSharedCheck_1880_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_fst_1810_);
lean_dec(v_a_1809_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1880_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
switch(lean_obj_tag(v_fst_1810_))
{
case 0:
{
lean_object* v___x_1814_; 
lean_del_object(v___x_1812_);
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v___x_1814_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; uint8_t v___x_1816_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_a_1815_);
lean_dec_ref(v___x_1814_);
v___x_1816_ = lean_unbox(v_a_1815_);
lean_dec(v_a_1815_);
if (v___x_1816_ == 0)
{
lean_object* v___x_1817_; 
v___x_1817_ = lean_box(0);
v___y_1740_ = v_a_1752_;
v___y_1741_ = v___x_1755_;
v_a_1742_ = v___x_1817_;
goto v___jp_1739_;
}
else
{
lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1818_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23);
v___x_1819_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_1818_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
v___y_1745_ = v_a_1752_;
v___y_1746_ = v___x_1755_;
v___y_1747_ = v___x_1819_;
goto v___jp_1744_;
}
}
else
{
lean_object* v_a_1820_; 
v_a_1820_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_a_1820_);
lean_dec_ref(v___x_1814_);
v___y_1735_ = v_a_1752_;
v___y_1736_ = v___x_1755_;
v_a_1737_ = v_a_1820_;
goto v___jp_1734_;
}
}
case 1:
{
lean_object* v___x_1821_; 
lean_inc(v_declName_1357_);
lean_inc(v_mvarId_1358_);
v___x_1821_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1358_, v_declName_1357_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
lean_inc(v_a_1822_);
lean_dec_ref(v___x_1821_);
if (lean_obj_tag(v_a_1822_) == 1)
{
lean_object* v_val_1823_; lean_object* v___x_1824_; 
lean_del_object(v___x_1812_);
lean_dec(v_mvarId_1358_);
v_val_1823_ = lean_ctor_get(v_a_1822_, 0);
lean_inc(v_val_1823_);
lean_dec_ref(v_a_1822_);
v___x_1824_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_a_1825_; uint8_t v___x_1826_; 
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
lean_inc(v_a_1825_);
lean_dec_ref(v___x_1824_);
v___x_1826_ = lean_unbox(v_a_1825_);
lean_dec(v_a_1825_);
if (v___x_1826_ == 0)
{
lean_object* v___x_1827_; 
v___x_1827_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1357_, v_val_1823_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
v___y_1745_ = v_a_1752_;
v___y_1746_ = v___x_1755_;
v___y_1747_ = v___x_1827_;
goto v___jp_1744_;
}
else
{
lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1828_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25);
v___x_1829_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_1828_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v___x_1830_; 
lean_dec_ref(v___x_1829_);
v___x_1830_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1357_, v_val_1823_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
v___y_1745_ = v_a_1752_;
v___y_1746_ = v___x_1755_;
v___y_1747_ = v___x_1830_;
goto v___jp_1744_;
}
else
{
lean_dec(v_val_1823_);
lean_dec(v_declName_1357_);
v___y_1745_ = v_a_1752_;
v___y_1746_ = v___x_1755_;
v___y_1747_ = v___x_1829_;
goto v___jp_1744_;
}
}
}
else
{
lean_object* v_a_1831_; 
lean_dec(v_val_1823_);
lean_dec(v_declName_1357_);
v_a_1831_ = lean_ctor_get(v___x_1824_, 0);
lean_inc(v_a_1831_);
lean_dec_ref(v___x_1824_);
v___y_1735_ = v_a_1752_;
v___y_1736_ = v___x_1755_;
v_a_1737_ = v_a_1831_;
goto v___jp_1734_;
}
}
else
{
lean_object* v___x_1832_; 
lean_dec(v_a_1822_);
lean_inc(v_mvarId_1358_);
v___x_1832_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v_a_1833_; 
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
lean_inc(v_a_1833_);
lean_dec_ref(v___x_1832_);
if (lean_obj_tag(v_a_1833_) == 1)
{
lean_object* v_val_1834_; lean_object* v___x_1835_; 
lean_del_object(v___x_1812_);
lean_dec(v_mvarId_1358_);
v_val_1834_ = lean_ctor_get(v_a_1833_, 0);
lean_inc(v_val_1834_);
lean_dec_ref(v_a_1833_);
v___x_1835_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; uint8_t v___x_1837_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_a_1836_);
lean_dec_ref(v___x_1835_);
v___x_1837_ = lean_unbox(v_a_1836_);
lean_dec(v_a_1836_);
if (v___x_1837_ == 0)
{
lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1838_ = lean_box(0);
v___x_1839_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1834_, v___x_1800_, v_declName_1357_, v___x_1838_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
lean_dec(v_val_1834_);
v___y_1745_ = v_a_1752_;
v___y_1746_ = v___x_1755_;
v___y_1747_ = v___x_1839_;
goto v___jp_1744_;
}
else
{
lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1840_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27);
v___x_1841_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_1840_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1843_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_a_1842_);
lean_dec_ref(v___x_1841_);
v___x_1843_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1834_, v___x_1800_, v_declName_1357_, v_a_1842_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
lean_dec(v_val_1834_);
v___y_1745_ = v_a_1752_;
v___y_1746_ = v___x_1755_;
v___y_1747_ = v___x_1843_;
goto v___jp_1744_;
}
else
{
lean_dec(v_val_1834_);
lean_dec(v_declName_1357_);
v___y_1745_ = v_a_1752_;
v___y_1746_ = v___x_1755_;
v___y_1747_ = v___x_1841_;
goto v___jp_1744_;
}
}
}
else
{
lean_object* v_a_1844_; 
lean_dec(v_val_1834_);
lean_dec(v_declName_1357_);
v_a_1844_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_a_1844_);
lean_dec_ref(v___x_1835_);
v___y_1735_ = v_a_1752_;
v___y_1736_ = v___x_1755_;
v_a_1737_ = v_a_1844_;
goto v___jp_1734_;
}
}
else
{
lean_object* v___x_1845_; 
lean_dec(v_a_1833_);
lean_inc(v_mvarId_1358_);
v___x_1845_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1358_, v_hasTrace_1377_, v_hasTrace_1377_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1867_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1848_ = v___x_1845_;
v_isShared_1849_ = v_isSharedCheck_1867_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1845_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1867_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
if (lean_obj_tag(v_a_1846_) == 1)
{
lean_object* v_val_1850_; lean_object* v___x_1851_; 
lean_del_object(v___x_1848_);
lean_del_object(v___x_1812_);
lean_dec(v_mvarId_1358_);
v_val_1850_ = lean_ctor_get(v_a_1846_, 0);
lean_inc(v_val_1850_);
lean_dec_ref(v_a_1846_);
v___x_1851_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v_a_1852_; uint8_t v___x_1853_; 
v_a_1852_ = lean_ctor_get(v___x_1851_, 0);
lean_inc(v_a_1852_);
lean_dec_ref(v___x_1851_);
v___x_1853_ = lean_unbox(v_a_1852_);
lean_dec(v_a_1852_);
if (v___x_1853_ == 0)
{
lean_object* v___x_1854_; 
v___x_1854_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_declName_1357_, v_val_1850_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
v___y_1745_ = v_a_1752_;
v___y_1746_ = v___x_1755_;
v___y_1747_ = v___x_1854_;
goto v___jp_1744_;
}
else
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1855_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29);
v___x_1856_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_1855_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v___x_1857_; 
lean_dec_ref(v___x_1856_);
v___x_1857_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_declName_1357_, v_val_1850_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
v___y_1745_ = v_a_1752_;
v___y_1746_ = v___x_1755_;
v___y_1747_ = v___x_1857_;
goto v___jp_1744_;
}
else
{
lean_dec(v_val_1850_);
lean_dec(v_declName_1357_);
v___y_1745_ = v_a_1752_;
v___y_1746_ = v___x_1755_;
v___y_1747_ = v___x_1856_;
goto v___jp_1744_;
}
}
}
else
{
lean_object* v_a_1858_; 
lean_dec(v_val_1850_);
lean_dec(v_declName_1357_);
v_a_1858_ = lean_ctor_get(v___x_1851_, 0);
lean_inc(v_a_1858_);
lean_dec_ref(v___x_1851_);
v___y_1735_ = v_a_1752_;
v___y_1736_ = v___x_1755_;
v_a_1737_ = v_a_1858_;
goto v___jp_1734_;
}
}
else
{
lean_object* v___x_1859_; lean_object* v___x_1861_; 
lean_dec(v_a_1846_);
lean_dec(v_declName_1357_);
v___x_1859_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31);
if (v_isShared_1849_ == 0)
{
lean_ctor_set_tag(v___x_1848_, 1);
lean_ctor_set(v___x_1848_, 0, v_mvarId_1358_);
v___x_1861_ = v___x_1848_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_mvarId_1358_);
v___x_1861_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
lean_object* v___x_1863_; 
if (v_isShared_1813_ == 0)
{
lean_ctor_set_tag(v___x_1812_, 7);
lean_ctor_set(v___x_1812_, 1, v___x_1861_);
lean_ctor_set(v___x_1812_, 0, v___x_1859_);
v___x_1863_ = v___x_1812_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v___x_1859_);
lean_ctor_set(v_reuseFailAlloc_1865_, 1, v___x_1861_);
v___x_1863_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
lean_object* v___x_1864_; 
v___x_1864_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1863_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
v___y_1745_ = v_a_1752_;
v___y_1746_ = v___x_1755_;
v___y_1747_ = v___x_1864_;
goto v___jp_1744_;
}
}
}
}
}
else
{
lean_object* v_a_1868_; 
lean_del_object(v___x_1812_);
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_1868_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_a_1868_);
lean_dec_ref(v___x_1845_);
v___y_1735_ = v_a_1752_;
v___y_1736_ = v___x_1755_;
v_a_1737_ = v_a_1868_;
goto v___jp_1734_;
}
}
}
else
{
lean_object* v_a_1869_; 
lean_del_object(v___x_1812_);
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_1869_ = lean_ctor_get(v___x_1832_, 0);
lean_inc(v_a_1869_);
lean_dec_ref(v___x_1832_);
v___y_1735_ = v_a_1752_;
v___y_1736_ = v___x_1755_;
v_a_1737_ = v_a_1869_;
goto v___jp_1734_;
}
}
}
else
{
lean_object* v_a_1870_; 
lean_del_object(v___x_1812_);
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_1870_ = lean_ctor_get(v___x_1821_, 0);
lean_inc(v_a_1870_);
lean_dec_ref(v___x_1821_);
v___y_1735_ = v_a_1752_;
v___y_1736_ = v___x_1755_;
v_a_1737_ = v_a_1870_;
goto v___jp_1734_;
}
}
default: 
{
lean_object* v_mvarId_1871_; lean_object* v___x_1872_; 
lean_del_object(v___x_1812_);
lean_dec(v_mvarId_1358_);
v_mvarId_1871_ = lean_ctor_get(v_fst_1810_, 0);
lean_inc(v_mvarId_1871_);
lean_dec_ref(v_fst_1810_);
v___x_1872_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; uint8_t v___x_1874_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1873_);
lean_dec_ref(v___x_1872_);
v___x_1874_ = lean_unbox(v_a_1873_);
lean_dec(v_a_1873_);
if (v___x_1874_ == 0)
{
lean_object* v___x_1875_; 
v___x_1875_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1357_, v_mvarId_1871_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
v___y_1745_ = v_a_1752_;
v___y_1746_ = v___x_1755_;
v___y_1747_ = v___x_1875_;
goto v___jp_1744_;
}
else
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33);
v___x_1877_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_1876_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v___x_1878_; 
lean_dec_ref(v___x_1877_);
v___x_1878_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1357_, v_mvarId_1871_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
v___y_1745_ = v_a_1752_;
v___y_1746_ = v___x_1755_;
v___y_1747_ = v___x_1878_;
goto v___jp_1744_;
}
else
{
lean_dec(v_mvarId_1871_);
lean_dec(v_declName_1357_);
v___y_1745_ = v_a_1752_;
v___y_1746_ = v___x_1755_;
v___y_1747_ = v___x_1877_;
goto v___jp_1744_;
}
}
}
else
{
lean_object* v_a_1879_; 
lean_dec(v_mvarId_1871_);
lean_dec(v_declName_1357_);
v_a_1879_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1879_);
lean_dec_ref(v___x_1872_);
v___y_1735_ = v_a_1752_;
v___y_1736_ = v___x_1755_;
v_a_1737_ = v_a_1879_;
goto v___jp_1734_;
}
}
}
}
}
else
{
lean_object* v_a_1882_; 
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_1882_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_a_1882_);
lean_dec_ref(v___x_1808_);
v___y_1735_ = v_a_1752_;
v___y_1736_ = v___x_1755_;
v_a_1737_ = v_a_1882_;
goto v___jp_1734_;
}
}
else
{
lean_object* v_a_1883_; 
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_1883_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_a_1883_);
lean_dec_ref(v___x_1805_);
v___y_1735_ = v_a_1752_;
v___y_1736_ = v___x_1755_;
v_a_1737_ = v_a_1883_;
goto v___jp_1734_;
}
}
}
else
{
lean_object* v_a_1884_; 
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_1884_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_a_1884_);
lean_dec_ref(v___x_1784_);
v___y_1735_ = v_a_1752_;
v___y_1736_ = v___x_1755_;
v_a_1737_ = v_a_1884_;
goto v___jp_1734_;
}
}
}
else
{
lean_object* v_a_1885_; 
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_1885_ = lean_ctor_get(v___x_1773_, 0);
lean_inc(v_a_1885_);
lean_dec_ref(v___x_1773_);
v___y_1735_ = v_a_1752_;
v___y_1736_ = v___x_1755_;
v_a_1737_ = v_a_1885_;
goto v___jp_1734_;
}
}
}
else
{
lean_object* v_a_1886_; 
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_1886_ = lean_ctor_get(v___x_1762_, 0);
lean_inc(v_a_1886_);
lean_dec_ref(v___x_1762_);
v___y_1735_ = v_a_1752_;
v___y_1736_ = v___x_1755_;
v_a_1737_ = v_a_1886_;
goto v___jp_1734_;
}
}
else
{
lean_object* v___x_1887_; 
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v___x_1887_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; uint8_t v___x_1889_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc(v_a_1888_);
lean_dec_ref(v___x_1887_);
v___x_1889_ = lean_unbox(v_a_1888_);
lean_dec(v_a_1888_);
if (v___x_1889_ == 0)
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1890_ = lean_box(0);
v___x_1891_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1890_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
v___y_1745_ = v_a_1752_;
v___y_1746_ = v___x_1755_;
v___y_1747_ = v___x_1891_;
goto v___jp_1744_;
}
else
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1892_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35);
v___x_1893_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_1892_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v_a_1894_; lean_object* v___x_1895_; 
v_a_1894_ = lean_ctor_get(v___x_1893_, 0);
lean_inc(v_a_1894_);
lean_dec_ref(v___x_1893_);
v___x_1895_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1894_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
v___y_1745_ = v_a_1752_;
v___y_1746_ = v___x_1755_;
v___y_1747_ = v___x_1895_;
goto v___jp_1744_;
}
else
{
v___y_1745_ = v_a_1752_;
v___y_1746_ = v___x_1755_;
v___y_1747_ = v___x_1893_;
goto v___jp_1744_;
}
}
}
else
{
lean_object* v_a_1896_; 
v_a_1896_ = lean_ctor_get(v___x_1887_, 0);
lean_inc(v_a_1896_);
lean_dec_ref(v___x_1887_);
v___y_1735_ = v_a_1752_;
v___y_1736_ = v___x_1755_;
v_a_1737_ = v_a_1896_;
goto v___jp_1734_;
}
}
}
else
{
lean_object* v_a_1897_; 
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_1897_ = lean_ctor_get(v___x_1759_, 0);
lean_inc(v_a_1897_);
lean_dec_ref(v___x_1759_);
v___y_1735_ = v_a_1752_;
v___y_1736_ = v___x_1755_;
v_a_1737_ = v_a_1897_;
goto v___jp_1734_;
}
}
else
{
lean_object* v___x_1898_; 
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v___x_1898_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; uint8_t v___x_1900_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
lean_inc(v_a_1899_);
lean_dec_ref(v___x_1898_);
v___x_1900_ = lean_unbox(v_a_1899_);
lean_dec(v_a_1899_);
if (v___x_1900_ == 0)
{
lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1901_ = lean_box(0);
v___x_1902_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1901_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
v___y_1745_ = v_a_1752_;
v___y_1746_ = v___x_1755_;
v___y_1747_ = v___x_1902_;
goto v___jp_1744_;
}
else
{
lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1903_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37);
v___x_1904_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_1903_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1906_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
lean_inc(v_a_1905_);
lean_dec_ref(v___x_1904_);
v___x_1906_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1905_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
v___y_1745_ = v_a_1752_;
v___y_1746_ = v___x_1755_;
v___y_1747_ = v___x_1906_;
goto v___jp_1744_;
}
else
{
v___y_1745_ = v_a_1752_;
v___y_1746_ = v___x_1755_;
v___y_1747_ = v___x_1904_;
goto v___jp_1744_;
}
}
}
else
{
lean_object* v_a_1907_; 
v_a_1907_ = lean_ctor_get(v___x_1898_, 0);
lean_inc(v_a_1907_);
lean_dec_ref(v___x_1898_);
v___y_1735_ = v_a_1752_;
v___y_1736_ = v___x_1755_;
v_a_1737_ = v_a_1907_;
goto v___jp_1734_;
}
}
}
else
{
lean_object* v_a_1908_; 
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_1908_ = lean_ctor_get(v___x_1756_, 0);
lean_inc(v_a_1908_);
lean_dec_ref(v___x_1756_);
v___y_1735_ = v_a_1752_;
v___y_1736_ = v___x_1755_;
v_a_1737_ = v_a_1908_;
goto v___jp_1734_;
}
}
else
{
lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1909_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_a_1361_);
lean_inc(v_mvarId_1358_);
v___x_1910_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_a_1911_; uint8_t v___x_1912_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
lean_inc(v_a_1911_);
lean_dec_ref(v___x_1910_);
v___x_1912_ = lean_unbox(v_a_1911_);
lean_dec(v_a_1911_);
if (v___x_1912_ == 0)
{
lean_object* v___x_1913_; 
lean_inc(v_mvarId_1358_);
v___x_1913_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; uint8_t v___x_1915_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_a_1914_);
lean_dec_ref(v___x_1913_);
v___x_1915_ = lean_unbox(v_a_1914_);
if (v___x_1915_ == 0)
{
lean_object* v___x_1916_; 
lean_inc(v_mvarId_1358_);
v___x_1916_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_a_1917_);
lean_dec_ref(v___x_1916_);
if (lean_obj_tag(v_a_1917_) == 1)
{
lean_object* v_val_1918_; lean_object* v___x_1919_; 
lean_dec(v_a_1914_);
lean_dec(v_mvarId_1358_);
v_val_1918_ = lean_ctor_get(v_a_1917_, 0);
lean_inc(v_val_1918_);
lean_dec_ref(v_a_1917_);
v___x_1919_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; uint8_t v___x_1921_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_a_1920_);
lean_dec_ref(v___x_1919_);
v___x_1921_ = lean_unbox(v_a_1920_);
lean_dec(v_a_1920_);
if (v___x_1921_ == 0)
{
lean_object* v___x_1922_; 
v___x_1922_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1357_, v_val_1918_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
v___y_1713_ = v___x_1909_;
v___y_1714_ = v_a_1752_;
v___y_1715_ = v___x_1922_;
goto v___jp_1712_;
}
else
{
lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1923_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6);
v___x_1924_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_1923_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v___x_1925_; 
lean_dec_ref(v___x_1924_);
v___x_1925_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1357_, v_val_1918_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
v___y_1713_ = v___x_1909_;
v___y_1714_ = v_a_1752_;
v___y_1715_ = v___x_1925_;
goto v___jp_1712_;
}
else
{
lean_dec(v_val_1918_);
lean_dec(v_declName_1357_);
v___y_1713_ = v___x_1909_;
v___y_1714_ = v_a_1752_;
v___y_1715_ = v___x_1924_;
goto v___jp_1712_;
}
}
}
else
{
lean_object* v_a_1926_; 
lean_dec(v_val_1918_);
lean_dec(v_declName_1357_);
v_a_1926_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_a_1926_);
lean_dec_ref(v___x_1919_);
v___y_1708_ = v___x_1909_;
v___y_1709_ = v_a_1752_;
v_a_1710_ = v_a_1926_;
goto v___jp_1707_;
}
}
else
{
lean_object* v___x_1927_; 
lean_dec(v_a_1917_);
lean_inc(v_mvarId_1358_);
v___x_1927_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref(v___x_1927_);
if (lean_obj_tag(v_a_1928_) == 1)
{
lean_object* v_val_1929_; lean_object* v___x_1930_; 
lean_dec(v_a_1914_);
lean_dec(v_mvarId_1358_);
v_val_1929_ = lean_ctor_get(v_a_1928_, 0);
lean_inc(v_val_1929_);
lean_dec_ref(v_a_1928_);
v___x_1930_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v_a_1931_; uint8_t v___x_1932_; 
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
lean_inc(v_a_1931_);
lean_dec_ref(v___x_1930_);
v___x_1932_ = lean_unbox(v_a_1931_);
lean_dec(v_a_1931_);
if (v___x_1932_ == 0)
{
lean_object* v___x_1933_; 
v___x_1933_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1357_, v_val_1929_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
v___y_1713_ = v___x_1909_;
v___y_1714_ = v_a_1752_;
v___y_1715_ = v___x_1933_;
goto v___jp_1712_;
}
else
{
lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1934_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1935_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_1934_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v___x_1936_; 
lean_dec_ref(v___x_1935_);
v___x_1936_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1357_, v_val_1929_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
v___y_1713_ = v___x_1909_;
v___y_1714_ = v_a_1752_;
v___y_1715_ = v___x_1936_;
goto v___jp_1712_;
}
else
{
lean_dec(v_val_1929_);
lean_dec(v_declName_1357_);
v___y_1713_ = v___x_1909_;
v___y_1714_ = v_a_1752_;
v___y_1715_ = v___x_1935_;
goto v___jp_1712_;
}
}
}
else
{
lean_object* v_a_1937_; 
lean_dec(v_val_1929_);
lean_dec(v_declName_1357_);
v_a_1937_ = lean_ctor_get(v___x_1930_, 0);
lean_inc(v_a_1937_);
lean_dec_ref(v___x_1930_);
v___y_1708_ = v___x_1909_;
v___y_1709_ = v_a_1752_;
v_a_1710_ = v_a_1937_;
goto v___jp_1707_;
}
}
else
{
lean_object* v___x_1938_; 
lean_dec(v_a_1928_);
lean_inc(v_mvarId_1358_);
v___x_1938_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1358_, v___x_1754_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_a_1939_);
lean_dec_ref(v___x_1938_);
if (lean_obj_tag(v_a_1939_) == 1)
{
lean_object* v_val_1940_; lean_object* v___x_1941_; 
lean_dec(v_a_1914_);
lean_dec(v_mvarId_1358_);
v_val_1940_ = lean_ctor_get(v_a_1939_, 0);
lean_inc(v_val_1940_);
lean_dec_ref(v_a_1939_);
v___x_1941_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_a_1942_; uint8_t v___x_1943_; 
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_a_1942_);
lean_dec_ref(v___x_1941_);
v___x_1943_ = lean_unbox(v_a_1942_);
lean_dec(v_a_1942_);
if (v___x_1943_ == 0)
{
lean_object* v___x_1944_; 
v___x_1944_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1357_, v_val_1940_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
v___y_1713_ = v___x_1909_;
v___y_1714_ = v_a_1752_;
v___y_1715_ = v___x_1944_;
goto v___jp_1712_;
}
else
{
lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1945_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
v___x_1946_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_1945_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v___x_1947_; 
lean_dec_ref(v___x_1946_);
v___x_1947_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1357_, v_val_1940_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
v___y_1713_ = v___x_1909_;
v___y_1714_ = v_a_1752_;
v___y_1715_ = v___x_1947_;
goto v___jp_1712_;
}
else
{
lean_dec(v_val_1940_);
lean_dec(v_declName_1357_);
v___y_1713_ = v___x_1909_;
v___y_1714_ = v_a_1752_;
v___y_1715_ = v___x_1946_;
goto v___jp_1712_;
}
}
}
else
{
lean_object* v_a_1948_; 
lean_dec(v_val_1940_);
lean_dec(v_declName_1357_);
v_a_1948_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_a_1948_);
lean_dec_ref(v___x_1941_);
v___y_1708_ = v___x_1909_;
v___y_1709_ = v_a_1752_;
v_a_1710_ = v_a_1948_;
goto v___jp_1707_;
}
}
else
{
lean_object* v___x_1949_; lean_object* v___x_1950_; uint8_t v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; uint8_t v___x_1954_; uint8_t v___x_1955_; uint8_t v___x_1956_; uint8_t v___x_1957_; uint8_t v___x_1958_; uint8_t v___x_1959_; uint8_t v___x_1960_; uint8_t v___x_1961_; uint8_t v___x_1962_; uint8_t v___x_1963_; uint8_t v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
lean_dec(v_a_1939_);
v___x_1949_ = lean_unsigned_to_nat(100000u);
v___x_1950_ = lean_unsigned_to_nat(2u);
v___x_1951_ = 0;
v___x_1952_ = lean_box(0);
v___x_1953_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1953_, 0, v___x_1949_);
lean_ctor_set(v___x_1953_, 1, v___x_1950_);
lean_ctor_set(v___x_1953_, 2, v___x_1952_);
v___x_1954_ = lean_unbox(v_a_1914_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*3, v___x_1954_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*3 + 1, v___x_1754_);
v___x_1955_ = lean_unbox(v_a_1914_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*3 + 2, v___x_1955_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*3 + 3, v___x_1754_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*3 + 4, v___x_1754_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*3 + 5, v___x_1754_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*3 + 6, v___x_1951_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*3 + 7, v___x_1754_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*3 + 8, v___x_1754_);
v___x_1956_ = lean_unbox(v_a_1914_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*3 + 9, v___x_1956_);
v___x_1957_ = lean_unbox(v_a_1914_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*3 + 10, v___x_1957_);
v___x_1958_ = lean_unbox(v_a_1914_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*3 + 11, v___x_1958_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*3 + 12, v___x_1754_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*3 + 13, v___x_1754_);
v___x_1959_ = lean_unbox(v_a_1914_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*3 + 14, v___x_1959_);
v___x_1960_ = lean_unbox(v_a_1914_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*3 + 15, v___x_1960_);
v___x_1961_ = lean_unbox(v_a_1914_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*3 + 16, v___x_1961_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*3 + 17, v___x_1754_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*3 + 18, v___x_1754_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*3 + 19, v___x_1754_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*3 + 20, v___x_1754_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*3 + 21, v___x_1754_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*3 + 22, v___x_1754_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*3 + 23, v___x_1754_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*3 + 24, v___x_1754_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*3 + 25, v___x_1754_);
v___x_1962_ = lean_unbox(v_a_1914_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*3 + 26, v___x_1962_);
v___x_1963_ = lean_unbox(v_a_1914_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*3 + 27, v___x_1963_);
v___x_1964_ = lean_unbox(v_a_1914_);
lean_dec(v_a_1914_);
lean_ctor_set_uint8(v___x_1953_, sizeof(void*)*3 + 28, v___x_1964_);
v___x_1965_ = lean_unsigned_to_nat(0u);
v___x_1966_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__11));
v___x_1967_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13);
v___x_1968_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15);
v___x_1969_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1969_, 0, v___x_1967_);
lean_ctor_set(v___x_1969_, 1, v___x_1968_);
lean_ctor_set_uint8(v___x_1969_, sizeof(void*)*2, v___x_1754_);
v___x_1970_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1953_, v___x_1966_, v___x_1969_, v_a_1359_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_a_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; 
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
lean_inc(v_a_1971_);
lean_dec_ref(v___x_1970_);
v___x_1972_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21);
lean_inc(v_mvarId_1358_);
v___x_1973_ = l_Lean_Meta_simpTargetStar(v_mvarId_1358_, v_a_1971_, v___x_1966_, v___x_1952_, v___x_1972_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; lean_object* v_fst_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_2045_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
lean_inc(v_a_1974_);
lean_dec_ref(v___x_1973_);
v_fst_1975_ = lean_ctor_get(v_a_1974_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v_a_1974_);
if (v_isSharedCheck_2045_ == 0)
{
lean_object* v_unused_2046_; 
v_unused_2046_ = lean_ctor_get(v_a_1974_, 1);
lean_dec(v_unused_2046_);
v___x_1977_ = v_a_1974_;
v_isShared_1978_ = v_isSharedCheck_2045_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_fst_1975_);
lean_dec(v_a_1974_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_2045_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
switch(lean_obj_tag(v_fst_1975_))
{
case 0:
{
lean_object* v___x_1979_; 
lean_del_object(v___x_1977_);
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v___x_1979_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; uint8_t v___x_1981_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_a_1980_);
lean_dec_ref(v___x_1979_);
v___x_1981_ = lean_unbox(v_a_1980_);
lean_dec(v_a_1980_);
if (v___x_1981_ == 0)
{
lean_object* v___x_1982_; 
v___x_1982_ = lean_box(0);
v___y_1703_ = v___x_1909_;
v___y_1704_ = v_a_1752_;
v_a_1705_ = v___x_1982_;
goto v___jp_1702_;
}
else
{
lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1983_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23);
v___x_1984_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_1983_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
v___y_1713_ = v___x_1909_;
v___y_1714_ = v_a_1752_;
v___y_1715_ = v___x_1984_;
goto v___jp_1712_;
}
}
else
{
lean_object* v_a_1985_; 
v_a_1985_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_a_1985_);
lean_dec_ref(v___x_1979_);
v___y_1708_ = v___x_1909_;
v___y_1709_ = v_a_1752_;
v_a_1710_ = v_a_1985_;
goto v___jp_1707_;
}
}
case 1:
{
lean_object* v___x_1986_; 
lean_inc(v_declName_1357_);
lean_inc(v_mvarId_1358_);
v___x_1986_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1358_, v_declName_1357_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v_a_1987_; 
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_a_1987_);
lean_dec_ref(v___x_1986_);
if (lean_obj_tag(v_a_1987_) == 1)
{
lean_object* v_val_1988_; lean_object* v___x_1989_; 
lean_del_object(v___x_1977_);
lean_dec(v_mvarId_1358_);
v_val_1988_ = lean_ctor_get(v_a_1987_, 0);
lean_inc(v_val_1988_);
lean_dec_ref(v_a_1987_);
v___x_1989_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; uint8_t v___x_1991_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
lean_inc(v_a_1990_);
lean_dec_ref(v___x_1989_);
v___x_1991_ = lean_unbox(v_a_1990_);
lean_dec(v_a_1990_);
if (v___x_1991_ == 0)
{
lean_object* v___x_1992_; 
v___x_1992_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1357_, v_val_1988_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
v___y_1713_ = v___x_1909_;
v___y_1714_ = v_a_1752_;
v___y_1715_ = v___x_1992_;
goto v___jp_1712_;
}
else
{
lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1993_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25);
v___x_1994_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_1993_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v___x_1995_; 
lean_dec_ref(v___x_1994_);
v___x_1995_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1357_, v_val_1988_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
v___y_1713_ = v___x_1909_;
v___y_1714_ = v_a_1752_;
v___y_1715_ = v___x_1995_;
goto v___jp_1712_;
}
else
{
lean_dec(v_val_1988_);
lean_dec(v_declName_1357_);
v___y_1713_ = v___x_1909_;
v___y_1714_ = v_a_1752_;
v___y_1715_ = v___x_1994_;
goto v___jp_1712_;
}
}
}
else
{
lean_object* v_a_1996_; 
lean_dec(v_val_1988_);
lean_dec(v_declName_1357_);
v_a_1996_ = lean_ctor_get(v___x_1989_, 0);
lean_inc(v_a_1996_);
lean_dec_ref(v___x_1989_);
v___y_1708_ = v___x_1909_;
v___y_1709_ = v_a_1752_;
v_a_1710_ = v_a_1996_;
goto v___jp_1707_;
}
}
else
{
lean_object* v___x_1997_; 
lean_dec(v_a_1987_);
lean_inc(v_mvarId_1358_);
v___x_1997_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_a_1998_; 
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_a_1998_);
lean_dec_ref(v___x_1997_);
if (lean_obj_tag(v_a_1998_) == 1)
{
lean_object* v_val_1999_; lean_object* v___x_2000_; 
lean_del_object(v___x_1977_);
lean_dec(v_mvarId_1358_);
v_val_1999_ = lean_ctor_get(v_a_1998_, 0);
lean_inc(v_val_1999_);
lean_dec_ref(v_a_1998_);
v___x_2000_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; uint8_t v___x_2002_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
lean_inc(v_a_2001_);
lean_dec_ref(v___x_2000_);
v___x_2002_ = lean_unbox(v_a_2001_);
lean_dec(v_a_2001_);
if (v___x_2002_ == 0)
{
lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2003_ = lean_box(0);
v___x_2004_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1999_, v___x_1965_, v_declName_1357_, v___x_2003_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
lean_dec(v_val_1999_);
v___y_1713_ = v___x_1909_;
v___y_1714_ = v_a_1752_;
v___y_1715_ = v___x_2004_;
goto v___jp_1712_;
}
else
{
lean_object* v___x_2005_; lean_object* v___x_2006_; 
v___x_2005_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27);
v___x_2006_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_2005_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v_a_2007_; lean_object* v___x_2008_; 
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
lean_inc(v_a_2007_);
lean_dec_ref(v___x_2006_);
v___x_2008_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1999_, v___x_1965_, v_declName_1357_, v_a_2007_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
lean_dec(v_val_1999_);
v___y_1713_ = v___x_1909_;
v___y_1714_ = v_a_1752_;
v___y_1715_ = v___x_2008_;
goto v___jp_1712_;
}
else
{
lean_dec(v_val_1999_);
lean_dec(v_declName_1357_);
v___y_1713_ = v___x_1909_;
v___y_1714_ = v_a_1752_;
v___y_1715_ = v___x_2006_;
goto v___jp_1712_;
}
}
}
else
{
lean_object* v_a_2009_; 
lean_dec(v_val_1999_);
lean_dec(v_declName_1357_);
v_a_2009_ = lean_ctor_get(v___x_2000_, 0);
lean_inc(v_a_2009_);
lean_dec_ref(v___x_2000_);
v___y_1708_ = v___x_1909_;
v___y_1709_ = v_a_1752_;
v_a_1710_ = v_a_2009_;
goto v___jp_1707_;
}
}
else
{
lean_object* v___x_2010_; 
lean_dec(v_a_1998_);
lean_inc(v_mvarId_1358_);
v___x_2010_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1358_, v___x_1754_, v___x_1754_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2032_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2013_ = v___x_2010_;
v_isShared_2014_ = v_isSharedCheck_2032_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_2010_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2032_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
if (lean_obj_tag(v_a_2011_) == 1)
{
lean_object* v_val_2015_; lean_object* v___x_2016_; 
lean_del_object(v___x_2013_);
lean_del_object(v___x_1977_);
lean_dec(v_mvarId_1358_);
v_val_2015_ = lean_ctor_get(v_a_2011_, 0);
lean_inc(v_val_2015_);
lean_dec_ref(v_a_2011_);
v___x_2016_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; uint8_t v___x_2018_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_a_2017_);
lean_dec_ref(v___x_2016_);
v___x_2018_ = lean_unbox(v_a_2017_);
lean_dec(v_a_2017_);
if (v___x_2018_ == 0)
{
lean_object* v___x_2019_; 
v___x_2019_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_declName_1357_, v_val_2015_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
v___y_1713_ = v___x_1909_;
v___y_1714_ = v_a_1752_;
v___y_1715_ = v___x_2019_;
goto v___jp_1712_;
}
else
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29);
v___x_2021_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_2020_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v___x_2022_; 
lean_dec_ref(v___x_2021_);
v___x_2022_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_declName_1357_, v_val_2015_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
v___y_1713_ = v___x_1909_;
v___y_1714_ = v_a_1752_;
v___y_1715_ = v___x_2022_;
goto v___jp_1712_;
}
else
{
lean_dec(v_val_2015_);
lean_dec(v_declName_1357_);
v___y_1713_ = v___x_1909_;
v___y_1714_ = v_a_1752_;
v___y_1715_ = v___x_2021_;
goto v___jp_1712_;
}
}
}
else
{
lean_object* v_a_2023_; 
lean_dec(v_val_2015_);
lean_dec(v_declName_1357_);
v_a_2023_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_a_2023_);
lean_dec_ref(v___x_2016_);
v___y_1708_ = v___x_1909_;
v___y_1709_ = v_a_1752_;
v_a_1710_ = v_a_2023_;
goto v___jp_1707_;
}
}
else
{
lean_object* v___x_2024_; lean_object* v___x_2026_; 
lean_dec(v_a_2011_);
lean_dec(v_declName_1357_);
v___x_2024_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31);
if (v_isShared_2014_ == 0)
{
lean_ctor_set_tag(v___x_2013_, 1);
lean_ctor_set(v___x_2013_, 0, v_mvarId_1358_);
v___x_2026_ = v___x_2013_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_mvarId_1358_);
v___x_2026_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
lean_object* v___x_2028_; 
if (v_isShared_1978_ == 0)
{
lean_ctor_set_tag(v___x_1977_, 7);
lean_ctor_set(v___x_1977_, 1, v___x_2026_);
lean_ctor_set(v___x_1977_, 0, v___x_2024_);
v___x_2028_ = v___x_1977_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v___x_2024_);
lean_ctor_set(v_reuseFailAlloc_2030_, 1, v___x_2026_);
v___x_2028_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
lean_object* v___x_2029_; 
v___x_2029_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_2028_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
v___y_1713_ = v___x_1909_;
v___y_1714_ = v_a_1752_;
v___y_1715_ = v___x_2029_;
goto v___jp_1712_;
}
}
}
}
}
else
{
lean_object* v_a_2033_; 
lean_del_object(v___x_1977_);
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_2033_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_a_2033_);
lean_dec_ref(v___x_2010_);
v___y_1708_ = v___x_1909_;
v___y_1709_ = v_a_1752_;
v_a_1710_ = v_a_2033_;
goto v___jp_1707_;
}
}
}
else
{
lean_object* v_a_2034_; 
lean_del_object(v___x_1977_);
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_2034_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_a_2034_);
lean_dec_ref(v___x_1997_);
v___y_1708_ = v___x_1909_;
v___y_1709_ = v_a_1752_;
v_a_1710_ = v_a_2034_;
goto v___jp_1707_;
}
}
}
else
{
lean_object* v_a_2035_; 
lean_del_object(v___x_1977_);
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_2035_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_a_2035_);
lean_dec_ref(v___x_1986_);
v___y_1708_ = v___x_1909_;
v___y_1709_ = v_a_1752_;
v_a_1710_ = v_a_2035_;
goto v___jp_1707_;
}
}
default: 
{
lean_object* v_mvarId_2036_; lean_object* v___x_2037_; 
lean_del_object(v___x_1977_);
lean_dec(v_mvarId_1358_);
v_mvarId_2036_ = lean_ctor_get(v_fst_1975_, 0);
lean_inc(v_mvarId_2036_);
lean_dec_ref(v_fst_1975_);
v___x_2037_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v_a_2038_; uint8_t v___x_2039_; 
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_a_2038_);
lean_dec_ref(v___x_2037_);
v___x_2039_ = lean_unbox(v_a_2038_);
lean_dec(v_a_2038_);
if (v___x_2039_ == 0)
{
lean_object* v___x_2040_; 
v___x_2040_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1357_, v_mvarId_2036_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
v___y_1713_ = v___x_1909_;
v___y_1714_ = v_a_1752_;
v___y_1715_ = v___x_2040_;
goto v___jp_1712_;
}
else
{
lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2041_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33);
v___x_2042_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_2041_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v___x_2043_; 
lean_dec_ref(v___x_2042_);
v___x_2043_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1357_, v_mvarId_2036_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
v___y_1713_ = v___x_1909_;
v___y_1714_ = v_a_1752_;
v___y_1715_ = v___x_2043_;
goto v___jp_1712_;
}
else
{
lean_dec(v_mvarId_2036_);
lean_dec(v_declName_1357_);
v___y_1713_ = v___x_1909_;
v___y_1714_ = v_a_1752_;
v___y_1715_ = v___x_2042_;
goto v___jp_1712_;
}
}
}
else
{
lean_object* v_a_2044_; 
lean_dec(v_mvarId_2036_);
lean_dec(v_declName_1357_);
v_a_2044_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_a_2044_);
lean_dec_ref(v___x_2037_);
v___y_1708_ = v___x_1909_;
v___y_1709_ = v_a_1752_;
v_a_1710_ = v_a_2044_;
goto v___jp_1707_;
}
}
}
}
}
else
{
lean_object* v_a_2047_; 
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_2047_ = lean_ctor_get(v___x_1973_, 0);
lean_inc(v_a_2047_);
lean_dec_ref(v___x_1973_);
v___y_1708_ = v___x_1909_;
v___y_1709_ = v_a_1752_;
v_a_1710_ = v_a_2047_;
goto v___jp_1707_;
}
}
else
{
lean_object* v_a_2048_; 
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_2048_ = lean_ctor_get(v___x_1970_, 0);
lean_inc(v_a_2048_);
lean_dec_ref(v___x_1970_);
v___y_1708_ = v___x_1909_;
v___y_1709_ = v_a_1752_;
v_a_1710_ = v_a_2048_;
goto v___jp_1707_;
}
}
}
else
{
lean_object* v_a_2049_; 
lean_dec(v_a_1914_);
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_2049_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_a_2049_);
lean_dec_ref(v___x_1938_);
v___y_1708_ = v___x_1909_;
v___y_1709_ = v_a_1752_;
v_a_1710_ = v_a_2049_;
goto v___jp_1707_;
}
}
}
else
{
lean_object* v_a_2050_; 
lean_dec(v_a_1914_);
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_2050_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_2050_);
lean_dec_ref(v___x_1927_);
v___y_1708_ = v___x_1909_;
v___y_1709_ = v_a_1752_;
v_a_1710_ = v_a_2050_;
goto v___jp_1707_;
}
}
}
else
{
lean_object* v_a_2051_; 
lean_dec(v_a_1914_);
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_2051_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_a_2051_);
lean_dec_ref(v___x_1916_);
v___y_1708_ = v___x_1909_;
v___y_1709_ = v_a_1752_;
v_a_1710_ = v_a_2051_;
goto v___jp_1707_;
}
}
else
{
lean_object* v___x_2052_; 
lean_dec(v_a_1914_);
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v___x_2052_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v_a_2053_; uint8_t v___x_2054_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
lean_inc(v_a_2053_);
lean_dec_ref(v___x_2052_);
v___x_2054_ = lean_unbox(v_a_2053_);
lean_dec(v_a_2053_);
if (v___x_2054_ == 0)
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2055_ = lean_box(0);
v___x_2056_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_2055_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
v___y_1713_ = v___x_1909_;
v___y_1714_ = v_a_1752_;
v___y_1715_ = v___x_2056_;
goto v___jp_1712_;
}
else
{
lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2057_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35);
v___x_2058_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_2057_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; lean_object* v___x_2060_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_a_2059_);
lean_dec_ref(v___x_2058_);
v___x_2060_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_2059_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
v___y_1713_ = v___x_1909_;
v___y_1714_ = v_a_1752_;
v___y_1715_ = v___x_2060_;
goto v___jp_1712_;
}
else
{
v___y_1713_ = v___x_1909_;
v___y_1714_ = v_a_1752_;
v___y_1715_ = v___x_2058_;
goto v___jp_1712_;
}
}
}
else
{
lean_object* v_a_2061_; 
v_a_2061_ = lean_ctor_get(v___x_2052_, 0);
lean_inc(v_a_2061_);
lean_dec_ref(v___x_2052_);
v___y_1708_ = v___x_1909_;
v___y_1709_ = v_a_1752_;
v_a_1710_ = v_a_2061_;
goto v___jp_1707_;
}
}
}
else
{
lean_object* v_a_2062_; 
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_2062_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_a_2062_);
lean_dec_ref(v___x_1913_);
v___y_1708_ = v___x_1909_;
v___y_1709_ = v_a_1752_;
v_a_1710_ = v_a_2062_;
goto v___jp_1707_;
}
}
else
{
lean_object* v___x_2063_; 
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v___x_2063_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_1378_, v_a_1361_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_a_2064_; uint8_t v___x_2065_; 
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2064_);
lean_dec_ref(v___x_2063_);
v___x_2065_ = lean_unbox(v_a_2064_);
lean_dec(v_a_2064_);
if (v___x_2065_ == 0)
{
lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2066_ = lean_box(0);
v___x_2067_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_2066_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
v___y_1713_ = v___x_1909_;
v___y_1714_ = v_a_1752_;
v___y_1715_ = v___x_2067_;
goto v___jp_1712_;
}
else
{
lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2068_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37);
v___x_2069_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_1378_, v___x_2068_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v_a_2070_; lean_object* v___x_2071_; 
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
lean_inc(v_a_2070_);
lean_dec_ref(v___x_2069_);
v___x_2071_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_2070_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
v___y_1713_ = v___x_1909_;
v___y_1714_ = v_a_1752_;
v___y_1715_ = v___x_2071_;
goto v___jp_1712_;
}
else
{
v___y_1713_ = v___x_1909_;
v___y_1714_ = v_a_1752_;
v___y_1715_ = v___x_2069_;
goto v___jp_1712_;
}
}
}
else
{
lean_object* v_a_2072_; 
v_a_2072_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2072_);
lean_dec_ref(v___x_2063_);
v___y_1708_ = v___x_1909_;
v___y_1709_ = v_a_1752_;
v_a_1710_ = v_a_2072_;
goto v___jp_1707_;
}
}
}
else
{
lean_object* v_a_2073_; 
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_2073_ = lean_ctor_get(v___x_1910_, 0);
lean_inc(v_a_2073_);
lean_dec_ref(v___x_1910_);
v___y_1708_ = v___x_1909_;
v___y_1709_ = v_a_1752_;
v_a_1710_ = v_a_2073_;
goto v___jp_1707_;
}
}
}
else
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
lean_dec_ref(v___f_1687_);
lean_dec(v_a_1686_);
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_2074_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_1751_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_1751_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
}
}
else
{
lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2399_; 
lean_dec(v_mvarId_1358_);
lean_dec(v_declName_1357_);
v_a_2392_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2394_ = v___x_1685_;
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_dec(v___x_1685_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2397_; 
if (v_isShared_2395_ == 0)
{
v___x_2397_ = v___x_2394_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_a_2392_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
}
v___jp_1364_:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1365_ = lean_box(0);
v___x_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1365_);
return v___x_1366_;
}
v___jp_1367_:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = lean_box(0);
v___x_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1368_);
return v___x_1369_;
}
v___jp_1370_:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1371_ = lean_box(0);
v___x_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1371_);
return v___x_1372_;
}
v___jp_1373_:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1374_ = lean_box(0);
v___x_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
return v___x_1375_;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(lean_object* v_declName_2400_, lean_object* v_as_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
if (lean_obj_tag(v_as_2401_) == 0)
{
lean_object* v___x_2407_; lean_object* v___x_2408_; 
lean_dec(v_declName_2400_);
v___x_2407_ = lean_box(0);
v___x_2408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2407_);
return v___x_2408_;
}
else
{
lean_object* v_head_2409_; lean_object* v_tail_2410_; lean_object* v___x_2411_; 
v_head_2409_ = lean_ctor_get(v_as_2401_, 0);
lean_inc(v_head_2409_);
v_tail_2410_ = lean_ctor_get(v_as_2401_, 1);
lean_inc(v_tail_2410_);
lean_dec_ref(v_as_2401_);
lean_inc(v_declName_2400_);
v___x_2411_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2400_, v_head_2409_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_dec_ref(v___x_2411_);
v_as_2401_ = v_tail_2410_;
goto _start;
}
else
{
lean_dec(v_tail_2410_);
lean_dec(v_declName_2400_);
return v___x_2411_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___boxed(lean_object* v_declName_2413_, lean_object* v_as_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_declName_2413_, v_as_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___boxed(lean_object* v_declName_2421_, lean_object* v_as_2422_, lean_object* v_i_2423_, lean_object* v_stop_2424_, lean_object* v_b_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
size_t v_i_boxed_2431_; size_t v_stop_boxed_2432_; lean_object* v_res_2433_; 
v_i_boxed_2431_ = lean_unbox_usize(v_i_2423_);
lean_dec(v_i_2423_);
v_stop_boxed_2432_ = lean_unbox_usize(v_stop_2424_);
lean_dec(v_stop_2424_);
v_res_2433_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_2421_, v_as_2422_, v_i_boxed_2431_, v_stop_boxed_2432_, v_b_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec_ref(v_as_2422_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5___boxed(lean_object* v_val_2434_, lean_object* v___x_2435_, lean_object* v_declName_2436_, lean_object* v_____r_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_2434_, v___x_2435_, v_declName_2436_, v_____r_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v___x_2435_);
lean_dec_ref(v_val_2434_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___boxed(lean_object* v_declName_2444_, lean_object* v_mvarId_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2444_, v_mvarId_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_);
lean_dec(v_a_2449_);
lean_dec_ref(v_a_2448_);
lean_dec(v_a_2447_);
lean_dec_ref(v_a_2446_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__8(lean_object* v_00_u03b1_2452_, lean_object* v_x_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
lean_object* v___x_2459_; 
v___x_2459_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__8___redArg(v_x_2453_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__8___boxed(lean_object* v_00_u03b1_2460_, lean_object* v_x_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__8(v_00_u03b1_2460_, v_x_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(lean_object* v_constName_2468_, uint8_t v_skipRealize_2469_, lean_object* v___y_2470_){
_start:
{
lean_object* v___x_2472_; lean_object* v_env_2473_; uint8_t v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2472_ = lean_st_ref_get(v___y_2470_);
v_env_2473_ = lean_ctor_get(v___x_2472_, 0);
lean_inc_ref(v_env_2473_);
lean_dec(v___x_2472_);
v___x_2474_ = l_Lean_Environment_contains(v_env_2473_, v_constName_2468_, v_skipRealize_2469_);
v___x_2475_ = lean_box(v___x_2474_);
v___x_2476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2475_);
return v___x_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg___boxed(lean_object* v_constName_2477_, lean_object* v_skipRealize_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
uint8_t v_skipRealize_boxed_2481_; lean_object* v_res_2482_; 
v_skipRealize_boxed_2481_ = lean_unbox(v_skipRealize_2478_);
v_res_2482_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(v_constName_2477_, v_skipRealize_boxed_2481_, v___y_2479_);
lean_dec(v___y_2479_);
return v_res_2482_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0(lean_object* v_constName_2483_, uint8_t v_skipRealize_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_){
_start:
{
lean_object* v___x_2490_; 
v___x_2490_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(v_constName_2483_, v_skipRealize_2484_, v___y_2488_);
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___boxed(lean_object* v_constName_2491_, lean_object* v_skipRealize_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_){
_start:
{
uint8_t v_skipRealize_boxed_2498_; lean_object* v_res_2499_; 
v_skipRealize_boxed_2498_ = lean_unbox(v_skipRealize_2492_);
v_res_2499_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0(v_constName_2491_, v_skipRealize_boxed_2498_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
lean_dec(v___y_2494_);
lean_dec_ref(v___y_2493_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0(lean_object* v_snd_2500_, lean_object* v___x_2501_, lean_object* v___x_2502_, lean_object* v_snd_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
lean_object* v___x_2509_; 
lean_inc_ref(v_snd_2500_);
v___x_2509_ = l_Lean_Meta_mkCongrArg(v_snd_2500_, v___x_2501_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_object* v_a_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v_a_2510_ = lean_ctor_get(v___x_2509_, 0);
lean_inc(v_a_2510_);
lean_dec_ref(v___x_2509_);
v___x_2511_ = l_Lean_Expr_app___override(v_snd_2500_, v___x_2502_);
v___x_2512_ = l_Lean_MVarId_replaceTargetEq(v_snd_2503_, v___x_2511_, v_a_2510_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
return v___x_2512_;
}
else
{
lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2520_; 
lean_dec(v_snd_2503_);
lean_dec_ref(v___x_2502_);
lean_dec_ref(v_snd_2500_);
v_a_2513_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2515_ = v___x_2509_;
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2509_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2518_; 
if (v_isShared_2516_ == 0)
{
v___x_2518_ = v___x_2515_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_a_2513_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0___boxed(lean_object* v_snd_2521_, lean_object* v___x_2522_, lean_object* v___x_2523_, lean_object* v_snd_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0(v_snd_2521_, v___x_2522_, v___x_2523_, v_snd_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
return v_res_2530_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2536_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__3));
v___x_2537_ = l_Lean_stringToMessageData(v___x_2536_);
return v___x_2537_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6(void){
_start:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2539_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__5));
v___x_2540_ = l_Lean_stringToMessageData(v___x_2539_);
return v___x_2540_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8(void){
_start:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2542_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__7));
v___x_2543_ = l_Lean_stringToMessageData(v___x_2542_);
return v___x_2543_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10(void){
_start:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2545_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__9));
v___x_2546_ = l_Lean_stringToMessageData(v___x_2545_);
return v___x_2546_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12(void){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2548_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__11));
v___x_2549_ = l_Lean_stringToMessageData(v___x_2548_);
return v___x_2549_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14(void){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__13));
v___x_2552_ = l_Lean_stringToMessageData(v___x_2551_);
return v___x_2552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1(lean_object* v_mvarId_2553_, lean_object* v_cls_2554_, lean_object* v___x_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
lean_object* v___x_2561_; 
lean_inc(v_mvarId_2553_);
v___x_2561_ = l_Lean_MVarId_getType(v_mvarId_2553_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v_a_2562_; lean_object* v___x_2563_; 
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
lean_inc(v_a_2562_);
lean_dec_ref(v___x_2561_);
v___x_2563_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS(v_a_2562_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v_a_2564_; lean_object* v_fst_2565_; lean_object* v_snd_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2716_; 
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
lean_inc(v_a_2564_);
lean_dec_ref(v___x_2563_);
v_fst_2565_ = lean_ctor_get(v_a_2564_, 0);
v_snd_2566_ = lean_ctor_get(v_a_2564_, 1);
v_isSharedCheck_2716_ = !lean_is_exclusive(v_a_2564_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2568_ = v_a_2564_;
v_isShared_2569_ = v_isSharedCheck_2716_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_snd_2566_);
lean_inc(v_fst_2565_);
lean_dec(v_a_2564_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2716_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; uint8_t v___x_2574_; lean_object* v___x_2575_; lean_object* v_a_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2715_; 
v___x_2570_ = l_Lean_Expr_getAppFn(v_fst_2565_);
v___x_2571_ = l_Lean_Expr_constName_x21(v___x_2570_);
v___x_2572_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__0));
v___x_2573_ = l_Lean_Name_str___override(v___x_2571_, v___x_2572_);
v___x_2574_ = 1;
lean_inc(v___x_2573_);
v___x_2575_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(v___x_2573_, v___x_2574_, v___y_2559_);
v_a_2576_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2578_ = v___x_2575_;
v_isShared_2579_ = v_isSharedCheck_2715_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_a_2576_);
lean_dec(v___x_2575_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2715_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v_nargs_2580_; lean_object* v___x_2581_; lean_object* v_dummy_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; uint8_t v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2631_; uint8_t v___x_2698_; 
v_nargs_2580_ = l_Lean_Expr_getAppNumArgs(v_fst_2565_);
v___x_2581_ = l_Lean_Expr_constLevels_x21(v___x_2570_);
lean_dec_ref(v___x_2570_);
v_dummy_2582_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0);
lean_inc(v_nargs_2580_);
v___x_2583_ = lean_mk_array(v_nargs_2580_, v_dummy_2582_);
v___x_2584_ = lean_unsigned_to_nat(1u);
v___x_2585_ = lean_nat_sub(v_nargs_2580_, v___x_2584_);
lean_dec(v_nargs_2580_);
v___x_2586_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_fst_2565_, v___x_2583_, v___x_2585_);
v___x_2698_ = lean_unbox(v_a_2576_);
lean_dec(v_a_2576_);
if (v___x_2698_ == 0)
{
lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2714_; 
lean_dec_ref(v___x_2586_);
lean_dec(v___x_2581_);
lean_del_object(v___x_2578_);
lean_del_object(v___x_2568_);
lean_dec(v_snd_2566_);
lean_dec_ref(v___x_2555_);
lean_dec(v_cls_2554_);
v___x_2699_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12);
v___x_2700_ = l_Lean_MessageData_ofName(v___x_2573_);
v___x_2701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2699_);
lean_ctor_set(v___x_2701_, 1, v___x_2700_);
v___x_2702_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14);
v___x_2703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2701_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
v___x_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2704_, 0, v_mvarId_2553_);
v___x_2705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2703_);
lean_ctor_set(v___x_2705_, 1, v___x_2704_);
v___x_2706_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_2705_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_);
lean_dec(v___y_2559_);
lean_dec_ref(v___y_2558_);
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
v_a_2707_ = lean_ctor_get(v___x_2706_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2706_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2709_ = v___x_2706_;
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_dec(v___x_2706_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2712_; 
if (v_isShared_2710_ == 0)
{
v___x_2712_ = v___x_2709_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_a_2707_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
}
}
}
else
{
v___y_2628_ = v___y_2556_;
v___y_2629_ = v___y_2557_;
v___y_2630_ = v___y_2558_;
v___y_2631_ = v___y_2559_;
goto v___jp_2627_;
}
v___jp_2587_:
{
lean_object* v___x_2596_; 
lean_inc(v___y_2595_);
lean_inc_ref(v___y_2594_);
lean_inc(v___y_2593_);
lean_inc_ref(v___y_2592_);
lean_inc_ref(v___y_2588_);
v___x_2596_ = lean_infer_type(v___y_2588_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_object* v_a_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v_a_2597_ = lean_ctor_get(v___x_2596_, 0);
lean_inc(v_a_2597_);
lean_dec_ref(v___x_2596_);
v___x_2598_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__2));
v___x_2599_ = l_Lean_MVarId_define(v_mvarId_2553_, v___x_2598_, v_a_2597_, v___y_2588_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v_a_2600_; lean_object* v___x_2601_; 
v_a_2600_ = lean_ctor_get(v___x_2599_, 0);
lean_inc(v_a_2600_);
lean_dec_ref(v___x_2599_);
v___x_2601_ = l_Lean_Meta_intro1Core(v_a_2600_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v_a_2602_; lean_object* v_fst_2603_; lean_object* v_snd_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___f_2609_; lean_object* v___x_2610_; 
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
lean_inc(v_a_2602_);
lean_dec_ref(v___x_2601_);
v_fst_2603_ = lean_ctor_get(v_a_2602_, 0);
lean_inc(v_fst_2603_);
v_snd_2604_ = lean_ctor_get(v_a_2602_, 1);
lean_inc(v_snd_2604_);
lean_dec(v_a_2602_);
v___x_2605_ = l_Lean_Expr_appFn_x21(v___y_2589_);
lean_dec_ref(v___y_2589_);
v___x_2606_ = l_Lean_mkFVar(v_fst_2603_);
v___x_2607_ = l_Lean_Expr_app___override(v___x_2605_, v___x_2606_);
v___x_2608_ = l_Lean_mkAppN(v___y_2590_, v___x_2586_);
lean_dec_ref(v___x_2586_);
lean_inc(v_snd_2604_);
v___f_2609_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2609_, 0, v_snd_2566_);
lean_closure_set(v___f_2609_, 1, v___x_2608_);
lean_closure_set(v___f_2609_, 2, v___x_2607_);
lean_closure_set(v___f_2609_, 3, v_snd_2604_);
v___x_2610_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_snd_2604_, v___f_2609_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
return v___x_2610_;
}
else
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2618_; 
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec_ref(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec_ref(v___x_2586_);
lean_dec(v_snd_2566_);
v_a_2611_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2613_ = v___x_2601_;
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2601_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2616_; 
if (v_isShared_2614_ == 0)
{
v___x_2616_ = v___x_2613_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_a_2611_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
else
{
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec_ref(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec_ref(v___x_2586_);
lean_dec(v_snd_2566_);
return v___x_2599_;
}
}
else
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec_ref(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec_ref(v___y_2588_);
lean_dec_ref(v___x_2586_);
lean_dec(v_snd_2566_);
lean_dec(v_mvarId_2553_);
v_a_2619_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v___x_2596_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2596_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2624_; 
if (v_isShared_2622_ == 0)
{
v___x_2624_ = v___x_2621_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2619_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
}
v___jp_2627_:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; 
lean_inc(v___x_2573_);
v___x_2632_ = l_Lean_mkConst(v___x_2573_, v___x_2581_);
lean_inc(v___y_2631_);
lean_inc_ref(v___y_2630_);
lean_inc(v___y_2629_);
lean_inc_ref(v___y_2628_);
lean_inc_ref(v___x_2632_);
v___x_2633_ = lean_infer_type(v___x_2632_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_);
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_object* v_a_2634_; lean_object* v___x_2635_; 
v_a_2634_ = lean_ctor_get(v___x_2633_, 0);
lean_inc(v_a_2634_);
lean_dec_ref(v___x_2633_);
v___x_2635_ = l_Lean_Meta_instantiateForall(v_a_2634_, v___x_2586_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_object* v_a_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; uint8_t v___x_2639_; 
v_a_2636_ = lean_ctor_get(v___x_2635_, 0);
lean_inc(v_a_2636_);
lean_dec_ref(v___x_2635_);
v___x_2637_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__1));
v___x_2638_ = lean_unsigned_to_nat(3u);
v___x_2639_ = l_Lean_Expr_isAppOfArity(v_a_2636_, v___x_2637_, v___x_2638_);
if (v___x_2639_ == 0)
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2643_; 
lean_dec(v_a_2636_);
lean_dec_ref(v___x_2632_);
lean_dec_ref(v___x_2586_);
lean_dec(v_snd_2566_);
lean_dec_ref(v___x_2555_);
lean_dec(v_cls_2554_);
v___x_2640_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4);
v___x_2641_ = l_Lean_MessageData_ofName(v___x_2573_);
if (v_isShared_2569_ == 0)
{
lean_ctor_set_tag(v___x_2568_, 7);
lean_ctor_set(v___x_2568_, 1, v___x_2641_);
lean_ctor_set(v___x_2568_, 0, v___x_2640_);
v___x_2643_ = v___x_2568_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___x_2640_);
lean_ctor_set(v_reuseFailAlloc_2651_, 1, v___x_2641_);
v___x_2643_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2647_; 
v___x_2644_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6);
v___x_2645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2645_, 0, v___x_2643_);
lean_ctor_set(v___x_2645_, 1, v___x_2644_);
if (v_isShared_2579_ == 0)
{
lean_ctor_set_tag(v___x_2578_, 1);
lean_ctor_set(v___x_2578_, 0, v_mvarId_2553_);
v___x_2647_ = v___x_2578_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_mvarId_2553_);
v___x_2647_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2645_);
lean_ctor_set(v___x_2648_, 1, v___x_2647_);
v___x_2649_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_2648_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
return v___x_2649_;
}
}
}
else
{
lean_object* v___x_2652_; lean_object* v_a_2653_; lean_object* v___x_2654_; lean_object* v_nargs_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; uint8_t v___x_2662_; 
lean_del_object(v___x_2578_);
lean_dec(v___x_2573_);
lean_inc(v_cls_2554_);
v___x_2652_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_2554_, v___y_2630_);
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_a_2653_);
lean_dec_ref(v___x_2652_);
v___x_2654_ = l_Lean_Expr_appArg_x21(v_a_2636_);
lean_dec(v_a_2636_);
v_nargs_2655_ = l_Lean_Expr_getAppNumArgs(v___x_2654_);
lean_inc(v_nargs_2655_);
v___x_2656_ = lean_mk_array(v_nargs_2655_, v_dummy_2582_);
v___x_2657_ = lean_nat_sub(v_nargs_2655_, v___x_2584_);
lean_dec(v_nargs_2655_);
lean_inc_ref(v___x_2654_);
v___x_2658_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_2654_, v___x_2656_, v___x_2657_);
v___x_2659_ = lean_array_get_size(v___x_2658_);
v___x_2660_ = lean_nat_sub(v___x_2659_, v___x_2584_);
v___x_2661_ = lean_array_get(v___x_2555_, v___x_2658_, v___x_2660_);
lean_dec(v___x_2660_);
lean_dec_ref(v___x_2658_);
v___x_2662_ = lean_unbox(v_a_2653_);
lean_dec(v_a_2653_);
if (v___x_2662_ == 0)
{
lean_del_object(v___x_2568_);
lean_dec(v_cls_2554_);
v___y_2588_ = v___x_2661_;
v___y_2589_ = v___x_2654_;
v___y_2590_ = v___x_2632_;
v___y_2591_ = v___x_2639_;
v___y_2592_ = v___y_2628_;
v___y_2593_ = v___y_2629_;
v___y_2594_ = v___y_2630_;
v___y_2595_ = v___y_2631_;
goto v___jp_2587_;
}
else
{
lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2667_; 
v___x_2663_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8);
v___x_2664_ = lean_unsigned_to_nat(30u);
lean_inc(v___x_2661_);
v___x_2665_ = l_Lean_inlineExpr(v___x_2661_, v___x_2664_);
if (v_isShared_2569_ == 0)
{
lean_ctor_set_tag(v___x_2568_, 7);
lean_ctor_set(v___x_2568_, 1, v___x_2665_);
lean_ctor_set(v___x_2568_, 0, v___x_2663_);
v___x_2667_ = v___x_2568_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2663_);
lean_ctor_set(v_reuseFailAlloc_2681_, 1, v___x_2665_);
v___x_2667_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2668_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10);
v___x_2669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2667_);
lean_ctor_set(v___x_2669_, 1, v___x_2668_);
lean_inc_ref(v___x_2654_);
v___x_2670_ = l_Lean_indentExpr(v___x_2654_);
v___x_2671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2669_);
lean_ctor_set(v___x_2671_, 1, v___x_2670_);
v___x_2672_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_cls_2554_, v___x_2671_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_dec_ref(v___x_2672_);
v___y_2588_ = v___x_2661_;
v___y_2589_ = v___x_2654_;
v___y_2590_ = v___x_2632_;
v___y_2591_ = v___x_2639_;
v___y_2592_ = v___y_2628_;
v___y_2593_ = v___y_2629_;
v___y_2594_ = v___y_2630_;
v___y_2595_ = v___y_2631_;
goto v___jp_2587_;
}
else
{
lean_object* v_a_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2680_; 
lean_dec(v___x_2661_);
lean_dec_ref(v___x_2654_);
lean_dec_ref(v___x_2632_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec_ref(v___x_2586_);
lean_dec(v_snd_2566_);
lean_dec(v_mvarId_2553_);
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2675_ = v___x_2672_;
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_a_2673_);
lean_dec(v___x_2672_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2678_; 
if (v_isShared_2676_ == 0)
{
v___x_2678_ = v___x_2675_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_a_2673_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2689_; 
lean_dec_ref(v___x_2632_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec_ref(v___x_2586_);
lean_del_object(v___x_2578_);
lean_dec(v___x_2573_);
lean_del_object(v___x_2568_);
lean_dec(v_snd_2566_);
lean_dec_ref(v___x_2555_);
lean_dec(v_cls_2554_);
lean_dec(v_mvarId_2553_);
v_a_2682_ = lean_ctor_get(v___x_2635_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2684_ = v___x_2635_;
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_a_2682_);
lean_dec(v___x_2635_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2687_; 
if (v_isShared_2685_ == 0)
{
v___x_2687_ = v___x_2684_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_a_2682_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
}
}
else
{
lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2697_; 
lean_dec_ref(v___x_2632_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec_ref(v___x_2586_);
lean_del_object(v___x_2578_);
lean_dec(v___x_2573_);
lean_del_object(v___x_2568_);
lean_dec(v_snd_2566_);
lean_dec_ref(v___x_2555_);
lean_dec(v_cls_2554_);
lean_dec(v_mvarId_2553_);
v_a_2690_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2692_ = v___x_2633_;
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v___x_2633_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2695_; 
if (v_isShared_2693_ == 0)
{
v___x_2695_ = v___x_2692_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_a_2690_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2724_; 
lean_dec(v___y_2559_);
lean_dec_ref(v___y_2558_);
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec_ref(v___x_2555_);
lean_dec(v_cls_2554_);
lean_dec(v_mvarId_2553_);
v_a_2717_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2719_ = v___x_2563_;
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___x_2563_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2722_; 
if (v_isShared_2720_ == 0)
{
v___x_2722_ = v___x_2719_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_a_2717_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
}
else
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2732_; 
lean_dec(v___y_2559_);
lean_dec_ref(v___y_2558_);
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec_ref(v___x_2555_);
lean_dec(v_cls_2554_);
lean_dec(v_mvarId_2553_);
v_a_2725_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2727_ = v___x_2561_;
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2561_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2730_; 
if (v_isShared_2728_ == 0)
{
v___x_2730_ = v___x_2727_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_a_2725_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___boxed(lean_object* v_mvarId_2733_, lean_object* v_cls_2734_, lean_object* v___x_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
lean_object* v_res_2741_; 
v_res_2741_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1(v_mvarId_2733_, v_cls_2734_, v___x_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
return v_res_2741_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; 
v___x_2743_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__0));
v___x_2744_ = l_Lean_stringToMessageData(v___x_2743_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2(lean_object* v_mvarId_2745_, lean_object* v_x_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2752_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1);
v___x_2753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2753_, 0, v_mvarId_2745_);
v___x_2754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2752_);
lean_ctor_set(v___x_2754_, 1, v___x_2753_);
v___x_2755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2754_);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___boxed(lean_object* v_mvarId_2756_, lean_object* v_x_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_){
_start:
{
lean_object* v_res_2763_; 
v_res_2763_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2(v_mvarId_2756_, v_x_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
lean_dec_ref(v_x_2757_);
return v_res_2763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(lean_object* v_declName_2764_, lean_object* v_mvarId_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_){
_start:
{
lean_object* v_options_2771_; uint8_t v_hasTrace_2772_; lean_object* v___x_2773_; lean_object* v_cls_2774_; lean_object* v___f_2775_; 
v_options_2771_ = lean_ctor_get(v_a_2768_, 2);
v_hasTrace_2772_ = lean_ctor_get_uint8(v_options_2771_, sizeof(void*)*1);
v___x_2773_ = l_Lean_instInhabitedExpr;
v_cls_2774_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4));
lean_inc(v_mvarId_2765_);
v___f_2775_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___boxed), 8, 3);
lean_closure_set(v___f_2775_, 0, v_mvarId_2765_);
lean_closure_set(v___f_2775_, 1, v_cls_2774_);
lean_closure_set(v___f_2775_, 2, v___x_2773_);
if (v_hasTrace_2772_ == 0)
{
lean_object* v___x_2776_; 
v___x_2776_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2765_, v___f_2775_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v_a_2777_; lean_object* v___x_2778_; 
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
lean_inc(v_a_2777_);
lean_dec_ref(v___x_2776_);
v___x_2778_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2764_, v_a_2777_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_);
return v___x_2778_;
}
else
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2786_; 
lean_dec(v_declName_2764_);
v_a_2779_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2781_ = v___x_2776_;
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2776_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2784_; 
if (v_isShared_2782_ == 0)
{
v___x_2784_ = v___x_2781_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_a_2779_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
}
else
{
lean_object* v___x_2787_; lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2882_; 
v___x_2787_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_cls_2774_, v_a_2768_);
v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2790_ = v___x_2787_;
v_isShared_2791_ = v_isSharedCheck_2882_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2787_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2882_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___f_2792_; lean_object* v___x_2793_; lean_object* v___y_2795_; lean_object* v___y_2796_; lean_object* v_a_2797_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v_a_2813_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v_a_2820_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v_a_2833_; uint8_t v___x_2868_; 
lean_inc(v_mvarId_2765_);
v___f_2792_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2792_, 0, v_mvarId_2765_);
v___x_2793_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___closed__0));
v___x_2868_ = lean_unbox(v_a_2788_);
if (v___x_2868_ == 0)
{
lean_object* v___x_2869_; uint8_t v___x_2870_; 
v___x_2869_ = l_Lean_trace_profiler;
v___x_2870_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_options_2771_, v___x_2869_);
if (v___x_2870_ == 0)
{
lean_object* v___x_2871_; 
lean_dec_ref(v___f_2792_);
lean_del_object(v___x_2790_);
lean_dec(v_a_2788_);
v___x_2871_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2765_, v___f_2775_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v_a_2872_; lean_object* v___x_2873_; 
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_a_2872_);
lean_dec_ref(v___x_2871_);
v___x_2873_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2764_, v_a_2872_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_);
return v___x_2873_;
}
else
{
lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2881_; 
lean_dec(v_declName_2764_);
v_a_2874_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2876_ = v___x_2871_;
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2871_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2879_; 
if (v_isShared_2877_ == 0)
{
v___x_2879_ = v___x_2876_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2874_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
}
else
{
goto v___jp_2835_;
}
}
else
{
goto v___jp_2835_;
}
v___jp_2794_:
{
lean_object* v___x_2798_; double v___x_2799_; double v___x_2800_; double v___x_2801_; double v___x_2802_; double v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; uint8_t v___x_2808_; lean_object* v___x_2809_; 
v___x_2798_ = lean_io_mono_nanos_now();
v___x_2799_ = lean_float_of_nat(v___y_2795_);
v___x_2800_ = lean_float_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38);
v___x_2801_ = lean_float_div(v___x_2799_, v___x_2800_);
v___x_2802_ = lean_float_of_nat(v___x_2798_);
v___x_2803_ = lean_float_div(v___x_2802_, v___x_2800_);
v___x_2804_ = lean_box_float(v___x_2801_);
v___x_2805_ = lean_box_float(v___x_2803_);
v___x_2806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2804_);
lean_ctor_set(v___x_2806_, 1, v___x_2805_);
v___x_2807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2807_, 0, v_a_2797_);
lean_ctor_set(v___x_2807_, 1, v___x_2806_);
v___x_2808_ = lean_unbox(v_a_2788_);
lean_dec(v_a_2788_);
v___x_2809_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6(v_cls_2774_, v_hasTrace_2772_, v___x_2793_, v_options_2771_, v___x_2808_, v___y_2796_, v___f_2792_, v___x_2807_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_);
return v___x_2809_;
}
v___jp_2810_:
{
lean_object* v___x_2815_; 
if (v_isShared_2791_ == 0)
{
lean_ctor_set(v___x_2790_, 0, v_a_2813_);
v___x_2815_ = v___x_2790_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2813_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
v___y_2795_ = v___y_2811_;
v___y_2796_ = v___y_2812_;
v_a_2797_ = v___x_2815_;
goto v___jp_2794_;
}
}
v___jp_2817_:
{
lean_object* v___x_2821_; double v___x_2822_; double v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; uint8_t v___x_2828_; lean_object* v___x_2829_; 
v___x_2821_ = lean_io_get_num_heartbeats();
v___x_2822_ = lean_float_of_nat(v___y_2818_);
v___x_2823_ = lean_float_of_nat(v___x_2821_);
v___x_2824_ = lean_box_float(v___x_2822_);
v___x_2825_ = lean_box_float(v___x_2823_);
v___x_2826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2824_);
lean_ctor_set(v___x_2826_, 1, v___x_2825_);
v___x_2827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2827_, 0, v_a_2820_);
lean_ctor_set(v___x_2827_, 1, v___x_2826_);
v___x_2828_ = lean_unbox(v_a_2788_);
lean_dec(v_a_2788_);
v___x_2829_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6(v_cls_2774_, v_hasTrace_2772_, v___x_2793_, v_options_2771_, v___x_2828_, v___y_2819_, v___f_2792_, v___x_2827_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_);
return v___x_2829_;
}
v___jp_2830_:
{
lean_object* v___x_2834_; 
v___x_2834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2834_, 0, v_a_2833_);
v___y_2818_ = v___y_2831_;
v___y_2819_ = v___y_2832_;
v_a_2820_ = v___x_2834_;
goto v___jp_2817_;
}
v___jp_2835_:
{
lean_object* v___x_2836_; lean_object* v_a_2837_; lean_object* v___x_2838_; uint8_t v___x_2839_; 
v___x_2836_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg(v_a_2769_);
v_a_2837_ = lean_ctor_get(v___x_2836_, 0);
lean_inc(v_a_2837_);
lean_dec_ref(v___x_2836_);
v___x_2838_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2839_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_options_2771_, v___x_2838_);
if (v___x_2839_ == 0)
{
lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2840_ = lean_io_mono_nanos_now();
v___x_2841_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2765_, v___f_2775_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_object* v_a_2842_; lean_object* v___x_2843_; 
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_a_2842_);
lean_dec_ref(v___x_2841_);
v___x_2843_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2764_, v_a_2842_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_);
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_object* v_a_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2851_; 
lean_del_object(v___x_2790_);
v_a_2844_ = lean_ctor_get(v___x_2843_, 0);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2846_ = v___x_2843_;
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_a_2844_);
lean_dec(v___x_2843_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v___x_2849_; 
if (v_isShared_2847_ == 0)
{
lean_ctor_set_tag(v___x_2846_, 1);
v___x_2849_ = v___x_2846_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_a_2844_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
v___y_2795_ = v___x_2840_;
v___y_2796_ = v_a_2837_;
v_a_2797_ = v___x_2849_;
goto v___jp_2794_;
}
}
}
else
{
lean_object* v_a_2852_; 
v_a_2852_ = lean_ctor_get(v___x_2843_, 0);
lean_inc(v_a_2852_);
lean_dec_ref(v___x_2843_);
v___y_2811_ = v___x_2840_;
v___y_2812_ = v_a_2837_;
v_a_2813_ = v_a_2852_;
goto v___jp_2810_;
}
}
else
{
lean_object* v_a_2853_; 
lean_dec(v_declName_2764_);
v_a_2853_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_a_2853_);
lean_dec_ref(v___x_2841_);
v___y_2811_ = v___x_2840_;
v___y_2812_ = v_a_2837_;
v_a_2813_ = v_a_2853_;
goto v___jp_2810_;
}
}
else
{
lean_object* v___x_2854_; lean_object* v___x_2855_; 
lean_del_object(v___x_2790_);
v___x_2854_ = lean_io_get_num_heartbeats();
v___x_2855_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2765_, v___f_2775_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_a_2856_; lean_object* v___x_2857_; 
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
lean_inc(v_a_2856_);
lean_dec_ref(v___x_2855_);
v___x_2857_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2764_, v_a_2856_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___x_2857_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2857_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2863_; 
if (v_isShared_2861_ == 0)
{
lean_ctor_set_tag(v___x_2860_, 1);
v___x_2863_ = v___x_2860_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_a_2858_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
v___y_2818_ = v___x_2854_;
v___y_2819_ = v_a_2837_;
v_a_2820_ = v___x_2863_;
goto v___jp_2817_;
}
}
}
else
{
lean_object* v_a_2866_; 
v_a_2866_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_a_2866_);
lean_dec_ref(v___x_2857_);
v___y_2831_ = v___x_2854_;
v___y_2832_ = v_a_2837_;
v_a_2833_ = v_a_2866_;
goto v___jp_2830_;
}
}
else
{
lean_object* v_a_2867_; 
lean_dec(v_declName_2764_);
v_a_2867_ = lean_ctor_get(v___x_2855_, 0);
lean_inc(v_a_2867_);
lean_dec_ref(v___x_2855_);
v___y_2831_ = v___x_2854_;
v___y_2832_ = v_a_2837_;
v_a_2833_ = v_a_2867_;
goto v___jp_2830_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___boxed(lean_object* v_declName_2883_, lean_object* v_mvarId_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_){
_start:
{
lean_object* v_res_2890_; 
v_res_2890_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(v_declName_2883_, v_mvarId_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_);
lean_dec(v_a_2888_);
lean_dec_ref(v_a_2887_);
lean_dec(v_a_2886_);
lean_dec_ref(v_a_2885_);
return v_res_2890_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(lean_object* v_e_2891_, lean_object* v___y_2892_){
_start:
{
uint8_t v___x_2894_; 
v___x_2894_ = l_Lean_Expr_hasMVar(v_e_2891_);
if (v___x_2894_ == 0)
{
lean_object* v___x_2895_; 
v___x_2895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2895_, 0, v_e_2891_);
return v___x_2895_;
}
else
{
lean_object* v___x_2896_; lean_object* v_mctx_2897_; lean_object* v___x_2898_; lean_object* v_fst_2899_; lean_object* v_snd_2900_; lean_object* v___x_2901_; lean_object* v_cache_2902_; lean_object* v_zetaDeltaFVarIds_2903_; lean_object* v_postponed_2904_; lean_object* v_diag_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2914_; 
v___x_2896_ = lean_st_ref_get(v___y_2892_);
v_mctx_2897_ = lean_ctor_get(v___x_2896_, 0);
lean_inc_ref(v_mctx_2897_);
lean_dec(v___x_2896_);
v___x_2898_ = l_Lean_instantiateMVarsCore(v_mctx_2897_, v_e_2891_);
v_fst_2899_ = lean_ctor_get(v___x_2898_, 0);
lean_inc(v_fst_2899_);
v_snd_2900_ = lean_ctor_get(v___x_2898_, 1);
lean_inc(v_snd_2900_);
lean_dec_ref(v___x_2898_);
v___x_2901_ = lean_st_ref_take(v___y_2892_);
v_cache_2902_ = lean_ctor_get(v___x_2901_, 1);
v_zetaDeltaFVarIds_2903_ = lean_ctor_get(v___x_2901_, 2);
v_postponed_2904_ = lean_ctor_get(v___x_2901_, 3);
v_diag_2905_ = lean_ctor_get(v___x_2901_, 4);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_2914_ == 0)
{
lean_object* v_unused_2915_; 
v_unused_2915_ = lean_ctor_get(v___x_2901_, 0);
lean_dec(v_unused_2915_);
v___x_2907_ = v___x_2901_;
v_isShared_2908_ = v_isSharedCheck_2914_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_diag_2905_);
lean_inc(v_postponed_2904_);
lean_inc(v_zetaDeltaFVarIds_2903_);
lean_inc(v_cache_2902_);
lean_dec(v___x_2901_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2914_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2910_; 
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 0, v_snd_2900_);
v___x_2910_ = v___x_2907_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_snd_2900_);
lean_ctor_set(v_reuseFailAlloc_2913_, 1, v_cache_2902_);
lean_ctor_set(v_reuseFailAlloc_2913_, 2, v_zetaDeltaFVarIds_2903_);
lean_ctor_set(v_reuseFailAlloc_2913_, 3, v_postponed_2904_);
lean_ctor_set(v_reuseFailAlloc_2913_, 4, v_diag_2905_);
v___x_2910_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2911_ = lean_st_ref_set(v___y_2892_, v___x_2910_);
v___x_2912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2912_, 0, v_fst_2899_);
return v___x_2912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg___boxed(lean_object* v_e_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_e_2916_, v___y_2917_);
lean_dec(v___y_2917_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0(lean_object* v_e_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_){
_start:
{
lean_object* v___x_2926_; 
v___x_2926_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_e_2920_, v___y_2922_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___boxed(lean_object* v_e_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_){
_start:
{
lean_object* v_res_2933_; 
v_res_2933_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0(v_e_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
return v_res_2933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(lean_object* v_k_2934_, uint8_t v_allowLevelAssignments_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_){
_start:
{
lean_object* v___x_2941_; 
v___x_2941_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2935_, v_k_2934_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_);
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_object* v_a_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2949_; 
v_a_2942_ = lean_ctor_get(v___x_2941_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2944_ = v___x_2941_;
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_a_2942_);
lean_dec(v___x_2941_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2947_; 
if (v_isShared_2945_ == 0)
{
v___x_2947_ = v___x_2944_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_a_2942_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
else
{
lean_object* v_a_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2957_; 
v_a_2950_ = lean_ctor_get(v___x_2941_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2952_ = v___x_2941_;
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_a_2950_);
lean_dec(v___x_2941_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2955_; 
if (v_isShared_2953_ == 0)
{
v___x_2955_ = v___x_2952_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_a_2950_);
v___x_2955_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
return v___x_2955_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg___boxed(lean_object* v_k_2958_, lean_object* v_allowLevelAssignments_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2965_; lean_object* v_res_2966_; 
v_allowLevelAssignments_boxed_2965_ = lean_unbox(v_allowLevelAssignments_2959_);
v_res_2966_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(v_k_2958_, v_allowLevelAssignments_boxed_2965_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
return v_res_2966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1(lean_object* v_00_u03b1_2967_, lean_object* v_k_2968_, uint8_t v_allowLevelAssignments_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_){
_start:
{
lean_object* v___x_2975_; 
v___x_2975_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(v_k_2968_, v_allowLevelAssignments_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___boxed(lean_object* v_00_u03b1_2976_, lean_object* v_k_2977_, lean_object* v_allowLevelAssignments_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2984_; lean_object* v_res_2985_; 
v_allowLevelAssignments_boxed_2984_ = lean_unbox(v_allowLevelAssignments_2978_);
v_res_2985_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1(v_00_u03b1_2976_, v_k_2977_, v_allowLevelAssignments_boxed_2984_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2981_);
lean_dec(v___y_2980_);
lean_dec_ref(v___y_2979_);
return v_res_2985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__0(lean_object* v___x_2986_, lean_object* v_e_2987_){
_start:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2988_ = l_Lean_indentD(v_e_2987_);
v___x_2989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2989_, 0, v___x_2986_);
lean_ctor_set(v___x_2989_, 1, v___x_2988_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1(lean_object* v_type_2990_, lean_object* v___x_2991_, lean_object* v_declName_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_){
_start:
{
lean_object* v___x_2998_; 
v___x_2998_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_2990_, v___x_2991_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
if (lean_obj_tag(v___x_2998_) == 0)
{
lean_object* v_a_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; 
v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
lean_inc(v_a_2999_);
lean_dec_ref(v___x_2998_);
v___x_3000_ = l_Lean_Expr_mvarId_x21(v_a_2999_);
v___x_3001_ = l_Lean_MVarId_intros(v___x_3000_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v_a_3002_; lean_object* v_snd_3003_; lean_object* v___x_3004_; 
v_a_3002_ = lean_ctor_get(v___x_3001_, 0);
lean_inc(v_a_3002_);
lean_dec_ref(v___x_3001_);
v_snd_3003_ = lean_ctor_get(v_a_3002_, 1);
lean_inc(v_snd_3003_);
lean_dec(v_a_3002_);
lean_inc_ref(v___y_2995_);
lean_inc(v_snd_3003_);
v___x_3004_ = l_Lean_Elab_Eqns_tryURefl(v_snd_3003_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; uint8_t v___x_3006_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_a_3005_);
lean_dec_ref(v___x_3004_);
v___x_3006_ = lean_unbox(v_a_3005_);
lean_dec(v_a_3005_);
if (v___x_3006_ == 0)
{
lean_object* v___x_3007_; 
v___x_3007_ = l_Lean_Elab_Eqns_deltaLHS(v_snd_3003_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_object* v_a_3008_; lean_object* v___x_3009_; 
v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
lean_inc(v_a_3008_);
lean_dec_ref(v___x_3007_);
v___x_3009_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(v_declName_2992_, v_a_3008_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
lean_dec_ref(v___y_2995_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v___x_3010_; 
lean_dec_ref(v___x_3009_);
v___x_3010_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_a_2999_, v___y_2994_);
return v___x_3010_;
}
else
{
lean_object* v_a_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3018_; 
lean_dec(v_a_2999_);
v_a_3011_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3013_ = v___x_3009_;
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_a_3011_);
lean_dec(v___x_3009_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3016_; 
if (v_isShared_3014_ == 0)
{
v___x_3016_ = v___x_3013_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_a_3011_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
}
}
else
{
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
lean_dec(v_a_2999_);
lean_dec_ref(v___y_2995_);
lean_dec(v_declName_2992_);
v_a_3019_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3021_ = v___x_3007_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_3007_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3024_; 
if (v_isShared_3022_ == 0)
{
v___x_3024_ = v___x_3021_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_a_3019_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
}
else
{
lean_object* v___x_3027_; 
lean_dec(v_snd_3003_);
lean_dec_ref(v___y_2995_);
lean_dec(v_declName_2992_);
v___x_3027_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_a_2999_, v___y_2994_);
return v___x_3027_;
}
}
else
{
lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3035_; 
lean_dec(v_snd_3003_);
lean_dec(v_a_2999_);
lean_dec_ref(v___y_2995_);
lean_dec(v_declName_2992_);
v_a_3028_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3030_ = v___x_3004_;
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_dec(v___x_3004_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3033_; 
if (v_isShared_3031_ == 0)
{
v___x_3033_ = v___x_3030_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_a_3028_);
v___x_3033_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
return v___x_3033_;
}
}
}
}
else
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3043_; 
lean_dec(v_a_2999_);
lean_dec_ref(v___y_2995_);
lean_dec(v_declName_2992_);
v_a_3036_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3038_ = v___x_3001_;
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_3001_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3041_; 
if (v_isShared_3039_ == 0)
{
v___x_3041_ = v___x_3038_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_a_3036_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
}
else
{
lean_dec_ref(v___y_2995_);
lean_dec(v_declName_2992_);
return v___x_2998_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1___boxed(lean_object* v_type_3044_, lean_object* v___x_3045_, lean_object* v_declName_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_){
_start:
{
lean_object* v_res_3052_; 
v_res_3052_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1(v_type_3044_, v___x_3045_, v_declName_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_);
lean_dec(v___y_3050_);
lean_dec(v___y_3048_);
lean_dec_ref(v___y_3047_);
return v_res_3052_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3054_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__0));
v___x_3055_ = l_Lean_stringToMessageData(v___x_3054_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2(lean_object* v_type_3056_, lean_object* v_x_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_){
_start:
{
lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3063_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1);
v___x_3064_ = l_Lean_indentExpr(v_type_3056_);
v___x_3065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3063_);
lean_ctor_set(v___x_3065_, 1, v___x_3064_);
v___x_3066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3065_);
return v___x_3066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___boxed(lean_object* v_type_3067_, lean_object* v_x_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_){
_start:
{
lean_object* v_res_3074_; 
v_res_3074_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2(v_type_3067_, v_x_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec_ref(v_x_3068_);
return v_res_3074_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2(lean_object* v_e_3075_){
_start:
{
if (lean_obj_tag(v_e_3075_) == 0)
{
uint8_t v___x_3076_; 
v___x_3076_ = 2;
return v___x_3076_;
}
else
{
uint8_t v___x_3077_; 
v___x_3077_ = 0;
return v___x_3077_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2___boxed(lean_object* v_e_3078_){
_start:
{
uint8_t v_res_3079_; lean_object* v_r_3080_; 
v_res_3079_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2(v_e_3078_);
lean_dec_ref(v_e_3078_);
v_r_3080_ = lean_box(v_res_3079_);
return v_r_3080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(lean_object* v_cls_3081_, uint8_t v_collapsed_3082_, lean_object* v_tag_3083_, lean_object* v_opts_3084_, uint8_t v_clsEnabled_3085_, lean_object* v_oldTraces_3086_, lean_object* v_msg_3087_, lean_object* v_resStartStop_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_){
_start:
{
lean_object* v_fst_3094_; lean_object* v_snd_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3193_; 
v_fst_3094_ = lean_ctor_get(v_resStartStop_3088_, 0);
v_snd_3095_ = lean_ctor_get(v_resStartStop_3088_, 1);
v_isSharedCheck_3193_ = !lean_is_exclusive(v_resStartStop_3088_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3097_ = v_resStartStop_3088_;
v_isShared_3098_ = v_isSharedCheck_3193_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_snd_3095_);
lean_inc(v_fst_3094_);
lean_dec(v_resStartStop_3088_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3193_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v_data_3102_; lean_object* v_fst_3113_; lean_object* v_snd_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3192_; 
v_fst_3113_ = lean_ctor_get(v_snd_3095_, 0);
v_snd_3114_ = lean_ctor_get(v_snd_3095_, 1);
v_isSharedCheck_3192_ = !lean_is_exclusive(v_snd_3095_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3116_ = v_snd_3095_;
v_isShared_3117_ = v_isSharedCheck_3192_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_snd_3114_);
lean_inc(v_fst_3113_);
lean_dec(v_snd_3095_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3192_;
goto v_resetjp_3115_;
}
v___jp_3099_:
{
lean_object* v___x_3103_; 
lean_inc(v___y_3101_);
v___x_3103_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__7(v_oldTraces_3086_, v_data_3102_, v___y_3101_, v___y_3100_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v___x_3104_; 
lean_dec_ref(v___x_3103_);
v___x_3104_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__8___redArg(v_fst_3094_);
return v___x_3104_;
}
else
{
lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3112_; 
lean_dec(v_fst_3094_);
v_a_3105_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3107_ = v___x_3103_;
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v___x_3103_);
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
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 1, 0);
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
}
v_resetjp_3115_:
{
lean_object* v___x_3118_; uint8_t v___x_3119_; lean_object* v___y_3121_; lean_object* v_a_3122_; uint8_t v___y_3146_; double v___y_3177_; 
v___x_3118_ = l_Lean_trace_profiler;
v___x_3119_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_opts_3084_, v___x_3118_);
if (v___x_3119_ == 0)
{
v___y_3146_ = v___x_3119_;
goto v___jp_3145_;
}
else
{
lean_object* v___x_3182_; uint8_t v___x_3183_; 
v___x_3182_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3183_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_opts_3084_, v___x_3182_);
if (v___x_3183_ == 0)
{
lean_object* v___x_3184_; lean_object* v___x_3185_; double v___x_3186_; double v___x_3187_; double v___x_3188_; 
v___x_3184_ = l_Lean_trace_profiler_threshold;
v___x_3185_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__9(v_opts_3084_, v___x_3184_);
v___x_3186_ = lean_float_of_nat(v___x_3185_);
v___x_3187_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__5);
v___x_3188_ = lean_float_div(v___x_3186_, v___x_3187_);
v___y_3177_ = v___x_3188_;
goto v___jp_3176_;
}
else
{
lean_object* v___x_3189_; lean_object* v___x_3190_; double v___x_3191_; 
v___x_3189_ = l_Lean_trace_profiler_threshold;
v___x_3190_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__9(v_opts_3084_, v___x_3189_);
v___x_3191_ = lean_float_of_nat(v___x_3190_);
v___y_3177_ = v___x_3191_;
goto v___jp_3176_;
}
}
v___jp_3120_:
{
uint8_t v_result_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3128_; 
v_result_3123_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2(v_fst_3094_);
v___x_3124_ = l_Lean_TraceResult_toEmoji(v_result_3123_);
v___x_3125_ = l_Lean_stringToMessageData(v___x_3124_);
v___x_3126_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__1);
if (v_isShared_3117_ == 0)
{
lean_ctor_set_tag(v___x_3116_, 7);
lean_ctor_set(v___x_3116_, 1, v___x_3126_);
lean_ctor_set(v___x_3116_, 0, v___x_3125_);
v___x_3128_ = v___x_3116_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v___x_3125_);
lean_ctor_set(v_reuseFailAlloc_3139_, 1, v___x_3126_);
v___x_3128_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
lean_object* v_m_3130_; 
if (v_isShared_3098_ == 0)
{
lean_ctor_set_tag(v___x_3097_, 7);
lean_ctor_set(v___x_3097_, 1, v_a_3122_);
lean_ctor_set(v___x_3097_, 0, v___x_3128_);
v_m_3130_ = v___x_3097_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v___x_3128_);
lean_ctor_set(v_reuseFailAlloc_3138_, 1, v_a_3122_);
v_m_3130_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; double v___x_3133_; lean_object* v_data_3134_; 
v___x_3131_ = lean_box(v_result_3123_);
v___x_3132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3131_);
v___x_3133_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__2);
lean_inc_ref(v_tag_3083_);
lean_inc_ref(v___x_3132_);
lean_inc(v_cls_3081_);
v_data_3134_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3134_, 0, v_cls_3081_);
lean_ctor_set(v_data_3134_, 1, v___x_3132_);
lean_ctor_set(v_data_3134_, 2, v_tag_3083_);
lean_ctor_set_float(v_data_3134_, sizeof(void*)*3, v___x_3133_);
lean_ctor_set_float(v_data_3134_, sizeof(void*)*3 + 8, v___x_3133_);
lean_ctor_set_uint8(v_data_3134_, sizeof(void*)*3 + 16, v_collapsed_3082_);
if (v___x_3119_ == 0)
{
lean_dec_ref(v___x_3132_);
lean_dec(v_snd_3114_);
lean_dec(v_fst_3113_);
lean_dec_ref(v_tag_3083_);
lean_dec(v_cls_3081_);
v___y_3100_ = v_m_3130_;
v___y_3101_ = v___y_3121_;
v_data_3102_ = v_data_3134_;
goto v___jp_3099_;
}
else
{
lean_object* v_data_3135_; double v___x_3136_; double v___x_3137_; 
lean_dec_ref(v_data_3134_);
v_data_3135_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3135_, 0, v_cls_3081_);
lean_ctor_set(v_data_3135_, 1, v___x_3132_);
lean_ctor_set(v_data_3135_, 2, v_tag_3083_);
v___x_3136_ = lean_unbox_float(v_fst_3113_);
lean_dec(v_fst_3113_);
lean_ctor_set_float(v_data_3135_, sizeof(void*)*3, v___x_3136_);
v___x_3137_ = lean_unbox_float(v_snd_3114_);
lean_dec(v_snd_3114_);
lean_ctor_set_float(v_data_3135_, sizeof(void*)*3 + 8, v___x_3137_);
lean_ctor_set_uint8(v_data_3135_, sizeof(void*)*3 + 16, v_collapsed_3082_);
v___y_3100_ = v_m_3130_;
v___y_3101_ = v___y_3121_;
v_data_3102_ = v_data_3135_;
goto v___jp_3099_;
}
}
}
}
v___jp_3140_:
{
lean_object* v_ref_3141_; lean_object* v___x_3142_; 
v_ref_3141_ = lean_ctor_get(v___y_3091_, 5);
lean_inc(v___y_3092_);
lean_inc_ref(v___y_3091_);
lean_inc(v___y_3090_);
lean_inc_ref(v___y_3089_);
lean_inc(v_fst_3094_);
v___x_3142_ = lean_apply_6(v_msg_3087_, v_fst_3094_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, lean_box(0));
if (lean_obj_tag(v___x_3142_) == 0)
{
lean_object* v_a_3143_; 
v_a_3143_ = lean_ctor_get(v___x_3142_, 0);
lean_inc(v_a_3143_);
lean_dec_ref(v___x_3142_);
v___y_3121_ = v_ref_3141_;
v_a_3122_ = v_a_3143_;
goto v___jp_3120_;
}
else
{
lean_object* v___x_3144_; 
lean_dec_ref(v___x_3142_);
v___x_3144_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6___closed__4);
v___y_3121_ = v_ref_3141_;
v_a_3122_ = v___x_3144_;
goto v___jp_3120_;
}
}
v___jp_3145_:
{
if (v_clsEnabled_3085_ == 0)
{
if (v___y_3146_ == 0)
{
lean_object* v___x_3147_; lean_object* v_traceState_3148_; lean_object* v_env_3149_; lean_object* v_nextMacroScope_3150_; lean_object* v_ngen_3151_; lean_object* v_auxDeclNGen_3152_; lean_object* v_cache_3153_; lean_object* v_messages_3154_; lean_object* v_infoState_3155_; lean_object* v_snapshotTasks_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3175_; 
lean_del_object(v___x_3116_);
lean_dec(v_snd_3114_);
lean_dec(v_fst_3113_);
lean_del_object(v___x_3097_);
lean_dec_ref(v_msg_3087_);
lean_dec_ref(v_tag_3083_);
lean_dec(v_cls_3081_);
v___x_3147_ = lean_st_ref_take(v___y_3092_);
v_traceState_3148_ = lean_ctor_get(v___x_3147_, 4);
v_env_3149_ = lean_ctor_get(v___x_3147_, 0);
v_nextMacroScope_3150_ = lean_ctor_get(v___x_3147_, 1);
v_ngen_3151_ = lean_ctor_get(v___x_3147_, 2);
v_auxDeclNGen_3152_ = lean_ctor_get(v___x_3147_, 3);
v_cache_3153_ = lean_ctor_get(v___x_3147_, 5);
v_messages_3154_ = lean_ctor_get(v___x_3147_, 6);
v_infoState_3155_ = lean_ctor_get(v___x_3147_, 7);
v_snapshotTasks_3156_ = lean_ctor_get(v___x_3147_, 8);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3147_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3158_ = v___x_3147_;
v_isShared_3159_ = v_isSharedCheck_3175_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_snapshotTasks_3156_);
lean_inc(v_infoState_3155_);
lean_inc(v_messages_3154_);
lean_inc(v_cache_3153_);
lean_inc(v_traceState_3148_);
lean_inc(v_auxDeclNGen_3152_);
lean_inc(v_ngen_3151_);
lean_inc(v_nextMacroScope_3150_);
lean_inc(v_env_3149_);
lean_dec(v___x_3147_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3175_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
uint64_t v_tid_3160_; lean_object* v_traces_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3174_; 
v_tid_3160_ = lean_ctor_get_uint64(v_traceState_3148_, sizeof(void*)*1);
v_traces_3161_ = lean_ctor_get(v_traceState_3148_, 0);
v_isSharedCheck_3174_ = !lean_is_exclusive(v_traceState_3148_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3163_ = v_traceState_3148_;
v_isShared_3164_ = v_isSharedCheck_3174_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_traces_3161_);
lean_dec(v_traceState_3148_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3174_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3165_; lean_object* v___x_3167_; 
v___x_3165_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3086_, v_traces_3161_);
lean_dec_ref(v_traces_3161_);
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 0, v___x_3165_);
v___x_3167_ = v___x_3163_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v___x_3165_);
lean_ctor_set_uint64(v_reuseFailAlloc_3173_, sizeof(void*)*1, v_tid_3160_);
v___x_3167_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
lean_object* v___x_3169_; 
if (v_isShared_3159_ == 0)
{
lean_ctor_set(v___x_3158_, 4, v___x_3167_);
v___x_3169_ = v___x_3158_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_env_3149_);
lean_ctor_set(v_reuseFailAlloc_3172_, 1, v_nextMacroScope_3150_);
lean_ctor_set(v_reuseFailAlloc_3172_, 2, v_ngen_3151_);
lean_ctor_set(v_reuseFailAlloc_3172_, 3, v_auxDeclNGen_3152_);
lean_ctor_set(v_reuseFailAlloc_3172_, 4, v___x_3167_);
lean_ctor_set(v_reuseFailAlloc_3172_, 5, v_cache_3153_);
lean_ctor_set(v_reuseFailAlloc_3172_, 6, v_messages_3154_);
lean_ctor_set(v_reuseFailAlloc_3172_, 7, v_infoState_3155_);
lean_ctor_set(v_reuseFailAlloc_3172_, 8, v_snapshotTasks_3156_);
v___x_3169_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
lean_object* v___x_3170_; lean_object* v___x_3171_; 
v___x_3170_ = lean_st_ref_set(v___y_3092_, v___x_3169_);
v___x_3171_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__8___redArg(v_fst_3094_);
return v___x_3171_;
}
}
}
}
}
else
{
goto v___jp_3140_;
}
}
else
{
goto v___jp_3140_;
}
}
v___jp_3176_:
{
double v___x_3178_; double v___x_3179_; double v___x_3180_; uint8_t v___x_3181_; 
v___x_3178_ = lean_unbox_float(v_snd_3114_);
v___x_3179_ = lean_unbox_float(v_fst_3113_);
v___x_3180_ = lean_float_sub(v___x_3178_, v___x_3179_);
v___x_3181_ = lean_float_decLt(v___y_3177_, v___x_3180_);
v___y_3146_ = v___x_3181_;
goto v___jp_3145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2___boxed(lean_object* v_cls_3194_, lean_object* v_collapsed_3195_, lean_object* v_tag_3196_, lean_object* v_opts_3197_, lean_object* v_clsEnabled_3198_, lean_object* v_oldTraces_3199_, lean_object* v_msg_3200_, lean_object* v_resStartStop_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_){
_start:
{
uint8_t v_collapsed_boxed_3207_; uint8_t v_clsEnabled_boxed_3208_; lean_object* v_res_3209_; 
v_collapsed_boxed_3207_ = lean_unbox(v_collapsed_3195_);
v_clsEnabled_boxed_3208_ = lean_unbox(v_clsEnabled_3198_);
v_res_3209_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(v_cls_3194_, v_collapsed_boxed_3207_, v_tag_3196_, v_opts_3197_, v_clsEnabled_boxed_3208_, v_oldTraces_3199_, v_msg_3200_, v_resStartStop_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
lean_dec(v___y_3205_);
lean_dec_ref(v___y_3204_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec_ref(v_opts_3197_);
return v_res_3209_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1(void){
_start:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3211_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__0));
v___x_3212_ = l_Lean_stringToMessageData(v___x_3211_);
return v___x_3212_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3(void){
_start:
{
lean_object* v___x_3214_; lean_object* v___x_3215_; 
v___x_3214_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__2));
v___x_3215_ = l_Lean_stringToMessageData(v___x_3214_);
return v___x_3215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof(lean_object* v_declName_3216_, lean_object* v_type_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_){
_start:
{
lean_object* v_options_3223_; uint8_t v_hasTrace_3224_; uint8_t v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___f_3231_; lean_object* v___x_3232_; lean_object* v___f_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
v_options_3223_ = lean_ctor_get(v_a_3220_, 2);
v_hasTrace_3224_ = lean_ctor_get_uint8(v_options_3223_, sizeof(void*)*1);
v___x_3225_ = 0;
lean_inc(v_declName_3216_);
v___x_3226_ = l_Lean_MessageData_ofConstName(v_declName_3216_, v___x_3225_);
v___x_3227_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1);
v___x_3228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3227_);
lean_ctor_set(v___x_3228_, 1, v___x_3226_);
v___x_3229_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3);
v___x_3230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3228_);
lean_ctor_set(v___x_3230_, 1, v___x_3229_);
v___f_3231_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__0), 2, 1);
lean_closure_set(v___f_3231_, 0, v___x_3230_);
v___x_3232_ = lean_box(0);
lean_inc_ref(v_type_3217_);
v___f_3233_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1___boxed), 8, 3);
lean_closure_set(v___f_3233_, 0, v_type_3217_);
lean_closure_set(v___f_3233_, 1, v___x_3232_);
lean_closure_set(v___f_3233_, 2, v_declName_3216_);
v___x_3234_ = lean_box(v___x_3225_);
v___x_3235_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___boxed), 8, 3);
lean_closure_set(v___x_3235_, 0, lean_box(0));
lean_closure_set(v___x_3235_, 1, v___f_3233_);
lean_closure_set(v___x_3235_, 2, v___x_3234_);
if (v_hasTrace_3224_ == 0)
{
lean_object* v___x_3236_; 
lean_dec_ref(v_type_3217_);
v___x_3236_ = l_Lean_Meta_mapErrorImp___redArg(v___x_3235_, v___f_3231_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_);
if (lean_obj_tag(v___x_3236_) == 0)
{
lean_object* v_a_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3244_; 
v_a_3237_ = lean_ctor_get(v___x_3236_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3239_ = v___x_3236_;
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_a_3237_);
lean_dec(v___x_3236_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___x_3242_; 
if (v_isShared_3240_ == 0)
{
v___x_3242_ = v___x_3239_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v_a_3237_);
v___x_3242_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
return v___x_3242_;
}
}
}
else
{
lean_object* v_a_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3252_; 
v_a_3245_ = lean_ctor_get(v___x_3236_, 0);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3247_ = v___x_3236_;
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_a_3245_);
lean_dec(v___x_3236_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3250_; 
if (v_isShared_3248_ == 0)
{
v___x_3250_ = v___x_3247_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_a_3245_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
}
else
{
lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v_a_3255_; lean_object* v___f_3256_; lean_object* v___x_3257_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v_a_3261_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v_a_3277_; uint8_t v___x_3328_; 
v___x_3253_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4));
v___x_3254_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v___x_3253_, v_a_3220_);
v_a_3255_ = lean_ctor_get(v___x_3254_, 0);
lean_inc(v_a_3255_);
lean_dec_ref(v___x_3254_);
v___f_3256_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___boxed), 7, 1);
lean_closure_set(v___f_3256_, 0, v_type_3217_);
v___x_3257_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___closed__0));
v___x_3328_ = lean_unbox(v_a_3255_);
if (v___x_3328_ == 0)
{
lean_object* v___x_3329_; uint8_t v___x_3330_; 
v___x_3329_ = l_Lean_trace_profiler;
v___x_3330_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_options_3223_, v___x_3329_);
if (v___x_3330_ == 0)
{
lean_object* v___x_3331_; 
lean_dec_ref(v___f_3256_);
lean_dec(v_a_3255_);
v___x_3331_ = l_Lean_Meta_mapErrorImp___redArg(v___x_3235_, v___f_3231_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_);
if (lean_obj_tag(v___x_3331_) == 0)
{
lean_object* v_a_3332_; lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3339_; 
v_a_3332_ = lean_ctor_get(v___x_3331_, 0);
v_isSharedCheck_3339_ = !lean_is_exclusive(v___x_3331_);
if (v_isSharedCheck_3339_ == 0)
{
v___x_3334_ = v___x_3331_;
v_isShared_3335_ = v_isSharedCheck_3339_;
goto v_resetjp_3333_;
}
else
{
lean_inc(v_a_3332_);
lean_dec(v___x_3331_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3339_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
lean_object* v___x_3337_; 
if (v_isShared_3335_ == 0)
{
v___x_3337_ = v___x_3334_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v_a_3332_);
v___x_3337_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
return v___x_3337_;
}
}
}
else
{
lean_object* v_a_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3347_; 
v_a_3340_ = lean_ctor_get(v___x_3331_, 0);
v_isSharedCheck_3347_ = !lean_is_exclusive(v___x_3331_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3342_ = v___x_3331_;
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_a_3340_);
lean_dec(v___x_3331_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v___x_3345_; 
if (v_isShared_3343_ == 0)
{
v___x_3345_ = v___x_3342_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_a_3340_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
}
}
}
}
else
{
goto v___jp_3287_;
}
}
else
{
goto v___jp_3287_;
}
v___jp_3258_:
{
lean_object* v___x_3262_; double v___x_3263_; double v___x_3264_; double v___x_3265_; double v___x_3266_; double v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; uint8_t v___x_3272_; lean_object* v___x_3273_; 
v___x_3262_ = lean_io_mono_nanos_now();
v___x_3263_ = lean_float_of_nat(v___y_3260_);
v___x_3264_ = lean_float_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38);
v___x_3265_ = lean_float_div(v___x_3263_, v___x_3264_);
v___x_3266_ = lean_float_of_nat(v___x_3262_);
v___x_3267_ = lean_float_div(v___x_3266_, v___x_3264_);
v___x_3268_ = lean_box_float(v___x_3265_);
v___x_3269_ = lean_box_float(v___x_3267_);
v___x_3270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3270_, 0, v___x_3268_);
lean_ctor_set(v___x_3270_, 1, v___x_3269_);
v___x_3271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3271_, 0, v_a_3261_);
lean_ctor_set(v___x_3271_, 1, v___x_3270_);
v___x_3272_ = lean_unbox(v_a_3255_);
lean_dec(v_a_3255_);
v___x_3273_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(v___x_3253_, v_hasTrace_3224_, v___x_3257_, v_options_3223_, v___x_3272_, v___y_3259_, v___f_3256_, v___x_3271_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_);
return v___x_3273_;
}
v___jp_3274_:
{
lean_object* v___x_3278_; double v___x_3279_; double v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; uint8_t v___x_3285_; lean_object* v___x_3286_; 
v___x_3278_ = lean_io_get_num_heartbeats();
v___x_3279_ = lean_float_of_nat(v___y_3276_);
v___x_3280_ = lean_float_of_nat(v___x_3278_);
v___x_3281_ = lean_box_float(v___x_3279_);
v___x_3282_ = lean_box_float(v___x_3280_);
v___x_3283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3281_);
lean_ctor_set(v___x_3283_, 1, v___x_3282_);
v___x_3284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3284_, 0, v_a_3277_);
lean_ctor_set(v___x_3284_, 1, v___x_3283_);
v___x_3285_ = lean_unbox(v_a_3255_);
lean_dec(v_a_3255_);
v___x_3286_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(v___x_3253_, v_hasTrace_3224_, v___x_3257_, v_options_3223_, v___x_3285_, v___y_3275_, v___f_3256_, v___x_3284_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_);
return v___x_3286_;
}
v___jp_3287_:
{
lean_object* v___x_3288_; lean_object* v_a_3289_; lean_object* v___x_3290_; uint8_t v___x_3291_; 
v___x_3288_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___redArg(v_a_3221_);
v_a_3289_ = lean_ctor_get(v___x_3288_, 0);
lean_inc(v_a_3289_);
lean_dec_ref(v___x_3288_);
v___x_3290_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3291_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_options_3223_, v___x_3290_);
if (v___x_3291_ == 0)
{
lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3292_ = lean_io_mono_nanos_now();
v___x_3293_ = l_Lean_Meta_mapErrorImp___redArg(v___x_3235_, v___f_3231_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_);
if (lean_obj_tag(v___x_3293_) == 0)
{
lean_object* v_a_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3301_; 
v_a_3294_ = lean_ctor_get(v___x_3293_, 0);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3293_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3296_ = v___x_3293_;
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_a_3294_);
lean_dec(v___x_3293_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v___x_3299_; 
if (v_isShared_3297_ == 0)
{
lean_ctor_set_tag(v___x_3296_, 1);
v___x_3299_ = v___x_3296_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v_a_3294_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
v___y_3259_ = v_a_3289_;
v___y_3260_ = v___x_3292_;
v_a_3261_ = v___x_3299_;
goto v___jp_3258_;
}
}
}
else
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3309_; 
v_a_3302_ = lean_ctor_get(v___x_3293_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3293_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3304_ = v___x_3293_;
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3293_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3307_; 
if (v_isShared_3305_ == 0)
{
lean_ctor_set_tag(v___x_3304_, 0);
v___x_3307_ = v___x_3304_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_a_3302_);
v___x_3307_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
v___y_3259_ = v_a_3289_;
v___y_3260_ = v___x_3292_;
v_a_3261_ = v___x_3307_;
goto v___jp_3258_;
}
}
}
}
else
{
lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3310_ = lean_io_get_num_heartbeats();
v___x_3311_ = l_Lean_Meta_mapErrorImp___redArg(v___x_3235_, v___f_3231_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_);
if (lean_obj_tag(v___x_3311_) == 0)
{
lean_object* v_a_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3319_; 
v_a_3312_ = lean_ctor_get(v___x_3311_, 0);
v_isSharedCheck_3319_ = !lean_is_exclusive(v___x_3311_);
if (v_isSharedCheck_3319_ == 0)
{
v___x_3314_ = v___x_3311_;
v_isShared_3315_ = v_isSharedCheck_3319_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_a_3312_);
lean_dec(v___x_3311_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3319_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v___x_3317_; 
if (v_isShared_3315_ == 0)
{
lean_ctor_set_tag(v___x_3314_, 1);
v___x_3317_ = v___x_3314_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v_a_3312_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
v___y_3275_ = v_a_3289_;
v___y_3276_ = v___x_3310_;
v_a_3277_ = v___x_3317_;
goto v___jp_3274_;
}
}
}
else
{
lean_object* v_a_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3327_; 
v_a_3320_ = lean_ctor_get(v___x_3311_, 0);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3311_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3322_ = v___x_3311_;
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_a_3320_);
lean_dec(v___x_3311_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v___x_3325_; 
if (v_isShared_3323_ == 0)
{
lean_ctor_set_tag(v___x_3322_, 0);
v___x_3325_ = v___x_3322_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_a_3320_);
v___x_3325_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
v___y_3275_ = v_a_3289_;
v___y_3276_ = v___x_3310_;
v_a_3277_ = v___x_3325_;
goto v___jp_3274_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___boxed(lean_object* v_declName_3348_, lean_object* v_type_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_){
_start:
{
lean_object* v_res_3355_; 
v_res_3355_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof(v_declName_3348_, v_type_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_);
lean_dec(v_a_3353_);
lean_dec_ref(v_a_3352_);
lean_dec(v_a_3351_);
lean_dec_ref(v_a_3350_);
return v_res_3355_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_(lean_object* v_env_3356_, lean_object* v_n_3357_, lean_object* v_x_3358_){
_start:
{
uint8_t v___x_3359_; lean_object* v___x_3360_; 
v___x_3359_ = 0;
v___x_3360_ = l_Lean_Environment_find_x3f(v_env_3356_, v_n_3357_, v___x_3359_);
if (lean_obj_tag(v___x_3360_) == 0)
{
return v___x_3359_;
}
else
{
lean_object* v_val_3361_; uint8_t v___x_3362_; 
v_val_3361_ = lean_ctor_get(v___x_3360_, 0);
lean_inc(v_val_3361_);
lean_dec_ref(v___x_3360_);
v___x_3362_ = l_Lean_ConstantInfo_hasValue(v_val_3361_, v___x_3359_);
lean_dec(v_val_3361_);
return v___x_3362_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2____boxed(lean_object* v_env_3363_, lean_object* v_n_3364_, lean_object* v_x_3365_){
_start:
{
uint8_t v_res_3366_; lean_object* v_r_3367_; 
v_res_3366_ = l_Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_(v_env_3363_, v_n_3364_, v_x_3365_);
lean_dec_ref(v_x_3365_);
v_r_3367_ = lean_box(v_res_3366_);
return v_r_3367_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_3368_, lean_object* v_x_3369_){
_start:
{
if (lean_obj_tag(v_x_3369_) == 0)
{
lean_object* v_k_3370_; lean_object* v_v_3371_; lean_object* v_l_3372_; lean_object* v_r_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; 
v_k_3370_ = lean_ctor_get(v_x_3369_, 1);
v_v_3371_ = lean_ctor_get(v_x_3369_, 2);
v_l_3372_ = lean_ctor_get(v_x_3369_, 3);
v_r_3373_ = lean_ctor_get(v_x_3369_, 4);
v___x_3374_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0(v_init_3368_, v_l_3372_);
lean_inc(v_v_3371_);
lean_inc(v_k_3370_);
v___x_3375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3375_, 0, v_k_3370_);
lean_ctor_set(v___x_3375_, 1, v_v_3371_);
v___x_3376_ = lean_array_push(v___x_3374_, v___x_3375_);
v_init_3368_ = v___x_3376_;
v_x_3369_ = v_r_3373_;
goto _start;
}
else
{
return v_init_3368_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_3378_, lean_object* v_x_3379_){
_start:
{
lean_object* v_res_3380_; 
v_res_3380_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0(v_init_3378_, v_x_3379_);
lean_dec(v_x_3379_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_(lean_object* v_env_3383_, lean_object* v_s_3384_, uint8_t v_x_3385_){
_start:
{
lean_object* v___f_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
v___f_3386_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2____boxed), 3, 1);
lean_closure_set(v___f_3386_, 0, v_env_3383_);
v___x_3387_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v___f_3386_, v_s_3384_);
v___x_3388_ = ((lean_object*)(l_Lean_Elab_Structural_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_));
v___x_3389_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0(v___x_3388_, v___x_3387_);
lean_dec(v___x_3387_);
return v___x_3389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2____boxed(lean_object* v_env_3390_, lean_object* v_s_3391_, lean_object* v_x_3392_){
_start:
{
uint8_t v_x_232__boxed_3393_; lean_object* v_res_3394_; 
v_x_232__boxed_3393_ = lean_unbox(v_x_3392_);
v_res_3394_ = l_Lean_Elab_Structural_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_(v_env_3390_, v_s_3391_, v_x_232__boxed_3393_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___f_3407_ = ((lean_object*)(l_Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_));
v___x_3408_ = ((lean_object*)(l_Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_));
v___x_3409_ = ((lean_object*)(l_Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_));
v___x_3410_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_3408_, v___x_3409_, v___f_3407_);
return v___x_3410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2____boxed(lean_object* v_a_3411_){
_start:
{
lean_object* v_res_3412_; 
v_res_3412_ = l_Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2_();
return v_res_3412_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__spec__0(lean_object* v_init_3413_, lean_object* v_t_3414_){
_start:
{
lean_object* v___x_3415_; 
v___x_3415_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__spec__0_spec__0(v_init_3413_, v_t_3414_);
return v___x_3415_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_3416_, lean_object* v_t_3417_){
_start:
{
lean_object* v_res_3418_; 
v_res_3418_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1270222229____hygCtx___hyg_2__spec__0(v_init_3416_, v_t_3417_);
lean_dec(v_t_3417_);
return v_res_3418_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__0(void){
_start:
{
lean_object* v___x_3419_; 
v___x_3419_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3419_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1(void){
_start:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; 
v___x_3420_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__0, &l_Lean_Elab_Structural_registerEqnsInfo___closed__0_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__0);
v___x_3421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3420_);
return v___x_3421_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__2(void){
_start:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; 
v___x_3422_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__1, &l_Lean_Elab_Structural_registerEqnsInfo___closed__1_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1);
v___x_3423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3422_);
lean_ctor_set(v___x_3423_, 1, v___x_3422_);
return v___x_3423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_registerEqnsInfo(lean_object* v_preDef_3424_, lean_object* v_declNames_3425_, lean_object* v_recArgPos_3426_, lean_object* v_fixedParamPerms_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_){
_start:
{
lean_object* v_levelParams_3431_; lean_object* v_declName_3432_; lean_object* v_type_3433_; lean_object* v_value_3434_; lean_object* v___x_3435_; 
v_levelParams_3431_ = lean_ctor_get(v_preDef_3424_, 1);
lean_inc(v_levelParams_3431_);
v_declName_3432_ = lean_ctor_get(v_preDef_3424_, 3);
lean_inc(v_declName_3432_);
v_type_3433_ = lean_ctor_get(v_preDef_3424_, 6);
lean_inc_ref(v_type_3433_);
v_value_3434_ = lean_ctor_get(v_preDef_3424_, 7);
lean_inc_ref(v_value_3434_);
lean_dec_ref(v_preDef_3424_);
lean_inc(v_declName_3432_);
v___x_3435_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_3432_, v_a_3428_, v_a_3429_);
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3465_; 
v_isSharedCheck_3465_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3465_ == 0)
{
lean_object* v_unused_3466_; 
v_unused_3466_ = lean_ctor_get(v___x_3435_, 0);
lean_dec(v_unused_3466_);
v___x_3437_ = v___x_3435_;
v_isShared_3438_ = v_isSharedCheck_3465_;
goto v_resetjp_3436_;
}
else
{
lean_dec(v___x_3435_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3465_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3439_; lean_object* v_env_3440_; lean_object* v_nextMacroScope_3441_; lean_object* v_ngen_3442_; lean_object* v_auxDeclNGen_3443_; lean_object* v_traceState_3444_; lean_object* v_messages_3445_; lean_object* v_infoState_3446_; lean_object* v_snapshotTasks_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3463_; 
v___x_3439_ = lean_st_ref_take(v_a_3429_);
v_env_3440_ = lean_ctor_get(v___x_3439_, 0);
v_nextMacroScope_3441_ = lean_ctor_get(v___x_3439_, 1);
v_ngen_3442_ = lean_ctor_get(v___x_3439_, 2);
v_auxDeclNGen_3443_ = lean_ctor_get(v___x_3439_, 3);
v_traceState_3444_ = lean_ctor_get(v___x_3439_, 4);
v_messages_3445_ = lean_ctor_get(v___x_3439_, 6);
v_infoState_3446_ = lean_ctor_get(v___x_3439_, 7);
v_snapshotTasks_3447_ = lean_ctor_get(v___x_3439_, 8);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3463_ == 0)
{
lean_object* v_unused_3464_; 
v_unused_3464_ = lean_ctor_get(v___x_3439_, 5);
lean_dec(v_unused_3464_);
v___x_3449_ = v___x_3439_;
v_isShared_3450_ = v_isSharedCheck_3463_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_snapshotTasks_3447_);
lean_inc(v_infoState_3446_);
lean_inc(v_messages_3445_);
lean_inc(v_traceState_3444_);
lean_inc(v_auxDeclNGen_3443_);
lean_inc(v_ngen_3442_);
lean_inc(v_nextMacroScope_3441_);
lean_inc(v_env_3440_);
lean_dec(v___x_3439_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3463_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3456_; 
v___x_3451_ = l_Lean_Elab_Structural_eqnInfoExt;
lean_inc(v_declName_3432_);
v___x_3452_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3452_, 0, v_declName_3432_);
lean_ctor_set(v___x_3452_, 1, v_levelParams_3431_);
lean_ctor_set(v___x_3452_, 2, v_type_3433_);
lean_ctor_set(v___x_3452_, 3, v_value_3434_);
lean_ctor_set(v___x_3452_, 4, v_recArgPos_3426_);
lean_ctor_set(v___x_3452_, 5, v_declNames_3425_);
lean_ctor_set(v___x_3452_, 6, v_fixedParamPerms_3427_);
v___x_3453_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3451_, v_env_3440_, v_declName_3432_, v___x_3452_);
v___x_3454_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__2, &l_Lean_Elab_Structural_registerEqnsInfo___closed__2_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__2);
if (v_isShared_3450_ == 0)
{
lean_ctor_set(v___x_3449_, 5, v___x_3454_);
lean_ctor_set(v___x_3449_, 0, v___x_3453_);
v___x_3456_ = v___x_3449_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v___x_3453_);
lean_ctor_set(v_reuseFailAlloc_3462_, 1, v_nextMacroScope_3441_);
lean_ctor_set(v_reuseFailAlloc_3462_, 2, v_ngen_3442_);
lean_ctor_set(v_reuseFailAlloc_3462_, 3, v_auxDeclNGen_3443_);
lean_ctor_set(v_reuseFailAlloc_3462_, 4, v_traceState_3444_);
lean_ctor_set(v_reuseFailAlloc_3462_, 5, v___x_3454_);
lean_ctor_set(v_reuseFailAlloc_3462_, 6, v_messages_3445_);
lean_ctor_set(v_reuseFailAlloc_3462_, 7, v_infoState_3446_);
lean_ctor_set(v_reuseFailAlloc_3462_, 8, v_snapshotTasks_3447_);
v___x_3456_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3460_; 
v___x_3457_ = lean_st_ref_set(v_a_3429_, v___x_3456_);
v___x_3458_ = lean_box(0);
if (v_isShared_3438_ == 0)
{
lean_ctor_set(v___x_3437_, 0, v___x_3458_);
v___x_3460_ = v___x_3437_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v___x_3458_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
return v___x_3460_;
}
}
}
}
}
else
{
lean_dec_ref(v_value_3434_);
lean_dec_ref(v_type_3433_);
lean_dec(v_declName_3432_);
lean_dec(v_levelParams_3431_);
lean_dec_ref(v_fixedParamPerms_3427_);
lean_dec(v_recArgPos_3426_);
lean_dec_ref(v_declNames_3425_);
return v___x_3435_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_registerEqnsInfo___boxed(lean_object* v_preDef_3467_, lean_object* v_declNames_3468_, lean_object* v_recArgPos_3469_, lean_object* v_fixedParamPerms_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_){
_start:
{
lean_object* v_res_3474_; 
v_res_3474_ = l_Lean_Elab_Structural_registerEqnsInfo(v_preDef_3467_, v_declNames_3468_, v_recArgPos_3469_, v_fixedParamPerms_3470_, v_a_3471_, v_a_3472_);
lean_dec(v_a_3472_);
lean_dec_ref(v_a_3471_);
return v_res_3474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(lean_object* v_e_3475_, lean_object* v_k_3476_, uint8_t v_cleanupAnnotations_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_){
_start:
{
lean_object* v___f_3483_; uint8_t v___x_3484_; uint8_t v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___f_3483_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3483_, 0, v_k_3476_);
v___x_3484_ = 1;
v___x_3485_ = 0;
v___x_3486_ = lean_box(0);
v___x_3487_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3475_, v___x_3484_, v___x_3485_, v___x_3484_, v___x_3485_, v___x_3486_, v___f_3483_, v_cleanupAnnotations_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_object* v_a_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3495_; 
v_a_3488_ = lean_ctor_get(v___x_3487_, 0);
v_isSharedCheck_3495_ = !lean_is_exclusive(v___x_3487_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3490_ = v___x_3487_;
v_isShared_3491_ = v_isSharedCheck_3495_;
goto v_resetjp_3489_;
}
else
{
lean_inc(v_a_3488_);
lean_dec(v___x_3487_);
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
v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3503_; 
v_a_3496_ = lean_ctor_get(v___x_3487_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3487_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3498_ = v___x_3487_;
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_3487_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg___boxed(lean_object* v_e_3504_, lean_object* v_k_3505_, lean_object* v_cleanupAnnotations_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3512_; lean_object* v_res_3513_; 
v_cleanupAnnotations_boxed_3512_ = lean_unbox(v_cleanupAnnotations_3506_);
v_res_3513_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(v_e_3504_, v_k_3505_, v_cleanupAnnotations_boxed_3512_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_);
lean_dec(v___y_3510_);
lean_dec_ref(v___y_3509_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
return v_res_3513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3(lean_object* v_00_u03b1_3514_, lean_object* v_e_3515_, lean_object* v_k_3516_, uint8_t v_cleanupAnnotations_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_){
_start:
{
lean_object* v___x_3523_; 
v___x_3523_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(v_e_3515_, v_k_3516_, v_cleanupAnnotations_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_);
return v___x_3523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___boxed(lean_object* v_00_u03b1_3524_, lean_object* v_e_3525_, lean_object* v_k_3526_, lean_object* v_cleanupAnnotations_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3533_; lean_object* v_res_3534_; 
v_cleanupAnnotations_boxed_3533_ = lean_unbox(v_cleanupAnnotations_3527_);
v_res_3534_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3(v_00_u03b1_3524_, v_e_3525_, v_k_3526_, v_cleanupAnnotations_boxed_3533_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_);
lean_dec(v___y_3531_);
lean_dec_ref(v___y_3530_);
lean_dec(v___y_3529_);
lean_dec_ref(v___y_3528_);
return v_res_3534_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(lean_object* v___y_3535_, uint8_t v_isExporting_3536_, lean_object* v___x_3537_, lean_object* v___y_3538_, lean_object* v___x_3539_, lean_object* v_a_x3f_3540_){
_start:
{
lean_object* v___x_3542_; lean_object* v_env_3543_; lean_object* v_nextMacroScope_3544_; lean_object* v_ngen_3545_; lean_object* v_auxDeclNGen_3546_; lean_object* v_traceState_3547_; lean_object* v_messages_3548_; lean_object* v_infoState_3549_; lean_object* v_snapshotTasks_3550_; lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3575_; 
v___x_3542_ = lean_st_ref_take(v___y_3535_);
v_env_3543_ = lean_ctor_get(v___x_3542_, 0);
v_nextMacroScope_3544_ = lean_ctor_get(v___x_3542_, 1);
v_ngen_3545_ = lean_ctor_get(v___x_3542_, 2);
v_auxDeclNGen_3546_ = lean_ctor_get(v___x_3542_, 3);
v_traceState_3547_ = lean_ctor_get(v___x_3542_, 4);
v_messages_3548_ = lean_ctor_get(v___x_3542_, 6);
v_infoState_3549_ = lean_ctor_get(v___x_3542_, 7);
v_snapshotTasks_3550_ = lean_ctor_get(v___x_3542_, 8);
v_isSharedCheck_3575_ = !lean_is_exclusive(v___x_3542_);
if (v_isSharedCheck_3575_ == 0)
{
lean_object* v_unused_3576_; 
v_unused_3576_ = lean_ctor_get(v___x_3542_, 5);
lean_dec(v_unused_3576_);
v___x_3552_ = v___x_3542_;
v_isShared_3553_ = v_isSharedCheck_3575_;
goto v_resetjp_3551_;
}
else
{
lean_inc(v_snapshotTasks_3550_);
lean_inc(v_infoState_3549_);
lean_inc(v_messages_3548_);
lean_inc(v_traceState_3547_);
lean_inc(v_auxDeclNGen_3546_);
lean_inc(v_ngen_3545_);
lean_inc(v_nextMacroScope_3544_);
lean_inc(v_env_3543_);
lean_dec(v___x_3542_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3575_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v___x_3554_; lean_object* v___x_3556_; 
v___x_3554_ = l_Lean_Environment_setExporting(v_env_3543_, v_isExporting_3536_);
if (v_isShared_3553_ == 0)
{
lean_ctor_set(v___x_3552_, 5, v___x_3537_);
lean_ctor_set(v___x_3552_, 0, v___x_3554_);
v___x_3556_ = v___x_3552_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v___x_3554_);
lean_ctor_set(v_reuseFailAlloc_3574_, 1, v_nextMacroScope_3544_);
lean_ctor_set(v_reuseFailAlloc_3574_, 2, v_ngen_3545_);
lean_ctor_set(v_reuseFailAlloc_3574_, 3, v_auxDeclNGen_3546_);
lean_ctor_set(v_reuseFailAlloc_3574_, 4, v_traceState_3547_);
lean_ctor_set(v_reuseFailAlloc_3574_, 5, v___x_3537_);
lean_ctor_set(v_reuseFailAlloc_3574_, 6, v_messages_3548_);
lean_ctor_set(v_reuseFailAlloc_3574_, 7, v_infoState_3549_);
lean_ctor_set(v_reuseFailAlloc_3574_, 8, v_snapshotTasks_3550_);
v___x_3556_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v_mctx_3559_; lean_object* v_zetaDeltaFVarIds_3560_; lean_object* v_postponed_3561_; lean_object* v_diag_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3572_; 
v___x_3557_ = lean_st_ref_set(v___y_3535_, v___x_3556_);
v___x_3558_ = lean_st_ref_take(v___y_3538_);
v_mctx_3559_ = lean_ctor_get(v___x_3558_, 0);
v_zetaDeltaFVarIds_3560_ = lean_ctor_get(v___x_3558_, 2);
v_postponed_3561_ = lean_ctor_get(v___x_3558_, 3);
v_diag_3562_ = lean_ctor_get(v___x_3558_, 4);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3572_ == 0)
{
lean_object* v_unused_3573_; 
v_unused_3573_ = lean_ctor_get(v___x_3558_, 1);
lean_dec(v_unused_3573_);
v___x_3564_ = v___x_3558_;
v_isShared_3565_ = v_isSharedCheck_3572_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_diag_3562_);
lean_inc(v_postponed_3561_);
lean_inc(v_zetaDeltaFVarIds_3560_);
lean_inc(v_mctx_3559_);
lean_dec(v___x_3558_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3572_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3567_; 
if (v_isShared_3565_ == 0)
{
lean_ctor_set(v___x_3564_, 1, v___x_3539_);
v___x_3567_ = v___x_3564_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v_mctx_3559_);
lean_ctor_set(v_reuseFailAlloc_3571_, 1, v___x_3539_);
lean_ctor_set(v_reuseFailAlloc_3571_, 2, v_zetaDeltaFVarIds_3560_);
lean_ctor_set(v_reuseFailAlloc_3571_, 3, v_postponed_3561_);
lean_ctor_set(v_reuseFailAlloc_3571_, 4, v_diag_3562_);
v___x_3567_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___x_3568_ = lean_st_ref_set(v___y_3538_, v___x_3567_);
v___x_3569_ = lean_box(0);
v___x_3570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3570_, 0, v___x_3569_);
return v___x_3570_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_3577_, lean_object* v_isExporting_3578_, lean_object* v___x_3579_, lean_object* v___y_3580_, lean_object* v___x_3581_, lean_object* v_a_x3f_3582_, lean_object* v___y_3583_){
_start:
{
uint8_t v_isExporting_boxed_3584_; lean_object* v_res_3585_; 
v_isExporting_boxed_3584_ = lean_unbox(v_isExporting_3578_);
v_res_3585_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(v___y_3577_, v_isExporting_boxed_3584_, v___x_3579_, v___y_3580_, v___x_3581_, v_a_x3f_3582_);
lean_dec(v_a_x3f_3582_);
lean_dec(v___y_3580_);
lean_dec(v___y_3577_);
return v_res_3585_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3586_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__1, &l_Lean_Elab_Structural_registerEqnsInfo___closed__1_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1);
v___x_3587_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3587_, 0, v___x_3586_);
lean_ctor_set(v___x_3587_, 1, v___x_3586_);
lean_ctor_set(v___x_3587_, 2, v___x_3586_);
lean_ctor_set(v___x_3587_, 3, v___x_3586_);
lean_ctor_set(v___x_3587_, 4, v___x_3586_);
lean_ctor_set(v___x_3587_, 5, v___x_3586_);
return v___x_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(lean_object* v_x_3588_, uint8_t v_isExporting_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
lean_object* v___x_3595_; lean_object* v_env_3596_; uint8_t v_isExporting_3597_; lean_object* v___x_3598_; lean_object* v_env_3599_; lean_object* v_nextMacroScope_3600_; lean_object* v_ngen_3601_; lean_object* v_auxDeclNGen_3602_; lean_object* v_traceState_3603_; lean_object* v_messages_3604_; lean_object* v_infoState_3605_; lean_object* v_snapshotTasks_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3660_; 
v___x_3595_ = lean_st_ref_get(v___y_3593_);
v_env_3596_ = lean_ctor_get(v___x_3595_, 0);
lean_inc_ref(v_env_3596_);
lean_dec(v___x_3595_);
v_isExporting_3597_ = lean_ctor_get_uint8(v_env_3596_, sizeof(void*)*8);
lean_dec_ref(v_env_3596_);
v___x_3598_ = lean_st_ref_take(v___y_3593_);
v_env_3599_ = lean_ctor_get(v___x_3598_, 0);
v_nextMacroScope_3600_ = lean_ctor_get(v___x_3598_, 1);
v_ngen_3601_ = lean_ctor_get(v___x_3598_, 2);
v_auxDeclNGen_3602_ = lean_ctor_get(v___x_3598_, 3);
v_traceState_3603_ = lean_ctor_get(v___x_3598_, 4);
v_messages_3604_ = lean_ctor_get(v___x_3598_, 6);
v_infoState_3605_ = lean_ctor_get(v___x_3598_, 7);
v_snapshotTasks_3606_ = lean_ctor_get(v___x_3598_, 8);
v_isSharedCheck_3660_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3660_ == 0)
{
lean_object* v_unused_3661_; 
v_unused_3661_ = lean_ctor_get(v___x_3598_, 5);
lean_dec(v_unused_3661_);
v___x_3608_ = v___x_3598_;
v_isShared_3609_ = v_isSharedCheck_3660_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_snapshotTasks_3606_);
lean_inc(v_infoState_3605_);
lean_inc(v_messages_3604_);
lean_inc(v_traceState_3603_);
lean_inc(v_auxDeclNGen_3602_);
lean_inc(v_ngen_3601_);
lean_inc(v_nextMacroScope_3600_);
lean_inc(v_env_3599_);
lean_dec(v___x_3598_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3660_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3613_; 
v___x_3610_ = l_Lean_Environment_setExporting(v_env_3599_, v_isExporting_3589_);
v___x_3611_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__2, &l_Lean_Elab_Structural_registerEqnsInfo___closed__2_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__2);
if (v_isShared_3609_ == 0)
{
lean_ctor_set(v___x_3608_, 5, v___x_3611_);
lean_ctor_set(v___x_3608_, 0, v___x_3610_);
v___x_3613_ = v___x_3608_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v___x_3610_);
lean_ctor_set(v_reuseFailAlloc_3659_, 1, v_nextMacroScope_3600_);
lean_ctor_set(v_reuseFailAlloc_3659_, 2, v_ngen_3601_);
lean_ctor_set(v_reuseFailAlloc_3659_, 3, v_auxDeclNGen_3602_);
lean_ctor_set(v_reuseFailAlloc_3659_, 4, v_traceState_3603_);
lean_ctor_set(v_reuseFailAlloc_3659_, 5, v___x_3611_);
lean_ctor_set(v_reuseFailAlloc_3659_, 6, v_messages_3604_);
lean_ctor_set(v_reuseFailAlloc_3659_, 7, v_infoState_3605_);
lean_ctor_set(v_reuseFailAlloc_3659_, 8, v_snapshotTasks_3606_);
v___x_3613_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v_mctx_3616_; lean_object* v_zetaDeltaFVarIds_3617_; lean_object* v_postponed_3618_; lean_object* v_diag_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3657_; 
v___x_3614_ = lean_st_ref_set(v___y_3593_, v___x_3613_);
v___x_3615_ = lean_st_ref_take(v___y_3591_);
v_mctx_3616_ = lean_ctor_get(v___x_3615_, 0);
v_zetaDeltaFVarIds_3617_ = lean_ctor_get(v___x_3615_, 2);
v_postponed_3618_ = lean_ctor_get(v___x_3615_, 3);
v_diag_3619_ = lean_ctor_get(v___x_3615_, 4);
v_isSharedCheck_3657_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3657_ == 0)
{
lean_object* v_unused_3658_; 
v_unused_3658_ = lean_ctor_get(v___x_3615_, 1);
lean_dec(v_unused_3658_);
v___x_3621_ = v___x_3615_;
v_isShared_3622_ = v_isSharedCheck_3657_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_diag_3619_);
lean_inc(v_postponed_3618_);
lean_inc(v_zetaDeltaFVarIds_3617_);
lean_inc(v_mctx_3616_);
lean_dec(v___x_3615_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3657_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3623_; lean_object* v___x_3625_; 
v___x_3623_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0);
if (v_isShared_3622_ == 0)
{
lean_ctor_set(v___x_3621_, 1, v___x_3623_);
v___x_3625_ = v___x_3621_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v_mctx_3616_);
lean_ctor_set(v_reuseFailAlloc_3656_, 1, v___x_3623_);
lean_ctor_set(v_reuseFailAlloc_3656_, 2, v_zetaDeltaFVarIds_3617_);
lean_ctor_set(v_reuseFailAlloc_3656_, 3, v_postponed_3618_);
lean_ctor_set(v_reuseFailAlloc_3656_, 4, v_diag_3619_);
v___x_3625_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
lean_object* v___x_3626_; lean_object* v_r_3627_; 
v___x_3626_ = lean_st_ref_set(v___y_3591_, v___x_3625_);
lean_inc(v___y_3593_);
lean_inc_ref(v___y_3592_);
lean_inc(v___y_3591_);
lean_inc_ref(v___y_3590_);
v_r_3627_ = lean_apply_5(v_x_3588_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, lean_box(0));
if (lean_obj_tag(v_r_3627_) == 0)
{
lean_object* v_a_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3644_; 
v_a_3628_ = lean_ctor_get(v_r_3627_, 0);
v_isSharedCheck_3644_ = !lean_is_exclusive(v_r_3627_);
if (v_isSharedCheck_3644_ == 0)
{
v___x_3630_ = v_r_3627_;
v_isShared_3631_ = v_isSharedCheck_3644_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_a_3628_);
lean_dec(v_r_3627_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3644_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3633_; 
lean_inc(v_a_3628_);
if (v_isShared_3631_ == 0)
{
lean_ctor_set_tag(v___x_3630_, 1);
v___x_3633_ = v___x_3630_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_a_3628_);
v___x_3633_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
lean_object* v___x_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3641_; 
v___x_3634_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(v___y_3593_, v_isExporting_3597_, v___x_3611_, v___y_3591_, v___x_3623_, v___x_3633_);
lean_dec_ref(v___x_3633_);
v_isSharedCheck_3641_ = !lean_is_exclusive(v___x_3634_);
if (v_isSharedCheck_3641_ == 0)
{
lean_object* v_unused_3642_; 
v_unused_3642_ = lean_ctor_get(v___x_3634_, 0);
lean_dec(v_unused_3642_);
v___x_3636_ = v___x_3634_;
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
else
{
lean_dec(v___x_3634_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
lean_object* v___x_3639_; 
if (v_isShared_3637_ == 0)
{
lean_ctor_set(v___x_3636_, 0, v_a_3628_);
v___x_3639_ = v___x_3636_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v_a_3628_);
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
lean_object* v_a_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3654_; 
v_a_3645_ = lean_ctor_get(v_r_3627_, 0);
lean_inc(v_a_3645_);
lean_dec_ref(v_r_3627_);
v___x_3646_ = lean_box(0);
v___x_3647_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(v___y_3593_, v_isExporting_3597_, v___x_3611_, v___y_3591_, v___x_3623_, v___x_3646_);
v_isSharedCheck_3654_ = !lean_is_exclusive(v___x_3647_);
if (v_isSharedCheck_3654_ == 0)
{
lean_object* v_unused_3655_; 
v_unused_3655_ = lean_ctor_get(v___x_3647_, 0);
lean_dec(v_unused_3655_);
v___x_3649_ = v___x_3647_;
v_isShared_3650_ = v_isSharedCheck_3654_;
goto v_resetjp_3648_;
}
else
{
lean_dec(v___x_3647_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3654_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
lean_object* v___x_3652_; 
if (v_isShared_3650_ == 0)
{
lean_ctor_set_tag(v___x_3649_, 1);
lean_ctor_set(v___x_3649_, 0, v_a_3645_);
v___x_3652_ = v___x_3649_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v_a_3645_);
v___x_3652_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
return v___x_3652_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___boxed(lean_object* v_x_3662_, lean_object* v_isExporting_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_){
_start:
{
uint8_t v_isExporting_boxed_3669_; lean_object* v_res_3670_; 
v_isExporting_boxed_3669_ = lean_unbox(v_isExporting_3663_);
v_res_3670_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(v_x_3662_, v_isExporting_boxed_3669_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_);
lean_dec(v___y_3667_);
lean_dec_ref(v___y_3666_);
lean_dec(v___y_3665_);
lean_dec_ref(v___y_3664_);
return v_res_3670_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(lean_object* v_x_3671_, uint8_t v_when_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_){
_start:
{
if (v_when_3672_ == 0)
{
lean_object* v___x_3678_; 
lean_inc(v___y_3676_);
lean_inc_ref(v___y_3675_);
lean_inc(v___y_3674_);
lean_inc_ref(v___y_3673_);
v___x_3678_ = lean_apply_5(v_x_3671_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_, lean_box(0));
return v___x_3678_;
}
else
{
uint8_t v___x_3679_; lean_object* v___x_3680_; 
v___x_3679_ = 0;
v___x_3680_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(v_x_3671_, v___x_3679_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_);
return v___x_3680_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg___boxed(lean_object* v_x_3681_, lean_object* v_when_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_){
_start:
{
uint8_t v_when_boxed_3688_; lean_object* v_res_3689_; 
v_when_boxed_3688_ = lean_unbox(v_when_3682_);
v_res_3689_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(v_x_3681_, v_when_boxed_3688_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_);
lean_dec(v___y_3686_);
lean_dec_ref(v___y_3685_);
lean_dec(v___y_3684_);
lean_dec_ref(v___y_3683_);
return v_res_3689_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__0(lean_object* v_a_3690_, lean_object* v_a_3691_){
_start:
{
if (lean_obj_tag(v_a_3690_) == 0)
{
lean_object* v___x_3692_; 
v___x_3692_ = l_List_reverse___redArg(v_a_3691_);
return v___x_3692_;
}
else
{
lean_object* v_head_3693_; lean_object* v_tail_3694_; lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3703_; 
v_head_3693_ = lean_ctor_get(v_a_3690_, 0);
v_tail_3694_ = lean_ctor_get(v_a_3690_, 1);
v_isSharedCheck_3703_ = !lean_is_exclusive(v_a_3690_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3696_ = v_a_3690_;
v_isShared_3697_ = v_isSharedCheck_3703_;
goto v_resetjp_3695_;
}
else
{
lean_inc(v_tail_3694_);
lean_inc(v_head_3693_);
lean_dec(v_a_3690_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3703_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v___x_3698_; lean_object* v___x_3700_; 
v___x_3698_ = l_Lean_mkLevelParam(v_head_3693_);
if (v_isShared_3697_ == 0)
{
lean_ctor_set(v___x_3696_, 1, v_a_3691_);
lean_ctor_set(v___x_3696_, 0, v___x_3698_);
v___x_3700_ = v___x_3696_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v___x_3698_);
lean_ctor_set(v_reuseFailAlloc_3702_, 1, v_a_3691_);
v___x_3700_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
v_a_3690_ = v_tail_3694_;
v_a_3691_ = v___x_3700_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0(lean_object* v_levelParams_3704_, lean_object* v_declName_3705_, lean_object* v_name_3706_, lean_object* v_xs_3707_, lean_object* v_body_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_){
_start:
{
lean_object* v___x_3714_; lean_object* v_us_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; 
v___x_3714_ = lean_box(0);
lean_inc(v_levelParams_3704_);
v_us_3715_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__0(v_levelParams_3704_, v___x_3714_);
lean_inc(v_declName_3705_);
v___x_3716_ = l_Lean_mkConst(v_declName_3705_, v_us_3715_);
v___x_3717_ = l_Lean_mkAppN(v___x_3716_, v_xs_3707_);
v___x_3718_ = l_Lean_Meta_mkEq(v___x_3717_, v_body_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_);
if (lean_obj_tag(v___x_3718_) == 0)
{
lean_object* v_a_3719_; lean_object* v___x_3720_; uint8_t v___x_3721_; lean_object* v___x_3722_; 
v_a_3719_ = lean_ctor_get(v___x_3718_, 0);
lean_inc(v_a_3719_);
lean_dec_ref(v___x_3718_);
lean_inc(v_a_3719_);
v___x_3720_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___boxed), 7, 2);
lean_closure_set(v___x_3720_, 0, v_declName_3705_);
lean_closure_set(v___x_3720_, 1, v_a_3719_);
v___x_3721_ = 1;
v___x_3722_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(v___x_3720_, v___x_3721_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_);
if (lean_obj_tag(v___x_3722_) == 0)
{
lean_object* v_a_3723_; uint8_t v___x_3724_; uint8_t v___x_3725_; lean_object* v___x_3726_; 
v_a_3723_ = lean_ctor_get(v___x_3722_, 0);
lean_inc(v_a_3723_);
lean_dec_ref(v___x_3722_);
v___x_3724_ = 0;
v___x_3725_ = 1;
v___x_3726_ = l_Lean_Meta_mkForallFVars(v_xs_3707_, v_a_3719_, v___x_3724_, v___x_3721_, v___x_3721_, v___x_3725_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_);
if (lean_obj_tag(v___x_3726_) == 0)
{
lean_object* v_a_3727_; lean_object* v___x_3728_; 
v_a_3727_ = lean_ctor_get(v___x_3726_, 0);
lean_inc(v_a_3727_);
lean_dec_ref(v___x_3726_);
v___x_3728_ = l_Lean_Meta_letToHave(v_a_3727_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_);
if (lean_obj_tag(v___x_3728_) == 0)
{
lean_object* v_a_3729_; lean_object* v___x_3730_; 
v_a_3729_ = lean_ctor_get(v___x_3728_, 0);
lean_inc(v_a_3729_);
lean_dec_ref(v___x_3728_);
v___x_3730_ = l_Lean_Meta_mkLambdaFVars(v_xs_3707_, v_a_3723_, v___x_3724_, v___x_3721_, v___x_3724_, v___x_3721_, v___x_3725_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_);
if (lean_obj_tag(v___x_3730_) == 0)
{
lean_object* v_a_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; 
v_a_3731_ = lean_ctor_get(v___x_3730_, 0);
lean_inc(v_a_3731_);
lean_dec_ref(v___x_3730_);
lean_inc(v_name_3706_);
v___x_3732_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3732_, 0, v_name_3706_);
lean_ctor_set(v___x_3732_, 1, v_levelParams_3704_);
lean_ctor_set(v___x_3732_, 2, v_a_3729_);
lean_inc(v_name_3706_);
v___x_3733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3733_, 0, v_name_3706_);
lean_ctor_set(v___x_3733_, 1, v___x_3714_);
v___x_3734_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3732_);
lean_ctor_set(v___x_3734_, 1, v_a_3731_);
lean_ctor_set(v___x_3734_, 2, v___x_3733_);
v___x_3735_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3734_);
v___x_3736_ = l_Lean_addDecl(v___x_3735_, v___x_3724_, v___y_3711_, v___y_3712_);
if (lean_obj_tag(v___x_3736_) == 0)
{
lean_object* v___x_3737_; 
lean_dec_ref(v___x_3736_);
v___x_3737_ = l_Lean_inferDefEqAttr(v_name_3706_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_);
return v___x_3737_;
}
else
{
lean_dec(v_name_3706_);
return v___x_3736_;
}
}
else
{
lean_object* v_a_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3745_; 
lean_dec(v_a_3729_);
lean_dec(v_name_3706_);
lean_dec(v_levelParams_3704_);
v_a_3738_ = lean_ctor_get(v___x_3730_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v___x_3730_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3740_ = v___x_3730_;
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_a_3738_);
lean_dec(v___x_3730_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
lean_object* v___x_3743_; 
if (v_isShared_3741_ == 0)
{
v___x_3743_ = v___x_3740_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_a_3738_);
v___x_3743_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
return v___x_3743_;
}
}
}
}
else
{
lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3753_; 
lean_dec(v_a_3723_);
lean_dec(v_name_3706_);
lean_dec(v_levelParams_3704_);
v_a_3746_ = lean_ctor_get(v___x_3728_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3728_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3748_ = v___x_3728_;
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v___x_3728_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3751_; 
if (v_isShared_3749_ == 0)
{
v___x_3751_ = v___x_3748_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_a_3746_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
}
}
else
{
lean_object* v_a_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3761_; 
lean_dec(v_a_3723_);
lean_dec(v_name_3706_);
lean_dec(v_levelParams_3704_);
v_a_3754_ = lean_ctor_get(v___x_3726_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3756_ = v___x_3726_;
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_a_3754_);
lean_dec(v___x_3726_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___x_3759_; 
if (v_isShared_3757_ == 0)
{
v___x_3759_ = v___x_3756_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_a_3754_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
}
}
else
{
lean_object* v_a_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3769_; 
lean_dec(v_a_3719_);
lean_dec(v_name_3706_);
lean_dec(v_levelParams_3704_);
v_a_3762_ = lean_ctor_get(v___x_3722_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3722_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3764_ = v___x_3722_;
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_a_3762_);
lean_dec(v___x_3722_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v___x_3767_; 
if (v_isShared_3765_ == 0)
{
v___x_3767_ = v___x_3764_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v_a_3762_);
v___x_3767_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
return v___x_3767_;
}
}
}
}
else
{
lean_object* v_a_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3777_; 
lean_dec(v_name_3706_);
lean_dec(v_declName_3705_);
lean_dec(v_levelParams_3704_);
v_a_3770_ = lean_ctor_get(v___x_3718_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3718_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3772_ = v___x_3718_;
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_a_3770_);
lean_dec(v___x_3718_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3775_; 
if (v_isShared_3773_ == 0)
{
v___x_3775_ = v___x_3772_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v_a_3770_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
return v___x_3775_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0___boxed(lean_object* v_levelParams_3778_, lean_object* v_declName_3779_, lean_object* v_name_3780_, lean_object* v_xs_3781_, lean_object* v_body_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_){
_start:
{
lean_object* v_res_3788_; 
v_res_3788_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0(v_levelParams_3778_, v_declName_3779_, v_name_3780_, v_xs_3781_, v_body_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_);
lean_dec(v___y_3786_);
lean_dec_ref(v___y_3785_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3783_);
lean_dec_ref(v_xs_3781_);
return v_res_3788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3(lean_object* v_o_3789_, lean_object* v_k_3790_, uint8_t v_v_3791_){
_start:
{
lean_object* v_map_3792_; uint8_t v_hasTrace_3793_; lean_object* v___x_3795_; uint8_t v_isShared_3796_; uint8_t v_isSharedCheck_3807_; 
v_map_3792_ = lean_ctor_get(v_o_3789_, 0);
v_hasTrace_3793_ = lean_ctor_get_uint8(v_o_3789_, sizeof(void*)*1);
v_isSharedCheck_3807_ = !lean_is_exclusive(v_o_3789_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3795_ = v_o_3789_;
v_isShared_3796_ = v_isSharedCheck_3807_;
goto v_resetjp_3794_;
}
else
{
lean_inc(v_map_3792_);
lean_dec(v_o_3789_);
v___x_3795_ = lean_box(0);
v_isShared_3796_ = v_isSharedCheck_3807_;
goto v_resetjp_3794_;
}
v_resetjp_3794_:
{
lean_object* v___x_3797_; lean_object* v___x_3798_; 
v___x_3797_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3797_, 0, v_v_3791_);
lean_inc(v_k_3790_);
v___x_3798_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_3790_, v___x_3797_, v_map_3792_);
if (v_hasTrace_3793_ == 0)
{
lean_object* v___x_3799_; uint8_t v___x_3800_; lean_object* v___x_3802_; 
v___x_3799_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___closed__1));
v___x_3800_ = l_Lean_Name_isPrefixOf(v___x_3799_, v_k_3790_);
lean_dec(v_k_3790_);
if (v_isShared_3796_ == 0)
{
lean_ctor_set(v___x_3795_, 0, v___x_3798_);
v___x_3802_ = v___x_3795_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v___x_3798_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
lean_ctor_set_uint8(v___x_3802_, sizeof(void*)*1, v___x_3800_);
return v___x_3802_;
}
}
else
{
lean_object* v___x_3805_; 
lean_dec(v_k_3790_);
if (v_isShared_3796_ == 0)
{
lean_ctor_set(v___x_3795_, 0, v___x_3798_);
v___x_3805_ = v___x_3795_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v___x_3798_);
lean_ctor_set_uint8(v_reuseFailAlloc_3806_, sizeof(void*)*1, v_hasTrace_3793_);
v___x_3805_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
return v___x_3805_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3___boxed(lean_object* v_o_3808_, lean_object* v_k_3809_, lean_object* v_v_3810_){
_start:
{
uint8_t v_v_boxed_3811_; lean_object* v_res_3812_; 
v_v_boxed_3811_ = lean_unbox(v_v_3810_);
v_res_3812_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3(v_o_3808_, v_k_3809_, v_v_boxed_3811_);
return v_res_3812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2(lean_object* v_opts_3813_, lean_object* v_opt_3814_, uint8_t v_val_3815_){
_start:
{
lean_object* v_name_3816_; lean_object* v___x_3817_; 
v_name_3816_ = lean_ctor_get(v_opt_3814_, 0);
lean_inc(v_name_3816_);
lean_dec_ref(v_opt_3814_);
v___x_3817_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3(v_opts_3813_, v_name_3816_, v_val_3815_);
return v___x_3817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2___boxed(lean_object* v_opts_3818_, lean_object* v_opt_3819_, lean_object* v_val_3820_){
_start:
{
uint8_t v_val_boxed_3821_; lean_object* v_res_3822_; 
v_val_boxed_3821_ = lean_unbox(v_val_3820_);
v_res_3822_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2(v_opts_3818_, v_opt_3819_, v_val_boxed_3821_);
return v_res_3822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize(lean_object* v_declName_3823_, lean_object* v_info_3824_, lean_object* v_name_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_, lean_object* v_a_3828_, lean_object* v_a_3829_){
_start:
{
lean_object* v___x_3831_; lean_object* v_levelParams_3832_; lean_object* v_value_3833_; lean_object* v_fileName_3834_; lean_object* v_fileMap_3835_; lean_object* v_options_3836_; lean_object* v_currRecDepth_3837_; lean_object* v_ref_3838_; lean_object* v_currNamespace_3839_; lean_object* v_openDecls_3840_; lean_object* v_initHeartbeats_3841_; lean_object* v_maxHeartbeats_3842_; lean_object* v_quotContext_3843_; lean_object* v_currMacroScope_3844_; lean_object* v_cancelTk_x3f_3845_; uint8_t v_suppressElabErrors_3846_; lean_object* v_inheritedTraceOptions_3847_; lean_object* v_env_3848_; lean_object* v___f_3849_; uint8_t v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; uint8_t v___x_3854_; lean_object* v_fileName_3856_; lean_object* v_fileMap_3857_; lean_object* v_currRecDepth_3858_; lean_object* v_ref_3859_; lean_object* v_currNamespace_3860_; lean_object* v_openDecls_3861_; lean_object* v_initHeartbeats_3862_; lean_object* v_maxHeartbeats_3863_; lean_object* v_quotContext_3864_; lean_object* v_currMacroScope_3865_; lean_object* v_cancelTk_x3f_3866_; uint8_t v_suppressElabErrors_3867_; lean_object* v_inheritedTraceOptions_3868_; lean_object* v___y_3869_; uint8_t v___y_3875_; uint8_t v___x_3896_; 
v___x_3831_ = lean_st_ref_get(v_a_3829_);
v_levelParams_3832_ = lean_ctor_get(v_info_3824_, 1);
lean_inc(v_levelParams_3832_);
v_value_3833_ = lean_ctor_get(v_info_3824_, 3);
lean_inc_ref(v_value_3833_);
lean_dec_ref(v_info_3824_);
v_fileName_3834_ = lean_ctor_get(v_a_3828_, 0);
lean_inc_ref(v_fileName_3834_);
v_fileMap_3835_ = lean_ctor_get(v_a_3828_, 1);
lean_inc_ref(v_fileMap_3835_);
v_options_3836_ = lean_ctor_get(v_a_3828_, 2);
lean_inc_ref(v_options_3836_);
v_currRecDepth_3837_ = lean_ctor_get(v_a_3828_, 3);
lean_inc(v_currRecDepth_3837_);
v_ref_3838_ = lean_ctor_get(v_a_3828_, 5);
lean_inc(v_ref_3838_);
v_currNamespace_3839_ = lean_ctor_get(v_a_3828_, 6);
lean_inc(v_currNamespace_3839_);
v_openDecls_3840_ = lean_ctor_get(v_a_3828_, 7);
lean_inc(v_openDecls_3840_);
v_initHeartbeats_3841_ = lean_ctor_get(v_a_3828_, 8);
lean_inc(v_initHeartbeats_3841_);
v_maxHeartbeats_3842_ = lean_ctor_get(v_a_3828_, 9);
lean_inc(v_maxHeartbeats_3842_);
v_quotContext_3843_ = lean_ctor_get(v_a_3828_, 10);
lean_inc(v_quotContext_3843_);
v_currMacroScope_3844_ = lean_ctor_get(v_a_3828_, 11);
lean_inc(v_currMacroScope_3844_);
v_cancelTk_x3f_3845_ = lean_ctor_get(v_a_3828_, 12);
lean_inc(v_cancelTk_x3f_3845_);
v_suppressElabErrors_3846_ = lean_ctor_get_uint8(v_a_3828_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3847_ = lean_ctor_get(v_a_3828_, 13);
lean_inc_ref(v_inheritedTraceOptions_3847_);
lean_dec_ref(v_a_3828_);
v_env_3848_ = lean_ctor_get(v___x_3831_, 0);
lean_inc_ref(v_env_3848_);
lean_dec(v___x_3831_);
v___f_3849_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3849_, 0, v_levelParams_3832_);
lean_closure_set(v___f_3849_, 1, v_declName_3823_);
lean_closure_set(v___f_3849_, 2, v_name_3825_);
v___x_3850_ = 0;
v___x_3851_ = l_Lean_Meta_tactic_hygienic;
v___x_3852_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2(v_options_3836_, v___x_3851_, v___x_3850_);
v___x_3853_ = l_Lean_diagnostics;
v___x_3854_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v___x_3852_, v___x_3853_);
v___x_3896_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3848_);
lean_dec_ref(v_env_3848_);
if (v___x_3896_ == 0)
{
if (v___x_3854_ == 0)
{
v_fileName_3856_ = v_fileName_3834_;
v_fileMap_3857_ = v_fileMap_3835_;
v_currRecDepth_3858_ = v_currRecDepth_3837_;
v_ref_3859_ = v_ref_3838_;
v_currNamespace_3860_ = v_currNamespace_3839_;
v_openDecls_3861_ = v_openDecls_3840_;
v_initHeartbeats_3862_ = v_initHeartbeats_3841_;
v_maxHeartbeats_3863_ = v_maxHeartbeats_3842_;
v_quotContext_3864_ = v_quotContext_3843_;
v_currMacroScope_3865_ = v_currMacroScope_3844_;
v_cancelTk_x3f_3866_ = v_cancelTk_x3f_3845_;
v_suppressElabErrors_3867_ = v_suppressElabErrors_3846_;
v_inheritedTraceOptions_3868_ = v_inheritedTraceOptions_3847_;
v___y_3869_ = v_a_3829_;
goto v___jp_3855_;
}
else
{
v___y_3875_ = v___x_3896_;
goto v___jp_3874_;
}
}
else
{
v___y_3875_ = v___x_3854_;
goto v___jp_3874_;
}
v___jp_3855_:
{
lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; 
v___x_3870_ = l_Lean_maxRecDepth;
v___x_3871_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__6_spec__9(v___x_3852_, v___x_3870_);
v___x_3872_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3872_, 0, v_fileName_3856_);
lean_ctor_set(v___x_3872_, 1, v_fileMap_3857_);
lean_ctor_set(v___x_3872_, 2, v___x_3852_);
lean_ctor_set(v___x_3872_, 3, v_currRecDepth_3858_);
lean_ctor_set(v___x_3872_, 4, v___x_3871_);
lean_ctor_set(v___x_3872_, 5, v_ref_3859_);
lean_ctor_set(v___x_3872_, 6, v_currNamespace_3860_);
lean_ctor_set(v___x_3872_, 7, v_openDecls_3861_);
lean_ctor_set(v___x_3872_, 8, v_initHeartbeats_3862_);
lean_ctor_set(v___x_3872_, 9, v_maxHeartbeats_3863_);
lean_ctor_set(v___x_3872_, 10, v_quotContext_3864_);
lean_ctor_set(v___x_3872_, 11, v_currMacroScope_3865_);
lean_ctor_set(v___x_3872_, 12, v_cancelTk_x3f_3866_);
lean_ctor_set(v___x_3872_, 13, v_inheritedTraceOptions_3868_);
lean_ctor_set_uint8(v___x_3872_, sizeof(void*)*14, v___x_3854_);
lean_ctor_set_uint8(v___x_3872_, sizeof(void*)*14 + 1, v_suppressElabErrors_3867_);
v___x_3873_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(v_value_3833_, v___f_3849_, v___x_3850_, v_a_3826_, v_a_3827_, v___x_3872_, v___y_3869_);
lean_dec_ref(v___x_3872_);
return v___x_3873_;
}
v___jp_3874_:
{
if (v___y_3875_ == 0)
{
lean_object* v___x_3876_; lean_object* v_env_3877_; lean_object* v_nextMacroScope_3878_; lean_object* v_ngen_3879_; lean_object* v_auxDeclNGen_3880_; lean_object* v_traceState_3881_; lean_object* v_messages_3882_; lean_object* v_infoState_3883_; lean_object* v_snapshotTasks_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3894_; 
v___x_3876_ = lean_st_ref_take(v_a_3829_);
v_env_3877_ = lean_ctor_get(v___x_3876_, 0);
v_nextMacroScope_3878_ = lean_ctor_get(v___x_3876_, 1);
v_ngen_3879_ = lean_ctor_get(v___x_3876_, 2);
v_auxDeclNGen_3880_ = lean_ctor_get(v___x_3876_, 3);
v_traceState_3881_ = lean_ctor_get(v___x_3876_, 4);
v_messages_3882_ = lean_ctor_get(v___x_3876_, 6);
v_infoState_3883_ = lean_ctor_get(v___x_3876_, 7);
v_snapshotTasks_3884_ = lean_ctor_get(v___x_3876_, 8);
v_isSharedCheck_3894_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3894_ == 0)
{
lean_object* v_unused_3895_; 
v_unused_3895_ = lean_ctor_get(v___x_3876_, 5);
lean_dec(v_unused_3895_);
v___x_3886_ = v___x_3876_;
v_isShared_3887_ = v_isSharedCheck_3894_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_snapshotTasks_3884_);
lean_inc(v_infoState_3883_);
lean_inc(v_messages_3882_);
lean_inc(v_traceState_3881_);
lean_inc(v_auxDeclNGen_3880_);
lean_inc(v_ngen_3879_);
lean_inc(v_nextMacroScope_3878_);
lean_inc(v_env_3877_);
lean_dec(v___x_3876_);
v___x_3886_ = lean_box(0);
v_isShared_3887_ = v_isSharedCheck_3894_;
goto v_resetjp_3885_;
}
v_resetjp_3885_:
{
lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3891_; 
v___x_3888_ = l_Lean_Kernel_enableDiag(v_env_3877_, v___x_3854_);
v___x_3889_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__2, &l_Lean_Elab_Structural_registerEqnsInfo___closed__2_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__2);
if (v_isShared_3887_ == 0)
{
lean_ctor_set(v___x_3886_, 5, v___x_3889_);
lean_ctor_set(v___x_3886_, 0, v___x_3888_);
v___x_3891_ = v___x_3886_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v___x_3888_);
lean_ctor_set(v_reuseFailAlloc_3893_, 1, v_nextMacroScope_3878_);
lean_ctor_set(v_reuseFailAlloc_3893_, 2, v_ngen_3879_);
lean_ctor_set(v_reuseFailAlloc_3893_, 3, v_auxDeclNGen_3880_);
lean_ctor_set(v_reuseFailAlloc_3893_, 4, v_traceState_3881_);
lean_ctor_set(v_reuseFailAlloc_3893_, 5, v___x_3889_);
lean_ctor_set(v_reuseFailAlloc_3893_, 6, v_messages_3882_);
lean_ctor_set(v_reuseFailAlloc_3893_, 7, v_infoState_3883_);
lean_ctor_set(v_reuseFailAlloc_3893_, 8, v_snapshotTasks_3884_);
v___x_3891_ = v_reuseFailAlloc_3893_;
goto v_reusejp_3890_;
}
v_reusejp_3890_:
{
lean_object* v___x_3892_; 
v___x_3892_ = lean_st_ref_set(v_a_3829_, v___x_3891_);
v_fileName_3856_ = v_fileName_3834_;
v_fileMap_3857_ = v_fileMap_3835_;
v_currRecDepth_3858_ = v_currRecDepth_3837_;
v_ref_3859_ = v_ref_3838_;
v_currNamespace_3860_ = v_currNamespace_3839_;
v_openDecls_3861_ = v_openDecls_3840_;
v_initHeartbeats_3862_ = v_initHeartbeats_3841_;
v_maxHeartbeats_3863_ = v_maxHeartbeats_3842_;
v_quotContext_3864_ = v_quotContext_3843_;
v_currMacroScope_3865_ = v_currMacroScope_3844_;
v_cancelTk_x3f_3866_ = v_cancelTk_x3f_3845_;
v_suppressElabErrors_3867_ = v_suppressElabErrors_3846_;
v_inheritedTraceOptions_3868_ = v_inheritedTraceOptions_3847_;
v___y_3869_ = v_a_3829_;
goto v___jp_3855_;
}
}
}
else
{
v_fileName_3856_ = v_fileName_3834_;
v_fileMap_3857_ = v_fileMap_3835_;
v_currRecDepth_3858_ = v_currRecDepth_3837_;
v_ref_3859_ = v_ref_3838_;
v_currNamespace_3860_ = v_currNamespace_3839_;
v_openDecls_3861_ = v_openDecls_3840_;
v_initHeartbeats_3862_ = v_initHeartbeats_3841_;
v_maxHeartbeats_3863_ = v_maxHeartbeats_3842_;
v_quotContext_3864_ = v_quotContext_3843_;
v_currMacroScope_3865_ = v_currMacroScope_3844_;
v_cancelTk_x3f_3866_ = v_cancelTk_x3f_3845_;
v_suppressElabErrors_3867_ = v_suppressElabErrors_3846_;
v_inheritedTraceOptions_3868_ = v_inheritedTraceOptions_3847_;
v___y_3869_ = v_a_3829_;
goto v___jp_3855_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___boxed(lean_object* v_declName_3897_, lean_object* v_info_3898_, lean_object* v_name_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_){
_start:
{
lean_object* v_res_3905_; 
v_res_3905_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize(v_declName_3897_, v_info_3898_, v_name_3899_, v_a_3900_, v_a_3901_, v_a_3902_, v_a_3903_);
lean_dec(v_a_3903_);
lean_dec(v_a_3901_);
lean_dec_ref(v_a_3900_);
return v_res_3905_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1(lean_object* v_00_u03b1_3906_, lean_object* v_x_3907_, uint8_t v_isExporting_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_){
_start:
{
lean_object* v___x_3914_; 
v___x_3914_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(v_x_3907_, v_isExporting_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_);
return v___x_3914_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___boxed(lean_object* v_00_u03b1_3915_, lean_object* v_x_3916_, lean_object* v_isExporting_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_){
_start:
{
uint8_t v_isExporting_boxed_3923_; lean_object* v_res_3924_; 
v_isExporting_boxed_3923_ = lean_unbox(v_isExporting_3917_);
v_res_3924_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1(v_00_u03b1_3915_, v_x_3916_, v_isExporting_boxed_3923_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_);
lean_dec(v___y_3921_);
lean_dec_ref(v___y_3920_);
lean_dec(v___y_3919_);
lean_dec_ref(v___y_3918_);
return v_res_3924_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1(lean_object* v_00_u03b1_3925_, lean_object* v_x_3926_, uint8_t v_when_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_){
_start:
{
lean_object* v___x_3933_; 
v___x_3933_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(v_x_3926_, v_when_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_);
return v___x_3933_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___boxed(lean_object* v_00_u03b1_3934_, lean_object* v_x_3935_, lean_object* v_when_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_){
_start:
{
uint8_t v_when_boxed_3942_; lean_object* v_res_3943_; 
v_when_boxed_3942_ = lean_unbox(v_when_3936_);
v_res_3943_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1(v_00_u03b1_3934_, v_x_3935_, v_when_boxed_3942_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_);
lean_dec(v___y_3940_);
lean_dec_ref(v___y_3939_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
return v_res_3943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq(lean_object* v_declName_3944_, lean_object* v_info_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_){
_start:
{
lean_object* v___x_3951_; lean_object* v_env_3952_; lean_object* v_declName_3953_; lean_object* v_declNames_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; 
v___x_3951_ = lean_st_ref_get(v_a_3949_);
v_env_3952_ = lean_ctor_get(v___x_3951_, 0);
lean_inc_ref(v_env_3952_);
lean_dec(v___x_3951_);
v_declName_3953_ = lean_ctor_get(v_info_3945_, 0);
v_declNames_3954_ = lean_ctor_get(v_info_3945_, 5);
v___x_3955_ = lean_box(0);
v___x_3956_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc(v_declName_3953_);
v___x_3957_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3952_, v_declName_3953_, v___x_3956_);
v___x_3958_ = lean_unsigned_to_nat(0u);
v___x_3959_ = lean_array_get(v___x_3955_, v_declNames_3954_, v___x_3958_);
lean_inc(v___x_3957_);
v___x_3960_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___boxed), 8, 3);
lean_closure_set(v___x_3960_, 0, v_declName_3944_);
lean_closure_set(v___x_3960_, 1, v_info_3945_);
lean_closure_set(v___x_3960_, 2, v___x_3957_);
lean_inc_ref(v_a_3948_);
lean_inc(v___x_3957_);
v___x_3961_ = l_Lean_Meta_realizeConst(v___x_3959_, v___x_3957_, v___x_3960_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_);
if (lean_obj_tag(v___x_3961_) == 0)
{
lean_object* v___x_3963_; uint8_t v_isShared_3964_; uint8_t v_isSharedCheck_3968_; 
v_isSharedCheck_3968_ = !lean_is_exclusive(v___x_3961_);
if (v_isSharedCheck_3968_ == 0)
{
lean_object* v_unused_3969_; 
v_unused_3969_ = lean_ctor_get(v___x_3961_, 0);
lean_dec(v_unused_3969_);
v___x_3963_ = v___x_3961_;
v_isShared_3964_ = v_isSharedCheck_3968_;
goto v_resetjp_3962_;
}
else
{
lean_dec(v___x_3961_);
v___x_3963_ = lean_box(0);
v_isShared_3964_ = v_isSharedCheck_3968_;
goto v_resetjp_3962_;
}
v_resetjp_3962_:
{
lean_object* v___x_3966_; 
if (v_isShared_3964_ == 0)
{
lean_ctor_set(v___x_3963_, 0, v___x_3957_);
v___x_3966_ = v___x_3963_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v___x_3957_);
v___x_3966_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
return v___x_3966_;
}
}
}
else
{
lean_object* v_a_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_3977_; 
lean_dec(v___x_3957_);
v_a_3970_ = lean_ctor_get(v___x_3961_, 0);
v_isSharedCheck_3977_ = !lean_is_exclusive(v___x_3961_);
if (v_isSharedCheck_3977_ == 0)
{
v___x_3972_ = v___x_3961_;
v_isShared_3973_ = v_isSharedCheck_3977_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_a_3970_);
lean_dec(v___x_3961_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_3977_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3975_; 
if (v_isShared_3973_ == 0)
{
v___x_3975_ = v___x_3972_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3976_; 
v_reuseFailAlloc_3976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3976_, 0, v_a_3970_);
v___x_3975_ = v_reuseFailAlloc_3976_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
return v___x_3975_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq___boxed(lean_object* v_declName_3978_, lean_object* v_info_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_){
_start:
{
lean_object* v_res_3985_; 
v_res_3985_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq(v_declName_3978_, v_info_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
lean_dec(v_a_3983_);
lean_dec_ref(v_a_3982_);
lean_dec(v_a_3981_);
lean_dec_ref(v_a_3980_);
return v_res_3985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f(lean_object* v_declName_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_){
_start:
{
lean_object* v___x_3992_; lean_object* v_env_3993_; lean_object* v___x_3994_; lean_object* v_toEnvExtension_3995_; lean_object* v_asyncMode_3996_; lean_object* v___x_3997_; uint8_t v___x_3998_; lean_object* v___x_3999_; 
v___x_3992_ = lean_st_ref_get(v_a_3990_);
v_env_3993_ = lean_ctor_get(v___x_3992_, 0);
lean_inc_ref(v_env_3993_);
lean_dec(v___x_3992_);
v___x_3994_ = l_Lean_Elab_Structural_eqnInfoExt;
v_toEnvExtension_3995_ = lean_ctor_get(v___x_3994_, 0);
lean_inc_ref(v_toEnvExtension_3995_);
v_asyncMode_3996_ = lean_ctor_get(v_toEnvExtension_3995_, 2);
lean_inc(v_asyncMode_3996_);
lean_dec_ref(v_toEnvExtension_3995_);
v___x_3997_ = l_Lean_Elab_Structural_instInhabitedEqnInfo_default;
v___x_3998_ = 0;
lean_inc(v_declName_3986_);
v___x_3999_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_3997_, v___x_3994_, v_env_3993_, v_declName_3986_, v_asyncMode_3996_, v___x_3998_);
lean_dec(v_asyncMode_3996_);
if (lean_obj_tag(v___x_3999_) == 1)
{
lean_object* v_val_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4024_; 
v_val_4000_ = lean_ctor_get(v___x_3999_, 0);
v_isSharedCheck_4024_ = !lean_is_exclusive(v___x_3999_);
if (v_isSharedCheck_4024_ == 0)
{
v___x_4002_ = v___x_3999_;
v_isShared_4003_ = v_isSharedCheck_4024_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_val_4000_);
lean_dec(v___x_3999_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4024_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
lean_object* v___x_4004_; 
v___x_4004_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq(v_declName_3986_, v_val_4000_, v_a_3987_, v_a_3988_, v_a_3989_, v_a_3990_);
if (lean_obj_tag(v___x_4004_) == 0)
{
lean_object* v_a_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4015_; 
v_a_4005_ = lean_ctor_get(v___x_4004_, 0);
v_isSharedCheck_4015_ = !lean_is_exclusive(v___x_4004_);
if (v_isSharedCheck_4015_ == 0)
{
v___x_4007_ = v___x_4004_;
v_isShared_4008_ = v_isSharedCheck_4015_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_a_4005_);
lean_dec(v___x_4004_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4015_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v___x_4010_; 
if (v_isShared_4003_ == 0)
{
lean_ctor_set(v___x_4002_, 0, v_a_4005_);
v___x_4010_ = v___x_4002_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v_a_4005_);
v___x_4010_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4009_;
}
v_reusejp_4009_:
{
lean_object* v___x_4012_; 
if (v_isShared_4008_ == 0)
{
lean_ctor_set(v___x_4007_, 0, v___x_4010_);
v___x_4012_ = v___x_4007_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4013_; 
v_reuseFailAlloc_4013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4013_, 0, v___x_4010_);
v___x_4012_ = v_reuseFailAlloc_4013_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
return v___x_4012_;
}
}
}
}
else
{
lean_object* v_a_4016_; lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4023_; 
lean_del_object(v___x_4002_);
v_a_4016_ = lean_ctor_get(v___x_4004_, 0);
v_isSharedCheck_4023_ = !lean_is_exclusive(v___x_4004_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_4018_ = v___x_4004_;
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
else
{
lean_inc(v_a_4016_);
lean_dec(v___x_4004_);
v___x_4018_ = lean_box(0);
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
v_resetjp_4017_:
{
lean_object* v___x_4021_; 
if (v_isShared_4019_ == 0)
{
v___x_4021_ = v___x_4018_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_a_4016_);
v___x_4021_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
return v___x_4021_;
}
}
}
}
}
else
{
lean_object* v___x_4025_; lean_object* v___x_4026_; 
lean_dec(v___x_3999_);
lean_dec(v_declName_3986_);
v___x_4025_ = lean_box(0);
v___x_4026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4026_, 0, v___x_4025_);
return v___x_4026_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f___boxed(lean_object* v_declName_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_){
_start:
{
lean_object* v_res_4033_; 
v_res_4033_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f(v_declName_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_);
lean_dec(v_a_4031_);
lean_dec_ref(v_a_4030_);
lean_dec(v_a_4029_);
lean_dec_ref(v_a_4028_);
return v_res_4033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(lean_object* v_declName_4034_, lean_object* v_a_4035_){
_start:
{
lean_object* v___x_4037_; lean_object* v_env_4038_; lean_object* v___x_4039_; lean_object* v_toEnvExtension_4040_; lean_object* v_asyncMode_4041_; lean_object* v___x_4042_; uint8_t v___x_4043_; lean_object* v___x_4044_; 
v___x_4037_ = lean_st_ref_get(v_a_4035_);
v_env_4038_ = lean_ctor_get(v___x_4037_, 0);
lean_inc_ref(v_env_4038_);
lean_dec(v___x_4037_);
v___x_4039_ = l_Lean_Elab_Structural_eqnInfoExt;
v_toEnvExtension_4040_ = lean_ctor_get(v___x_4039_, 0);
lean_inc_ref(v_toEnvExtension_4040_);
v_asyncMode_4041_ = lean_ctor_get(v_toEnvExtension_4040_, 2);
lean_inc(v_asyncMode_4041_);
lean_dec_ref(v_toEnvExtension_4040_);
v___x_4042_ = l_Lean_Elab_Structural_instInhabitedEqnInfo_default;
v___x_4043_ = 0;
v___x_4044_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_4042_, v___x_4039_, v_env_4038_, v_declName_4034_, v_asyncMode_4041_, v___x_4043_);
lean_dec(v_asyncMode_4041_);
if (lean_obj_tag(v___x_4044_) == 1)
{
lean_object* v_val_4045_; lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4054_; 
v_val_4045_ = lean_ctor_get(v___x_4044_, 0);
v_isSharedCheck_4054_ = !lean_is_exclusive(v___x_4044_);
if (v_isSharedCheck_4054_ == 0)
{
v___x_4047_ = v___x_4044_;
v_isShared_4048_ = v_isSharedCheck_4054_;
goto v_resetjp_4046_;
}
else
{
lean_inc(v_val_4045_);
lean_dec(v___x_4044_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4054_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v_recArgPos_4049_; lean_object* v___x_4051_; 
v_recArgPos_4049_ = lean_ctor_get(v_val_4045_, 4);
lean_inc(v_recArgPos_4049_);
lean_dec(v_val_4045_);
if (v_isShared_4048_ == 0)
{
lean_ctor_set(v___x_4047_, 0, v_recArgPos_4049_);
v___x_4051_ = v___x_4047_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_recArgPos_4049_);
v___x_4051_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
lean_object* v___x_4052_; 
v___x_4052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4052_, 0, v___x_4051_);
return v___x_4052_;
}
}
}
else
{
lean_object* v___x_4055_; lean_object* v___x_4056_; 
lean_dec(v___x_4044_);
v___x_4055_ = lean_box(0);
v___x_4056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4056_, 0, v___x_4055_);
return v___x_4056_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg___boxed(lean_object* v_declName_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_){
_start:
{
lean_object* v_res_4060_; 
v_res_4060_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(v_declName_4057_, v_a_4058_);
lean_dec(v_a_4058_);
return v_res_4060_;
}
}
LEAN_EXPORT lean_object* lean_get_structural_rec_arg_pos(lean_object* v_declName_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_){
_start:
{
lean_object* v___x_4065_; 
lean_dec_ref(v_a_4062_);
v___x_4065_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(v_declName_4061_, v_a_4063_);
lean_dec(v_a_4063_);
return v___x_4065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___boxed(lean_object* v_declName_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_){
_start:
{
lean_object* v_res_4070_; 
v_res_4070_ = lean_get_structural_rec_arg_pos(v_declName_4066_, v_a_4067_, v_a_4068_);
return v_res_4070_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; 
v___x_4128_ = lean_unsigned_to_nat(2295916746u);
v___x_4129_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__22_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_4130_ = l_Lean_Name_num___override(v___x_4129_, v___x_4128_);
return v___x_4130_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; 
v___x_4132_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__24_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_4133_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_4134_ = l_Lean_Name_str___override(v___x_4133_, v___x_4132_);
return v___x_4134_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; 
v___x_4136_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__26_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_4137_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_4138_ = l_Lean_Name_str___override(v___x_4137_, v___x_4136_);
return v___x_4138_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; 
v___x_4139_ = lean_unsigned_to_nat(2u);
v___x_4140_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_4141_ = l_Lean_Name_num___override(v___x_4140_, v___x_4139_);
return v___x_4141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4143_; lean_object* v___x_4144_; 
v___x_4143_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_4144_ = l_Lean_Meta_registerGetUnfoldEqnFn(v___x_4143_);
if (lean_obj_tag(v___x_4144_) == 0)
{
lean_object* v___x_4145_; uint8_t v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; 
lean_dec_ref(v___x_4144_);
v___x_4145_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4));
v___x_4146_ = 0;
v___x_4147_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_4148_ = l_Lean_registerTraceClass(v___x_4145_, v___x_4146_, v___x_4147_);
return v___x_4148_;
}
else
{
return v___x_4144_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2____boxed(lean_object* v_a_4149_){
_start:
{
lean_object* v_res_4150_; 
v_res_4150_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_();
return v_res_4150_;
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
