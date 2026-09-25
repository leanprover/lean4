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
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
extern lean_object* l_Lean_Meta_tactic_hygienic;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
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
lean_object* v_declName_325_; lean_object* v___f_326_; lean_object* v___x_327_; lean_object* v_env_328_; uint8_t v___x_329_; 
v_declName_325_ = lean_ctor_get(v_x_297_, 0);
v___f_326_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__2));
v___x_327_ = lean_st_ref_get(v___y_303_);
v_env_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc_ref(v_env_328_);
lean_dec(v___x_327_);
lean_inc(v_declName_325_);
v___x_329_ = l_Lean_isBRecOnRecursor(v_env_328_, v_declName_325_);
if (v___x_329_ == 0)
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
lean_object* v___x_330_; 
lean_inc(v___y_303_);
lean_inc_ref(v___y_302_);
lean_inc(v___y_301_);
lean_inc_ref(v___y_300_);
lean_inc_ref(v_x_297_);
v___x_330_ = lean_infer_type(v_x_297_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; uint8_t v___x_332_; lean_object* v___x_333_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_a_331_);
lean_dec_ref_known(v___x_330_, 1);
v___x_332_ = 0;
v___x_333_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg(v_a_331_, v___f_326_, v___x_332_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
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
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___f_342_; lean_object* v___x_343_; 
lean_dec_ref(v_e_295_);
v___x_337_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_334_);
lean_inc_ref(v_x_298_);
v___x_338_ = l_Array_toSubarray___redArg(v_x_298_, v___x_337_, v_a_334_);
v___x_339_ = l_Subarray_copy___redArg(v___x_338_);
v___x_340_ = l_Lean_mkAppN(v_x_297_, v___x_339_);
lean_dec_ref(v___x_339_);
v___x_341_ = l_Array_toSubarray___redArg(v_x_298_, v_a_334_, v___x_335_);
lean_inc_ref(v___x_340_);
v___f_342_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__2___boxed), 9, 3);
lean_closure_set(v___f_342_, 0, v___x_341_);
lean_closure_set(v___f_342_, 1, v_k_296_);
lean_closure_set(v___f_342_, 2, v___x_340_);
lean_inc(v___y_303_);
lean_inc_ref(v___y_302_);
lean_inc(v___y_301_);
lean_inc_ref(v___y_300_);
v___x_343_ = lean_infer_type(v___x_340_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v_a_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v_a_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_a_344_);
lean_dec_ref_known(v___x_343_, 1);
v___x_345_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__4));
v___x_346_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2___redArg(v___x_345_, v_a_344_, v___f_342_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
return v___x_346_;
}
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
lean_dec_ref(v___f_342_);
v_a_347_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_343_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_343_);
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
v_a_363_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_370_ == 0)
{
v___x_365_ = v___x_330_;
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_330_);
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
uint8_t v___x_647__boxed_560_; lean_object* v_res_561_; 
v___x_647__boxed_560_ = lean_unbox(v___x_551_);
v_res_561_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___lam__0(v___x_550_, v___x_647__boxed_560_, v_brecOnApp_552_, v_x_553_, v_c_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
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
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; uint8_t v___x_674_; lean_object* v___x_675_; 
lean_del_object(v___x_661_);
v___x_670_ = l_Lean_Expr_appFn_x21(v_a_659_);
v___x_671_ = l_Lean_Expr_appArg_x21(v___x_670_);
lean_dec_ref(v___x_670_);
v___x_672_ = l_Lean_Expr_appArg_x21(v_a_659_);
lean_dec(v_a_659_);
v___x_673_ = l_Lean_Expr_consumeMData(v___x_672_);
lean_dec_ref(v___x_672_);
v___x_674_ = 0;
v___x_675_ = l_Lean_Meta_delta_x3f(v___x_673_, v___f_652_, v___x_674_, v___y_655_, v___y_656_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_719_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_719_ == 0)
{
v___x_678_ = v___x_675_;
v_isShared_679_ = v_isSharedCheck_719_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_675_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_719_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
if (lean_obj_tag(v_a_676_) == 1)
{
lean_object* v_val_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_714_; 
lean_del_object(v___x_678_);
v_val_680_ = lean_ctor_get(v_a_676_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v_a_676_);
if (v_isSharedCheck_714_ == 0)
{
v___x_682_ = v_a_676_;
v_isShared_683_ = v_isSharedCheck_714_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_val_680_);
lean_dec(v_a_676_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_714_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_684_; 
v___x_684_ = l_Lean_Meta_mkEq(v___x_671_, v_val_680_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
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
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 0, v_a_687_);
v___x_692_ = v___x_682_;
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
lean_del_object(v___x_682_);
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
lean_del_object(v___x_682_);
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
lean_dec(v_a_676_);
lean_dec_ref(v___x_671_);
lean_dec(v_mvarId_651_);
v___x_715_ = lean_box(0);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 0, v___x_715_);
v___x_717_ = v___x_678_;
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
lean_dec_ref(v___x_671_);
lean_dec(v_mvarId_651_);
v_a_720_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_727_ == 0)
{
v___x_722_ = v___x_675_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_675_);
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
lean_object* v___x_774_; lean_object* v_traceState_775_; lean_object* v_traces_776_; lean_object* v___x_777_; lean_object* v_traceState_778_; lean_object* v_env_779_; lean_object* v_nextMacroScope_780_; lean_object* v_ngen_781_; lean_object* v_auxDeclNGen_782_; lean_object* v_cache_783_; lean_object* v_recordedDeps_784_; lean_object* v_messages_785_; lean_object* v_infoState_786_; lean_object* v_snapshotTasks_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_806_; 
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
v_recordedDeps_784_ = lean_ctor_get(v___x_777_, 6);
v_messages_785_ = lean_ctor_get(v___x_777_, 7);
v_infoState_786_ = lean_ctor_get(v___x_777_, 8);
v_snapshotTasks_787_ = lean_ctor_get(v___x_777_, 9);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_806_ == 0)
{
v___x_789_ = v___x_777_;
v_isShared_790_ = v_isSharedCheck_806_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_snapshotTasks_787_);
lean_inc(v_infoState_786_);
lean_inc(v_messages_785_);
lean_inc(v_recordedDeps_784_);
lean_inc(v_cache_783_);
lean_inc(v_traceState_778_);
lean_inc(v_auxDeclNGen_782_);
lean_inc(v_ngen_781_);
lean_inc(v_nextMacroScope_780_);
lean_inc(v_env_779_);
lean_dec(v___x_777_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_806_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
uint64_t v_tid_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_804_; 
v_tid_791_ = lean_ctor_get_uint64(v_traceState_778_, sizeof(void*)*1);
v_isSharedCheck_804_ = !lean_is_exclusive(v_traceState_778_);
if (v_isSharedCheck_804_ == 0)
{
lean_object* v_unused_805_; 
v_unused_805_ = lean_ctor_get(v_traceState_778_, 0);
lean_dec(v_unused_805_);
v___x_793_ = v_traceState_778_;
v_isShared_794_ = v_isSharedCheck_804_;
goto v_resetjp_792_;
}
else
{
lean_dec(v_traceState_778_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_804_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_795_; lean_object* v___x_797_; 
v___x_795_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__1);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v___x_795_);
v___x_797_ = v___x_793_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v___x_795_);
lean_ctor_set_uint64(v_reuseFailAlloc_803_, sizeof(void*)*1, v_tid_791_);
v___x_797_ = v_reuseFailAlloc_803_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
lean_object* v___x_799_; 
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 4, v___x_797_);
v___x_799_ = v___x_789_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_env_779_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v_nextMacroScope_780_);
lean_ctor_set(v_reuseFailAlloc_802_, 2, v_ngen_781_);
lean_ctor_set(v_reuseFailAlloc_802_, 3, v_auxDeclNGen_782_);
lean_ctor_set(v_reuseFailAlloc_802_, 4, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_802_, 5, v_cache_783_);
lean_ctor_set(v_reuseFailAlloc_802_, 6, v_recordedDeps_784_);
lean_ctor_set(v_reuseFailAlloc_802_, 7, v_messages_785_);
lean_ctor_set(v_reuseFailAlloc_802_, 8, v_infoState_786_);
lean_ctor_set(v_reuseFailAlloc_802_, 9, v_snapshotTasks_787_);
v___x_799_ = v_reuseFailAlloc_802_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = lean_st_ref_put(v___y_772_, v___x_799_);
v___x_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_801_, 0, v_traces_776_);
return v___x_801_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___boxed(lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(v___y_807_);
lean_dec(v___y_807_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(v___y_813_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___boxed(lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v___y_816_, v___y_817_, v___y_818_, v___y_819_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
return v_res_821_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(lean_object* v_opts_822_, lean_object* v_opt_823_){
_start:
{
lean_object* v_name_824_; lean_object* v_defValue_825_; lean_object* v_map_826_; lean_object* v___x_827_; 
v_name_824_ = lean_ctor_get(v_opt_823_, 0);
v_defValue_825_ = lean_ctor_get(v_opt_823_, 1);
v_map_826_ = lean_ctor_get(v_opts_822_, 0);
v___x_827_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_826_, v_name_824_);
if (lean_obj_tag(v___x_827_) == 0)
{
uint8_t v___x_828_; 
v___x_828_ = lean_unbox(v_defValue_825_);
return v___x_828_;
}
else
{
lean_object* v_val_829_; 
v_val_829_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_val_829_);
lean_dec_ref_known(v___x_827_, 1);
if (lean_obj_tag(v_val_829_) == 1)
{
uint8_t v_v_830_; 
v_v_830_ = lean_ctor_get_uint8(v_val_829_, 0);
lean_dec_ref_known(v_val_829_, 0);
return v_v_830_;
}
else
{
uint8_t v___x_831_; 
lean_dec(v_val_829_);
v___x_831_ = lean_unbox(v_defValue_825_);
return v___x_831_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___boxed(lean_object* v_opts_832_, lean_object* v_opt_833_){
_start:
{
uint8_t v_res_834_; lean_object* v_r_835_; 
v_res_834_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_opts_832_, v_opt_833_);
lean_dec_ref(v_opt_833_);
lean_dec_ref(v_opts_832_);
v_r_835_ = lean_box(v_res_834_);
return v_r_835_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1(void){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__0));
v___x_838_ = l_Lean_stringToMessageData(v___x_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0(lean_object* v_mvarId_839_, lean_object* v_x_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_846_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1);
v___x_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_847_, 0, v_mvarId_839_);
v___x_848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_846_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
v___x_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___boxed(lean_object* v_mvarId_850_, lean_object* v_x_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0(v_mvarId_850_, v_x_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec_ref(v_x_851_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(lean_object* v_____r_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = lean_box(0);
v___x_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1___boxed(lean_object* v_____r_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_____r_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
return v_res_872_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0(void){
_start:
{
lean_object* v___x_873_; double v___x_874_; 
v___x_873_ = lean_unsigned_to_nat(0u);
v___x_874_ = lean_float_of_nat(v___x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(lean_object* v_cls_878_, lean_object* v_msg_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v_ref_885_; lean_object* v___x_886_; lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_932_; 
v_ref_885_ = lean_ctor_get(v___y_882_, 2);
v___x_886_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(v_msg_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
v_a_887_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_932_ == 0)
{
v___x_889_ = v___x_886_;
v_isShared_890_ = v_isSharedCheck_932_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_886_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_932_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_891_; lean_object* v_traceState_892_; lean_object* v_env_893_; lean_object* v_nextMacroScope_894_; lean_object* v_ngen_895_; lean_object* v_auxDeclNGen_896_; lean_object* v_cache_897_; lean_object* v_recordedDeps_898_; lean_object* v_messages_899_; lean_object* v_infoState_900_; lean_object* v_snapshotTasks_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_931_; 
v___x_891_ = lean_st_ref_take(v___y_883_);
v_traceState_892_ = lean_ctor_get(v___x_891_, 4);
v_env_893_ = lean_ctor_get(v___x_891_, 0);
v_nextMacroScope_894_ = lean_ctor_get(v___x_891_, 1);
v_ngen_895_ = lean_ctor_get(v___x_891_, 2);
v_auxDeclNGen_896_ = lean_ctor_get(v___x_891_, 3);
v_cache_897_ = lean_ctor_get(v___x_891_, 5);
v_recordedDeps_898_ = lean_ctor_get(v___x_891_, 6);
v_messages_899_ = lean_ctor_get(v___x_891_, 7);
v_infoState_900_ = lean_ctor_get(v___x_891_, 8);
v_snapshotTasks_901_ = lean_ctor_get(v___x_891_, 9);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_931_ == 0)
{
v___x_903_ = v___x_891_;
v_isShared_904_ = v_isSharedCheck_931_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_snapshotTasks_901_);
lean_inc(v_infoState_900_);
lean_inc(v_messages_899_);
lean_inc(v_recordedDeps_898_);
lean_inc(v_cache_897_);
lean_inc(v_traceState_892_);
lean_inc(v_auxDeclNGen_896_);
lean_inc(v_ngen_895_);
lean_inc(v_nextMacroScope_894_);
lean_inc(v_env_893_);
lean_dec(v___x_891_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_931_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
uint64_t v_tid_905_; lean_object* v_traces_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_930_; 
v_tid_905_ = lean_ctor_get_uint64(v_traceState_892_, sizeof(void*)*1);
v_traces_906_ = lean_ctor_get(v_traceState_892_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v_traceState_892_);
if (v_isSharedCheck_930_ == 0)
{
v___x_908_ = v_traceState_892_;
v_isShared_909_ = v_isSharedCheck_930_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_traces_906_);
lean_dec(v_traceState_892_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_930_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_910_; lean_object* v___x_911_; double v___x_912_; uint8_t v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_921_; 
v___x_910_ = lean_box(0);
v___x_911_ = lean_box(0);
v___x_912_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0);
v___x_913_ = 0;
v___x_914_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__1));
v___x_915_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_915_, 0, v_cls_878_);
lean_ctor_set(v___x_915_, 1, v___x_911_);
lean_ctor_set(v___x_915_, 2, v___x_914_);
lean_ctor_set_float(v___x_915_, sizeof(void*)*3, v___x_912_);
lean_ctor_set_float(v___x_915_, sizeof(void*)*3 + 8, v___x_912_);
lean_ctor_set_uint8(v___x_915_, sizeof(void*)*3 + 16, v___x_913_);
v___x_916_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__2));
v___x_917_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_917_, 0, v___x_915_);
lean_ctor_set(v___x_917_, 1, v_a_887_);
lean_ctor_set(v___x_917_, 2, v___x_916_);
lean_inc(v_ref_885_);
v___x_918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_918_, 0, v_ref_885_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = l_Lean_PersistentArray_push___redArg(v_traces_906_, v___x_918_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 0, v___x_919_);
v___x_921_ = v___x_908_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_919_);
lean_ctor_set_uint64(v_reuseFailAlloc_929_, sizeof(void*)*1, v_tid_905_);
v___x_921_ = v_reuseFailAlloc_929_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v___x_923_; 
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 4, v___x_921_);
v___x_923_ = v___x_903_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_env_893_);
lean_ctor_set(v_reuseFailAlloc_928_, 1, v_nextMacroScope_894_);
lean_ctor_set(v_reuseFailAlloc_928_, 2, v_ngen_895_);
lean_ctor_set(v_reuseFailAlloc_928_, 3, v_auxDeclNGen_896_);
lean_ctor_set(v_reuseFailAlloc_928_, 4, v___x_921_);
lean_ctor_set(v_reuseFailAlloc_928_, 5, v_cache_897_);
lean_ctor_set(v_reuseFailAlloc_928_, 6, v_recordedDeps_898_);
lean_ctor_set(v_reuseFailAlloc_928_, 7, v_messages_899_);
lean_ctor_set(v_reuseFailAlloc_928_, 8, v_infoState_900_);
lean_ctor_set(v_reuseFailAlloc_928_, 9, v_snapshotTasks_901_);
v___x_923_ = v_reuseFailAlloc_928_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
lean_object* v___x_924_; lean_object* v___x_926_; 
v___x_924_ = lean_st_ref_put(v___y_883_, v___x_923_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v___x_910_);
v___x_926_ = v___x_889_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_910_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___boxed(lean_object* v_cls_933_, lean_object* v_msg_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_933_, v_msg_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(lean_object* v_opts_941_, lean_object* v_opt_942_){
_start:
{
lean_object* v_name_943_; lean_object* v_defValue_944_; lean_object* v_map_945_; lean_object* v___x_946_; 
v_name_943_ = lean_ctor_get(v_opt_942_, 0);
v_defValue_944_ = lean_ctor_get(v_opt_942_, 1);
v_map_945_ = lean_ctor_get(v_opts_941_, 0);
v___x_946_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_945_, v_name_943_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_inc(v_defValue_944_);
return v_defValue_944_;
}
else
{
lean_object* v_val_947_; 
v_val_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_val_947_);
lean_dec_ref_known(v___x_946_, 1);
if (lean_obj_tag(v_val_947_) == 3)
{
lean_object* v_v_948_; 
v_v_948_ = lean_ctor_get(v_val_947_, 0);
lean_inc(v_v_948_);
lean_dec_ref_known(v_val_947_, 1);
return v_v_948_;
}
else
{
lean_dec(v_val_947_);
lean_inc(v_defValue_944_);
return v_defValue_944_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8___boxed(lean_object* v_opts_949_, lean_object* v_opt_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v_opts_949_, v_opt_950_);
lean_dec_ref(v_opt_950_);
lean_dec_ref(v_opts_949_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5_spec__6(size_t v_sz_952_, size_t v_i_953_, lean_object* v_bs_954_){
_start:
{
uint8_t v___x_955_; 
v___x_955_ = lean_usize_dec_lt(v_i_953_, v_sz_952_);
if (v___x_955_ == 0)
{
return v_bs_954_;
}
else
{
lean_object* v_v_956_; lean_object* v_msg_957_; lean_object* v___x_958_; lean_object* v_bs_x27_959_; size_t v___x_960_; size_t v___x_961_; lean_object* v___x_962_; 
v_v_956_ = lean_array_uget_borrowed(v_bs_954_, v_i_953_);
v_msg_957_ = lean_ctor_get(v_v_956_, 1);
lean_inc_ref(v_msg_957_);
v___x_958_ = lean_unsigned_to_nat(0u);
v_bs_x27_959_ = lean_array_uset(v_bs_954_, v_i_953_, v___x_958_);
v___x_960_ = ((size_t)1ULL);
v___x_961_ = lean_usize_add(v_i_953_, v___x_960_);
v___x_962_ = lean_array_uset(v_bs_x27_959_, v_i_953_, v_msg_957_);
v_i_953_ = v___x_961_;
v_bs_954_ = v___x_962_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5_spec__6___boxed(lean_object* v_sz_964_, lean_object* v_i_965_, lean_object* v_bs_966_){
_start:
{
size_t v_sz_boxed_967_; size_t v_i_boxed_968_; lean_object* v_res_969_; 
v_sz_boxed_967_ = lean_unbox_usize(v_sz_964_);
lean_dec(v_sz_964_);
v_i_boxed_968_ = lean_unbox_usize(v_i_965_);
lean_dec(v_i_965_);
v_res_969_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5_spec__6(v_sz_boxed_967_, v_i_boxed_968_, v_bs_966_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5(lean_object* v_oldTraces_970_, lean_object* v_data_971_, lean_object* v_ref_972_, lean_object* v_msg_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v_toCold_979_; lean_object* v_currRecDepth_980_; lean_object* v_ref_981_; uint16_t v_optionFlags_982_; uint8_t v_suppressElabErrors_983_; uint8_t v_isRecordingDeps_984_; lean_object* v_ref_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v_traceState_988_; lean_object* v_traces_989_; lean_object* v___x_990_; size_t v_sz_991_; size_t v___x_992_; lean_object* v___x_993_; lean_object* v_msg_994_; lean_object* v___x_995_; lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1034_; 
v_toCold_979_ = lean_ctor_get(v___y_976_, 0);
v_currRecDepth_980_ = lean_ctor_get(v___y_976_, 1);
v_ref_981_ = lean_ctor_get(v___y_976_, 2);
v_optionFlags_982_ = lean_ctor_get_uint16(v___y_976_, sizeof(void*)*3);
v_suppressElabErrors_983_ = lean_ctor_get_uint8(v___y_976_, sizeof(void*)*3 + 2);
v_isRecordingDeps_984_ = lean_ctor_get_uint8(v___y_976_, sizeof(void*)*3 + 3);
v_ref_985_ = l_Lean_replaceRef(v_ref_972_, v_ref_981_);
lean_inc(v_currRecDepth_980_);
lean_inc_ref(v_toCold_979_);
v___x_986_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_986_, 0, v_toCold_979_);
lean_ctor_set(v___x_986_, 1, v_currRecDepth_980_);
lean_ctor_set(v___x_986_, 2, v_ref_985_);
lean_ctor_set_uint16(v___x_986_, sizeof(void*)*3, v_optionFlags_982_);
lean_ctor_set_uint8(v___x_986_, sizeof(void*)*3 + 2, v_suppressElabErrors_983_);
lean_ctor_set_uint8(v___x_986_, sizeof(void*)*3 + 3, v_isRecordingDeps_984_);
v___x_987_ = lean_st_ref_get(v___y_977_);
v_traceState_988_ = lean_ctor_get(v___x_987_, 4);
lean_inc_ref(v_traceState_988_);
lean_dec(v___x_987_);
v_traces_989_ = lean_ctor_get(v_traceState_988_, 0);
lean_inc_ref(v_traces_989_);
lean_dec_ref(v_traceState_988_);
v___x_990_ = l_Lean_PersistentArray_toArray___redArg(v_traces_989_);
lean_dec_ref(v_traces_989_);
v_sz_991_ = lean_array_size(v___x_990_);
v___x_992_ = ((size_t)0ULL);
v___x_993_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5_spec__6(v_sz_991_, v___x_992_, v___x_990_);
v_msg_994_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_994_, 0, v_data_971_);
lean_ctor_set(v_msg_994_, 1, v_msg_973_);
lean_ctor_set(v_msg_994_, 2, v___x_993_);
v___x_995_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(v_msg_994_, v___y_974_, v___y_975_, v___x_986_, v___y_977_);
lean_dec_ref_known(v___x_986_, 3);
v_a_996_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_998_ = v___x_995_;
v_isShared_999_ = v_isSharedCheck_1034_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_995_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1034_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1000_; lean_object* v_traceState_1001_; lean_object* v_env_1002_; lean_object* v_nextMacroScope_1003_; lean_object* v_ngen_1004_; lean_object* v_auxDeclNGen_1005_; lean_object* v_cache_1006_; lean_object* v_recordedDeps_1007_; lean_object* v_messages_1008_; lean_object* v_infoState_1009_; lean_object* v_snapshotTasks_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1033_; 
v___x_1000_ = lean_st_ref_take(v___y_977_);
v_traceState_1001_ = lean_ctor_get(v___x_1000_, 4);
v_env_1002_ = lean_ctor_get(v___x_1000_, 0);
v_nextMacroScope_1003_ = lean_ctor_get(v___x_1000_, 1);
v_ngen_1004_ = lean_ctor_get(v___x_1000_, 2);
v_auxDeclNGen_1005_ = lean_ctor_get(v___x_1000_, 3);
v_cache_1006_ = lean_ctor_get(v___x_1000_, 5);
v_recordedDeps_1007_ = lean_ctor_get(v___x_1000_, 6);
v_messages_1008_ = lean_ctor_get(v___x_1000_, 7);
v_infoState_1009_ = lean_ctor_get(v___x_1000_, 8);
v_snapshotTasks_1010_ = lean_ctor_get(v___x_1000_, 9);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1012_ = v___x_1000_;
v_isShared_1013_ = v_isSharedCheck_1033_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_snapshotTasks_1010_);
lean_inc(v_infoState_1009_);
lean_inc(v_messages_1008_);
lean_inc(v_recordedDeps_1007_);
lean_inc(v_cache_1006_);
lean_inc(v_traceState_1001_);
lean_inc(v_auxDeclNGen_1005_);
lean_inc(v_ngen_1004_);
lean_inc(v_nextMacroScope_1003_);
lean_inc(v_env_1002_);
lean_dec(v___x_1000_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1033_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
uint64_t v_tid_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1031_; 
v_tid_1014_ = lean_ctor_get_uint64(v_traceState_1001_, sizeof(void*)*1);
v_isSharedCheck_1031_ = !lean_is_exclusive(v_traceState_1001_);
if (v_isSharedCheck_1031_ == 0)
{
lean_object* v_unused_1032_; 
v_unused_1032_ = lean_ctor_get(v_traceState_1001_, 0);
lean_dec(v_unused_1032_);
v___x_1016_ = v_traceState_1001_;
v_isShared_1017_ = v_isSharedCheck_1031_;
goto v_resetjp_1015_;
}
else
{
lean_dec(v_traceState_1001_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1031_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1022_; 
v___x_1018_ = lean_box(0);
v___x_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1019_, 0, v_ref_972_);
lean_ctor_set(v___x_1019_, 1, v_a_996_);
v___x_1020_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_970_, v___x_1019_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 0, v___x_1020_);
v___x_1022_ = v___x_1016_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1020_);
lean_ctor_set_uint64(v_reuseFailAlloc_1030_, sizeof(void*)*1, v_tid_1014_);
v___x_1022_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
lean_object* v___x_1024_; 
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 4, v___x_1022_);
v___x_1024_ = v___x_1012_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_env_1002_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_nextMacroScope_1003_);
lean_ctor_set(v_reuseFailAlloc_1029_, 2, v_ngen_1004_);
lean_ctor_set(v_reuseFailAlloc_1029_, 3, v_auxDeclNGen_1005_);
lean_ctor_set(v_reuseFailAlloc_1029_, 4, v___x_1022_);
lean_ctor_set(v_reuseFailAlloc_1029_, 5, v_cache_1006_);
lean_ctor_set(v_reuseFailAlloc_1029_, 6, v_recordedDeps_1007_);
lean_ctor_set(v_reuseFailAlloc_1029_, 7, v_messages_1008_);
lean_ctor_set(v_reuseFailAlloc_1029_, 8, v_infoState_1009_);
lean_ctor_set(v_reuseFailAlloc_1029_, 9, v_snapshotTasks_1010_);
v___x_1024_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1025_; lean_object* v___x_1027_; 
v___x_1025_ = lean_st_ref_put(v___y_977_, v___x_1024_);
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 0, v___x_1018_);
v___x_1027_ = v___x_998_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1018_);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5___boxed(lean_object* v_oldTraces_1035_, lean_object* v_data_1036_, lean_object* v_ref_1037_, lean_object* v_msg_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5(v_oldTraces_1035_, v_data_1036_, v_ref_1037_, v_msg_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(lean_object* v_x_1045_){
_start:
{
if (lean_obj_tag(v_x_1045_) == 0)
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
v_a_1047_ = lean_ctor_get(v_x_1045_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v_x_1045_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v_x_1045_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v_x_1045_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
lean_ctor_set_tag(v___x_1049_, 1);
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
v_a_1055_ = lean_ctor_get(v_x_1045_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v_x_1045_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v_x_1045_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v_x_1045_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
lean_ctor_set_tag(v___x_1057_, 0);
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg___boxed(lean_object* v_x_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(v_x_1063_);
return v_res_1065_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7(lean_object* v_e_1066_){
_start:
{
if (lean_obj_tag(v_e_1066_) == 0)
{
uint8_t v___x_1067_; 
v___x_1067_ = 2;
return v___x_1067_;
}
else
{
uint8_t v___x_1068_; 
v___x_1068_ = 0;
return v___x_1068_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7___boxed(lean_object* v_e_1069_){
_start:
{
uint8_t v_res_1070_; lean_object* v_r_1071_; 
v_res_1070_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7(v_e_1069_);
lean_dec_ref(v_e_1069_);
v_r_1071_ = lean_box(v_res_1070_);
return v_r_1071_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__0));
v___x_1074_ = l_Lean_stringToMessageData(v___x_1073_);
return v___x_1074_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2(void){
_start:
{
lean_object* v___x_1075_; double v___x_1076_; 
v___x_1075_ = lean_unsigned_to_nat(1000u);
v___x_1076_ = lean_float_of_nat(v___x_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(lean_object* v_cls_1077_, uint8_t v_collapsed_1078_, lean_object* v_tag_1079_, lean_object* v_opts_1080_, uint8_t v_clsEnabled_1081_, lean_object* v_oldTraces_1082_, lean_object* v_msg_1083_, lean_object* v_resStartStop_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v_fst_1090_; lean_object* v_snd_1091_; lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v_data_1095_; lean_object* v_fst_1098_; lean_object* v_snd_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; lean_object* v___y_1103_; lean_object* v_a_1104_; uint8_t v___y_1119_; double v___y_1151_; 
v_fst_1090_ = lean_ctor_get(v_resStartStop_1084_, 0);
lean_inc(v_fst_1090_);
v_snd_1091_ = lean_ctor_get(v_resStartStop_1084_, 1);
lean_inc(v_snd_1091_);
lean_dec_ref(v_resStartStop_1084_);
v_fst_1098_ = lean_ctor_get(v_snd_1091_, 0);
lean_inc(v_fst_1098_);
v_snd_1099_ = lean_ctor_get(v_snd_1091_, 1);
lean_inc(v_snd_1099_);
lean_dec(v_snd_1091_);
v___x_1100_ = l_Lean_trace_profiler;
v___x_1101_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_opts_1080_, v___x_1100_);
if (v___x_1101_ == 0)
{
v___y_1119_ = v___x_1101_;
goto v___jp_1118_;
}
else
{
lean_object* v___x_1156_; uint8_t v___x_1157_; 
v___x_1156_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1157_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_opts_1080_, v___x_1156_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1158_; lean_object* v___x_1159_; double v___x_1160_; double v___x_1161_; double v___x_1162_; 
v___x_1158_ = l_Lean_trace_profiler_threshold;
v___x_1159_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v_opts_1080_, v___x_1158_);
v___x_1160_ = lean_float_of_nat(v___x_1159_);
v___x_1161_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2);
v___x_1162_ = lean_float_div(v___x_1160_, v___x_1161_);
v___y_1151_ = v___x_1162_;
goto v___jp_1150_;
}
else
{
lean_object* v___x_1163_; lean_object* v___x_1164_; double v___x_1165_; 
v___x_1163_ = l_Lean_trace_profiler_threshold;
v___x_1164_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v_opts_1080_, v___x_1163_);
v___x_1165_ = lean_float_of_nat(v___x_1164_);
v___y_1151_ = v___x_1165_;
goto v___jp_1150_;
}
}
v___jp_1092_:
{
lean_object* v___x_1096_; 
lean_inc(v___y_1094_);
v___x_1096_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5(v_oldTraces_1082_, v_data_1095_, v___y_1094_, v___y_1093_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v___x_1097_; 
lean_dec_ref_known(v___x_1096_, 1);
v___x_1097_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(v_fst_1090_);
return v___x_1097_;
}
else
{
lean_dec(v_fst_1090_);
return v___x_1096_;
}
}
v___jp_1102_:
{
uint8_t v_result_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; double v___x_1108_; lean_object* v_data_1109_; 
v_result_1105_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7(v_fst_1090_);
v___x_1106_ = lean_box(v_result_1105_);
v___x_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
v___x_1108_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0);
lean_inc_ref(v_tag_1079_);
lean_inc_ref(v___x_1107_);
lean_inc(v_cls_1077_);
v_data_1109_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1109_, 0, v_cls_1077_);
lean_ctor_set(v_data_1109_, 1, v___x_1107_);
lean_ctor_set(v_data_1109_, 2, v_tag_1079_);
lean_ctor_set_float(v_data_1109_, sizeof(void*)*3, v___x_1108_);
lean_ctor_set_float(v_data_1109_, sizeof(void*)*3 + 8, v___x_1108_);
lean_ctor_set_uint8(v_data_1109_, sizeof(void*)*3 + 16, v_collapsed_1078_);
if (v___x_1101_ == 0)
{
lean_dec_ref_known(v___x_1107_, 1);
lean_dec(v_snd_1099_);
lean_dec(v_fst_1098_);
lean_dec_ref(v_tag_1079_);
lean_dec(v_cls_1077_);
v___y_1093_ = v_a_1104_;
v___y_1094_ = v___y_1103_;
v_data_1095_ = v_data_1109_;
goto v___jp_1092_;
}
else
{
lean_object* v_data_1110_; double v___x_1111_; double v___x_1112_; 
lean_dec_ref_known(v_data_1109_, 3);
v_data_1110_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1110_, 0, v_cls_1077_);
lean_ctor_set(v_data_1110_, 1, v___x_1107_);
lean_ctor_set(v_data_1110_, 2, v_tag_1079_);
v___x_1111_ = lean_unbox_float(v_fst_1098_);
lean_dec(v_fst_1098_);
lean_ctor_set_float(v_data_1110_, sizeof(void*)*3, v___x_1111_);
v___x_1112_ = lean_unbox_float(v_snd_1099_);
lean_dec(v_snd_1099_);
lean_ctor_set_float(v_data_1110_, sizeof(void*)*3 + 8, v___x_1112_);
lean_ctor_set_uint8(v_data_1110_, sizeof(void*)*3 + 16, v_collapsed_1078_);
v___y_1093_ = v_a_1104_;
v___y_1094_ = v___y_1103_;
v_data_1095_ = v_data_1110_;
goto v___jp_1092_;
}
}
v___jp_1113_:
{
lean_object* v_ref_1114_; lean_object* v___x_1115_; 
v_ref_1114_ = lean_ctor_get(v___y_1087_, 2);
lean_inc(v___y_1088_);
lean_inc_ref(v___y_1087_);
lean_inc(v___y_1086_);
lean_inc_ref(v___y_1085_);
lean_inc(v_fst_1090_);
v___x_1115_ = lean_apply_6(v_msg_1083_, v_fst_1090_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, lean_box(0));
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1116_);
lean_dec_ref_known(v___x_1115_, 1);
v___y_1103_ = v_ref_1114_;
v_a_1104_ = v_a_1116_;
goto v___jp_1102_;
}
else
{
lean_object* v___x_1117_; 
lean_dec_ref_known(v___x_1115_, 1);
v___x_1117_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1);
v___y_1103_ = v_ref_1114_;
v_a_1104_ = v___x_1117_;
goto v___jp_1102_;
}
}
v___jp_1118_:
{
if (v_clsEnabled_1081_ == 0)
{
if (v___y_1119_ == 0)
{
lean_object* v___x_1120_; lean_object* v_traceState_1121_; lean_object* v_env_1122_; lean_object* v_nextMacroScope_1123_; lean_object* v_ngen_1124_; lean_object* v_auxDeclNGen_1125_; lean_object* v_cache_1126_; lean_object* v_recordedDeps_1127_; lean_object* v_messages_1128_; lean_object* v_infoState_1129_; lean_object* v_snapshotTasks_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1149_; 
lean_dec(v_snd_1099_);
lean_dec(v_fst_1098_);
lean_dec_ref(v_msg_1083_);
lean_dec_ref(v_tag_1079_);
lean_dec(v_cls_1077_);
v___x_1120_ = lean_st_ref_take(v___y_1088_);
v_traceState_1121_ = lean_ctor_get(v___x_1120_, 4);
v_env_1122_ = lean_ctor_get(v___x_1120_, 0);
v_nextMacroScope_1123_ = lean_ctor_get(v___x_1120_, 1);
v_ngen_1124_ = lean_ctor_get(v___x_1120_, 2);
v_auxDeclNGen_1125_ = lean_ctor_get(v___x_1120_, 3);
v_cache_1126_ = lean_ctor_get(v___x_1120_, 5);
v_recordedDeps_1127_ = lean_ctor_get(v___x_1120_, 6);
v_messages_1128_ = lean_ctor_get(v___x_1120_, 7);
v_infoState_1129_ = lean_ctor_get(v___x_1120_, 8);
v_snapshotTasks_1130_ = lean_ctor_get(v___x_1120_, 9);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1132_ = v___x_1120_;
v_isShared_1133_ = v_isSharedCheck_1149_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_snapshotTasks_1130_);
lean_inc(v_infoState_1129_);
lean_inc(v_messages_1128_);
lean_inc(v_recordedDeps_1127_);
lean_inc(v_cache_1126_);
lean_inc(v_traceState_1121_);
lean_inc(v_auxDeclNGen_1125_);
lean_inc(v_ngen_1124_);
lean_inc(v_nextMacroScope_1123_);
lean_inc(v_env_1122_);
lean_dec(v___x_1120_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1149_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
uint64_t v_tid_1134_; lean_object* v_traces_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1148_; 
v_tid_1134_ = lean_ctor_get_uint64(v_traceState_1121_, sizeof(void*)*1);
v_traces_1135_ = lean_ctor_get(v_traceState_1121_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v_traceState_1121_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1137_ = v_traceState_1121_;
v_isShared_1138_ = v_isSharedCheck_1148_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_traces_1135_);
lean_dec(v_traceState_1121_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1148_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1139_; lean_object* v___x_1141_; 
v___x_1139_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1082_, v_traces_1135_);
lean_dec_ref(v_traces_1135_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1139_);
v___x_1141_ = v___x_1137_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1139_);
lean_ctor_set_uint64(v_reuseFailAlloc_1147_, sizeof(void*)*1, v_tid_1134_);
v___x_1141_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
lean_object* v___x_1143_; 
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 4, v___x_1141_);
v___x_1143_ = v___x_1132_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_env_1122_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_nextMacroScope_1123_);
lean_ctor_set(v_reuseFailAlloc_1146_, 2, v_ngen_1124_);
lean_ctor_set(v_reuseFailAlloc_1146_, 3, v_auxDeclNGen_1125_);
lean_ctor_set(v_reuseFailAlloc_1146_, 4, v___x_1141_);
lean_ctor_set(v_reuseFailAlloc_1146_, 5, v_cache_1126_);
lean_ctor_set(v_reuseFailAlloc_1146_, 6, v_recordedDeps_1127_);
lean_ctor_set(v_reuseFailAlloc_1146_, 7, v_messages_1128_);
lean_ctor_set(v_reuseFailAlloc_1146_, 8, v_infoState_1129_);
lean_ctor_set(v_reuseFailAlloc_1146_, 9, v_snapshotTasks_1130_);
v___x_1143_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = lean_st_ref_put(v___y_1088_, v___x_1143_);
v___x_1145_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(v_fst_1090_);
return v___x_1145_;
}
}
}
}
}
else
{
goto v___jp_1113_;
}
}
else
{
goto v___jp_1113_;
}
}
v___jp_1150_:
{
double v___x_1152_; double v___x_1153_; double v___x_1154_; uint8_t v___x_1155_; 
v___x_1152_ = lean_unbox_float(v_snd_1099_);
v___x_1153_ = lean_unbox_float(v_fst_1098_);
v___x_1154_ = lean_float_sub(v___x_1152_, v___x_1153_);
v___x_1155_ = lean_float_decLt(v___y_1151_, v___x_1154_);
v___y_1119_ = v___x_1155_;
goto v___jp_1118_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___boxed(lean_object* v_cls_1166_, lean_object* v_collapsed_1167_, lean_object* v_tag_1168_, lean_object* v_opts_1169_, lean_object* v_clsEnabled_1170_, lean_object* v_oldTraces_1171_, lean_object* v_msg_1172_, lean_object* v_resStartStop_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
uint8_t v_collapsed_boxed_1179_; uint8_t v_clsEnabled_boxed_1180_; lean_object* v_res_1181_; 
v_collapsed_boxed_1179_ = lean_unbox(v_collapsed_1167_);
v_clsEnabled_boxed_1180_ = lean_unbox(v_clsEnabled_1170_);
v_res_1181_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_1166_, v_collapsed_boxed_1179_, v_tag_1168_, v_opts_1169_, v_clsEnabled_boxed_1180_, v_oldTraces_1171_, v_msg_1172_, v_resStartStop_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec_ref(v_opts_1169_);
return v_res_1181_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3(void){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1184_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4(void){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1185_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3);
v___x_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
return v___x_1186_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1(void){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1187_ = lean_box(0);
v___x_1188_ = lean_unsigned_to_nat(16u);
v___x_1189_ = lean_mk_array(v___x_1188_, v___x_1187_);
return v___x_1189_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2(void){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1190_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1);
v___x_1191_ = lean_unsigned_to_nat(0u);
v___x_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
lean_ctor_set(v___x_1192_, 1, v___x_1190_);
return v___x_1192_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5(void){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; uint8_t v___x_1195_; lean_object* v___x_1196_; 
v___x_1193_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1194_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2);
v___x_1195_ = 1;
v___x_1196_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1196_, 0, v___x_1194_);
lean_ctor_set(v___x_1196_, 1, v___x_1193_);
lean_ctor_set_uint8(v___x_1196_, sizeof(void*)*2, v___x_1195_);
return v___x_1196_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7(void){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1197_ = lean_unsigned_to_nat(32u);
v___x_1198_ = lean_mk_empty_array_with_capacity(v___x_1197_);
v___x_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
return v___x_1199_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8(void){
_start:
{
size_t v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1200_ = ((size_t)5ULL);
v___x_1201_ = lean_unsigned_to_nat(0u);
v___x_1202_ = lean_unsigned_to_nat(32u);
v___x_1203_ = lean_mk_empty_array_with_capacity(v___x_1202_);
v___x_1204_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7);
v___x_1205_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1205_, 0, v___x_1204_);
lean_ctor_set(v___x_1205_, 1, v___x_1203_);
lean_ctor_set(v___x_1205_, 2, v___x_1201_);
lean_ctor_set(v___x_1205_, 3, v___x_1201_);
lean_ctor_set_usize(v___x_1205_, 4, v___x_1200_);
return v___x_1205_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9(void){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1206_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1207_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1208_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
lean_ctor_set(v___x_1208_, 1, v___x_1207_);
lean_ctor_set(v___x_1208_, 2, v___x_1207_);
lean_ctor_set(v___x_1208_, 3, v___x_1206_);
return v___x_1208_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6(void){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1209_ = lean_unsigned_to_nat(0u);
v___x_1210_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
lean_ctor_set(v___x_1211_, 1, v___x_1209_);
return v___x_1211_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10(void){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1212_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9);
v___x_1213_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6);
v___x_1214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
lean_ctor_set(v___x_1214_, 1, v___x_1212_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(lean_object* v_declName_1215_, lean_object* v_as_1216_, size_t v_i_1217_, size_t v_stop_1218_, lean_object* v_b_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
uint8_t v___x_1225_; 
v___x_1225_ = lean_usize_dec_eq(v_i_1217_, v_stop_1218_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = lean_array_uget_borrowed(v_as_1216_, v_i_1217_);
lean_inc(v___x_1226_);
lean_inc(v_declName_1215_);
v___x_1227_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1215_, v___x_1226_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v_a_1228_; size_t v___x_1229_; size_t v___x_1230_; 
v_a_1228_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_a_1228_);
lean_dec_ref_known(v___x_1227_, 1);
v___x_1229_ = ((size_t)1ULL);
v___x_1230_ = lean_usize_add(v_i_1217_, v___x_1229_);
v_i_1217_ = v___x_1230_;
v_b_1219_ = v_a_1228_;
goto _start;
}
else
{
lean_dec(v_declName_1215_);
return v___x_1227_;
}
}
else
{
lean_object* v___x_1232_; 
lean_dec(v_declName_1215_);
v___x_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1232_, 0, v_b_1219_);
return v___x_1232_;
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12(void){
_start:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1234_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__11));
v___x_1235_ = l_Lean_stringToMessageData(v___x_1234_);
return v___x_1235_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20(void){
_start:
{
lean_object* v_cls_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v_cls_1248_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17));
v___x_1249_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19));
v___x_1250_ = l_Lean_Name_append(v___x_1249_, v_cls_1248_);
return v___x_1250_;
}
}
static double _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21(void){
_start:
{
lean_object* v___x_1251_; double v___x_1252_; 
v___x_1251_ = lean_unsigned_to_nat(1000000000u);
v___x_1252_ = lean_float_of_nat(v___x_1251_);
return v___x_1252_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23(void){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1254_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__22));
v___x_1255_ = l_Lean_stringToMessageData(v___x_1254_);
return v___x_1255_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25(void){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__24));
v___x_1258_ = l_Lean_stringToMessageData(v___x_1257_);
return v___x_1258_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27(void){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__26));
v___x_1261_ = l_Lean_stringToMessageData(v___x_1260_);
return v___x_1261_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29(void){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__28));
v___x_1264_ = l_Lean_stringToMessageData(v___x_1263_);
return v___x_1264_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31(void){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__30));
v___x_1267_ = l_Lean_stringToMessageData(v___x_1266_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(lean_object* v_val_1268_, lean_object* v___x_1269_, lean_object* v_declName_1270_, lean_object* v_____r_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; 
v___x_1277_ = lean_array_get_size(v_val_1268_);
v___x_1278_ = lean_box(0);
v___x_1279_ = lean_nat_dec_lt(v___x_1269_, v___x_1277_);
if (v___x_1279_ == 0)
{
lean_object* v___x_1280_; 
lean_dec(v_declName_1270_);
v___x_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1278_);
return v___x_1280_;
}
else
{
uint8_t v___x_1281_; 
v___x_1281_ = lean_nat_dec_le(v___x_1277_, v___x_1277_);
if (v___x_1281_ == 0)
{
if (v___x_1279_ == 0)
{
lean_object* v___x_1282_; 
lean_dec(v_declName_1270_);
v___x_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1278_);
return v___x_1282_;
}
else
{
size_t v___x_1283_; size_t v___x_1284_; lean_object* v___x_1285_; 
v___x_1283_ = ((size_t)0ULL);
v___x_1284_ = lean_usize_of_nat(v___x_1277_);
v___x_1285_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1270_, v_val_1268_, v___x_1283_, v___x_1284_, v___x_1278_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
return v___x_1285_;
}
}
else
{
size_t v___x_1286_; size_t v___x_1287_; lean_object* v___x_1288_; 
v___x_1286_ = ((size_t)0ULL);
v___x_1287_ = lean_usize_of_nat(v___x_1277_);
v___x_1288_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1270_, v_val_1268_, v___x_1286_, v___x_1287_, v___x_1278_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
return v___x_1288_;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33(void){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__32));
v___x_1291_ = l_Lean_stringToMessageData(v___x_1290_);
return v___x_1291_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35(void){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__34));
v___x_1294_ = l_Lean_stringToMessageData(v___x_1293_);
return v___x_1294_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__36));
v___x_1297_ = l_Lean_stringToMessageData(v___x_1296_);
return v___x_1297_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38));
v___x_1300_ = l_Lean_stringToMessageData(v___x_1299_);
return v___x_1300_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41(void){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__40));
v___x_1303_ = l_Lean_stringToMessageData(v___x_1302_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(lean_object* v_declName_1304_, lean_object* v_mvarId_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_){
_start:
{
lean_object* v_toCold_1317_; lean_object* v_options_1318_; uint8_t v_hasTrace_1319_; 
v_toCold_1317_ = lean_ctor_get(v_a_1308_, 0);
v_options_1318_ = lean_ctor_get(v_toCold_1317_, 2);
v_hasTrace_1319_ = lean_ctor_get_uint8(v_options_1318_, sizeof(void*)*1);
if (v_hasTrace_1319_ == 0)
{
lean_object* v___x_1320_; 
lean_inc(v_mvarId_1305_);
v___x_1320_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1504_; 
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1323_ = v___x_1320_;
v_isShared_1324_ = v_isSharedCheck_1504_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1320_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1504_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
uint8_t v___x_1325_; 
v___x_1325_ = lean_unbox(v_a_1321_);
lean_dec(v_a_1321_);
if (v___x_1325_ == 0)
{
uint8_t v___x_1326_; lean_object* v___x_1327_; 
lean_del_object(v___x_1323_);
v___x_1326_ = 1;
lean_inc(v_mvarId_1305_);
v___x_1327_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1491_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1330_ = v___x_1327_;
v_isShared_1331_ = v_isSharedCheck_1491_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1327_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1491_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
uint8_t v___x_1332_; 
v___x_1332_ = lean_unbox(v_a_1328_);
if (v___x_1332_ == 0)
{
lean_object* v___x_1333_; 
lean_del_object(v___x_1330_);
lean_inc(v_mvarId_1305_);
v___x_1333_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v_a_1334_; 
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
lean_inc(v_a_1334_);
lean_dec_ref_known(v___x_1333_, 1);
if (lean_obj_tag(v_a_1334_) == 1)
{
lean_object* v_val_1335_; 
lean_dec(v_a_1328_);
lean_dec(v_mvarId_1305_);
v_val_1335_ = lean_ctor_get(v_a_1334_, 0);
lean_inc(v_val_1335_);
lean_dec_ref_known(v_a_1334_, 1);
v_mvarId_1305_ = v_val_1335_;
goto _start;
}
else
{
lean_object* v___x_1337_; 
lean_dec(v_a_1334_);
lean_inc(v_mvarId_1305_);
v___x_1337_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_a_1338_; 
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_a_1338_);
lean_dec_ref_known(v___x_1337_, 1);
if (lean_obj_tag(v_a_1338_) == 1)
{
lean_object* v_val_1339_; 
lean_dec(v_a_1328_);
lean_dec(v_mvarId_1305_);
v_val_1339_ = lean_ctor_get(v_a_1338_, 0);
lean_inc(v_val_1339_);
lean_dec_ref_known(v_a_1338_, 1);
v_mvarId_1305_ = v_val_1339_;
goto _start;
}
else
{
lean_object* v___x_1341_; 
lean_dec(v_a_1338_);
lean_inc(v_mvarId_1305_);
v___x_1341_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1305_, v___x_1326_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_a_1342_; 
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_a_1342_);
lean_dec_ref_known(v___x_1341_, 1);
if (lean_obj_tag(v_a_1342_) == 1)
{
lean_object* v_val_1343_; 
lean_dec(v_a_1328_);
lean_dec(v_mvarId_1305_);
v_val_1343_ = lean_ctor_get(v_a_1342_, 0);
lean_inc(v_val_1343_);
lean_dec_ref_known(v_a_1342_, 1);
v_mvarId_1305_ = v_val_1343_;
goto _start;
}
else
{
lean_object* v___x_1345_; lean_object* v___x_1346_; uint8_t v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; uint8_t v___x_1350_; uint8_t v___x_1351_; uint8_t v___x_1352_; uint8_t v___x_1353_; uint8_t v___x_1354_; uint8_t v___x_1355_; uint8_t v___x_1356_; uint8_t v___x_1357_; uint8_t v___x_1358_; uint8_t v___x_1359_; uint8_t v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
lean_dec(v_a_1342_);
v___x_1345_ = lean_unsigned_to_nat(100000u);
v___x_1346_ = lean_unsigned_to_nat(2u);
v___x_1347_ = 0;
v___x_1348_ = lean_box(0);
v___x_1349_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1349_, 0, v___x_1345_);
lean_ctor_set(v___x_1349_, 1, v___x_1346_);
lean_ctor_set(v___x_1349_, 2, v___x_1348_);
v___x_1350_ = lean_unbox(v_a_1328_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*3, v___x_1350_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*3 + 1, v___x_1326_);
v___x_1351_ = lean_unbox(v_a_1328_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*3 + 2, v___x_1351_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*3 + 3, v___x_1326_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*3 + 4, v___x_1326_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*3 + 5, v___x_1326_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*3 + 6, v___x_1347_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*3 + 7, v___x_1326_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*3 + 8, v___x_1326_);
v___x_1352_ = lean_unbox(v_a_1328_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*3 + 9, v___x_1352_);
v___x_1353_ = lean_unbox(v_a_1328_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*3 + 10, v___x_1353_);
v___x_1354_ = lean_unbox(v_a_1328_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*3 + 11, v___x_1354_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*3 + 12, v___x_1326_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*3 + 13, v___x_1326_);
v___x_1355_ = lean_unbox(v_a_1328_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*3 + 14, v___x_1355_);
v___x_1356_ = lean_unbox(v_a_1328_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*3 + 15, v___x_1356_);
v___x_1357_ = lean_unbox(v_a_1328_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*3 + 16, v___x_1357_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*3 + 17, v___x_1326_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*3 + 18, v___x_1326_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*3 + 19, v___x_1326_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*3 + 20, v___x_1326_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*3 + 21, v___x_1326_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*3 + 22, v___x_1326_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*3 + 23, v___x_1326_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*3 + 24, v___x_1326_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*3 + 25, v___x_1326_);
v___x_1358_ = lean_unbox(v_a_1328_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*3 + 26, v___x_1358_);
v___x_1359_ = lean_unbox(v_a_1328_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*3 + 27, v___x_1359_);
v___x_1360_ = lean_unbox(v_a_1328_);
lean_dec(v_a_1328_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*3 + 28, v___x_1360_);
v___x_1361_ = lean_unsigned_to_nat(0u);
v___x_1362_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0));
v___x_1363_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5);
v___x_1364_ = l_Lean_Options_empty;
v___x_1365_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1349_, v___x_1362_, v___x_1363_, v___x_1364_, v_a_1306_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_a_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_a_1366_);
lean_dec_ref_known(v___x_1365_, 1);
v___x_1367_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
lean_inc(v_mvarId_1305_);
v___x_1368_ = l_Lean_Meta_simpTargetStar(v_mvarId_1305_, v_a_1366_, v___x_1362_, v___x_1348_, v___x_1367_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1446_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1371_ = v___x_1368_;
v_isShared_1372_ = v_isSharedCheck_1446_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1368_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1446_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v_fst_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1444_; 
v_fst_1373_ = lean_ctor_get(v_a_1369_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v_a_1369_);
if (v_isSharedCheck_1444_ == 0)
{
lean_object* v_unused_1445_; 
v_unused_1445_ = lean_ctor_get(v_a_1369_, 1);
lean_dec(v_unused_1445_);
v___x_1375_ = v_a_1369_;
v_isShared_1376_ = v_isSharedCheck_1444_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_fst_1373_);
lean_dec(v_a_1369_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1444_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
switch(lean_obj_tag(v_fst_1373_))
{
case 0:
{
lean_object* v___x_1377_; lean_object* v___x_1379_; 
lean_del_object(v___x_1375_);
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v___x_1377_ = lean_box(0);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v___x_1377_);
v___x_1379_ = v___x_1371_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1377_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
case 1:
{
lean_object* v___x_1381_; 
lean_del_object(v___x_1371_);
lean_inc(v_declName_1304_);
lean_inc(v_mvarId_1305_);
v___x_1381_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1305_, v_declName_1304_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_a_1382_);
lean_dec_ref_known(v___x_1381_, 1);
if (lean_obj_tag(v_a_1382_) == 1)
{
lean_object* v_val_1383_; 
lean_del_object(v___x_1375_);
lean_dec(v_mvarId_1305_);
v_val_1383_ = lean_ctor_get(v_a_1382_, 0);
lean_inc(v_val_1383_);
lean_dec_ref_known(v_a_1382_, 1);
v_mvarId_1305_ = v_val_1383_;
goto _start;
}
else
{
lean_object* v___x_1385_; 
lean_dec(v_a_1382_);
lean_inc(v_mvarId_1305_);
v___x_1385_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1425_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1388_ = v___x_1385_;
v_isShared_1389_ = v_isSharedCheck_1425_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1385_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1425_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
if (lean_obj_tag(v_a_1386_) == 1)
{
lean_object* v_val_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; uint8_t v___x_1393_; 
lean_del_object(v___x_1375_);
lean_dec(v_mvarId_1305_);
v_val_1390_ = lean_ctor_get(v_a_1386_, 0);
lean_inc(v_val_1390_);
lean_dec_ref_known(v_a_1386_, 1);
v___x_1391_ = lean_array_get_size(v_val_1390_);
v___x_1392_ = lean_box(0);
v___x_1393_ = lean_nat_dec_lt(v___x_1361_, v___x_1391_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1395_; 
lean_dec(v_val_1390_);
lean_dec(v_declName_1304_);
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 0, v___x_1392_);
v___x_1395_ = v___x_1388_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1392_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
else
{
uint8_t v___x_1397_; 
v___x_1397_ = lean_nat_dec_le(v___x_1391_, v___x_1391_);
if (v___x_1397_ == 0)
{
if (v___x_1393_ == 0)
{
lean_object* v___x_1399_; 
lean_dec(v_val_1390_);
lean_dec(v_declName_1304_);
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 0, v___x_1392_);
v___x_1399_ = v___x_1388_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1392_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
else
{
size_t v___x_1401_; size_t v___x_1402_; lean_object* v___x_1403_; 
lean_del_object(v___x_1388_);
v___x_1401_ = ((size_t)0ULL);
v___x_1402_ = lean_usize_of_nat(v___x_1391_);
v___x_1403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1304_, v_val_1390_, v___x_1401_, v___x_1402_, v___x_1392_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
lean_dec(v_val_1390_);
return v___x_1403_;
}
}
else
{
size_t v___x_1404_; size_t v___x_1405_; lean_object* v___x_1406_; 
lean_del_object(v___x_1388_);
v___x_1404_ = ((size_t)0ULL);
v___x_1405_ = lean_usize_of_nat(v___x_1391_);
v___x_1406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1304_, v_val_1390_, v___x_1404_, v___x_1405_, v___x_1392_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
lean_dec(v_val_1390_);
return v___x_1406_;
}
}
}
else
{
lean_object* v___x_1407_; 
lean_del_object(v___x_1388_);
lean_dec(v_a_1386_);
lean_inc(v_mvarId_1305_);
v___x_1407_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1305_, v___x_1326_, v___x_1326_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v_a_1408_; 
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_a_1408_);
lean_dec_ref_known(v___x_1407_, 1);
if (lean_obj_tag(v_a_1408_) == 1)
{
lean_object* v_val_1409_; lean_object* v___x_1410_; 
lean_del_object(v___x_1375_);
lean_dec(v_mvarId_1305_);
v_val_1409_ = lean_ctor_get(v_a_1408_, 0);
lean_inc(v_val_1409_);
lean_dec_ref_known(v_a_1408_, 1);
v___x_1410_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1304_, v_val_1409_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
return v___x_1410_;
}
else
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1414_; 
lean_dec(v_a_1408_);
lean_dec(v_declName_1304_);
v___x_1411_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
v___x_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1412_, 0, v_mvarId_1305_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set_tag(v___x_1375_, 7);
lean_ctor_set(v___x_1375_, 1, v___x_1412_);
lean_ctor_set(v___x_1375_, 0, v___x_1411_);
v___x_1414_ = v___x_1375_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1411_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
lean_object* v___x_1415_; 
v___x_1415_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1414_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
return v___x_1415_;
}
}
}
else
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1424_; 
lean_del_object(v___x_1375_);
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_1417_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1419_ = v___x_1407_;
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1407_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1422_; 
if (v_isShared_1420_ == 0)
{
v___x_1422_ = v___x_1419_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1417_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
}
}
else
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1433_; 
lean_del_object(v___x_1375_);
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_1426_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1428_ = v___x_1385_;
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1385_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1431_; 
if (v_isShared_1429_ == 0)
{
v___x_1431_ = v___x_1428_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_a_1426_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
}
else
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
lean_del_object(v___x_1375_);
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_1434_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1436_ = v___x_1381_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1381_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_a_1434_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
default: 
{
lean_object* v_mvarId_1442_; 
lean_del_object(v___x_1375_);
lean_del_object(v___x_1371_);
lean_dec(v_mvarId_1305_);
v_mvarId_1442_ = lean_ctor_get(v_fst_1373_, 0);
lean_inc(v_mvarId_1442_);
lean_dec_ref_known(v_fst_1373_, 1);
v_mvarId_1305_ = v_mvarId_1442_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_1447_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1368_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1368_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
else
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1462_; 
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_1455_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1457_ = v___x_1365_;
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1365_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1460_; 
if (v_isShared_1458_ == 0)
{
v___x_1460_ = v___x_1457_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_a_1455_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
}
else
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
lean_dec(v_a_1328_);
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_1463_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1341_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1341_);
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
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
lean_dec(v_a_1328_);
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_1471_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1337_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1337_);
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
lean_dec(v_a_1328_);
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_1479_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v___x_1333_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1333_);
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
else
{
lean_object* v___x_1487_; lean_object* v___x_1489_; 
lean_dec(v_a_1328_);
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v___x_1487_ = lean_box(0);
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 0, v___x_1487_);
v___x_1489_ = v___x_1330_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1487_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
else
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_1492_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___x_1327_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1327_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1492_);
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
lean_object* v___x_1500_; lean_object* v___x_1502_; 
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v___x_1500_ = lean_box(0);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v___x_1500_);
v___x_1502_ = v___x_1323_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1500_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
}
else
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1512_; 
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_1505_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1507_ = v___x_1320_;
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1320_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1505_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_1513_; lean_object* v___f_1514_; lean_object* v_cls_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; uint8_t v___x_1518_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v_a_1522_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v_a_1534_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v_a_1539_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v_a_1550_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v_a_1565_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v_a_1570_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; 
v_inheritedTraceOptions_1513_ = lean_ctor_get(v_toCold_1317_, 11);
lean_inc(v_mvarId_1305_);
v___f_1514_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1514_, 0, v_mvarId_1305_);
v_cls_1515_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17));
v___x_1516_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__1));
v___x_1517_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20);
v___x_1518_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1513_, v_options_1318_, v___x_1517_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1857_; uint8_t v___x_1858_; 
v___x_1857_ = l_Lean_trace_profiler;
v___x_1858_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_1318_, v___x_1857_);
if (v___x_1858_ == 0)
{
lean_object* v___x_1859_; 
lean_dec_ref(v___f_1514_);
lean_inc(v_mvarId_1305_);
v___x_1859_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_a_1860_; uint8_t v___x_1861_; 
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
lean_inc(v_a_1860_);
lean_dec_ref_known(v___x_1859_, 1);
v___x_1861_ = lean_unbox(v_a_1860_);
lean_dec(v_a_1860_);
if (v___x_1861_ == 0)
{
lean_object* v___x_1862_; 
lean_inc(v_mvarId_1305_);
v___x_1862_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v_a_1863_; uint8_t v___x_1864_; 
v_a_1863_ = lean_ctor_get(v___x_1862_, 0);
lean_inc(v_a_1863_);
lean_dec_ref_known(v___x_1862_, 1);
v___x_1864_ = lean_unbox(v_a_1863_);
if (v___x_1864_ == 0)
{
lean_object* v___x_1865_; 
lean_inc(v_mvarId_1305_);
v___x_1865_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v_a_1866_; 
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc(v_a_1866_);
lean_dec_ref_known(v___x_1865_, 1);
if (lean_obj_tag(v_a_1866_) == 1)
{
lean_dec(v_a_1863_);
lean_dec(v_mvarId_1305_);
if (v___x_1518_ == 0)
{
lean_object* v_val_1867_; 
v_val_1867_ = lean_ctor_get(v_a_1866_, 0);
lean_inc(v_val_1867_);
lean_dec_ref_known(v_a_1866_, 1);
v_mvarId_1305_ = v_val_1867_;
goto _start;
}
else
{
lean_object* v_val_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
v_val_1869_ = lean_ctor_get(v_a_1866_, 0);
lean_inc(v_val_1869_);
lean_dec_ref_known(v_a_1866_, 1);
v___x_1870_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23);
v___x_1871_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1515_, v___x_1870_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_dec_ref_known(v___x_1871_, 1);
v_mvarId_1305_ = v_val_1869_;
goto _start;
}
else
{
lean_dec(v_val_1869_);
lean_dec(v_declName_1304_);
return v___x_1871_;
}
}
}
else
{
lean_object* v___x_1873_; 
lean_dec(v_a_1866_);
lean_inc(v_mvarId_1305_);
v___x_1873_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1874_; 
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
lean_inc(v_a_1874_);
lean_dec_ref_known(v___x_1873_, 1);
if (lean_obj_tag(v_a_1874_) == 1)
{
lean_dec(v_a_1863_);
lean_dec(v_mvarId_1305_);
if (v___x_1518_ == 0)
{
lean_object* v_val_1875_; 
v_val_1875_ = lean_ctor_get(v_a_1874_, 0);
lean_inc(v_val_1875_);
lean_dec_ref_known(v_a_1874_, 1);
v_mvarId_1305_ = v_val_1875_;
goto _start;
}
else
{
lean_object* v_val_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v_val_1877_ = lean_ctor_get(v_a_1874_, 0);
lean_inc(v_val_1877_);
lean_dec_ref_known(v_a_1874_, 1);
v___x_1878_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25);
v___x_1879_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1515_, v___x_1878_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_dec_ref_known(v___x_1879_, 1);
v_mvarId_1305_ = v_val_1877_;
goto _start;
}
else
{
lean_dec(v_val_1877_);
lean_dec(v_declName_1304_);
return v___x_1879_;
}
}
}
else
{
lean_object* v___x_1881_; 
lean_dec(v_a_1874_);
lean_inc(v_mvarId_1305_);
v___x_1881_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1305_, v_hasTrace_1319_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_a_1882_; 
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
lean_inc(v_a_1882_);
lean_dec_ref_known(v___x_1881_, 1);
if (lean_obj_tag(v_a_1882_) == 1)
{
lean_dec(v_a_1863_);
lean_dec(v_mvarId_1305_);
if (v___x_1518_ == 0)
{
lean_object* v_val_1883_; 
v_val_1883_ = lean_ctor_get(v_a_1882_, 0);
lean_inc(v_val_1883_);
lean_dec_ref_known(v_a_1882_, 1);
v_mvarId_1305_ = v_val_1883_;
goto _start;
}
else
{
lean_object* v_val_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
v_val_1885_ = lean_ctor_get(v_a_1882_, 0);
lean_inc(v_val_1885_);
lean_dec_ref_known(v_a_1882_, 1);
v___x_1886_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27);
v___x_1887_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1515_, v___x_1886_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_dec_ref_known(v___x_1887_, 1);
v_mvarId_1305_ = v_val_1885_;
goto _start;
}
else
{
lean_dec(v_val_1885_);
lean_dec(v_declName_1304_);
return v___x_1887_;
}
}
}
else
{
lean_object* v___x_1889_; lean_object* v___x_1890_; uint8_t v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; uint8_t v___x_1894_; uint8_t v___x_1895_; uint8_t v___x_1896_; uint8_t v___x_1897_; uint8_t v___x_1898_; uint8_t v___x_1899_; uint8_t v___x_1900_; uint8_t v___x_1901_; uint8_t v___x_1902_; uint8_t v___x_1903_; uint8_t v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
lean_dec(v_a_1882_);
v___x_1889_ = lean_unsigned_to_nat(100000u);
v___x_1890_ = lean_unsigned_to_nat(2u);
v___x_1891_ = 0;
v___x_1892_ = lean_box(0);
v___x_1893_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1893_, 0, v___x_1889_);
lean_ctor_set(v___x_1893_, 1, v___x_1890_);
lean_ctor_set(v___x_1893_, 2, v___x_1892_);
v___x_1894_ = lean_unbox(v_a_1863_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*3, v___x_1894_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*3 + 1, v_hasTrace_1319_);
v___x_1895_ = lean_unbox(v_a_1863_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*3 + 2, v___x_1895_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*3 + 3, v_hasTrace_1319_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*3 + 4, v_hasTrace_1319_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*3 + 5, v_hasTrace_1319_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*3 + 6, v___x_1891_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*3 + 7, v_hasTrace_1319_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*3 + 8, v_hasTrace_1319_);
v___x_1896_ = lean_unbox(v_a_1863_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*3 + 9, v___x_1896_);
v___x_1897_ = lean_unbox(v_a_1863_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*3 + 10, v___x_1897_);
v___x_1898_ = lean_unbox(v_a_1863_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*3 + 11, v___x_1898_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*3 + 12, v_hasTrace_1319_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*3 + 13, v_hasTrace_1319_);
v___x_1899_ = lean_unbox(v_a_1863_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*3 + 14, v___x_1899_);
v___x_1900_ = lean_unbox(v_a_1863_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*3 + 15, v___x_1900_);
v___x_1901_ = lean_unbox(v_a_1863_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*3 + 16, v___x_1901_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*3 + 17, v_hasTrace_1319_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*3 + 18, v_hasTrace_1319_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*3 + 19, v_hasTrace_1319_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*3 + 20, v_hasTrace_1319_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*3 + 21, v_hasTrace_1319_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*3 + 22, v_hasTrace_1319_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*3 + 23, v_hasTrace_1319_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*3 + 24, v_hasTrace_1319_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*3 + 25, v_hasTrace_1319_);
v___x_1902_ = lean_unbox(v_a_1863_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*3 + 26, v___x_1902_);
v___x_1903_ = lean_unbox(v_a_1863_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*3 + 27, v___x_1903_);
v___x_1904_ = lean_unbox(v_a_1863_);
lean_dec(v_a_1863_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*3 + 28, v___x_1904_);
v___x_1905_ = lean_unsigned_to_nat(0u);
v___x_1906_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0));
v___x_1907_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2);
v___x_1908_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1909_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1909_, 0, v___x_1907_);
lean_ctor_set(v___x_1909_, 1, v___x_1908_);
lean_ctor_set_uint8(v___x_1909_, sizeof(void*)*2, v_hasTrace_1319_);
v___x_1910_ = l_Lean_Options_empty;
v___x_1911_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1893_, v___x_1906_, v___x_1909_, v___x_1910_, v_a_1306_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1912_);
lean_dec_ref_known(v___x_1911_, 1);
v___x_1913_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
lean_inc(v_mvarId_1305_);
v___x_1914_ = l_Lean_Meta_simpTargetStar(v_mvarId_1305_, v_a_1912_, v___x_1906_, v___x_1892_, v___x_1913_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_2013_; 
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_1917_ = v___x_1914_;
v_isShared_1918_ = v_isSharedCheck_2013_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1914_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_2013_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v_fst_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_2011_; 
v_fst_1919_ = lean_ctor_get(v_a_1915_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v_a_1915_);
if (v_isSharedCheck_2011_ == 0)
{
lean_object* v_unused_2012_; 
v_unused_2012_ = lean_ctor_get(v_a_1915_, 1);
lean_dec(v_unused_2012_);
v___x_1921_ = v_a_1915_;
v_isShared_1922_ = v_isSharedCheck_2011_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_fst_1919_);
lean_dec(v_a_1915_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_2011_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
switch(lean_obj_tag(v_fst_1919_))
{
case 0:
{
lean_del_object(v___x_1921_);
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1923_; lean_object* v___x_1925_; 
v___x_1923_ = lean_box(0);
if (v_isShared_1918_ == 0)
{
lean_ctor_set(v___x_1917_, 0, v___x_1923_);
v___x_1925_ = v___x_1917_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1923_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
else
{
lean_object* v___x_1927_; lean_object* v___x_1928_; 
lean_del_object(v___x_1917_);
v___x_1927_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29);
v___x_1928_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1515_, v___x_1927_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
return v___x_1928_;
}
}
case 1:
{
lean_object* v___x_1929_; 
lean_del_object(v___x_1917_);
lean_inc(v_declName_1304_);
lean_inc(v_mvarId_1305_);
v___x_1929_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1305_, v_declName_1304_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_a_1930_);
lean_dec_ref_known(v___x_1929_, 1);
if (lean_obj_tag(v_a_1930_) == 1)
{
lean_del_object(v___x_1921_);
lean_dec(v_mvarId_1305_);
if (v___x_1518_ == 0)
{
lean_object* v_val_1931_; 
v_val_1931_ = lean_ctor_get(v_a_1930_, 0);
lean_inc(v_val_1931_);
lean_dec_ref_known(v_a_1930_, 1);
v_mvarId_1305_ = v_val_1931_;
goto _start;
}
else
{
lean_object* v_val_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v_val_1933_ = lean_ctor_get(v_a_1930_, 0);
lean_inc(v_val_1933_);
lean_dec_ref_known(v_a_1930_, 1);
v___x_1934_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31);
v___x_1935_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1515_, v___x_1934_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_dec_ref_known(v___x_1935_, 1);
v_mvarId_1305_ = v_val_1933_;
goto _start;
}
else
{
lean_dec(v_val_1933_);
lean_dec(v_declName_1304_);
return v___x_1935_;
}
}
}
else
{
lean_object* v___x_1937_; 
lean_dec(v_a_1930_);
lean_inc(v_mvarId_1305_);
v___x_1937_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1988_; 
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1940_ = v___x_1937_;
v_isShared_1941_ = v_isSharedCheck_1988_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1937_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1988_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
if (lean_obj_tag(v_a_1938_) == 1)
{
lean_object* v_val_1942_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; 
lean_del_object(v___x_1921_);
lean_dec(v_mvarId_1305_);
v_val_1942_ = lean_ctor_get(v_a_1938_, 0);
lean_inc(v_val_1942_);
lean_dec_ref_known(v_a_1938_, 1);
if (v___x_1518_ == 0)
{
v___y_1944_ = v_a_1306_;
v___y_1945_ = v_a_1307_;
v___y_1946_ = v_a_1308_;
v___y_1947_ = v_a_1309_;
goto v___jp_1943_;
}
else
{
lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1964_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33);
v___x_1965_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1515_, v___x_1964_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_dec_ref_known(v___x_1965_, 1);
v___y_1944_ = v_a_1306_;
v___y_1945_ = v_a_1307_;
v___y_1946_ = v_a_1308_;
v___y_1947_ = v_a_1309_;
goto v___jp_1943_;
}
else
{
lean_dec(v_val_1942_);
lean_del_object(v___x_1940_);
lean_dec(v_declName_1304_);
return v___x_1965_;
}
}
v___jp_1943_:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; uint8_t v___x_1950_; 
v___x_1948_ = lean_array_get_size(v_val_1942_);
v___x_1949_ = lean_box(0);
v___x_1950_ = lean_nat_dec_lt(v___x_1905_, v___x_1948_);
if (v___x_1950_ == 0)
{
lean_object* v___x_1952_; 
lean_dec(v_val_1942_);
lean_dec(v_declName_1304_);
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 0, v___x_1949_);
v___x_1952_ = v___x_1940_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v___x_1949_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
else
{
uint8_t v___x_1954_; 
v___x_1954_ = lean_nat_dec_le(v___x_1948_, v___x_1948_);
if (v___x_1954_ == 0)
{
if (v___x_1950_ == 0)
{
lean_object* v___x_1956_; 
lean_dec(v_val_1942_);
lean_dec(v_declName_1304_);
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 0, v___x_1949_);
v___x_1956_ = v___x_1940_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v___x_1949_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
else
{
size_t v___x_1958_; size_t v___x_1959_; lean_object* v___x_1960_; 
lean_del_object(v___x_1940_);
v___x_1958_ = ((size_t)0ULL);
v___x_1959_ = lean_usize_of_nat(v___x_1948_);
v___x_1960_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1304_, v_val_1942_, v___x_1958_, v___x_1959_, v___x_1949_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
lean_dec(v_val_1942_);
return v___x_1960_;
}
}
else
{
size_t v___x_1961_; size_t v___x_1962_; lean_object* v___x_1963_; 
lean_del_object(v___x_1940_);
v___x_1961_ = ((size_t)0ULL);
v___x_1962_ = lean_usize_of_nat(v___x_1948_);
v___x_1963_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1304_, v_val_1942_, v___x_1961_, v___x_1962_, v___x_1949_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
lean_dec(v_val_1942_);
return v___x_1963_;
}
}
}
}
else
{
lean_object* v___x_1966_; 
lean_del_object(v___x_1940_);
lean_dec(v_a_1938_);
lean_inc(v_mvarId_1305_);
v___x_1966_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1305_, v_hasTrace_1319_, v_hasTrace_1319_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc(v_a_1967_);
lean_dec_ref_known(v___x_1966_, 1);
if (lean_obj_tag(v_a_1967_) == 1)
{
lean_del_object(v___x_1921_);
lean_dec(v_mvarId_1305_);
if (v___x_1518_ == 0)
{
lean_object* v_val_1968_; lean_object* v___x_1969_; 
v_val_1968_ = lean_ctor_get(v_a_1967_, 0);
lean_inc(v_val_1968_);
lean_dec_ref_known(v_a_1967_, 1);
v___x_1969_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1304_, v_val_1968_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
return v___x_1969_;
}
else
{
lean_object* v_val_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v_val_1970_ = lean_ctor_get(v_a_1967_, 0);
lean_inc(v_val_1970_);
lean_dec_ref_known(v_a_1967_, 1);
v___x_1971_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35);
v___x_1972_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1515_, v___x_1971_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v___x_1973_; 
lean_dec_ref_known(v___x_1972_, 1);
v___x_1973_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1304_, v_val_1970_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
return v___x_1973_;
}
else
{
lean_dec(v_val_1970_);
lean_dec(v_declName_1304_);
return v___x_1972_;
}
}
}
else
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1977_; 
lean_dec(v_a_1967_);
lean_dec(v_declName_1304_);
v___x_1974_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
v___x_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1975_, 0, v_mvarId_1305_);
if (v_isShared_1922_ == 0)
{
lean_ctor_set_tag(v___x_1921_, 7);
lean_ctor_set(v___x_1921_, 1, v___x_1975_);
lean_ctor_set(v___x_1921_, 0, v___x_1974_);
v___x_1977_ = v___x_1921_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1974_);
lean_ctor_set(v_reuseFailAlloc_1979_, 1, v___x_1975_);
v___x_1977_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
lean_object* v___x_1978_; 
v___x_1978_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1977_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
return v___x_1978_;
}
}
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
lean_del_object(v___x_1921_);
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_1980_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1966_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1966_);
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
}
else
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_1996_; 
lean_del_object(v___x_1921_);
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_1989_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1991_ = v___x_1937_;
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1937_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1994_; 
if (v_isShared_1992_ == 0)
{
v___x_1994_ = v___x_1991_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_a_1989_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
}
}
else
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2004_; 
lean_del_object(v___x_1921_);
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_1997_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1999_ = v___x_1929_;
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1929_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
if (v_isShared_2000_ == 0)
{
v___x_2002_ = v___x_1999_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_a_1997_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
default: 
{
lean_del_object(v___x_1921_);
lean_del_object(v___x_1917_);
lean_dec(v_mvarId_1305_);
if (v___x_1518_ == 0)
{
lean_object* v_mvarId_2005_; 
v_mvarId_2005_ = lean_ctor_get(v_fst_1919_, 0);
lean_inc(v_mvarId_2005_);
lean_dec_ref_known(v_fst_1919_, 1);
v_mvarId_1305_ = v_mvarId_2005_;
goto _start;
}
else
{
lean_object* v_mvarId_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v_mvarId_2007_ = lean_ctor_get(v_fst_1919_, 0);
lean_inc(v_mvarId_2007_);
lean_dec_ref_known(v_fst_1919_, 1);
v___x_2008_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37);
v___x_2009_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1515_, v___x_2008_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_dec_ref_known(v___x_2009_, 1);
v_mvarId_1305_ = v_mvarId_2007_;
goto _start;
}
else
{
lean_dec(v_mvarId_2007_);
lean_dec(v_declName_1304_);
return v___x_2009_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2021_; 
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_2014_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2016_ = v___x_1914_;
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_a_2014_);
lean_dec(v___x_1914_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2019_; 
if (v_isShared_2017_ == 0)
{
v___x_2019_ = v___x_2016_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_a_2014_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
}
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_2022_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2024_ = v___x_1911_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_1911_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2025_ == 0)
{
v___x_2027_ = v___x_2024_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_a_2022_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
}
else
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
lean_dec(v_a_1863_);
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_2030_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2032_ = v___x_1881_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_1881_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2030_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
}
}
else
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_dec(v_a_1863_);
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_2038_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_1873_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_1873_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
}
else
{
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2053_; 
lean_dec(v_a_1863_);
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_2046_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2048_ = v___x_1865_;
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_1865_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2051_; 
if (v_isShared_2049_ == 0)
{
v___x_2051_ = v___x_2048_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_a_2046_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
}
else
{
lean_dec(v_a_1863_);
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
if (v___x_1518_ == 0)
{
goto v___jp_1314_;
}
else
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2054_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39);
v___x_2055_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1515_, v___x_2054_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_dec_ref_known(v___x_2055_, 1);
goto v___jp_1314_;
}
else
{
return v___x_2055_;
}
}
}
}
else
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_2056_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2058_ = v___x_1862_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_1862_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
if (v_isShared_2059_ == 0)
{
v___x_2061_ = v___x_2058_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2056_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
else
{
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
if (v___x_1518_ == 0)
{
goto v___jp_1311_;
}
else
{
lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2064_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41);
v___x_2065_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1515_, v___x_2064_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_dec_ref_known(v___x_2065_, 1);
goto v___jp_1311_;
}
else
{
return v___x_2065_;
}
}
}
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_2066_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_1859_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_1859_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
else
{
goto v___jp_1578_;
}
}
else
{
goto v___jp_1578_;
}
v___jp_1519_:
{
lean_object* v___x_1523_; double v___x_1524_; double v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1523_ = lean_io_get_num_heartbeats();
v___x_1524_ = lean_float_of_nat(v___y_1521_);
v___x_1525_ = lean_float_of_nat(v___x_1523_);
v___x_1526_ = lean_box_float(v___x_1524_);
v___x_1527_ = lean_box_float(v___x_1525_);
v___x_1528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1526_);
lean_ctor_set(v___x_1528_, 1, v___x_1527_);
v___x_1529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1529_, 0, v_a_1522_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
v___x_1530_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_1515_, v_hasTrace_1319_, v___x_1516_, v_options_1318_, v___x_1518_, v___y_1520_, v___f_1514_, v___x_1529_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
return v___x_1530_;
}
v___jp_1531_:
{
lean_object* v___x_1535_; 
v___x_1535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1535_, 0, v_a_1534_);
v___y_1520_ = v___y_1532_;
v___y_1521_ = v___y_1533_;
v_a_1522_ = v___x_1535_;
goto v___jp_1519_;
}
v___jp_1536_:
{
lean_object* v___x_1540_; 
v___x_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1540_, 0, v_a_1539_);
v___y_1520_ = v___y_1537_;
v___y_1521_ = v___y_1538_;
v_a_1522_ = v___x_1540_;
goto v___jp_1519_;
}
v___jp_1541_:
{
if (lean_obj_tag(v___y_1544_) == 0)
{
lean_object* v_a_1545_; 
v_a_1545_ = lean_ctor_get(v___y_1544_, 0);
lean_inc(v_a_1545_);
lean_dec_ref_known(v___y_1544_, 1);
v___y_1537_ = v___y_1542_;
v___y_1538_ = v___y_1543_;
v_a_1539_ = v_a_1545_;
goto v___jp_1536_;
}
else
{
lean_object* v_a_1546_; 
v_a_1546_ = lean_ctor_get(v___y_1544_, 0);
lean_inc(v_a_1546_);
lean_dec_ref_known(v___y_1544_, 1);
v___y_1532_ = v___y_1542_;
v___y_1533_ = v___y_1543_;
v_a_1534_ = v_a_1546_;
goto v___jp_1531_;
}
}
v___jp_1547_:
{
lean_object* v___x_1551_; double v___x_1552_; double v___x_1553_; double v___x_1554_; double v___x_1555_; double v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1551_ = lean_io_mono_nanos_now();
v___x_1552_ = lean_float_of_nat(v___y_1548_);
v___x_1553_ = lean_float_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21);
v___x_1554_ = lean_float_div(v___x_1552_, v___x_1553_);
v___x_1555_ = lean_float_of_nat(v___x_1551_);
v___x_1556_ = lean_float_div(v___x_1555_, v___x_1553_);
v___x_1557_ = lean_box_float(v___x_1554_);
v___x_1558_ = lean_box_float(v___x_1556_);
v___x_1559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1557_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
v___x_1560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1560_, 0, v_a_1550_);
lean_ctor_set(v___x_1560_, 1, v___x_1559_);
v___x_1561_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_1515_, v_hasTrace_1319_, v___x_1516_, v_options_1318_, v___x_1518_, v___y_1549_, v___f_1514_, v___x_1560_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
return v___x_1561_;
}
v___jp_1562_:
{
lean_object* v___x_1566_; 
v___x_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1566_, 0, v_a_1565_);
v___y_1548_ = v___y_1563_;
v___y_1549_ = v___y_1564_;
v_a_1550_ = v___x_1566_;
goto v___jp_1547_;
}
v___jp_1567_:
{
lean_object* v___x_1571_; 
v___x_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1571_, 0, v_a_1570_);
v___y_1548_ = v___y_1568_;
v___y_1549_ = v___y_1569_;
v_a_1550_ = v___x_1571_;
goto v___jp_1547_;
}
v___jp_1572_:
{
if (lean_obj_tag(v___y_1575_) == 0)
{
lean_object* v_a_1576_; 
v_a_1576_ = lean_ctor_get(v___y_1575_, 0);
lean_inc(v_a_1576_);
lean_dec_ref_known(v___y_1575_, 1);
v___y_1563_ = v___y_1573_;
v___y_1564_ = v___y_1574_;
v_a_1565_ = v_a_1576_;
goto v___jp_1562_;
}
else
{
lean_object* v_a_1577_; 
v_a_1577_ = lean_ctor_get(v___y_1575_, 0);
lean_inc(v_a_1577_);
lean_dec_ref_known(v___y_1575_, 1);
v___y_1568_ = v___y_1573_;
v___y_1569_ = v___y_1574_;
v_a_1570_ = v_a_1577_;
goto v___jp_1567_;
}
}
v___jp_1578_:
{
lean_object* v___x_1579_; 
v___x_1579_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(v_a_1309_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v___x_1581_; uint8_t v___x_1582_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
lean_dec_ref_known(v___x_1579_, 1);
v___x_1581_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1582_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_1318_, v___x_1581_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1583_ = lean_io_mono_nanos_now();
lean_inc(v_mvarId_1305_);
v___x_1584_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; uint8_t v___x_1586_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v___x_1584_, 1);
v___x_1586_ = lean_unbox(v_a_1585_);
lean_dec(v_a_1585_);
if (v___x_1586_ == 0)
{
lean_object* v___x_1587_; 
lean_inc(v_mvarId_1305_);
v___x_1587_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; uint8_t v___x_1589_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_a_1588_);
lean_dec_ref_known(v___x_1587_, 1);
v___x_1589_ = lean_unbox(v_a_1588_);
if (v___x_1589_ == 0)
{
lean_object* v___x_1590_; 
lean_inc(v_mvarId_1305_);
v___x_1590_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1591_);
lean_dec_ref_known(v___x_1590_, 1);
if (lean_obj_tag(v_a_1591_) == 1)
{
lean_dec(v_a_1588_);
lean_dec(v_mvarId_1305_);
if (v___x_1518_ == 0)
{
lean_object* v_val_1592_; lean_object* v___x_1593_; 
v_val_1592_ = lean_ctor_get(v_a_1591_, 0);
lean_inc(v_val_1592_);
lean_dec_ref_known(v_a_1591_, 1);
v___x_1593_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1304_, v_val_1592_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1573_ = v___x_1583_;
v___y_1574_ = v_a_1580_;
v___y_1575_ = v___x_1593_;
goto v___jp_1572_;
}
else
{
lean_object* v_val_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v_val_1594_ = lean_ctor_get(v_a_1591_, 0);
lean_inc(v_val_1594_);
lean_dec_ref_known(v_a_1591_, 1);
v___x_1595_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23);
v___x_1596_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1515_, v___x_1595_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v___x_1597_; 
lean_dec_ref_known(v___x_1596_, 1);
v___x_1597_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1304_, v_val_1594_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1573_ = v___x_1583_;
v___y_1574_ = v_a_1580_;
v___y_1575_ = v___x_1597_;
goto v___jp_1572_;
}
else
{
lean_dec(v_val_1594_);
lean_dec(v_declName_1304_);
v___y_1573_ = v___x_1583_;
v___y_1574_ = v_a_1580_;
v___y_1575_ = v___x_1596_;
goto v___jp_1572_;
}
}
}
else
{
lean_object* v___x_1598_; 
lean_dec(v_a_1591_);
lean_inc(v_mvarId_1305_);
v___x_1598_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref_known(v___x_1598_, 1);
if (lean_obj_tag(v_a_1599_) == 1)
{
lean_dec(v_a_1588_);
lean_dec(v_mvarId_1305_);
if (v___x_1518_ == 0)
{
lean_object* v_val_1600_; lean_object* v___x_1601_; 
v_val_1600_ = lean_ctor_get(v_a_1599_, 0);
lean_inc(v_val_1600_);
lean_dec_ref_known(v_a_1599_, 1);
v___x_1601_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1304_, v_val_1600_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1573_ = v___x_1583_;
v___y_1574_ = v_a_1580_;
v___y_1575_ = v___x_1601_;
goto v___jp_1572_;
}
else
{
lean_object* v_val_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v_val_1602_ = lean_ctor_get(v_a_1599_, 0);
lean_inc(v_val_1602_);
lean_dec_ref_known(v_a_1599_, 1);
v___x_1603_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25);
v___x_1604_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1515_, v___x_1603_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v___x_1605_; 
lean_dec_ref_known(v___x_1604_, 1);
v___x_1605_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1304_, v_val_1602_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1573_ = v___x_1583_;
v___y_1574_ = v_a_1580_;
v___y_1575_ = v___x_1605_;
goto v___jp_1572_;
}
else
{
lean_dec(v_val_1602_);
lean_dec(v_declName_1304_);
v___y_1573_ = v___x_1583_;
v___y_1574_ = v_a_1580_;
v___y_1575_ = v___x_1604_;
goto v___jp_1572_;
}
}
}
else
{
lean_object* v___x_1606_; 
lean_dec(v_a_1599_);
lean_inc(v_mvarId_1305_);
v___x_1606_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1305_, v_hasTrace_1319_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v_a_1607_; 
v_a_1607_ = lean_ctor_get(v___x_1606_, 0);
lean_inc(v_a_1607_);
lean_dec_ref_known(v___x_1606_, 1);
if (lean_obj_tag(v_a_1607_) == 1)
{
lean_dec(v_a_1588_);
lean_dec(v_mvarId_1305_);
if (v___x_1518_ == 0)
{
lean_object* v_val_1608_; lean_object* v___x_1609_; 
v_val_1608_ = lean_ctor_get(v_a_1607_, 0);
lean_inc(v_val_1608_);
lean_dec_ref_known(v_a_1607_, 1);
v___x_1609_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1304_, v_val_1608_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1573_ = v___x_1583_;
v___y_1574_ = v_a_1580_;
v___y_1575_ = v___x_1609_;
goto v___jp_1572_;
}
else
{
lean_object* v_val_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
v_val_1610_ = lean_ctor_get(v_a_1607_, 0);
lean_inc(v_val_1610_);
lean_dec_ref_known(v_a_1607_, 1);
v___x_1611_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27);
v___x_1612_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1515_, v___x_1611_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_object* v___x_1613_; 
lean_dec_ref_known(v___x_1612_, 1);
v___x_1613_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1304_, v_val_1610_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1573_ = v___x_1583_;
v___y_1574_ = v_a_1580_;
v___y_1575_ = v___x_1613_;
goto v___jp_1572_;
}
else
{
lean_dec(v_val_1610_);
lean_dec(v_declName_1304_);
v___y_1573_ = v___x_1583_;
v___y_1574_ = v_a_1580_;
v___y_1575_ = v___x_1612_;
goto v___jp_1572_;
}
}
}
else
{
lean_object* v___x_1614_; lean_object* v___x_1615_; uint8_t v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; uint8_t v___x_1619_; uint8_t v___x_1620_; uint8_t v___x_1621_; uint8_t v___x_1622_; uint8_t v___x_1623_; uint8_t v___x_1624_; uint8_t v___x_1625_; uint8_t v___x_1626_; uint8_t v___x_1627_; uint8_t v___x_1628_; uint8_t v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
lean_dec(v_a_1607_);
v___x_1614_ = lean_unsigned_to_nat(100000u);
v___x_1615_ = lean_unsigned_to_nat(2u);
v___x_1616_ = 0;
v___x_1617_ = lean_box(0);
v___x_1618_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1618_, 0, v___x_1614_);
lean_ctor_set(v___x_1618_, 1, v___x_1615_);
lean_ctor_set(v___x_1618_, 2, v___x_1617_);
v___x_1619_ = lean_unbox(v_a_1588_);
lean_ctor_set_uint8(v___x_1618_, sizeof(void*)*3, v___x_1619_);
lean_ctor_set_uint8(v___x_1618_, sizeof(void*)*3 + 1, v_hasTrace_1319_);
v___x_1620_ = lean_unbox(v_a_1588_);
lean_ctor_set_uint8(v___x_1618_, sizeof(void*)*3 + 2, v___x_1620_);
lean_ctor_set_uint8(v___x_1618_, sizeof(void*)*3 + 3, v_hasTrace_1319_);
lean_ctor_set_uint8(v___x_1618_, sizeof(void*)*3 + 4, v_hasTrace_1319_);
lean_ctor_set_uint8(v___x_1618_, sizeof(void*)*3 + 5, v_hasTrace_1319_);
lean_ctor_set_uint8(v___x_1618_, sizeof(void*)*3 + 6, v___x_1616_);
lean_ctor_set_uint8(v___x_1618_, sizeof(void*)*3 + 7, v_hasTrace_1319_);
lean_ctor_set_uint8(v___x_1618_, sizeof(void*)*3 + 8, v_hasTrace_1319_);
v___x_1621_ = lean_unbox(v_a_1588_);
lean_ctor_set_uint8(v___x_1618_, sizeof(void*)*3 + 9, v___x_1621_);
v___x_1622_ = lean_unbox(v_a_1588_);
lean_ctor_set_uint8(v___x_1618_, sizeof(void*)*3 + 10, v___x_1622_);
v___x_1623_ = lean_unbox(v_a_1588_);
lean_ctor_set_uint8(v___x_1618_, sizeof(void*)*3 + 11, v___x_1623_);
lean_ctor_set_uint8(v___x_1618_, sizeof(void*)*3 + 12, v_hasTrace_1319_);
lean_ctor_set_uint8(v___x_1618_, sizeof(void*)*3 + 13, v_hasTrace_1319_);
v___x_1624_ = lean_unbox(v_a_1588_);
lean_ctor_set_uint8(v___x_1618_, sizeof(void*)*3 + 14, v___x_1624_);
v___x_1625_ = lean_unbox(v_a_1588_);
lean_ctor_set_uint8(v___x_1618_, sizeof(void*)*3 + 15, v___x_1625_);
v___x_1626_ = lean_unbox(v_a_1588_);
lean_ctor_set_uint8(v___x_1618_, sizeof(void*)*3 + 16, v___x_1626_);
lean_ctor_set_uint8(v___x_1618_, sizeof(void*)*3 + 17, v_hasTrace_1319_);
lean_ctor_set_uint8(v___x_1618_, sizeof(void*)*3 + 18, v_hasTrace_1319_);
lean_ctor_set_uint8(v___x_1618_, sizeof(void*)*3 + 19, v_hasTrace_1319_);
lean_ctor_set_uint8(v___x_1618_, sizeof(void*)*3 + 20, v_hasTrace_1319_);
lean_ctor_set_uint8(v___x_1618_, sizeof(void*)*3 + 21, v_hasTrace_1319_);
lean_ctor_set_uint8(v___x_1618_, sizeof(void*)*3 + 22, v_hasTrace_1319_);
lean_ctor_set_uint8(v___x_1618_, sizeof(void*)*3 + 23, v_hasTrace_1319_);
lean_ctor_set_uint8(v___x_1618_, sizeof(void*)*3 + 24, v_hasTrace_1319_);
lean_ctor_set_uint8(v___x_1618_, sizeof(void*)*3 + 25, v_hasTrace_1319_);
v___x_1627_ = lean_unbox(v_a_1588_);
lean_ctor_set_uint8(v___x_1618_, sizeof(void*)*3 + 26, v___x_1627_);
v___x_1628_ = lean_unbox(v_a_1588_);
lean_ctor_set_uint8(v___x_1618_, sizeof(void*)*3 + 27, v___x_1628_);
v___x_1629_ = lean_unbox(v_a_1588_);
lean_dec(v_a_1588_);
lean_ctor_set_uint8(v___x_1618_, sizeof(void*)*3 + 28, v___x_1629_);
v___x_1630_ = lean_unsigned_to_nat(0u);
v___x_1631_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0));
v___x_1632_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2);
v___x_1633_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1634_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1634_, 0, v___x_1632_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*2, v_hasTrace_1319_);
v___x_1635_ = l_Lean_Options_empty;
v___x_1636_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1618_, v___x_1631_, v___x_1634_, v___x_1635_, v_a_1306_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_a_1637_);
lean_dec_ref_known(v___x_1636_, 1);
v___x_1638_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
lean_inc(v_mvarId_1305_);
v___x_1639_ = l_Lean_Meta_simpTargetStar(v_mvarId_1305_, v_a_1637_, v___x_1631_, v___x_1617_, v___x_1638_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v_fst_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1695_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1640_);
lean_dec_ref_known(v___x_1639_, 1);
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
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1645_; 
v___x_1645_ = lean_box(0);
v___y_1563_ = v___x_1583_;
v___y_1564_ = v_a_1580_;
v_a_1565_ = v___x_1645_;
goto v___jp_1562_;
}
else
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1646_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29);
v___x_1647_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1515_, v___x_1646_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1573_ = v___x_1583_;
v___y_1574_ = v_a_1580_;
v___y_1575_ = v___x_1647_;
goto v___jp_1572_;
}
}
case 1:
{
lean_object* v___x_1648_; 
lean_inc(v_declName_1304_);
lean_inc(v_mvarId_1305_);
v___x_1648_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1305_, v_declName_1304_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; 
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_a_1649_);
lean_dec_ref_known(v___x_1648_, 1);
if (lean_obj_tag(v_a_1649_) == 1)
{
lean_del_object(v___x_1643_);
lean_dec(v_mvarId_1305_);
if (v___x_1518_ == 0)
{
lean_object* v_val_1650_; lean_object* v___x_1651_; 
v_val_1650_ = lean_ctor_get(v_a_1649_, 0);
lean_inc(v_val_1650_);
lean_dec_ref_known(v_a_1649_, 1);
v___x_1651_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1304_, v_val_1650_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1573_ = v___x_1583_;
v___y_1574_ = v_a_1580_;
v___y_1575_ = v___x_1651_;
goto v___jp_1572_;
}
else
{
lean_object* v_val_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v_val_1652_ = lean_ctor_get(v_a_1649_, 0);
lean_inc(v_val_1652_);
lean_dec_ref_known(v_a_1649_, 1);
v___x_1653_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31);
v___x_1654_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1515_, v___x_1653_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v___x_1655_; 
lean_dec_ref_known(v___x_1654_, 1);
v___x_1655_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1304_, v_val_1652_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1573_ = v___x_1583_;
v___y_1574_ = v_a_1580_;
v___y_1575_ = v___x_1655_;
goto v___jp_1572_;
}
else
{
lean_dec(v_val_1652_);
lean_dec(v_declName_1304_);
v___y_1573_ = v___x_1583_;
v___y_1574_ = v_a_1580_;
v___y_1575_ = v___x_1654_;
goto v___jp_1572_;
}
}
}
else
{
lean_object* v___x_1656_; 
lean_dec(v_a_1649_);
lean_inc(v_mvarId_1305_);
v___x_1656_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_a_1657_);
lean_dec_ref_known(v___x_1656_, 1);
if (lean_obj_tag(v_a_1657_) == 1)
{
lean_del_object(v___x_1643_);
lean_dec(v_mvarId_1305_);
if (v___x_1518_ == 0)
{
lean_object* v_val_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v_val_1658_ = lean_ctor_get(v_a_1657_, 0);
lean_inc(v_val_1658_);
lean_dec_ref_known(v_a_1657_, 1);
v___x_1659_ = lean_box(0);
v___x_1660_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1658_, v___x_1630_, v_declName_1304_, v___x_1659_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
lean_dec(v_val_1658_);
v___y_1573_ = v___x_1583_;
v___y_1574_ = v_a_1580_;
v___y_1575_ = v___x_1660_;
goto v___jp_1572_;
}
else
{
lean_object* v_val_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v_val_1661_ = lean_ctor_get(v_a_1657_, 0);
lean_inc(v_val_1661_);
lean_dec_ref_known(v_a_1657_, 1);
v___x_1662_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33);
v___x_1663_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1515_, v___x_1662_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_a_1664_; lean_object* v___x_1665_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_a_1664_);
lean_dec_ref_known(v___x_1663_, 1);
v___x_1665_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1661_, v___x_1630_, v_declName_1304_, v_a_1664_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
lean_dec(v_val_1661_);
v___y_1573_ = v___x_1583_;
v___y_1574_ = v_a_1580_;
v___y_1575_ = v___x_1665_;
goto v___jp_1572_;
}
else
{
lean_dec(v_val_1661_);
lean_dec(v_declName_1304_);
v___y_1573_ = v___x_1583_;
v___y_1574_ = v_a_1580_;
v___y_1575_ = v___x_1663_;
goto v___jp_1572_;
}
}
}
else
{
lean_object* v___x_1666_; 
lean_dec(v_a_1657_);
lean_inc(v_mvarId_1305_);
v___x_1666_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1305_, v_hasTrace_1319_, v_hasTrace_1319_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
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
lean_dec(v_mvarId_1305_);
if (v___x_1518_ == 0)
{
lean_object* v_val_1671_; lean_object* v___x_1672_; 
v_val_1671_ = lean_ctor_get(v_a_1667_, 0);
lean_inc(v_val_1671_);
lean_dec_ref_known(v_a_1667_, 1);
v___x_1672_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1304_, v_val_1671_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1573_ = v___x_1583_;
v___y_1574_ = v_a_1580_;
v___y_1575_ = v___x_1672_;
goto v___jp_1572_;
}
else
{
lean_object* v_val_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v_val_1673_ = lean_ctor_get(v_a_1667_, 0);
lean_inc(v_val_1673_);
lean_dec_ref_known(v_a_1667_, 1);
v___x_1674_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35);
v___x_1675_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1515_, v___x_1674_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v___x_1676_; 
lean_dec_ref_known(v___x_1675_, 1);
v___x_1676_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1304_, v_val_1673_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1573_ = v___x_1583_;
v___y_1574_ = v_a_1580_;
v___y_1575_ = v___x_1676_;
goto v___jp_1572_;
}
else
{
lean_dec(v_val_1673_);
lean_dec(v_declName_1304_);
v___y_1573_ = v___x_1583_;
v___y_1574_ = v_a_1580_;
v___y_1575_ = v___x_1675_;
goto v___jp_1572_;
}
}
}
else
{
lean_object* v___x_1677_; lean_object* v___x_1679_; 
lean_dec(v_a_1667_);
lean_dec(v_declName_1304_);
v___x_1677_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
if (v_isShared_1670_ == 0)
{
lean_ctor_set_tag(v___x_1669_, 1);
lean_ctor_set(v___x_1669_, 0, v_mvarId_1305_);
v___x_1679_ = v___x_1669_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_mvarId_1305_);
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
v___x_1682_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1681_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1573_ = v___x_1583_;
v___y_1574_ = v_a_1580_;
v___y_1575_ = v___x_1682_;
goto v___jp_1572_;
}
}
}
}
}
else
{
lean_object* v_a_1686_; 
lean_del_object(v___x_1643_);
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_1686_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_a_1686_);
lean_dec_ref_known(v___x_1666_, 1);
v___y_1568_ = v___x_1583_;
v___y_1569_ = v_a_1580_;
v_a_1570_ = v_a_1686_;
goto v___jp_1567_;
}
}
}
else
{
lean_object* v_a_1687_; 
lean_del_object(v___x_1643_);
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_1687_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_a_1687_);
lean_dec_ref_known(v___x_1656_, 1);
v___y_1568_ = v___x_1583_;
v___y_1569_ = v_a_1580_;
v_a_1570_ = v_a_1687_;
goto v___jp_1567_;
}
}
}
else
{
lean_object* v_a_1688_; 
lean_del_object(v___x_1643_);
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_1688_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_a_1688_);
lean_dec_ref_known(v___x_1648_, 1);
v___y_1568_ = v___x_1583_;
v___y_1569_ = v_a_1580_;
v_a_1570_ = v_a_1688_;
goto v___jp_1567_;
}
}
default: 
{
lean_del_object(v___x_1643_);
lean_dec(v_mvarId_1305_);
if (v___x_1518_ == 0)
{
lean_object* v_mvarId_1689_; lean_object* v___x_1690_; 
v_mvarId_1689_ = lean_ctor_get(v_fst_1641_, 0);
lean_inc(v_mvarId_1689_);
lean_dec_ref_known(v_fst_1641_, 1);
v___x_1690_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1304_, v_mvarId_1689_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1573_ = v___x_1583_;
v___y_1574_ = v_a_1580_;
v___y_1575_ = v___x_1690_;
goto v___jp_1572_;
}
else
{
lean_object* v_mvarId_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v_mvarId_1691_ = lean_ctor_get(v_fst_1641_, 0);
lean_inc(v_mvarId_1691_);
lean_dec_ref_known(v_fst_1641_, 1);
v___x_1692_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37);
v___x_1693_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1515_, v___x_1692_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v___x_1694_; 
lean_dec_ref_known(v___x_1693_, 1);
v___x_1694_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1304_, v_mvarId_1691_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1573_ = v___x_1583_;
v___y_1574_ = v_a_1580_;
v___y_1575_ = v___x_1694_;
goto v___jp_1572_;
}
else
{
lean_dec(v_mvarId_1691_);
lean_dec(v_declName_1304_);
v___y_1573_ = v___x_1583_;
v___y_1574_ = v_a_1580_;
v___y_1575_ = v___x_1693_;
goto v___jp_1572_;
}
}
}
}
}
}
else
{
lean_object* v_a_1697_; 
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_1697_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1697_);
lean_dec_ref_known(v___x_1639_, 1);
v___y_1568_ = v___x_1583_;
v___y_1569_ = v_a_1580_;
v_a_1570_ = v_a_1697_;
goto v___jp_1567_;
}
}
else
{
lean_object* v_a_1698_; 
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_1698_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_a_1698_);
lean_dec_ref_known(v___x_1636_, 1);
v___y_1568_ = v___x_1583_;
v___y_1569_ = v_a_1580_;
v_a_1570_ = v_a_1698_;
goto v___jp_1567_;
}
}
}
else
{
lean_object* v_a_1699_; 
lean_dec(v_a_1588_);
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_1699_ = lean_ctor_get(v___x_1606_, 0);
lean_inc(v_a_1699_);
lean_dec_ref_known(v___x_1606_, 1);
v___y_1568_ = v___x_1583_;
v___y_1569_ = v_a_1580_;
v_a_1570_ = v_a_1699_;
goto v___jp_1567_;
}
}
}
else
{
lean_object* v_a_1700_; 
lean_dec(v_a_1588_);
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_1700_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1700_);
lean_dec_ref_known(v___x_1598_, 1);
v___y_1568_ = v___x_1583_;
v___y_1569_ = v_a_1580_;
v_a_1570_ = v_a_1700_;
goto v___jp_1567_;
}
}
}
else
{
lean_object* v_a_1701_; 
lean_dec(v_a_1588_);
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_1701_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1701_);
lean_dec_ref_known(v___x_1590_, 1);
v___y_1568_ = v___x_1583_;
v___y_1569_ = v_a_1580_;
v_a_1570_ = v_a_1701_;
goto v___jp_1567_;
}
}
else
{
lean_dec(v_a_1588_);
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1702_ = lean_box(0);
v___x_1703_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1702_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1573_ = v___x_1583_;
v___y_1574_ = v_a_1580_;
v___y_1575_ = v___x_1703_;
goto v___jp_1572_;
}
else
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1704_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39);
v___x_1705_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1515_, v___x_1704_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; lean_object* v___x_1707_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_a_1706_);
lean_dec_ref_known(v___x_1705_, 1);
v___x_1707_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1706_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1573_ = v___x_1583_;
v___y_1574_ = v_a_1580_;
v___y_1575_ = v___x_1707_;
goto v___jp_1572_;
}
else
{
v___y_1573_ = v___x_1583_;
v___y_1574_ = v_a_1580_;
v___y_1575_ = v___x_1705_;
goto v___jp_1572_;
}
}
}
}
else
{
lean_object* v_a_1708_; 
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_1708_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_a_1708_);
lean_dec_ref_known(v___x_1587_, 1);
v___y_1568_ = v___x_1583_;
v___y_1569_ = v_a_1580_;
v_a_1570_ = v_a_1708_;
goto v___jp_1567_;
}
}
else
{
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = lean_box(0);
v___x_1710_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1709_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1573_ = v___x_1583_;
v___y_1574_ = v_a_1580_;
v___y_1575_ = v___x_1710_;
goto v___jp_1572_;
}
else
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1711_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41);
v___x_1712_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1515_, v___x_1711_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v_a_1713_; lean_object* v___x_1714_; 
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
lean_inc(v_a_1713_);
lean_dec_ref_known(v___x_1712_, 1);
v___x_1714_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1713_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1573_ = v___x_1583_;
v___y_1574_ = v_a_1580_;
v___y_1575_ = v___x_1714_;
goto v___jp_1572_;
}
else
{
v___y_1573_ = v___x_1583_;
v___y_1574_ = v_a_1580_;
v___y_1575_ = v___x_1712_;
goto v___jp_1572_;
}
}
}
}
else
{
lean_object* v_a_1715_; 
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_1715_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1715_);
lean_dec_ref_known(v___x_1584_, 1);
v___y_1568_ = v___x_1583_;
v___y_1569_ = v_a_1580_;
v_a_1570_ = v_a_1715_;
goto v___jp_1567_;
}
}
else
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1716_ = lean_io_get_num_heartbeats();
lean_inc(v_mvarId_1305_);
v___x_1717_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v_a_1718_; uint8_t v___x_1719_; 
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
lean_inc(v_a_1718_);
lean_dec_ref_known(v___x_1717_, 1);
v___x_1719_ = lean_unbox(v_a_1718_);
lean_dec(v_a_1718_);
if (v___x_1719_ == 0)
{
lean_object* v___x_1720_; 
lean_inc(v_mvarId_1305_);
v___x_1720_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1721_; uint8_t v___x_1722_; 
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_a_1721_);
lean_dec_ref_known(v___x_1720_, 1);
v___x_1722_ = lean_unbox(v_a_1721_);
if (v___x_1722_ == 0)
{
lean_object* v___x_1723_; 
lean_inc(v_mvarId_1305_);
v___x_1723_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v_a_1724_; 
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
lean_inc(v_a_1724_);
lean_dec_ref_known(v___x_1723_, 1);
if (lean_obj_tag(v_a_1724_) == 1)
{
lean_dec(v_a_1721_);
lean_dec(v_mvarId_1305_);
if (v___x_1518_ == 0)
{
lean_object* v_val_1725_; lean_object* v___x_1726_; 
v_val_1725_ = lean_ctor_get(v_a_1724_, 0);
lean_inc(v_val_1725_);
lean_dec_ref_known(v_a_1724_, 1);
v___x_1726_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1304_, v_val_1725_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1542_ = v_a_1580_;
v___y_1543_ = v___x_1716_;
v___y_1544_ = v___x_1726_;
goto v___jp_1541_;
}
else
{
lean_object* v_val_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v_val_1727_ = lean_ctor_get(v_a_1724_, 0);
lean_inc(v_val_1727_);
lean_dec_ref_known(v_a_1724_, 1);
v___x_1728_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23);
v___x_1729_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1515_, v___x_1728_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v___x_1730_; 
lean_dec_ref_known(v___x_1729_, 1);
v___x_1730_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1304_, v_val_1727_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1542_ = v_a_1580_;
v___y_1543_ = v___x_1716_;
v___y_1544_ = v___x_1730_;
goto v___jp_1541_;
}
else
{
lean_dec(v_val_1727_);
lean_dec(v_declName_1304_);
v___y_1542_ = v_a_1580_;
v___y_1543_ = v___x_1716_;
v___y_1544_ = v___x_1729_;
goto v___jp_1541_;
}
}
}
else
{
lean_object* v___x_1731_; 
lean_dec(v_a_1724_);
lean_inc(v_mvarId_1305_);
v___x_1731_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_object* v_a_1732_; 
v_a_1732_ = lean_ctor_get(v___x_1731_, 0);
lean_inc(v_a_1732_);
lean_dec_ref_known(v___x_1731_, 1);
if (lean_obj_tag(v_a_1732_) == 1)
{
lean_dec(v_a_1721_);
lean_dec(v_mvarId_1305_);
if (v___x_1518_ == 0)
{
lean_object* v_val_1733_; lean_object* v___x_1734_; 
v_val_1733_ = lean_ctor_get(v_a_1732_, 0);
lean_inc(v_val_1733_);
lean_dec_ref_known(v_a_1732_, 1);
v___x_1734_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1304_, v_val_1733_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1542_ = v_a_1580_;
v___y_1543_ = v___x_1716_;
v___y_1544_ = v___x_1734_;
goto v___jp_1541_;
}
else
{
lean_object* v_val_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v_val_1735_ = lean_ctor_get(v_a_1732_, 0);
lean_inc(v_val_1735_);
lean_dec_ref_known(v_a_1732_, 1);
v___x_1736_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25);
v___x_1737_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1515_, v___x_1736_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v___x_1738_; 
lean_dec_ref_known(v___x_1737_, 1);
v___x_1738_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1304_, v_val_1735_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1542_ = v_a_1580_;
v___y_1543_ = v___x_1716_;
v___y_1544_ = v___x_1738_;
goto v___jp_1541_;
}
else
{
lean_dec(v_val_1735_);
lean_dec(v_declName_1304_);
v___y_1542_ = v_a_1580_;
v___y_1543_ = v___x_1716_;
v___y_1544_ = v___x_1737_;
goto v___jp_1541_;
}
}
}
else
{
lean_object* v___x_1739_; 
lean_dec(v_a_1732_);
lean_inc(v_mvarId_1305_);
v___x_1739_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1305_, v___x_1582_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_a_1740_);
lean_dec_ref_known(v___x_1739_, 1);
if (lean_obj_tag(v_a_1740_) == 1)
{
lean_dec(v_a_1721_);
lean_dec(v_mvarId_1305_);
if (v___x_1518_ == 0)
{
lean_object* v_val_1741_; lean_object* v___x_1742_; 
v_val_1741_ = lean_ctor_get(v_a_1740_, 0);
lean_inc(v_val_1741_);
lean_dec_ref_known(v_a_1740_, 1);
v___x_1742_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1304_, v_val_1741_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1542_ = v_a_1580_;
v___y_1543_ = v___x_1716_;
v___y_1544_ = v___x_1742_;
goto v___jp_1541_;
}
else
{
lean_object* v_val_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v_val_1743_ = lean_ctor_get(v_a_1740_, 0);
lean_inc(v_val_1743_);
lean_dec_ref_known(v_a_1740_, 1);
v___x_1744_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27);
v___x_1745_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1515_, v___x_1744_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v___x_1746_; 
lean_dec_ref_known(v___x_1745_, 1);
v___x_1746_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1304_, v_val_1743_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1542_ = v_a_1580_;
v___y_1543_ = v___x_1716_;
v___y_1544_ = v___x_1746_;
goto v___jp_1541_;
}
else
{
lean_dec(v_val_1743_);
lean_dec(v_declName_1304_);
v___y_1542_ = v_a_1580_;
v___y_1543_ = v___x_1716_;
v___y_1544_ = v___x_1745_;
goto v___jp_1541_;
}
}
}
else
{
lean_object* v___x_1747_; lean_object* v___x_1748_; uint8_t v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; uint8_t v___x_1752_; uint8_t v___x_1753_; uint8_t v___x_1754_; uint8_t v___x_1755_; uint8_t v___x_1756_; uint8_t v___x_1757_; uint8_t v___x_1758_; uint8_t v___x_1759_; uint8_t v___x_1760_; uint8_t v___x_1761_; uint8_t v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
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
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 1, v___x_1582_);
v___x_1753_ = lean_unbox(v_a_1721_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 2, v___x_1753_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 3, v___x_1582_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 4, v___x_1582_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 5, v___x_1582_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 6, v___x_1749_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 7, v___x_1582_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 8, v___x_1582_);
v___x_1754_ = lean_unbox(v_a_1721_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 9, v___x_1754_);
v___x_1755_ = lean_unbox(v_a_1721_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 10, v___x_1755_);
v___x_1756_ = lean_unbox(v_a_1721_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 11, v___x_1756_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 12, v___x_1582_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 13, v___x_1582_);
v___x_1757_ = lean_unbox(v_a_1721_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 14, v___x_1757_);
v___x_1758_ = lean_unbox(v_a_1721_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 15, v___x_1758_);
v___x_1759_ = lean_unbox(v_a_1721_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 16, v___x_1759_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 17, v___x_1582_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 18, v___x_1582_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 19, v___x_1582_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 20, v___x_1582_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 21, v___x_1582_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 22, v___x_1582_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 23, v___x_1582_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 24, v___x_1582_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 25, v___x_1582_);
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
lean_ctor_set_uint8(v___x_1767_, sizeof(void*)*2, v___x_1582_);
v___x_1768_ = l_Lean_Options_empty;
v___x_1769_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1751_, v___x_1764_, v___x_1767_, v___x_1768_, v_a_1306_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_a_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
lean_inc(v_a_1770_);
lean_dec_ref_known(v___x_1769_, 1);
v___x_1771_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
lean_inc(v_mvarId_1305_);
v___x_1772_ = l_Lean_Meta_simpTargetStar(v_mvarId_1305_, v_a_1770_, v___x_1764_, v___x_1750_, v___x_1771_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_a_1773_; lean_object* v_fst_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1828_; 
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_a_1773_);
lean_dec_ref_known(v___x_1772_, 1);
v_fst_1774_ = lean_ctor_get(v_a_1773_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v_a_1773_);
if (v_isSharedCheck_1828_ == 0)
{
lean_object* v_unused_1829_; 
v_unused_1829_ = lean_ctor_get(v_a_1773_, 1);
lean_dec(v_unused_1829_);
v___x_1776_ = v_a_1773_;
v_isShared_1777_ = v_isSharedCheck_1828_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_fst_1774_);
lean_dec(v_a_1773_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1828_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
switch(lean_obj_tag(v_fst_1774_))
{
case 0:
{
lean_del_object(v___x_1776_);
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1778_; 
v___x_1778_ = lean_box(0);
v___y_1537_ = v_a_1580_;
v___y_1538_ = v___x_1716_;
v_a_1539_ = v___x_1778_;
goto v___jp_1536_;
}
else
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1779_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29);
v___x_1780_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1515_, v___x_1779_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1542_ = v_a_1580_;
v___y_1543_ = v___x_1716_;
v___y_1544_ = v___x_1780_;
goto v___jp_1541_;
}
}
case 1:
{
lean_object* v___x_1781_; 
lean_inc(v_declName_1304_);
lean_inc(v_mvarId_1305_);
v___x_1781_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1305_, v_declName_1304_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v_a_1782_; 
v_a_1782_ = lean_ctor_get(v___x_1781_, 0);
lean_inc(v_a_1782_);
lean_dec_ref_known(v___x_1781_, 1);
if (lean_obj_tag(v_a_1782_) == 1)
{
lean_del_object(v___x_1776_);
lean_dec(v_mvarId_1305_);
if (v___x_1518_ == 0)
{
lean_object* v_val_1783_; lean_object* v___x_1784_; 
v_val_1783_ = lean_ctor_get(v_a_1782_, 0);
lean_inc(v_val_1783_);
lean_dec_ref_known(v_a_1782_, 1);
v___x_1784_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1304_, v_val_1783_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1542_ = v_a_1580_;
v___y_1543_ = v___x_1716_;
v___y_1544_ = v___x_1784_;
goto v___jp_1541_;
}
else
{
lean_object* v_val_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v_val_1785_ = lean_ctor_get(v_a_1782_, 0);
lean_inc(v_val_1785_);
lean_dec_ref_known(v_a_1782_, 1);
v___x_1786_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31);
v___x_1787_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1515_, v___x_1786_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v___x_1788_; 
lean_dec_ref_known(v___x_1787_, 1);
v___x_1788_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1304_, v_val_1785_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1542_ = v_a_1580_;
v___y_1543_ = v___x_1716_;
v___y_1544_ = v___x_1788_;
goto v___jp_1541_;
}
else
{
lean_dec(v_val_1785_);
lean_dec(v_declName_1304_);
v___y_1542_ = v_a_1580_;
v___y_1543_ = v___x_1716_;
v___y_1544_ = v___x_1787_;
goto v___jp_1541_;
}
}
}
else
{
lean_object* v___x_1789_; 
lean_dec(v_a_1782_);
lean_inc(v_mvarId_1305_);
v___x_1789_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v_a_1790_; 
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
lean_inc(v_a_1790_);
lean_dec_ref_known(v___x_1789_, 1);
if (lean_obj_tag(v_a_1790_) == 1)
{
lean_del_object(v___x_1776_);
lean_dec(v_mvarId_1305_);
if (v___x_1518_ == 0)
{
lean_object* v_val_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v_val_1791_ = lean_ctor_get(v_a_1790_, 0);
lean_inc(v_val_1791_);
lean_dec_ref_known(v_a_1790_, 1);
v___x_1792_ = lean_box(0);
v___x_1793_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1791_, v___x_1763_, v_declName_1304_, v___x_1792_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
lean_dec(v_val_1791_);
v___y_1542_ = v_a_1580_;
v___y_1543_ = v___x_1716_;
v___y_1544_ = v___x_1793_;
goto v___jp_1541_;
}
else
{
lean_object* v_val_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v_val_1794_ = lean_ctor_get(v_a_1790_, 0);
lean_inc(v_val_1794_);
lean_dec_ref_known(v_a_1790_, 1);
v___x_1795_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33);
v___x_1796_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1515_, v___x_1795_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; lean_object* v___x_1798_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_a_1797_);
lean_dec_ref_known(v___x_1796_, 1);
v___x_1798_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1794_, v___x_1763_, v_declName_1304_, v_a_1797_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
lean_dec(v_val_1794_);
v___y_1542_ = v_a_1580_;
v___y_1543_ = v___x_1716_;
v___y_1544_ = v___x_1798_;
goto v___jp_1541_;
}
else
{
lean_dec(v_val_1794_);
lean_dec(v_declName_1304_);
v___y_1542_ = v_a_1580_;
v___y_1543_ = v___x_1716_;
v___y_1544_ = v___x_1796_;
goto v___jp_1541_;
}
}
}
else
{
lean_object* v___x_1799_; 
lean_dec(v_a_1790_);
lean_inc(v_mvarId_1305_);
v___x_1799_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1305_, v___x_1582_, v___x_1582_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1818_; 
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1802_ = v___x_1799_;
v_isShared_1803_ = v_isSharedCheck_1818_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1799_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1818_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
if (lean_obj_tag(v_a_1800_) == 1)
{
lean_del_object(v___x_1802_);
lean_del_object(v___x_1776_);
lean_dec(v_mvarId_1305_);
if (v___x_1518_ == 0)
{
lean_object* v_val_1804_; lean_object* v___x_1805_; 
v_val_1804_ = lean_ctor_get(v_a_1800_, 0);
lean_inc(v_val_1804_);
lean_dec_ref_known(v_a_1800_, 1);
v___x_1805_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1304_, v_val_1804_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1542_ = v_a_1580_;
v___y_1543_ = v___x_1716_;
v___y_1544_ = v___x_1805_;
goto v___jp_1541_;
}
else
{
lean_object* v_val_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v_val_1806_ = lean_ctor_get(v_a_1800_, 0);
lean_inc(v_val_1806_);
lean_dec_ref_known(v_a_1800_, 1);
v___x_1807_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35);
v___x_1808_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1515_, v___x_1807_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v___x_1809_; 
lean_dec_ref_known(v___x_1808_, 1);
v___x_1809_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1304_, v_val_1806_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1542_ = v_a_1580_;
v___y_1543_ = v___x_1716_;
v___y_1544_ = v___x_1809_;
goto v___jp_1541_;
}
else
{
lean_dec(v_val_1806_);
lean_dec(v_declName_1304_);
v___y_1542_ = v_a_1580_;
v___y_1543_ = v___x_1716_;
v___y_1544_ = v___x_1808_;
goto v___jp_1541_;
}
}
}
else
{
lean_object* v___x_1810_; lean_object* v___x_1812_; 
lean_dec(v_a_1800_);
lean_dec(v_declName_1304_);
v___x_1810_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
if (v_isShared_1803_ == 0)
{
lean_ctor_set_tag(v___x_1802_, 1);
lean_ctor_set(v___x_1802_, 0, v_mvarId_1305_);
v___x_1812_ = v___x_1802_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_mvarId_1305_);
v___x_1812_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
lean_object* v___x_1814_; 
if (v_isShared_1777_ == 0)
{
lean_ctor_set_tag(v___x_1776_, 7);
lean_ctor_set(v___x_1776_, 1, v___x_1812_);
lean_ctor_set(v___x_1776_, 0, v___x_1810_);
v___x_1814_ = v___x_1776_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1810_);
lean_ctor_set(v_reuseFailAlloc_1816_, 1, v___x_1812_);
v___x_1814_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
lean_object* v___x_1815_; 
v___x_1815_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1814_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1542_ = v_a_1580_;
v___y_1543_ = v___x_1716_;
v___y_1544_ = v___x_1815_;
goto v___jp_1541_;
}
}
}
}
}
else
{
lean_object* v_a_1819_; 
lean_del_object(v___x_1776_);
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_1819_ = lean_ctor_get(v___x_1799_, 0);
lean_inc(v_a_1819_);
lean_dec_ref_known(v___x_1799_, 1);
v___y_1532_ = v_a_1580_;
v___y_1533_ = v___x_1716_;
v_a_1534_ = v_a_1819_;
goto v___jp_1531_;
}
}
}
else
{
lean_object* v_a_1820_; 
lean_del_object(v___x_1776_);
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_1820_ = lean_ctor_get(v___x_1789_, 0);
lean_inc(v_a_1820_);
lean_dec_ref_known(v___x_1789_, 1);
v___y_1532_ = v_a_1580_;
v___y_1533_ = v___x_1716_;
v_a_1534_ = v_a_1820_;
goto v___jp_1531_;
}
}
}
else
{
lean_object* v_a_1821_; 
lean_del_object(v___x_1776_);
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_1821_ = lean_ctor_get(v___x_1781_, 0);
lean_inc(v_a_1821_);
lean_dec_ref_known(v___x_1781_, 1);
v___y_1532_ = v_a_1580_;
v___y_1533_ = v___x_1716_;
v_a_1534_ = v_a_1821_;
goto v___jp_1531_;
}
}
default: 
{
lean_del_object(v___x_1776_);
lean_dec(v_mvarId_1305_);
if (v___x_1518_ == 0)
{
lean_object* v_mvarId_1822_; lean_object* v___x_1823_; 
v_mvarId_1822_ = lean_ctor_get(v_fst_1774_, 0);
lean_inc(v_mvarId_1822_);
lean_dec_ref_known(v_fst_1774_, 1);
v___x_1823_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1304_, v_mvarId_1822_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1542_ = v_a_1580_;
v___y_1543_ = v___x_1716_;
v___y_1544_ = v___x_1823_;
goto v___jp_1541_;
}
else
{
lean_object* v_mvarId_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
v_mvarId_1824_ = lean_ctor_get(v_fst_1774_, 0);
lean_inc(v_mvarId_1824_);
lean_dec_ref_known(v_fst_1774_, 1);
v___x_1825_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37);
v___x_1826_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1515_, v___x_1825_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v___x_1827_; 
lean_dec_ref_known(v___x_1826_, 1);
v___x_1827_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1304_, v_mvarId_1824_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1542_ = v_a_1580_;
v___y_1543_ = v___x_1716_;
v___y_1544_ = v___x_1827_;
goto v___jp_1541_;
}
else
{
lean_dec(v_mvarId_1824_);
lean_dec(v_declName_1304_);
v___y_1542_ = v_a_1580_;
v___y_1543_ = v___x_1716_;
v___y_1544_ = v___x_1826_;
goto v___jp_1541_;
}
}
}
}
}
}
else
{
lean_object* v_a_1830_; 
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_1830_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_a_1830_);
lean_dec_ref_known(v___x_1772_, 1);
v___y_1532_ = v_a_1580_;
v___y_1533_ = v___x_1716_;
v_a_1534_ = v_a_1830_;
goto v___jp_1531_;
}
}
else
{
lean_object* v_a_1831_; 
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_1831_ = lean_ctor_get(v___x_1769_, 0);
lean_inc(v_a_1831_);
lean_dec_ref_known(v___x_1769_, 1);
v___y_1532_ = v_a_1580_;
v___y_1533_ = v___x_1716_;
v_a_1534_ = v_a_1831_;
goto v___jp_1531_;
}
}
}
else
{
lean_object* v_a_1832_; 
lean_dec(v_a_1721_);
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_1832_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_a_1832_);
lean_dec_ref_known(v___x_1739_, 1);
v___y_1532_ = v_a_1580_;
v___y_1533_ = v___x_1716_;
v_a_1534_ = v_a_1832_;
goto v___jp_1531_;
}
}
}
else
{
lean_object* v_a_1833_; 
lean_dec(v_a_1721_);
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_1833_ = lean_ctor_get(v___x_1731_, 0);
lean_inc(v_a_1833_);
lean_dec_ref_known(v___x_1731_, 1);
v___y_1532_ = v_a_1580_;
v___y_1533_ = v___x_1716_;
v_a_1534_ = v_a_1833_;
goto v___jp_1531_;
}
}
}
else
{
lean_object* v_a_1834_; 
lean_dec(v_a_1721_);
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_1834_ = lean_ctor_get(v___x_1723_, 0);
lean_inc(v_a_1834_);
lean_dec_ref_known(v___x_1723_, 1);
v___y_1532_ = v_a_1580_;
v___y_1533_ = v___x_1716_;
v_a_1534_ = v_a_1834_;
goto v___jp_1531_;
}
}
else
{
lean_dec(v_a_1721_);
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1835_ = lean_box(0);
v___x_1836_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1835_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1542_ = v_a_1580_;
v___y_1543_ = v___x_1716_;
v___y_1544_ = v___x_1836_;
goto v___jp_1541_;
}
else
{
lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1837_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39);
v___x_1838_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1515_, v___x_1837_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_object* v_a_1839_; lean_object* v___x_1840_; 
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
lean_inc(v_a_1839_);
lean_dec_ref_known(v___x_1838_, 1);
v___x_1840_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1839_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1542_ = v_a_1580_;
v___y_1543_ = v___x_1716_;
v___y_1544_ = v___x_1840_;
goto v___jp_1541_;
}
else
{
v___y_1542_ = v_a_1580_;
v___y_1543_ = v___x_1716_;
v___y_1544_ = v___x_1838_;
goto v___jp_1541_;
}
}
}
}
else
{
lean_object* v_a_1841_; 
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_1841_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_a_1841_);
lean_dec_ref_known(v___x_1720_, 1);
v___y_1532_ = v_a_1580_;
v___y_1533_ = v___x_1716_;
v_a_1534_ = v_a_1841_;
goto v___jp_1531_;
}
}
else
{
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1842_ = lean_box(0);
v___x_1843_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1842_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1542_ = v_a_1580_;
v___y_1543_ = v___x_1716_;
v___y_1544_ = v___x_1843_;
goto v___jp_1541_;
}
else
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1844_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41);
v___x_1845_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1515_, v___x_1844_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; lean_object* v___x_1847_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_a_1846_);
lean_dec_ref_known(v___x_1845_, 1);
v___x_1847_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1846_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1542_ = v_a_1580_;
v___y_1543_ = v___x_1716_;
v___y_1544_ = v___x_1847_;
goto v___jp_1541_;
}
else
{
v___y_1542_ = v_a_1580_;
v___y_1543_ = v___x_1716_;
v___y_1544_ = v___x_1845_;
goto v___jp_1541_;
}
}
}
}
else
{
lean_object* v_a_1848_; 
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_1848_ = lean_ctor_get(v___x_1717_, 0);
lean_inc(v_a_1848_);
lean_dec_ref_known(v___x_1717_, 1);
v___y_1532_ = v_a_1580_;
v___y_1533_ = v___x_1716_;
v_a_1534_ = v_a_1848_;
goto v___jp_1531_;
}
}
}
else
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
lean_dec_ref(v___f_1514_);
lean_dec(v_mvarId_1305_);
lean_dec(v_declName_1304_);
v_a_1849_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1579_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1579_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_a_1849_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
}
v___jp_1311_:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = lean_box(0);
v___x_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
return v___x_1313_;
}
v___jp_1314_:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = lean_box(0);
v___x_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1315_);
return v___x_1316_;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(lean_object* v_declName_2074_, lean_object* v_as_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
if (lean_obj_tag(v_as_2075_) == 0)
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
lean_dec(v_declName_2074_);
v___x_2081_ = lean_box(0);
v___x_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
return v___x_2082_;
}
else
{
lean_object* v_head_2083_; lean_object* v_tail_2084_; lean_object* v___x_2085_; 
v_head_2083_ = lean_ctor_get(v_as_2075_, 0);
lean_inc(v_head_2083_);
v_tail_2084_ = lean_ctor_get(v_as_2075_, 1);
lean_inc(v_tail_2084_);
lean_dec_ref_known(v_as_2075_, 2);
lean_inc(v_declName_2074_);
v___x_2085_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2074_, v_head_2083_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_dec_ref_known(v___x_2085_, 1);
v_as_2075_ = v_tail_2084_;
goto _start;
}
else
{
lean_dec(v_tail_2084_);
lean_dec(v_declName_2074_);
return v___x_2085_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___boxed(lean_object* v_declName_2087_, lean_object* v_as_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
lean_object* v_res_2094_; 
v_res_2094_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_2087_, v_as_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___boxed(lean_object* v_declName_2095_, lean_object* v_as_2096_, lean_object* v_i_2097_, lean_object* v_stop_2098_, lean_object* v_b_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
size_t v_i_boxed_2105_; size_t v_stop_boxed_2106_; lean_object* v_res_2107_; 
v_i_boxed_2105_ = lean_unbox_usize(v_i_2097_);
lean_dec(v_i_2097_);
v_stop_boxed_2106_ = lean_unbox_usize(v_stop_2098_);
lean_dec(v_stop_2098_);
v_res_2107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_2095_, v_as_2096_, v_i_boxed_2105_, v_stop_boxed_2106_, v_b_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec_ref(v_as_2096_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5___boxed(lean_object* v_val_2108_, lean_object* v___x_2109_, lean_object* v_declName_2110_, lean_object* v_____r_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_2108_, v___x_2109_, v_declName_2110_, v_____r_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec(v___x_2109_);
lean_dec_ref(v_val_2108_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___boxed(lean_object* v_declName_2118_, lean_object* v_mvarId_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_){
_start:
{
lean_object* v_res_2125_; 
v_res_2125_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2118_, v_mvarId_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_);
lean_dec(v_a_2123_);
lean_dec_ref(v_a_2122_);
lean_dec(v_a_2121_);
lean_dec_ref(v_a_2120_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6(lean_object* v_00_u03b1_2126_, lean_object* v_x_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v___x_2133_; 
v___x_2133_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(v_x_2127_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___boxed(lean_object* v_00_u03b1_2134_, lean_object* v_x_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_){
_start:
{
lean_object* v_res_2141_; 
v_res_2141_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6(v_00_u03b1_2134_, v_x_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(lean_object* v_constName_2142_, uint8_t v_skipRealize_2143_, lean_object* v___y_2144_){
_start:
{
lean_object* v___x_2146_; lean_object* v_env_2147_; uint8_t v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2146_ = lean_st_ref_get(v___y_2144_);
v_env_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc_ref(v_env_2147_);
lean_dec(v___x_2146_);
v___x_2148_ = l_Lean_Environment_contains(v_env_2147_, v_constName_2142_, v_skipRealize_2143_);
v___x_2149_ = lean_box(v___x_2148_);
v___x_2150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2149_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg___boxed(lean_object* v_constName_2151_, lean_object* v_skipRealize_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_){
_start:
{
uint8_t v_skipRealize_boxed_2155_; lean_object* v_res_2156_; 
v_skipRealize_boxed_2155_ = lean_unbox(v_skipRealize_2152_);
v_res_2156_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(v_constName_2151_, v_skipRealize_boxed_2155_, v___y_2153_);
lean_dec(v___y_2153_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0(lean_object* v_constName_2157_, uint8_t v_skipRealize_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v___x_2164_; 
v___x_2164_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(v_constName_2157_, v_skipRealize_2158_, v___y_2162_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___boxed(lean_object* v_constName_2165_, lean_object* v_skipRealize_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
uint8_t v_skipRealize_boxed_2172_; lean_object* v_res_2173_; 
v_skipRealize_boxed_2172_ = lean_unbox(v_skipRealize_2166_);
v_res_2173_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0(v_constName_2165_, v_skipRealize_boxed_2172_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0(lean_object* v_snd_2174_, lean_object* v___x_2175_, lean_object* v___x_2176_, lean_object* v_snd_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
lean_object* v___x_2183_; 
lean_inc_ref(v_snd_2174_);
v___x_2183_ = l_Lean_Meta_mkCongrArg(v_snd_2174_, v___x_2175_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v_a_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_a_2184_);
lean_dec_ref_known(v___x_2183_, 1);
v___x_2185_ = l_Lean_Expr_app___override(v_snd_2174_, v___x_2176_);
v___x_2186_ = l_Lean_MVarId_replaceTargetEq(v_snd_2177_, v___x_2185_, v_a_2184_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
return v___x_2186_;
}
else
{
lean_object* v_a_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2194_; 
lean_dec(v_snd_2177_);
lean_dec_ref(v___x_2176_);
lean_dec_ref(v_snd_2174_);
v_a_2187_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2189_ = v___x_2183_;
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_a_2187_);
lean_dec(v___x_2183_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2192_; 
if (v_isShared_2190_ == 0)
{
v___x_2192_ = v___x_2189_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_a_2187_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0___boxed(lean_object* v_snd_2195_, lean_object* v___x_2196_, lean_object* v___x_2197_, lean_object* v_snd_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0(v_snd_2195_, v___x_2196_, v___x_2197_, v_snd_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
return v_res_2204_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2210_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__3));
v___x_2211_ = l_Lean_stringToMessageData(v___x_2210_);
return v___x_2211_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6(void){
_start:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2213_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__5));
v___x_2214_ = l_Lean_stringToMessageData(v___x_2213_);
return v___x_2214_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8(void){
_start:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2216_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__7));
v___x_2217_ = l_Lean_stringToMessageData(v___x_2216_);
return v___x_2217_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10(void){
_start:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2219_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__9));
v___x_2220_ = l_Lean_stringToMessageData(v___x_2219_);
return v___x_2220_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12(void){
_start:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2222_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__11));
v___x_2223_ = l_Lean_stringToMessageData(v___x_2222_);
return v___x_2223_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14(void){
_start:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2225_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__13));
v___x_2226_ = l_Lean_stringToMessageData(v___x_2225_);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1(lean_object* v_mvarId_2227_, lean_object* v___x_2228_, lean_object* v_cls_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_){
_start:
{
lean_object* v___x_2235_; 
lean_inc(v_mvarId_2227_);
v___x_2235_ = l_Lean_MVarId_getType(v_mvarId_2227_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; lean_object* v___x_2237_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_a_2236_);
lean_dec_ref_known(v___x_2235_, 1);
v___x_2237_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS(v_a_2236_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v_a_2238_; lean_object* v_fst_2239_; lean_object* v_snd_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2394_; 
v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
lean_inc(v_a_2238_);
lean_dec_ref_known(v___x_2237_, 1);
v_fst_2239_ = lean_ctor_get(v_a_2238_, 0);
v_snd_2240_ = lean_ctor_get(v_a_2238_, 1);
v_isSharedCheck_2394_ = !lean_is_exclusive(v_a_2238_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2242_ = v_a_2238_;
v_isShared_2243_ = v_isSharedCheck_2394_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_snd_2240_);
lean_inc(v_fst_2239_);
lean_dec(v_a_2238_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2394_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v_dummy_2249_; lean_object* v_nargs_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; uint8_t v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2260_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; lean_object* v___y_2296_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2299_; uint8_t v___x_2368_; lean_object* v___x_2369_; lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2393_; 
v___x_2244_ = l_Lean_Expr_getAppFn(v_fst_2239_);
v___x_2245_ = l_Lean_Expr_constName_x21(v___x_2244_);
v___x_2246_ = l_Lean_Expr_constLevels_x21(v___x_2244_);
lean_dec_ref(v___x_2244_);
v___x_2247_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__0));
v___x_2248_ = l_Lean_Name_str___override(v___x_2245_, v___x_2247_);
v_dummy_2249_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0);
v_nargs_2250_ = l_Lean_Expr_getAppNumArgs(v_fst_2239_);
lean_inc(v_nargs_2250_);
v___x_2251_ = lean_mk_array(v_nargs_2250_, v_dummy_2249_);
v___x_2252_ = lean_unsigned_to_nat(1u);
v___x_2253_ = lean_nat_sub(v_nargs_2250_, v___x_2252_);
lean_dec(v_nargs_2250_);
v___x_2254_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_fst_2239_, v___x_2251_, v___x_2253_);
v___x_2368_ = 1;
lean_inc(v___x_2248_);
v___x_2369_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(v___x_2248_, v___x_2368_, v___y_2233_);
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2372_ = v___x_2369_;
v_isShared_2373_ = v_isSharedCheck_2393_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2369_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2393_;
goto v_resetjp_2371_;
}
v___jp_2255_:
{
lean_object* v___x_2264_; 
lean_inc(v___y_2263_);
lean_inc_ref(v___y_2262_);
lean_inc(v___y_2261_);
lean_inc_ref(v___y_2260_);
lean_inc_ref(v___y_2258_);
v___x_2264_ = lean_infer_type(v___y_2258_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v_a_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v_a_2265_ = lean_ctor_get(v___x_2264_, 0);
lean_inc(v_a_2265_);
lean_dec_ref_known(v___x_2264_, 1);
v___x_2266_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__2));
v___x_2267_ = l_Lean_MVarId_define(v_mvarId_2227_, v___x_2266_, v_a_2265_, v___y_2258_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
if (lean_obj_tag(v___x_2267_) == 0)
{
lean_object* v_a_2268_; lean_object* v___x_2269_; 
v_a_2268_ = lean_ctor_get(v___x_2267_, 0);
lean_inc(v_a_2268_);
lean_dec_ref_known(v___x_2267_, 1);
v___x_2269_ = l_Lean_Meta_intro1Core(v_a_2268_, v___y_2256_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; lean_object* v_fst_2271_; lean_object* v_snd_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___f_2277_; lean_object* v___x_2278_; 
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
lean_inc(v_a_2270_);
lean_dec_ref_known(v___x_2269_, 1);
v_fst_2271_ = lean_ctor_get(v_a_2270_, 0);
lean_inc(v_fst_2271_);
v_snd_2272_ = lean_ctor_get(v_a_2270_, 1);
lean_inc_n(v_snd_2272_, 2);
lean_dec(v_a_2270_);
v___x_2273_ = l_Lean_Expr_appFn_x21(v___y_2259_);
lean_dec_ref(v___y_2259_);
v___x_2274_ = l_Lean_mkFVar(v_fst_2271_);
v___x_2275_ = l_Lean_Expr_app___override(v___x_2273_, v___x_2274_);
v___x_2276_ = l_Lean_mkAppN(v___y_2257_, v___x_2254_);
lean_dec_ref(v___x_2254_);
v___f_2277_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2277_, 0, v_snd_2240_);
lean_closure_set(v___f_2277_, 1, v___x_2276_);
lean_closure_set(v___f_2277_, 2, v___x_2275_);
lean_closure_set(v___f_2277_, 3, v_snd_2272_);
v___x_2278_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_snd_2272_, v___f_2277_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
return v___x_2278_;
}
else
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2286_; 
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec_ref(v___y_2257_);
lean_dec_ref(v___x_2254_);
lean_dec(v_snd_2240_);
v_a_2279_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2281_ = v___x_2269_;
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2269_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2284_; 
if (v_isShared_2282_ == 0)
{
v___x_2284_ = v___x_2281_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_a_2279_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
}
}
else
{
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec_ref(v___y_2257_);
lean_dec_ref(v___x_2254_);
lean_dec(v_snd_2240_);
return v___x_2267_;
}
}
else
{
lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2294_; 
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec_ref(v___x_2254_);
lean_dec(v_snd_2240_);
lean_dec(v_mvarId_2227_);
v_a_2287_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2289_ = v___x_2264_;
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2264_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2292_; 
if (v_isShared_2290_ == 0)
{
v___x_2292_ = v___x_2289_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_a_2287_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
}
v___jp_2295_:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; 
lean_inc(v___x_2248_);
v___x_2300_ = l_Lean_mkConst(v___x_2248_, v___x_2246_);
lean_inc(v___y_2299_);
lean_inc_ref(v___y_2298_);
lean_inc(v___y_2297_);
lean_inc_ref(v___y_2296_);
lean_inc_ref(v___x_2300_);
v___x_2301_ = lean_infer_type(v___x_2300_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v___x_2303_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
lean_inc(v_a_2302_);
lean_dec_ref_known(v___x_2301_, 1);
v___x_2303_ = l_Lean_Meta_instantiateForall(v_a_2302_, v___x_2254_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v_a_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; uint8_t v___x_2307_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_a_2304_);
lean_dec_ref_known(v___x_2303_, 1);
v___x_2305_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__1));
v___x_2306_ = lean_unsigned_to_nat(3u);
v___x_2307_ = l_Lean_Expr_isAppOfArity(v_a_2304_, v___x_2305_, v___x_2306_);
if (v___x_2307_ == 0)
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2311_; 
lean_dec(v_a_2304_);
lean_dec_ref(v___x_2300_);
lean_dec_ref(v___x_2254_);
lean_dec(v_snd_2240_);
lean_dec(v_cls_2229_);
v___x_2308_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4);
v___x_2309_ = l_Lean_MessageData_ofName(v___x_2248_);
if (v_isShared_2243_ == 0)
{
lean_ctor_set_tag(v___x_2242_, 7);
lean_ctor_set(v___x_2242_, 1, v___x_2309_);
lean_ctor_set(v___x_2242_, 0, v___x_2308_);
v___x_2311_ = v___x_2242_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v___x_2308_);
lean_ctor_set(v_reuseFailAlloc_2317_, 1, v___x_2309_);
v___x_2311_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2312_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6);
v___x_2313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2311_);
lean_ctor_set(v___x_2313_, 1, v___x_2312_);
v___x_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2314_, 0, v_mvarId_2227_);
v___x_2315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2313_);
lean_ctor_set(v___x_2315_, 1, v___x_2314_);
v___x_2316_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_2315_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
return v___x_2316_;
}
}
else
{
lean_object* v_toCold_2318_; lean_object* v_options_2319_; lean_object* v_inheritedTraceOptions_2320_; uint8_t v_hasTrace_2321_; lean_object* v___x_2322_; lean_object* v_nargs_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
lean_dec(v___x_2248_);
v_toCold_2318_ = lean_ctor_get(v___y_2298_, 0);
v_options_2319_ = lean_ctor_get(v_toCold_2318_, 2);
v_inheritedTraceOptions_2320_ = lean_ctor_get(v_toCold_2318_, 11);
v_hasTrace_2321_ = lean_ctor_get_uint8(v_options_2319_, sizeof(void*)*1);
v___x_2322_ = l_Lean_Expr_appArg_x21(v_a_2304_);
lean_dec(v_a_2304_);
v_nargs_2323_ = l_Lean_Expr_getAppNumArgs(v___x_2322_);
lean_inc(v_nargs_2323_);
v___x_2324_ = lean_mk_array(v_nargs_2323_, v_dummy_2249_);
v___x_2325_ = lean_nat_sub(v_nargs_2323_, v___x_2252_);
lean_dec(v_nargs_2323_);
lean_inc_ref(v___x_2322_);
v___x_2326_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_2322_, v___x_2324_, v___x_2325_);
v___x_2327_ = lean_array_get_size(v___x_2326_);
v___x_2328_ = lean_nat_sub(v___x_2327_, v___x_2252_);
v___x_2329_ = lean_array_get(v___x_2228_, v___x_2326_, v___x_2328_);
lean_dec(v___x_2328_);
lean_dec_ref(v___x_2326_);
if (v_hasTrace_2321_ == 0)
{
lean_del_object(v___x_2242_);
lean_dec(v_cls_2229_);
v___y_2256_ = v___x_2307_;
v___y_2257_ = v___x_2300_;
v___y_2258_ = v___x_2329_;
v___y_2259_ = v___x_2322_;
v___y_2260_ = v___y_2296_;
v___y_2261_ = v___y_2297_;
v___y_2262_ = v___y_2298_;
v___y_2263_ = v___y_2299_;
goto v___jp_2255_;
}
else
{
lean_object* v___x_2330_; lean_object* v___x_2331_; uint8_t v___x_2332_; 
v___x_2330_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19));
lean_inc(v_cls_2229_);
v___x_2331_ = l_Lean_Name_append(v___x_2330_, v_cls_2229_);
v___x_2332_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2320_, v_options_2319_, v___x_2331_);
lean_dec(v___x_2331_);
if (v___x_2332_ == 0)
{
lean_del_object(v___x_2242_);
lean_dec(v_cls_2229_);
v___y_2256_ = v___x_2307_;
v___y_2257_ = v___x_2300_;
v___y_2258_ = v___x_2329_;
v___y_2259_ = v___x_2322_;
v___y_2260_ = v___y_2296_;
v___y_2261_ = v___y_2297_;
v___y_2262_ = v___y_2298_;
v___y_2263_ = v___y_2299_;
goto v___jp_2255_;
}
else
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2337_; 
v___x_2333_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8);
v___x_2334_ = lean_unsigned_to_nat(30u);
lean_inc(v___x_2329_);
v___x_2335_ = l_Lean_inlineExpr(v___x_2329_, v___x_2334_);
if (v_isShared_2243_ == 0)
{
lean_ctor_set_tag(v___x_2242_, 7);
lean_ctor_set(v___x_2242_, 1, v___x_2335_);
lean_ctor_set(v___x_2242_, 0, v___x_2333_);
v___x_2337_ = v___x_2242_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2333_);
lean_ctor_set(v_reuseFailAlloc_2351_, 1, v___x_2335_);
v___x_2337_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2338_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10);
v___x_2339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2337_);
lean_ctor_set(v___x_2339_, 1, v___x_2338_);
lean_inc_ref(v___x_2322_);
v___x_2340_ = l_Lean_indentExpr(v___x_2322_);
v___x_2341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2339_);
lean_ctor_set(v___x_2341_, 1, v___x_2340_);
v___x_2342_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_2229_, v___x_2341_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_dec_ref_known(v___x_2342_, 1);
v___y_2256_ = v___x_2307_;
v___y_2257_ = v___x_2300_;
v___y_2258_ = v___x_2329_;
v___y_2259_ = v___x_2322_;
v___y_2260_ = v___y_2296_;
v___y_2261_ = v___y_2297_;
v___y_2262_ = v___y_2298_;
v___y_2263_ = v___y_2299_;
goto v___jp_2255_;
}
else
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2350_; 
lean_dec(v___x_2329_);
lean_dec_ref(v___x_2322_);
lean_dec_ref(v___x_2300_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec_ref(v___x_2254_);
lean_dec(v_snd_2240_);
lean_dec(v_mvarId_2227_);
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2345_ = v___x_2342_;
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2342_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2348_; 
if (v_isShared_2346_ == 0)
{
v___x_2348_ = v___x_2345_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_a_2343_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
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
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2359_; 
lean_dec_ref(v___x_2300_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec_ref(v___x_2254_);
lean_dec(v___x_2248_);
lean_del_object(v___x_2242_);
lean_dec(v_snd_2240_);
lean_dec(v_cls_2229_);
lean_dec(v_mvarId_2227_);
v_a_2352_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2354_ = v___x_2303_;
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2303_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2352_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_dec_ref(v___x_2300_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec_ref(v___x_2254_);
lean_dec(v___x_2248_);
lean_del_object(v___x_2242_);
lean_dec(v_snd_2240_);
lean_dec(v_cls_2229_);
lean_dec(v_mvarId_2227_);
v_a_2360_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2301_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2301_);
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
v_resetjp_2371_:
{
uint8_t v___x_2374_; 
v___x_2374_ = lean_unbox(v_a_2370_);
lean_dec(v_a_2370_);
if (v___x_2374_ == 0)
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2381_; 
lean_dec_ref(v___x_2254_);
lean_dec(v___x_2246_);
lean_del_object(v___x_2242_);
lean_dec(v_snd_2240_);
lean_dec(v_cls_2229_);
v___x_2375_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12);
v___x_2376_ = l_Lean_MessageData_ofName(v___x_2248_);
v___x_2377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2375_);
lean_ctor_set(v___x_2377_, 1, v___x_2376_);
v___x_2378_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14);
v___x_2379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2377_);
lean_ctor_set(v___x_2379_, 1, v___x_2378_);
if (v_isShared_2373_ == 0)
{
lean_ctor_set_tag(v___x_2372_, 1);
lean_ctor_set(v___x_2372_, 0, v_mvarId_2227_);
v___x_2381_ = v___x_2372_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_mvarId_2227_);
v___x_2381_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2391_; 
v___x_2382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2379_);
lean_ctor_set(v___x_2382_, 1, v___x_2381_);
v___x_2383_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_2382_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
v_a_2384_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2386_ = v___x_2383_;
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2383_);
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
lean_del_object(v___x_2372_);
v___y_2296_ = v___y_2230_;
v___y_2297_ = v___y_2231_;
v___y_2298_ = v___y_2232_;
v___y_2299_ = v___y_2233_;
goto v___jp_2295_;
}
}
}
}
else
{
lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2402_; 
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v_cls_2229_);
lean_dec(v_mvarId_2227_);
v_a_2395_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2397_ = v___x_2237_;
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2237_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2400_; 
if (v_isShared_2398_ == 0)
{
v___x_2400_ = v___x_2397_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_a_2395_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
}
else
{
lean_object* v_a_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2410_; 
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v_cls_2229_);
lean_dec(v_mvarId_2227_);
v_a_2403_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2410_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2410_ == 0)
{
v___x_2405_ = v___x_2235_;
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_a_2403_);
lean_dec(v___x_2235_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2408_; 
if (v_isShared_2406_ == 0)
{
v___x_2408_ = v___x_2405_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_a_2403_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
return v___x_2408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___boxed(lean_object* v_mvarId_2411_, lean_object* v___x_2412_, lean_object* v_cls_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1(v_mvarId_2411_, v___x_2412_, v_cls_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_);
lean_dec_ref(v___x_2412_);
return v_res_2419_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2421_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__0));
v___x_2422_ = l_Lean_stringToMessageData(v___x_2421_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2(lean_object* v_mvarId_2423_, lean_object* v_x_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2430_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1);
v___x_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2431_, 0, v_mvarId_2423_);
v___x_2432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2432_, 0, v___x_2430_);
lean_ctor_set(v___x_2432_, 1, v___x_2431_);
v___x_2433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2432_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___boxed(lean_object* v_mvarId_2434_, lean_object* v_x_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2(v_mvarId_2434_, v_x_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
lean_dec_ref(v_x_2435_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(lean_object* v_declName_2442_, lean_object* v_mvarId_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_){
_start:
{
lean_object* v_toCold_2449_; lean_object* v_options_2450_; lean_object* v_inheritedTraceOptions_2451_; uint8_t v_hasTrace_2452_; lean_object* v___x_2453_; lean_object* v_cls_2454_; lean_object* v___f_2455_; 
v_toCold_2449_ = lean_ctor_get(v_a_2446_, 0);
v_options_2450_ = lean_ctor_get(v_toCold_2449_, 2);
v_inheritedTraceOptions_2451_ = lean_ctor_get(v_toCold_2449_, 11);
v_hasTrace_2452_ = lean_ctor_get_uint8(v_options_2450_, sizeof(void*)*1);
v___x_2453_ = l_Lean_instInhabitedExpr;
v_cls_2454_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17));
lean_inc(v_mvarId_2443_);
v___f_2455_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___boxed), 8, 3);
lean_closure_set(v___f_2455_, 0, v_mvarId_2443_);
lean_closure_set(v___f_2455_, 1, v___x_2453_);
lean_closure_set(v___f_2455_, 2, v_cls_2454_);
if (v_hasTrace_2452_ == 0)
{
lean_object* v___x_2456_; 
v___x_2456_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2443_, v___f_2455_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_object* v_a_2457_; lean_object* v___x_2458_; 
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
lean_inc(v_a_2457_);
lean_dec_ref_known(v___x_2456_, 1);
v___x_2458_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2442_, v_a_2457_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_);
return v___x_2458_;
}
else
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2466_; 
lean_dec(v_declName_2442_);
v_a_2459_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2461_ = v___x_2456_;
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2456_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
if (v_isShared_2462_ == 0)
{
v___x_2464_ = v___x_2461_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_a_2459_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
else
{
lean_object* v___f_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; uint8_t v___x_2470_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v_a_2474_; lean_object* v___y_2487_; lean_object* v___y_2488_; lean_object* v_a_2489_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v_a_2494_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v_a_2506_; 
lean_inc(v_mvarId_2443_);
v___f_2467_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2467_, 0, v_mvarId_2443_);
v___x_2468_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__1));
v___x_2469_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20);
v___x_2470_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2451_, v_options_2450_, v___x_2469_);
if (v___x_2470_ == 0)
{
lean_object* v___x_2541_; uint8_t v___x_2542_; 
v___x_2541_ = l_Lean_trace_profiler;
v___x_2542_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_2450_, v___x_2541_);
if (v___x_2542_ == 0)
{
lean_object* v___x_2543_; 
lean_dec_ref(v___f_2467_);
v___x_2543_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2443_, v___f_2455_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v_a_2544_; lean_object* v___x_2545_; 
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc(v_a_2544_);
lean_dec_ref_known(v___x_2543_, 1);
v___x_2545_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2442_, v_a_2544_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_);
return v___x_2545_;
}
else
{
lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2553_; 
lean_dec(v_declName_2442_);
v_a_2546_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2548_ = v___x_2543_;
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___x_2543_);
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
else
{
goto v___jp_2508_;
}
}
else
{
goto v___jp_2508_;
}
v___jp_2471_:
{
lean_object* v___x_2475_; double v___x_2476_; double v___x_2477_; double v___x_2478_; double v___x_2479_; double v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; 
v___x_2475_ = lean_io_mono_nanos_now();
v___x_2476_ = lean_float_of_nat(v___y_2473_);
v___x_2477_ = lean_float_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21);
v___x_2478_ = lean_float_div(v___x_2476_, v___x_2477_);
v___x_2479_ = lean_float_of_nat(v___x_2475_);
v___x_2480_ = lean_float_div(v___x_2479_, v___x_2477_);
v___x_2481_ = lean_box_float(v___x_2478_);
v___x_2482_ = lean_box_float(v___x_2480_);
v___x_2483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2481_);
lean_ctor_set(v___x_2483_, 1, v___x_2482_);
v___x_2484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2484_, 0, v_a_2474_);
lean_ctor_set(v___x_2484_, 1, v___x_2483_);
v___x_2485_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_2454_, v_hasTrace_2452_, v___x_2468_, v_options_2450_, v___x_2470_, v___y_2472_, v___f_2467_, v___x_2484_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_);
return v___x_2485_;
}
v___jp_2486_:
{
lean_object* v___x_2490_; 
v___x_2490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2490_, 0, v_a_2489_);
v___y_2472_ = v___y_2487_;
v___y_2473_ = v___y_2488_;
v_a_2474_ = v___x_2490_;
goto v___jp_2471_;
}
v___jp_2491_:
{
lean_object* v___x_2495_; double v___x_2496_; double v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2495_ = lean_io_get_num_heartbeats();
v___x_2496_ = lean_float_of_nat(v___y_2492_);
v___x_2497_ = lean_float_of_nat(v___x_2495_);
v___x_2498_ = lean_box_float(v___x_2496_);
v___x_2499_ = lean_box_float(v___x_2497_);
v___x_2500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2498_);
lean_ctor_set(v___x_2500_, 1, v___x_2499_);
v___x_2501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2501_, 0, v_a_2494_);
lean_ctor_set(v___x_2501_, 1, v___x_2500_);
v___x_2502_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_2454_, v_hasTrace_2452_, v___x_2468_, v_options_2450_, v___x_2470_, v___y_2493_, v___f_2467_, v___x_2501_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_);
return v___x_2502_;
}
v___jp_2503_:
{
lean_object* v___x_2507_; 
v___x_2507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2507_, 0, v_a_2506_);
v___y_2492_ = v___y_2504_;
v___y_2493_ = v___y_2505_;
v_a_2494_ = v___x_2507_;
goto v___jp_2491_;
}
v___jp_2508_:
{
lean_object* v___x_2509_; lean_object* v_a_2510_; lean_object* v___x_2511_; uint8_t v___x_2512_; 
v___x_2509_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(v_a_2447_);
v_a_2510_ = lean_ctor_get(v___x_2509_, 0);
lean_inc(v_a_2510_);
lean_dec_ref(v___x_2509_);
v___x_2511_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2512_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_2450_, v___x_2511_);
if (v___x_2512_ == 0)
{
lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2513_ = lean_io_mono_nanos_now();
v___x_2514_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2443_, v___f_2455_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v_a_2515_; lean_object* v___x_2516_; 
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_a_2515_);
lean_dec_ref_known(v___x_2514_, 1);
v___x_2516_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2442_, v_a_2515_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_);
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_object* v_a_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2524_; 
v_a_2517_ = lean_ctor_get(v___x_2516_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2516_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2519_ = v___x_2516_;
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_a_2517_);
lean_dec(v___x_2516_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2522_; 
if (v_isShared_2520_ == 0)
{
lean_ctor_set_tag(v___x_2519_, 1);
v___x_2522_ = v___x_2519_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_a_2517_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
v___y_2472_ = v_a_2510_;
v___y_2473_ = v___x_2513_;
v_a_2474_ = v___x_2522_;
goto v___jp_2471_;
}
}
}
else
{
lean_object* v_a_2525_; 
v_a_2525_ = lean_ctor_get(v___x_2516_, 0);
lean_inc(v_a_2525_);
lean_dec_ref_known(v___x_2516_, 1);
v___y_2487_ = v_a_2510_;
v___y_2488_ = v___x_2513_;
v_a_2489_ = v_a_2525_;
goto v___jp_2486_;
}
}
else
{
lean_object* v_a_2526_; 
lean_dec(v_declName_2442_);
v_a_2526_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_a_2526_);
lean_dec_ref_known(v___x_2514_, 1);
v___y_2487_ = v_a_2510_;
v___y_2488_ = v___x_2513_;
v_a_2489_ = v_a_2526_;
goto v___jp_2486_;
}
}
else
{
lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2527_ = lean_io_get_num_heartbeats();
v___x_2528_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2443_, v___f_2455_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_object* v_a_2529_; lean_object* v___x_2530_; 
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
lean_inc(v_a_2529_);
lean_dec_ref_known(v___x_2528_, 1);
v___x_2530_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2442_, v_a_2529_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2538_; 
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2533_ = v___x_2530_;
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2530_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2536_; 
if (v_isShared_2534_ == 0)
{
lean_ctor_set_tag(v___x_2533_, 1);
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
v___y_2492_ = v___x_2527_;
v___y_2493_ = v_a_2510_;
v_a_2494_ = v___x_2536_;
goto v___jp_2491_;
}
}
}
else
{
lean_object* v_a_2539_; 
v_a_2539_ = lean_ctor_get(v___x_2530_, 0);
lean_inc(v_a_2539_);
lean_dec_ref_known(v___x_2530_, 1);
v___y_2504_ = v___x_2527_;
v___y_2505_ = v_a_2510_;
v_a_2506_ = v_a_2539_;
goto v___jp_2503_;
}
}
else
{
lean_object* v_a_2540_; 
lean_dec(v_declName_2442_);
v_a_2540_ = lean_ctor_get(v___x_2528_, 0);
lean_inc(v_a_2540_);
lean_dec_ref_known(v___x_2528_, 1);
v___y_2504_ = v___x_2527_;
v___y_2505_ = v_a_2510_;
v_a_2506_ = v_a_2540_;
goto v___jp_2503_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___boxed(lean_object* v_declName_2554_, lean_object* v_mvarId_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(v_declName_2554_, v_mvarId_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_);
lean_dec(v_a_2559_);
lean_dec_ref(v_a_2558_);
lean_dec(v_a_2557_);
lean_dec_ref(v_a_2556_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(lean_object* v_e_2562_, lean_object* v___y_2563_){
_start:
{
uint8_t v___x_2565_; 
v___x_2565_ = l_Lean_Expr_hasMVar(v_e_2562_);
if (v___x_2565_ == 0)
{
lean_object* v___x_2566_; 
v___x_2566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2566_, 0, v_e_2562_);
return v___x_2566_;
}
else
{
lean_object* v___x_2567_; lean_object* v_mctx_2568_; lean_object* v___x_2569_; lean_object* v_fst_2570_; lean_object* v_snd_2571_; lean_object* v___x_2572_; lean_object* v_cache_2573_; lean_object* v_zetaDeltaFVarIds_2574_; lean_object* v_postponed_2575_; lean_object* v_diag_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2585_; 
v___x_2567_ = lean_st_ref_get(v___y_2563_);
v_mctx_2568_ = lean_ctor_get(v___x_2567_, 0);
lean_inc_ref(v_mctx_2568_);
lean_dec(v___x_2567_);
v___x_2569_ = l_Lean_instantiateMVarsCore(v_mctx_2568_, v_e_2562_);
v_fst_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc(v_fst_2570_);
v_snd_2571_ = lean_ctor_get(v___x_2569_, 1);
lean_inc(v_snd_2571_);
lean_dec_ref(v___x_2569_);
v___x_2572_ = lean_st_ref_take(v___y_2563_);
v_cache_2573_ = lean_ctor_get(v___x_2572_, 1);
v_zetaDeltaFVarIds_2574_ = lean_ctor_get(v___x_2572_, 2);
v_postponed_2575_ = lean_ctor_get(v___x_2572_, 3);
v_diag_2576_ = lean_ctor_get(v___x_2572_, 4);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2585_ == 0)
{
lean_object* v_unused_2586_; 
v_unused_2586_ = lean_ctor_get(v___x_2572_, 0);
lean_dec(v_unused_2586_);
v___x_2578_ = v___x_2572_;
v_isShared_2579_ = v_isSharedCheck_2585_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_diag_2576_);
lean_inc(v_postponed_2575_);
lean_inc(v_zetaDeltaFVarIds_2574_);
lean_inc(v_cache_2573_);
lean_dec(v___x_2572_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2585_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2581_; 
if (v_isShared_2579_ == 0)
{
lean_ctor_set(v___x_2578_, 0, v_snd_2571_);
v___x_2581_ = v___x_2578_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_snd_2571_);
lean_ctor_set(v_reuseFailAlloc_2584_, 1, v_cache_2573_);
lean_ctor_set(v_reuseFailAlloc_2584_, 2, v_zetaDeltaFVarIds_2574_);
lean_ctor_set(v_reuseFailAlloc_2584_, 3, v_postponed_2575_);
lean_ctor_set(v_reuseFailAlloc_2584_, 4, v_diag_2576_);
v___x_2581_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2582_ = lean_st_ref_put(v___y_2563_, v___x_2581_);
v___x_2583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2583_, 0, v_fst_2570_);
return v___x_2583_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg___boxed(lean_object* v_e_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
lean_object* v_res_2590_; 
v_res_2590_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_e_2587_, v___y_2588_);
lean_dec(v___y_2588_);
return v_res_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0(lean_object* v_e_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_){
_start:
{
lean_object* v___x_2597_; 
v___x_2597_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_e_2591_, v___y_2593_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___boxed(lean_object* v_e_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0(v_e_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(lean_object* v_k_2605_, uint8_t v_allowLevelAssignments_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
lean_object* v___x_2612_; 
v___x_2612_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2606_, v_k_2605_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2612_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2612_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2618_; 
if (v_isShared_2616_ == 0)
{
v___x_2618_ = v___x_2615_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_a_2613_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
else
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
v_a_2621_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___x_2612_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2612_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2626_; 
if (v_isShared_2624_ == 0)
{
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_a_2621_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg___boxed(lean_object* v_k_2629_, lean_object* v_allowLevelAssignments_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2636_; lean_object* v_res_2637_; 
v_allowLevelAssignments_boxed_2636_ = lean_unbox(v_allowLevelAssignments_2630_);
v_res_2637_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(v_k_2629_, v_allowLevelAssignments_boxed_2636_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
return v_res_2637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1(lean_object* v_00_u03b1_2638_, lean_object* v_k_2639_, uint8_t v_allowLevelAssignments_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v___x_2646_; 
v___x_2646_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(v_k_2639_, v_allowLevelAssignments_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
return v___x_2646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___boxed(lean_object* v_00_u03b1_2647_, lean_object* v_k_2648_, lean_object* v_allowLevelAssignments_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2655_; lean_object* v_res_2656_; 
v_allowLevelAssignments_boxed_2655_ = lean_unbox(v_allowLevelAssignments_2649_);
v_res_2656_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1(v_00_u03b1_2647_, v_k_2648_, v_allowLevelAssignments_boxed_2655_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__0(lean_object* v___x_2657_, lean_object* v_e_2658_){
_start:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2659_ = l_Lean_indentD(v_e_2658_);
v___x_2660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2657_);
lean_ctor_set(v___x_2660_, 1, v___x_2659_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1(lean_object* v_type_2661_, lean_object* v___x_2662_, lean_object* v_declName_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_){
_start:
{
lean_object* v___x_2669_; 
v___x_2669_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_2661_, v___x_2662_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_);
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v_a_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v_a_2670_ = lean_ctor_get(v___x_2669_, 0);
lean_inc(v_a_2670_);
lean_dec_ref_known(v___x_2669_, 1);
v___x_2671_ = l_Lean_Expr_mvarId_x21(v_a_2670_);
v___x_2672_ = l_Lean_MVarId_intros(v___x_2671_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_a_2673_; lean_object* v_snd_2674_; lean_object* v___x_2675_; 
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_a_2673_);
lean_dec_ref_known(v___x_2672_, 1);
v_snd_2674_ = lean_ctor_get(v_a_2673_, 1);
lean_inc_n(v_snd_2674_, 2);
lean_dec(v_a_2673_);
v___x_2675_ = l_Lean_Elab_Eqns_tryURefl(v_snd_2674_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v_a_2676_; uint8_t v___x_2677_; 
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_a_2676_);
lean_dec_ref_known(v___x_2675_, 1);
v___x_2677_ = lean_unbox(v_a_2676_);
lean_dec(v_a_2676_);
if (v___x_2677_ == 0)
{
lean_object* v___x_2678_; 
v___x_2678_ = l_Lean_Elab_Eqns_deltaLHS(v_snd_2674_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; lean_object* v___x_2680_; 
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
lean_inc(v_a_2679_);
lean_dec_ref_known(v___x_2678_, 1);
v___x_2680_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(v_declName_2663_, v_a_2679_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v___x_2681_; 
lean_dec_ref_known(v___x_2680_, 1);
v___x_2681_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_a_2670_, v___y_2665_);
return v___x_2681_;
}
else
{
lean_object* v_a_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2689_; 
lean_dec(v_a_2670_);
v_a_2682_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2684_ = v___x_2680_;
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_a_2682_);
lean_dec(v___x_2680_);
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
lean_dec(v_a_2670_);
lean_dec(v_declName_2663_);
v_a_2690_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2692_ = v___x_2678_;
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v___x_2678_);
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
else
{
lean_object* v___x_2698_; 
lean_dec(v_snd_2674_);
lean_dec(v_declName_2663_);
v___x_2698_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_a_2670_, v___y_2665_);
return v___x_2698_;
}
}
else
{
lean_object* v_a_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2706_; 
lean_dec(v_snd_2674_);
lean_dec(v_a_2670_);
lean_dec(v_declName_2663_);
v_a_2699_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2701_ = v___x_2675_;
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_a_2699_);
lean_dec(v___x_2675_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v___x_2704_; 
if (v_isShared_2702_ == 0)
{
v___x_2704_ = v___x_2701_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_a_2699_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
}
}
else
{
lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2714_; 
lean_dec(v_a_2670_);
lean_dec(v_declName_2663_);
v_a_2707_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2709_ = v___x_2672_;
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_dec(v___x_2672_);
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
}
else
{
lean_dec(v_declName_2663_);
return v___x_2669_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1___boxed(lean_object* v_type_2715_, lean_object* v___x_2716_, lean_object* v_declName_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1(v_type_2715_, v___x_2716_, v_declName_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
return v_res_2723_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2725_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__0));
v___x_2726_ = l_Lean_stringToMessageData(v___x_2725_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2(lean_object* v_type_2727_, lean_object* v_x_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_){
_start:
{
lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2734_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1);
v___x_2735_ = l_Lean_indentExpr(v_type_2727_);
v___x_2736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2734_);
lean_ctor_set(v___x_2736_, 1, v___x_2735_);
v___x_2737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2736_);
return v___x_2737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___boxed(lean_object* v_type_2738_, lean_object* v_x_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_){
_start:
{
lean_object* v_res_2745_; 
v_res_2745_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2(v_type_2738_, v_x_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec_ref(v_x_2739_);
return v_res_2745_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2(lean_object* v_e_2746_){
_start:
{
if (lean_obj_tag(v_e_2746_) == 0)
{
uint8_t v___x_2747_; 
v___x_2747_ = 2;
return v___x_2747_;
}
else
{
lean_object* v_a_2748_; uint8_t v___x_2749_; 
v_a_2748_ = lean_ctor_get(v_e_2746_, 0);
v___x_2749_ = l_Lean_Expr_hasSyntheticSorry(v_a_2748_);
if (v___x_2749_ == 0)
{
uint8_t v___x_2750_; 
v___x_2750_ = 0;
return v___x_2750_;
}
else
{
uint8_t v___x_2751_; 
v___x_2751_ = 1;
return v___x_2751_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2___boxed(lean_object* v_e_2752_){
_start:
{
uint8_t v_res_2753_; lean_object* v_r_2754_; 
v_res_2753_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2(v_e_2752_);
lean_dec_ref(v_e_2752_);
v_r_2754_ = lean_box(v_res_2753_);
return v_r_2754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(lean_object* v_cls_2755_, uint8_t v_collapsed_2756_, lean_object* v_tag_2757_, lean_object* v_opts_2758_, uint8_t v_clsEnabled_2759_, lean_object* v_oldTraces_2760_, lean_object* v_msg_2761_, lean_object* v_resStartStop_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_){
_start:
{
lean_object* v_fst_2768_; lean_object* v_snd_2769_; lean_object* v___y_2771_; lean_object* v___y_2772_; lean_object* v_data_2773_; lean_object* v_fst_2784_; lean_object* v_snd_2785_; lean_object* v___x_2786_; uint8_t v___x_2787_; lean_object* v___y_2789_; lean_object* v_a_2790_; uint8_t v___y_2805_; double v___y_2837_; 
v_fst_2768_ = lean_ctor_get(v_resStartStop_2762_, 0);
lean_inc(v_fst_2768_);
v_snd_2769_ = lean_ctor_get(v_resStartStop_2762_, 1);
lean_inc(v_snd_2769_);
lean_dec_ref(v_resStartStop_2762_);
v_fst_2784_ = lean_ctor_get(v_snd_2769_, 0);
lean_inc(v_fst_2784_);
v_snd_2785_ = lean_ctor_get(v_snd_2769_, 1);
lean_inc(v_snd_2785_);
lean_dec(v_snd_2769_);
v___x_2786_ = l_Lean_trace_profiler;
v___x_2787_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_opts_2758_, v___x_2786_);
if (v___x_2787_ == 0)
{
v___y_2805_ = v___x_2787_;
goto v___jp_2804_;
}
else
{
lean_object* v___x_2842_; uint8_t v___x_2843_; 
v___x_2842_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2843_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_opts_2758_, v___x_2842_);
if (v___x_2843_ == 0)
{
lean_object* v___x_2844_; lean_object* v___x_2845_; double v___x_2846_; double v___x_2847_; double v___x_2848_; 
v___x_2844_ = l_Lean_trace_profiler_threshold;
v___x_2845_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v_opts_2758_, v___x_2844_);
v___x_2846_ = lean_float_of_nat(v___x_2845_);
v___x_2847_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2);
v___x_2848_ = lean_float_div(v___x_2846_, v___x_2847_);
v___y_2837_ = v___x_2848_;
goto v___jp_2836_;
}
else
{
lean_object* v___x_2849_; lean_object* v___x_2850_; double v___x_2851_; 
v___x_2849_ = l_Lean_trace_profiler_threshold;
v___x_2850_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v_opts_2758_, v___x_2849_);
v___x_2851_ = lean_float_of_nat(v___x_2850_);
v___y_2837_ = v___x_2851_;
goto v___jp_2836_;
}
}
v___jp_2770_:
{
lean_object* v___x_2774_; 
lean_inc(v___y_2772_);
v___x_2774_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5(v_oldTraces_2760_, v_data_2773_, v___y_2772_, v___y_2771_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_);
if (lean_obj_tag(v___x_2774_) == 0)
{
lean_object* v___x_2775_; 
lean_dec_ref_known(v___x_2774_, 1);
v___x_2775_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(v_fst_2768_);
return v___x_2775_;
}
else
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2783_; 
lean_dec(v_fst_2768_);
v_a_2776_ = lean_ctor_get(v___x_2774_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2778_ = v___x_2774_;
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2774_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2781_; 
if (v_isShared_2779_ == 0)
{
v___x_2781_ = v___x_2778_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_a_2776_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
}
v___jp_2788_:
{
uint8_t v_result_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; double v___x_2794_; lean_object* v_data_2795_; 
v_result_2791_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2(v_fst_2768_);
v___x_2792_ = lean_box(v_result_2791_);
v___x_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2792_);
v___x_2794_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0);
lean_inc_ref(v_tag_2757_);
lean_inc_ref(v___x_2793_);
lean_inc(v_cls_2755_);
v_data_2795_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2795_, 0, v_cls_2755_);
lean_ctor_set(v_data_2795_, 1, v___x_2793_);
lean_ctor_set(v_data_2795_, 2, v_tag_2757_);
lean_ctor_set_float(v_data_2795_, sizeof(void*)*3, v___x_2794_);
lean_ctor_set_float(v_data_2795_, sizeof(void*)*3 + 8, v___x_2794_);
lean_ctor_set_uint8(v_data_2795_, sizeof(void*)*3 + 16, v_collapsed_2756_);
if (v___x_2787_ == 0)
{
lean_dec_ref_known(v___x_2793_, 1);
lean_dec(v_snd_2785_);
lean_dec(v_fst_2784_);
lean_dec_ref(v_tag_2757_);
lean_dec(v_cls_2755_);
v___y_2771_ = v_a_2790_;
v___y_2772_ = v___y_2789_;
v_data_2773_ = v_data_2795_;
goto v___jp_2770_;
}
else
{
lean_object* v_data_2796_; double v___x_2797_; double v___x_2798_; 
lean_dec_ref_known(v_data_2795_, 3);
v_data_2796_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2796_, 0, v_cls_2755_);
lean_ctor_set(v_data_2796_, 1, v___x_2793_);
lean_ctor_set(v_data_2796_, 2, v_tag_2757_);
v___x_2797_ = lean_unbox_float(v_fst_2784_);
lean_dec(v_fst_2784_);
lean_ctor_set_float(v_data_2796_, sizeof(void*)*3, v___x_2797_);
v___x_2798_ = lean_unbox_float(v_snd_2785_);
lean_dec(v_snd_2785_);
lean_ctor_set_float(v_data_2796_, sizeof(void*)*3 + 8, v___x_2798_);
lean_ctor_set_uint8(v_data_2796_, sizeof(void*)*3 + 16, v_collapsed_2756_);
v___y_2771_ = v_a_2790_;
v___y_2772_ = v___y_2789_;
v_data_2773_ = v_data_2796_;
goto v___jp_2770_;
}
}
v___jp_2799_:
{
lean_object* v_ref_2800_; lean_object* v___x_2801_; 
v_ref_2800_ = lean_ctor_get(v___y_2765_, 2);
lean_inc(v___y_2766_);
lean_inc_ref(v___y_2765_);
lean_inc(v___y_2764_);
lean_inc_ref(v___y_2763_);
lean_inc(v_fst_2768_);
v___x_2801_ = lean_apply_6(v_msg_2761_, v_fst_2768_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, lean_box(0));
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v_a_2802_; 
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_a_2802_);
lean_dec_ref_known(v___x_2801_, 1);
v___y_2789_ = v_ref_2800_;
v_a_2790_ = v_a_2802_;
goto v___jp_2788_;
}
else
{
lean_object* v___x_2803_; 
lean_dec_ref_known(v___x_2801_, 1);
v___x_2803_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1);
v___y_2789_ = v_ref_2800_;
v_a_2790_ = v___x_2803_;
goto v___jp_2788_;
}
}
v___jp_2804_:
{
if (v_clsEnabled_2759_ == 0)
{
if (v___y_2805_ == 0)
{
lean_object* v___x_2806_; lean_object* v_traceState_2807_; lean_object* v_env_2808_; lean_object* v_nextMacroScope_2809_; lean_object* v_ngen_2810_; lean_object* v_auxDeclNGen_2811_; lean_object* v_cache_2812_; lean_object* v_recordedDeps_2813_; lean_object* v_messages_2814_; lean_object* v_infoState_2815_; lean_object* v_snapshotTasks_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2835_; 
lean_dec(v_snd_2785_);
lean_dec(v_fst_2784_);
lean_dec_ref(v_msg_2761_);
lean_dec_ref(v_tag_2757_);
lean_dec(v_cls_2755_);
v___x_2806_ = lean_st_ref_take(v___y_2766_);
v_traceState_2807_ = lean_ctor_get(v___x_2806_, 4);
v_env_2808_ = lean_ctor_get(v___x_2806_, 0);
v_nextMacroScope_2809_ = lean_ctor_get(v___x_2806_, 1);
v_ngen_2810_ = lean_ctor_get(v___x_2806_, 2);
v_auxDeclNGen_2811_ = lean_ctor_get(v___x_2806_, 3);
v_cache_2812_ = lean_ctor_get(v___x_2806_, 5);
v_recordedDeps_2813_ = lean_ctor_get(v___x_2806_, 6);
v_messages_2814_ = lean_ctor_get(v___x_2806_, 7);
v_infoState_2815_ = lean_ctor_get(v___x_2806_, 8);
v_snapshotTasks_2816_ = lean_ctor_get(v___x_2806_, 9);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2818_ = v___x_2806_;
v_isShared_2819_ = v_isSharedCheck_2835_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_snapshotTasks_2816_);
lean_inc(v_infoState_2815_);
lean_inc(v_messages_2814_);
lean_inc(v_recordedDeps_2813_);
lean_inc(v_cache_2812_);
lean_inc(v_traceState_2807_);
lean_inc(v_auxDeclNGen_2811_);
lean_inc(v_ngen_2810_);
lean_inc(v_nextMacroScope_2809_);
lean_inc(v_env_2808_);
lean_dec(v___x_2806_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2835_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
uint64_t v_tid_2820_; lean_object* v_traces_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2834_; 
v_tid_2820_ = lean_ctor_get_uint64(v_traceState_2807_, sizeof(void*)*1);
v_traces_2821_ = lean_ctor_get(v_traceState_2807_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v_traceState_2807_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2823_ = v_traceState_2807_;
v_isShared_2824_ = v_isSharedCheck_2834_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_traces_2821_);
lean_dec(v_traceState_2807_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2834_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2825_; lean_object* v___x_2827_; 
v___x_2825_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2760_, v_traces_2821_);
lean_dec_ref(v_traces_2821_);
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 0, v___x_2825_);
v___x_2827_ = v___x_2823_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v___x_2825_);
lean_ctor_set_uint64(v_reuseFailAlloc_2833_, sizeof(void*)*1, v_tid_2820_);
v___x_2827_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
lean_object* v___x_2829_; 
if (v_isShared_2819_ == 0)
{
lean_ctor_set(v___x_2818_, 4, v___x_2827_);
v___x_2829_ = v___x_2818_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_env_2808_);
lean_ctor_set(v_reuseFailAlloc_2832_, 1, v_nextMacroScope_2809_);
lean_ctor_set(v_reuseFailAlloc_2832_, 2, v_ngen_2810_);
lean_ctor_set(v_reuseFailAlloc_2832_, 3, v_auxDeclNGen_2811_);
lean_ctor_set(v_reuseFailAlloc_2832_, 4, v___x_2827_);
lean_ctor_set(v_reuseFailAlloc_2832_, 5, v_cache_2812_);
lean_ctor_set(v_reuseFailAlloc_2832_, 6, v_recordedDeps_2813_);
lean_ctor_set(v_reuseFailAlloc_2832_, 7, v_messages_2814_);
lean_ctor_set(v_reuseFailAlloc_2832_, 8, v_infoState_2815_);
lean_ctor_set(v_reuseFailAlloc_2832_, 9, v_snapshotTasks_2816_);
v___x_2829_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2830_ = lean_st_ref_put(v___y_2766_, v___x_2829_);
v___x_2831_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(v_fst_2768_);
return v___x_2831_;
}
}
}
}
}
else
{
goto v___jp_2799_;
}
}
else
{
goto v___jp_2799_;
}
}
v___jp_2836_:
{
double v___x_2838_; double v___x_2839_; double v___x_2840_; uint8_t v___x_2841_; 
v___x_2838_ = lean_unbox_float(v_snd_2785_);
v___x_2839_ = lean_unbox_float(v_fst_2784_);
v___x_2840_ = lean_float_sub(v___x_2838_, v___x_2839_);
v___x_2841_ = lean_float_decLt(v___y_2837_, v___x_2840_);
v___y_2805_ = v___x_2841_;
goto v___jp_2804_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2___boxed(lean_object* v_cls_2852_, lean_object* v_collapsed_2853_, lean_object* v_tag_2854_, lean_object* v_opts_2855_, lean_object* v_clsEnabled_2856_, lean_object* v_oldTraces_2857_, lean_object* v_msg_2858_, lean_object* v_resStartStop_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_){
_start:
{
uint8_t v_collapsed_boxed_2865_; uint8_t v_clsEnabled_boxed_2866_; lean_object* v_res_2867_; 
v_collapsed_boxed_2865_ = lean_unbox(v_collapsed_2853_);
v_clsEnabled_boxed_2866_ = lean_unbox(v_clsEnabled_2856_);
v_res_2867_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(v_cls_2852_, v_collapsed_boxed_2865_, v_tag_2854_, v_opts_2855_, v_clsEnabled_boxed_2866_, v_oldTraces_2857_, v_msg_2858_, v_resStartStop_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
lean_dec(v___y_2863_);
lean_dec_ref(v___y_2862_);
lean_dec(v___y_2861_);
lean_dec_ref(v___y_2860_);
lean_dec_ref(v_opts_2855_);
return v_res_2867_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1(void){
_start:
{
lean_object* v___x_2869_; lean_object* v___x_2870_; 
v___x_2869_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__0));
v___x_2870_ = l_Lean_stringToMessageData(v___x_2869_);
return v___x_2870_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3(void){
_start:
{
lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2872_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__2));
v___x_2873_ = l_Lean_stringToMessageData(v___x_2872_);
return v___x_2873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof(lean_object* v_declName_2874_, lean_object* v_type_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_){
_start:
{
lean_object* v_toCold_2881_; lean_object* v_options_2882_; lean_object* v_inheritedTraceOptions_2883_; uint8_t v_hasTrace_2884_; uint8_t v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___f_2891_; lean_object* v___x_2892_; lean_object* v___f_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v_toCold_2881_ = lean_ctor_get(v_a_2878_, 0);
v_options_2882_ = lean_ctor_get(v_toCold_2881_, 2);
v_inheritedTraceOptions_2883_ = lean_ctor_get(v_toCold_2881_, 11);
v_hasTrace_2884_ = lean_ctor_get_uint8(v_options_2882_, sizeof(void*)*1);
v___x_2885_ = 0;
lean_inc(v_declName_2874_);
v___x_2886_ = l_Lean_MessageData_ofConstName(v_declName_2874_, v___x_2885_);
v___x_2887_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1);
v___x_2888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2887_);
lean_ctor_set(v___x_2888_, 1, v___x_2886_);
v___x_2889_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3);
v___x_2890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2888_);
lean_ctor_set(v___x_2890_, 1, v___x_2889_);
v___f_2891_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__0), 2, 1);
lean_closure_set(v___f_2891_, 0, v___x_2890_);
v___x_2892_ = lean_box(0);
lean_inc_ref(v_type_2875_);
v___f_2893_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1___boxed), 8, 3);
lean_closure_set(v___f_2893_, 0, v_type_2875_);
lean_closure_set(v___f_2893_, 1, v___x_2892_);
lean_closure_set(v___f_2893_, 2, v_declName_2874_);
v___x_2894_ = lean_box(v___x_2885_);
v___x_2895_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___boxed), 8, 3);
lean_closure_set(v___x_2895_, 0, lean_box(0));
lean_closure_set(v___x_2895_, 1, v___f_2893_);
lean_closure_set(v___x_2895_, 2, v___x_2894_);
if (v_hasTrace_2884_ == 0)
{
lean_object* v___x_2896_; 
lean_dec_ref(v_type_2875_);
v___x_2896_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2895_, v___f_2891_, v_a_2876_, v_a_2877_, v_a_2878_, v_a_2879_);
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2904_; 
v_a_2897_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2899_ = v___x_2896_;
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v___x_2896_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2902_; 
if (v_isShared_2900_ == 0)
{
v___x_2902_ = v___x_2899_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_a_2897_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
else
{
lean_object* v_a_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2912_; 
v_a_2905_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2907_ = v___x_2896_;
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_a_2905_);
lean_dec(v___x_2896_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2910_; 
if (v_isShared_2908_ == 0)
{
v___x_2910_ = v___x_2907_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_a_2905_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
}
else
{
lean_object* v___f_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; uint8_t v___x_2917_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v_a_2921_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v_a_2936_; 
v___f_2913_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2913_, 0, v_type_2875_);
v___x_2914_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17));
v___x_2915_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__1));
v___x_2916_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20);
v___x_2917_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2883_, v_options_2882_, v___x_2916_);
if (v___x_2917_ == 0)
{
lean_object* v___x_2986_; uint8_t v___x_2987_; 
v___x_2986_ = l_Lean_trace_profiler;
v___x_2987_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_2882_, v___x_2986_);
if (v___x_2987_ == 0)
{
lean_object* v___x_2988_; 
lean_dec_ref(v___f_2913_);
v___x_2988_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2895_, v___f_2891_, v_a_2876_, v_a_2877_, v_a_2878_, v_a_2879_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
v_a_2989_ = lean_ctor_get(v___x_2988_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2991_ = v___x_2988_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v___x_2988_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2989_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
else
{
lean_object* v_a_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3004_; 
v_a_2997_ = lean_ctor_get(v___x_2988_, 0);
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2999_ = v___x_2988_;
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_a_2997_);
lean_dec(v___x_2988_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3002_; 
if (v_isShared_3000_ == 0)
{
v___x_3002_ = v___x_2999_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v_a_2997_);
v___x_3002_ = v_reuseFailAlloc_3003_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
return v___x_3002_;
}
}
}
}
else
{
goto v___jp_2945_;
}
}
else
{
goto v___jp_2945_;
}
v___jp_2918_:
{
lean_object* v___x_2922_; double v___x_2923_; double v___x_2924_; double v___x_2925_; double v___x_2926_; double v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2922_ = lean_io_mono_nanos_now();
v___x_2923_ = lean_float_of_nat(v___y_2920_);
v___x_2924_ = lean_float_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21);
v___x_2925_ = lean_float_div(v___x_2923_, v___x_2924_);
v___x_2926_ = lean_float_of_nat(v___x_2922_);
v___x_2927_ = lean_float_div(v___x_2926_, v___x_2924_);
v___x_2928_ = lean_box_float(v___x_2925_);
v___x_2929_ = lean_box_float(v___x_2927_);
v___x_2930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2928_);
lean_ctor_set(v___x_2930_, 1, v___x_2929_);
v___x_2931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2931_, 0, v_a_2921_);
lean_ctor_set(v___x_2931_, 1, v___x_2930_);
v___x_2932_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(v___x_2914_, v_hasTrace_2884_, v___x_2915_, v_options_2882_, v___x_2917_, v___y_2919_, v___f_2913_, v___x_2931_, v_a_2876_, v_a_2877_, v_a_2878_, v_a_2879_);
return v___x_2932_;
}
v___jp_2933_:
{
lean_object* v___x_2937_; double v___x_2938_; double v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; 
v___x_2937_ = lean_io_get_num_heartbeats();
v___x_2938_ = lean_float_of_nat(v___y_2934_);
v___x_2939_ = lean_float_of_nat(v___x_2937_);
v___x_2940_ = lean_box_float(v___x_2938_);
v___x_2941_ = lean_box_float(v___x_2939_);
v___x_2942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2940_);
lean_ctor_set(v___x_2942_, 1, v___x_2941_);
v___x_2943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2943_, 0, v_a_2936_);
lean_ctor_set(v___x_2943_, 1, v___x_2942_);
v___x_2944_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(v___x_2914_, v_hasTrace_2884_, v___x_2915_, v_options_2882_, v___x_2917_, v___y_2935_, v___f_2913_, v___x_2943_, v_a_2876_, v_a_2877_, v_a_2878_, v_a_2879_);
return v___x_2944_;
}
v___jp_2945_:
{
lean_object* v___x_2946_; lean_object* v_a_2947_; lean_object* v___x_2948_; uint8_t v___x_2949_; 
v___x_2946_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(v_a_2879_);
v_a_2947_ = lean_ctor_get(v___x_2946_, 0);
lean_inc(v_a_2947_);
lean_dec_ref(v___x_2946_);
v___x_2948_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2949_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_2882_, v___x_2948_);
if (v___x_2949_ == 0)
{
lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2950_ = lean_io_mono_nanos_now();
v___x_2951_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2895_, v___f_2891_, v_a_2876_, v_a_2877_, v_a_2878_, v_a_2879_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2959_; 
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2954_ = v___x_2951_;
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v___x_2951_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2957_; 
if (v_isShared_2955_ == 0)
{
lean_ctor_set_tag(v___x_2954_, 1);
v___x_2957_ = v___x_2954_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_a_2952_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
v___y_2919_ = v_a_2947_;
v___y_2920_ = v___x_2950_;
v_a_2921_ = v___x_2957_;
goto v___jp_2918_;
}
}
}
else
{
lean_object* v_a_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2967_; 
v_a_2960_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_2967_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2962_ = v___x_2951_;
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_a_2960_);
lean_dec(v___x_2951_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2965_; 
if (v_isShared_2963_ == 0)
{
lean_ctor_set_tag(v___x_2962_, 0);
v___x_2965_ = v___x_2962_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_a_2960_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
v___y_2919_ = v_a_2947_;
v___y_2920_ = v___x_2950_;
v_a_2921_ = v___x_2965_;
goto v___jp_2918_;
}
}
}
}
else
{
lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2968_ = lean_io_get_num_heartbeats();
v___x_2969_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2895_, v___f_2891_, v_a_2876_, v_a_2877_, v_a_2878_, v_a_2879_);
if (lean_obj_tag(v___x_2969_) == 0)
{
lean_object* v_a_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2977_; 
v_a_2970_ = lean_ctor_get(v___x_2969_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2972_ = v___x_2969_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2969_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2975_; 
if (v_isShared_2973_ == 0)
{
lean_ctor_set_tag(v___x_2972_, 1);
v___x_2975_ = v___x_2972_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_a_2970_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
v___y_2934_ = v___x_2968_;
v___y_2935_ = v_a_2947_;
v_a_2936_ = v___x_2975_;
goto v___jp_2933_;
}
}
}
else
{
lean_object* v_a_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2985_; 
v_a_2978_ = lean_ctor_get(v___x_2969_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2980_ = v___x_2969_;
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_a_2978_);
lean_dec(v___x_2969_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2983_; 
if (v_isShared_2981_ == 0)
{
lean_ctor_set_tag(v___x_2980_, 0);
v___x_2983_ = v___x_2980_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_a_2978_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
v___y_2934_ = v___x_2968_;
v___y_2935_ = v_a_2947_;
v_a_2936_ = v___x_2983_;
goto v___jp_2933_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___boxed(lean_object* v_declName_3005_, lean_object* v_type_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof(v_declName_3005_, v_type_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_);
lean_dec(v_a_3010_);
lean_dec_ref(v_a_3009_);
lean_dec(v_a_3008_);
lean_dec_ref(v_a_3007_);
return v_res_3012_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_(lean_object* v_env_3013_, lean_object* v_n_3014_, lean_object* v_x_3015_){
_start:
{
uint8_t v___x_3016_; 
v___x_3016_ = l_Lean_Environment_hasExposedBody(v_env_3013_, v_n_3014_);
return v___x_3016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2____boxed(lean_object* v_env_3017_, lean_object* v_n_3018_, lean_object* v_x_3019_){
_start:
{
uint8_t v_res_3020_; lean_object* v_r_3021_; 
v_res_3020_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_(v_env_3017_, v_n_3018_, v_x_3019_);
lean_dec_ref(v_x_3019_);
v_r_3021_ = lean_box(v_res_3020_);
return v_r_3021_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_3022_, lean_object* v_x_3023_){
_start:
{
if (lean_obj_tag(v_x_3023_) == 0)
{
lean_object* v_k_3024_; lean_object* v_v_3025_; lean_object* v_l_3026_; lean_object* v_r_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
v_k_3024_ = lean_ctor_get(v_x_3023_, 1);
v_v_3025_ = lean_ctor_get(v_x_3023_, 2);
v_l_3026_ = lean_ctor_get(v_x_3023_, 3);
v_r_3027_ = lean_ctor_get(v_x_3023_, 4);
v___x_3028_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0(v_init_3022_, v_l_3026_);
lean_inc(v_v_3025_);
lean_inc(v_k_3024_);
v___x_3029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3029_, 0, v_k_3024_);
lean_ctor_set(v___x_3029_, 1, v_v_3025_);
v___x_3030_ = lean_array_push(v___x_3028_, v___x_3029_);
v_init_3022_ = v___x_3030_;
v_x_3023_ = v_r_3027_;
goto _start;
}
else
{
return v_init_3022_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_3032_, lean_object* v_x_3033_){
_start:
{
lean_object* v_res_3034_; 
v_res_3034_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0(v_init_3032_, v_x_3033_);
lean_dec(v_x_3033_);
return v_res_3034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_(lean_object* v_env_3037_, lean_object* v_s_3038_){
_start:
{
lean_object* v___f_3039_; lean_object* v___x_3040_; lean_object* v_all_3041_; lean_object* v___x_3042_; lean_object* v_exported_3043_; lean_object* v___x_3044_; 
v___f_3039_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2____boxed), 3, 1);
lean_closure_set(v___f_3039_, 0, v_env_3037_);
v___x_3040_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_));
v_all_3041_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0(v___x_3040_, v_s_3038_);
v___x_3042_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v___f_3039_, v_s_3038_);
v_exported_3043_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0(v___x_3040_, v___x_3042_);
lean_dec(v___x_3042_);
lean_inc_ref(v_exported_3043_);
v___x_3044_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3044_, 0, v_exported_3043_);
lean_ctor_set(v___x_3044_, 1, v_exported_3043_);
lean_ctor_set(v___x_3044_, 2, v_all_3041_);
return v___x_3044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___f_3057_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_));
v___x_3058_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_));
v___x_3059_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_));
v___x_3060_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_3058_, v___x_3059_, v___f_3057_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2____boxed(lean_object* v_a_3061_){
_start:
{
lean_object* v_res_3062_; 
v_res_3062_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_();
return v_res_3062_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0(lean_object* v_init_3063_, lean_object* v_t_3064_){
_start:
{
lean_object* v___x_3065_; 
v___x_3065_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0(v_init_3063_, v_t_3064_);
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_3066_, lean_object* v_t_3067_){
_start:
{
lean_object* v_res_3068_; 
v_res_3068_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0(v_init_3066_, v_t_3067_);
lean_dec(v_t_3067_);
return v_res_3068_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__0(void){
_start:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3069_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3);
v___x_3070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3069_);
return v___x_3070_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1(void){
_start:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3071_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__0, &l_Lean_Elab_Structural_registerEqnsInfo___closed__0_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__0);
v___x_3072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3071_);
lean_ctor_set(v___x_3072_, 1, v___x_3071_);
return v___x_3072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_registerEqnsInfo(lean_object* v_preDef_3073_, lean_object* v_declNames_3074_, lean_object* v_recArgPos_3075_, lean_object* v_fixedParamPerms_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_){
_start:
{
lean_object* v_levelParams_3080_; lean_object* v_declName_3081_; lean_object* v_type_3082_; lean_object* v_value_3083_; lean_object* v___x_3084_; 
v_levelParams_3080_ = lean_ctor_get(v_preDef_3073_, 1);
lean_inc(v_levelParams_3080_);
v_declName_3081_ = lean_ctor_get(v_preDef_3073_, 3);
lean_inc_n(v_declName_3081_, 2);
v_type_3082_ = lean_ctor_get(v_preDef_3073_, 6);
lean_inc_ref(v_type_3082_);
v_value_3083_ = lean_ctor_get(v_preDef_3073_, 7);
lean_inc_ref(v_value_3083_);
lean_dec_ref(v_preDef_3073_);
v___x_3084_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_3081_, v_a_3077_, v_a_3078_);
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3115_; 
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3115_ == 0)
{
lean_object* v_unused_3116_; 
v_unused_3116_ = lean_ctor_get(v___x_3084_, 0);
lean_dec(v_unused_3116_);
v___x_3086_ = v___x_3084_;
v_isShared_3087_ = v_isSharedCheck_3115_;
goto v_resetjp_3085_;
}
else
{
lean_dec(v___x_3084_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3115_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3088_; lean_object* v_env_3089_; lean_object* v_nextMacroScope_3090_; lean_object* v_ngen_3091_; lean_object* v_auxDeclNGen_3092_; lean_object* v_traceState_3093_; lean_object* v_recordedDeps_3094_; lean_object* v_messages_3095_; lean_object* v_infoState_3096_; lean_object* v_snapshotTasks_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3113_; 
v___x_3088_ = lean_st_ref_take(v_a_3078_);
v_env_3089_ = lean_ctor_get(v___x_3088_, 0);
v_nextMacroScope_3090_ = lean_ctor_get(v___x_3088_, 1);
v_ngen_3091_ = lean_ctor_get(v___x_3088_, 2);
v_auxDeclNGen_3092_ = lean_ctor_get(v___x_3088_, 3);
v_traceState_3093_ = lean_ctor_get(v___x_3088_, 4);
v_recordedDeps_3094_ = lean_ctor_get(v___x_3088_, 6);
v_messages_3095_ = lean_ctor_get(v___x_3088_, 7);
v_infoState_3096_ = lean_ctor_get(v___x_3088_, 8);
v_snapshotTasks_3097_ = lean_ctor_get(v___x_3088_, 9);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3113_ == 0)
{
lean_object* v_unused_3114_; 
v_unused_3114_ = lean_ctor_get(v___x_3088_, 5);
lean_dec(v_unused_3114_);
v___x_3099_ = v___x_3088_;
v_isShared_3100_ = v_isSharedCheck_3113_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_snapshotTasks_3097_);
lean_inc(v_infoState_3096_);
lean_inc(v_messages_3095_);
lean_inc(v_recordedDeps_3094_);
lean_inc(v_traceState_3093_);
lean_inc(v_auxDeclNGen_3092_);
lean_inc(v_ngen_3091_);
lean_inc(v_nextMacroScope_3090_);
lean_inc(v_env_3089_);
lean_dec(v___x_3088_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3113_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3107_; 
v___x_3101_ = lean_box(0);
v___x_3102_ = l_Lean_Elab_Structural_eqnInfoExt;
lean_inc(v_declName_3081_);
v___x_3103_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3103_, 0, v_declName_3081_);
lean_ctor_set(v___x_3103_, 1, v_levelParams_3080_);
lean_ctor_set(v___x_3103_, 2, v_type_3082_);
lean_ctor_set(v___x_3103_, 3, v_value_3083_);
lean_ctor_set(v___x_3103_, 4, v_recArgPos_3075_);
lean_ctor_set(v___x_3103_, 5, v_declNames_3074_);
lean_ctor_set(v___x_3103_, 6, v_fixedParamPerms_3076_);
v___x_3104_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3102_, v_env_3089_, v_declName_3081_, v___x_3103_);
v___x_3105_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__1, &l_Lean_Elab_Structural_registerEqnsInfo___closed__1_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1);
if (v_isShared_3100_ == 0)
{
lean_ctor_set(v___x_3099_, 5, v___x_3105_);
lean_ctor_set(v___x_3099_, 0, v___x_3104_);
v___x_3107_ = v___x_3099_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v___x_3104_);
lean_ctor_set(v_reuseFailAlloc_3112_, 1, v_nextMacroScope_3090_);
lean_ctor_set(v_reuseFailAlloc_3112_, 2, v_ngen_3091_);
lean_ctor_set(v_reuseFailAlloc_3112_, 3, v_auxDeclNGen_3092_);
lean_ctor_set(v_reuseFailAlloc_3112_, 4, v_traceState_3093_);
lean_ctor_set(v_reuseFailAlloc_3112_, 5, v___x_3105_);
lean_ctor_set(v_reuseFailAlloc_3112_, 6, v_recordedDeps_3094_);
lean_ctor_set(v_reuseFailAlloc_3112_, 7, v_messages_3095_);
lean_ctor_set(v_reuseFailAlloc_3112_, 8, v_infoState_3096_);
lean_ctor_set(v_reuseFailAlloc_3112_, 9, v_snapshotTasks_3097_);
v___x_3107_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
lean_object* v___x_3108_; lean_object* v___x_3110_; 
v___x_3108_ = lean_st_ref_put(v_a_3078_, v___x_3107_);
if (v_isShared_3087_ == 0)
{
lean_ctor_set(v___x_3086_, 0, v___x_3101_);
v___x_3110_ = v___x_3086_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3101_);
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
}
else
{
lean_dec_ref(v_value_3083_);
lean_dec_ref(v_type_3082_);
lean_dec(v_declName_3081_);
lean_dec(v_levelParams_3080_);
lean_dec_ref(v_fixedParamPerms_3076_);
lean_dec(v_recArgPos_3075_);
lean_dec_ref(v_declNames_3074_);
return v___x_3084_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_registerEqnsInfo___boxed(lean_object* v_preDef_3117_, lean_object* v_declNames_3118_, lean_object* v_recArgPos_3119_, lean_object* v_fixedParamPerms_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_){
_start:
{
lean_object* v_res_3124_; 
v_res_3124_ = l_Lean_Elab_Structural_registerEqnsInfo(v_preDef_3117_, v_declNames_3118_, v_recArgPos_3119_, v_fixedParamPerms_3120_, v_a_3121_, v_a_3122_);
lean_dec(v_a_3122_);
lean_dec_ref(v_a_3121_);
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(lean_object* v_e_3125_, lean_object* v_k_3126_, uint8_t v_cleanupAnnotations_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_){
_start:
{
lean_object* v___f_3133_; uint8_t v___x_3134_; uint8_t v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___f_3133_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3133_, 0, v_k_3126_);
v___x_3134_ = 1;
v___x_3135_ = 0;
v___x_3136_ = lean_box(0);
v___x_3137_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3125_, v___x_3134_, v___x_3135_, v___x_3134_, v___x_3135_, v___x_3136_, v___f_3133_, v_cleanupAnnotations_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_object* v_a_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3145_; 
v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3140_ = v___x_3137_;
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_a_3138_);
lean_dec(v___x_3137_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3143_; 
if (v_isShared_3141_ == 0)
{
v___x_3143_ = v___x_3140_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_a_3138_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
else
{
lean_object* v_a_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3153_; 
v_a_3146_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3148_ = v___x_3137_;
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_a_3146_);
lean_dec(v___x_3137_);
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
v_reuseFailAlloc_3152_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg___boxed(lean_object* v_e_3154_, lean_object* v_k_3155_, lean_object* v_cleanupAnnotations_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3162_; lean_object* v_res_3163_; 
v_cleanupAnnotations_boxed_3162_ = lean_unbox(v_cleanupAnnotations_3156_);
v_res_3163_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(v_e_3154_, v_k_3155_, v_cleanupAnnotations_boxed_3162_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
return v_res_3163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3(lean_object* v_00_u03b1_3164_, lean_object* v_e_3165_, lean_object* v_k_3166_, uint8_t v_cleanupAnnotations_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_){
_start:
{
lean_object* v___x_3173_; 
v___x_3173_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(v_e_3165_, v_k_3166_, v_cleanupAnnotations_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
return v___x_3173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___boxed(lean_object* v_00_u03b1_3174_, lean_object* v_e_3175_, lean_object* v_k_3176_, lean_object* v_cleanupAnnotations_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3183_; lean_object* v_res_3184_; 
v_cleanupAnnotations_boxed_3183_ = lean_unbox(v_cleanupAnnotations_3177_);
v_res_3184_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3(v_00_u03b1_3174_, v_e_3175_, v_k_3176_, v_cleanupAnnotations_boxed_3183_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
lean_dec(v___y_3179_);
lean_dec_ref(v___y_3178_);
return v_res_3184_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(lean_object* v___y_3185_, uint8_t v_isExporting_3186_, lean_object* v___x_3187_, lean_object* v___y_3188_, lean_object* v___x_3189_, lean_object* v_a_x3f_3190_){
_start:
{
lean_object* v___x_3192_; lean_object* v_env_3193_; lean_object* v_nextMacroScope_3194_; lean_object* v_ngen_3195_; lean_object* v_auxDeclNGen_3196_; lean_object* v_traceState_3197_; lean_object* v_recordedDeps_3198_; lean_object* v_messages_3199_; lean_object* v_infoState_3200_; lean_object* v_snapshotTasks_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3226_; 
v___x_3192_ = lean_st_ref_take(v___y_3185_);
v_env_3193_ = lean_ctor_get(v___x_3192_, 0);
v_nextMacroScope_3194_ = lean_ctor_get(v___x_3192_, 1);
v_ngen_3195_ = lean_ctor_get(v___x_3192_, 2);
v_auxDeclNGen_3196_ = lean_ctor_get(v___x_3192_, 3);
v_traceState_3197_ = lean_ctor_get(v___x_3192_, 4);
v_recordedDeps_3198_ = lean_ctor_get(v___x_3192_, 6);
v_messages_3199_ = lean_ctor_get(v___x_3192_, 7);
v_infoState_3200_ = lean_ctor_get(v___x_3192_, 8);
v_snapshotTasks_3201_ = lean_ctor_get(v___x_3192_, 9);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3226_ == 0)
{
lean_object* v_unused_3227_; 
v_unused_3227_ = lean_ctor_get(v___x_3192_, 5);
lean_dec(v_unused_3227_);
v___x_3203_ = v___x_3192_;
v_isShared_3204_ = v_isSharedCheck_3226_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_snapshotTasks_3201_);
lean_inc(v_infoState_3200_);
lean_inc(v_messages_3199_);
lean_inc(v_recordedDeps_3198_);
lean_inc(v_traceState_3197_);
lean_inc(v_auxDeclNGen_3196_);
lean_inc(v_ngen_3195_);
lean_inc(v_nextMacroScope_3194_);
lean_inc(v_env_3193_);
lean_dec(v___x_3192_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3226_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3205_; lean_object* v___x_3207_; 
v___x_3205_ = l_Lean_Environment_setExporting(v_env_3193_, v_isExporting_3186_);
if (v_isShared_3204_ == 0)
{
lean_ctor_set(v___x_3203_, 5, v___x_3187_);
lean_ctor_set(v___x_3203_, 0, v___x_3205_);
v___x_3207_ = v___x_3203_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v___x_3205_);
lean_ctor_set(v_reuseFailAlloc_3225_, 1, v_nextMacroScope_3194_);
lean_ctor_set(v_reuseFailAlloc_3225_, 2, v_ngen_3195_);
lean_ctor_set(v_reuseFailAlloc_3225_, 3, v_auxDeclNGen_3196_);
lean_ctor_set(v_reuseFailAlloc_3225_, 4, v_traceState_3197_);
lean_ctor_set(v_reuseFailAlloc_3225_, 5, v___x_3187_);
lean_ctor_set(v_reuseFailAlloc_3225_, 6, v_recordedDeps_3198_);
lean_ctor_set(v_reuseFailAlloc_3225_, 7, v_messages_3199_);
lean_ctor_set(v_reuseFailAlloc_3225_, 8, v_infoState_3200_);
lean_ctor_set(v_reuseFailAlloc_3225_, 9, v_snapshotTasks_3201_);
v___x_3207_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v_mctx_3210_; lean_object* v_zetaDeltaFVarIds_3211_; lean_object* v_postponed_3212_; lean_object* v_diag_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3223_; 
v___x_3208_ = lean_st_ref_put(v___y_3185_, v___x_3207_);
v___x_3209_ = lean_st_ref_take(v___y_3188_);
v_mctx_3210_ = lean_ctor_get(v___x_3209_, 0);
v_zetaDeltaFVarIds_3211_ = lean_ctor_get(v___x_3209_, 2);
v_postponed_3212_ = lean_ctor_get(v___x_3209_, 3);
v_diag_3213_ = lean_ctor_get(v___x_3209_, 4);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3209_);
if (v_isSharedCheck_3223_ == 0)
{
lean_object* v_unused_3224_; 
v_unused_3224_ = lean_ctor_get(v___x_3209_, 1);
lean_dec(v_unused_3224_);
v___x_3215_ = v___x_3209_;
v_isShared_3216_ = v_isSharedCheck_3223_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_diag_3213_);
lean_inc(v_postponed_3212_);
lean_inc(v_zetaDeltaFVarIds_3211_);
lean_inc(v_mctx_3210_);
lean_dec(v___x_3209_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3223_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3217_; lean_object* v___x_3219_; 
v___x_3217_ = lean_box(0);
if (v_isShared_3216_ == 0)
{
lean_ctor_set(v___x_3215_, 1, v___x_3189_);
v___x_3219_ = v___x_3215_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_mctx_3210_);
lean_ctor_set(v_reuseFailAlloc_3222_, 1, v___x_3189_);
lean_ctor_set(v_reuseFailAlloc_3222_, 2, v_zetaDeltaFVarIds_3211_);
lean_ctor_set(v_reuseFailAlloc_3222_, 3, v_postponed_3212_);
lean_ctor_set(v_reuseFailAlloc_3222_, 4, v_diag_3213_);
v___x_3219_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; 
v___x_3220_ = lean_st_ref_put(v___y_3188_, v___x_3219_);
v___x_3221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3217_);
return v___x_3221_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_3228_, lean_object* v_isExporting_3229_, lean_object* v___x_3230_, lean_object* v___y_3231_, lean_object* v___x_3232_, lean_object* v_a_x3f_3233_, lean_object* v___y_3234_){
_start:
{
uint8_t v_isExporting_boxed_3235_; lean_object* v_res_3236_; 
v_isExporting_boxed_3235_ = lean_unbox(v_isExporting_3229_);
v_res_3236_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(v___y_3228_, v_isExporting_boxed_3235_, v___x_3230_, v___y_3231_, v___x_3232_, v_a_x3f_3233_);
lean_dec(v_a_x3f_3233_);
lean_dec(v___y_3231_);
lean_dec(v___y_3228_);
return v_res_3236_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3237_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__0, &l_Lean_Elab_Structural_registerEqnsInfo___closed__0_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__0);
v___x_3238_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3237_);
lean_ctor_set(v___x_3238_, 1, v___x_3237_);
lean_ctor_set(v___x_3238_, 2, v___x_3237_);
lean_ctor_set(v___x_3238_, 3, v___x_3237_);
lean_ctor_set(v___x_3238_, 4, v___x_3237_);
lean_ctor_set(v___x_3238_, 5, v___x_3237_);
return v___x_3238_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(lean_object* v_x_3239_, uint8_t v_isExporting_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_){
_start:
{
lean_object* v___x_3246_; lean_object* v_env_3247_; lean_object* v___x_3248_; uint8_t v_isModule_3249_; 
v___x_3246_ = lean_st_ref_get(v___y_3244_);
v_env_3247_ = lean_ctor_get(v___x_3246_, 0);
lean_inc_ref(v_env_3247_);
lean_dec(v___x_3246_);
v___x_3248_ = l_Lean_Environment_header(v_env_3247_);
v_isModule_3249_ = lean_ctor_get_uint8(v___x_3248_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3248_);
if (v_isModule_3249_ == 0)
{
lean_object* v___x_3250_; 
lean_dec_ref(v_env_3247_);
lean_inc(v___y_3244_);
lean_inc_ref(v___y_3243_);
lean_inc(v___y_3242_);
lean_inc_ref(v___y_3241_);
v___x_3250_ = lean_apply_5(v_x_3239_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, lean_box(0));
return v___x_3250_;
}
else
{
uint8_t v_isExporting_3251_; 
v_isExporting_3251_ = lean_ctor_get_uint8(v_env_3247_, sizeof(void*)*8);
lean_dec_ref(v_env_3247_);
if (v_isExporting_3240_ == 0)
{
if (v_isExporting_3251_ == 0)
{
lean_object* v___x_3318_; 
lean_inc(v___y_3244_);
lean_inc_ref(v___y_3243_);
lean_inc(v___y_3242_);
lean_inc_ref(v___y_3241_);
v___x_3318_ = lean_apply_5(v_x_3239_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, lean_box(0));
return v___x_3318_;
}
else
{
goto v___jp_3252_;
}
}
else
{
if (v_isExporting_3251_ == 0)
{
goto v___jp_3252_;
}
else
{
lean_object* v___x_3319_; 
lean_inc(v___y_3244_);
lean_inc_ref(v___y_3243_);
lean_inc(v___y_3242_);
lean_inc_ref(v___y_3241_);
v___x_3319_ = lean_apply_5(v_x_3239_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, lean_box(0));
return v___x_3319_;
}
}
v___jp_3252_:
{
lean_object* v___x_3253_; lean_object* v_env_3254_; lean_object* v_nextMacroScope_3255_; lean_object* v_ngen_3256_; lean_object* v_auxDeclNGen_3257_; lean_object* v_traceState_3258_; lean_object* v_recordedDeps_3259_; lean_object* v_messages_3260_; lean_object* v_infoState_3261_; lean_object* v_snapshotTasks_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3316_; 
v___x_3253_ = lean_st_ref_take(v___y_3244_);
v_env_3254_ = lean_ctor_get(v___x_3253_, 0);
v_nextMacroScope_3255_ = lean_ctor_get(v___x_3253_, 1);
v_ngen_3256_ = lean_ctor_get(v___x_3253_, 2);
v_auxDeclNGen_3257_ = lean_ctor_get(v___x_3253_, 3);
v_traceState_3258_ = lean_ctor_get(v___x_3253_, 4);
v_recordedDeps_3259_ = lean_ctor_get(v___x_3253_, 6);
v_messages_3260_ = lean_ctor_get(v___x_3253_, 7);
v_infoState_3261_ = lean_ctor_get(v___x_3253_, 8);
v_snapshotTasks_3262_ = lean_ctor_get(v___x_3253_, 9);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3253_);
if (v_isSharedCheck_3316_ == 0)
{
lean_object* v_unused_3317_; 
v_unused_3317_ = lean_ctor_get(v___x_3253_, 5);
lean_dec(v_unused_3317_);
v___x_3264_ = v___x_3253_;
v_isShared_3265_ = v_isSharedCheck_3316_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_snapshotTasks_3262_);
lean_inc(v_infoState_3261_);
lean_inc(v_messages_3260_);
lean_inc(v_recordedDeps_3259_);
lean_inc(v_traceState_3258_);
lean_inc(v_auxDeclNGen_3257_);
lean_inc(v_ngen_3256_);
lean_inc(v_nextMacroScope_3255_);
lean_inc(v_env_3254_);
lean_dec(v___x_3253_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3316_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3269_; 
v___x_3266_ = l_Lean_Environment_setExporting(v_env_3254_, v_isExporting_3240_);
v___x_3267_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__1, &l_Lean_Elab_Structural_registerEqnsInfo___closed__1_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1);
if (v_isShared_3265_ == 0)
{
lean_ctor_set(v___x_3264_, 5, v___x_3267_);
lean_ctor_set(v___x_3264_, 0, v___x_3266_);
v___x_3269_ = v___x_3264_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v___x_3266_);
lean_ctor_set(v_reuseFailAlloc_3315_, 1, v_nextMacroScope_3255_);
lean_ctor_set(v_reuseFailAlloc_3315_, 2, v_ngen_3256_);
lean_ctor_set(v_reuseFailAlloc_3315_, 3, v_auxDeclNGen_3257_);
lean_ctor_set(v_reuseFailAlloc_3315_, 4, v_traceState_3258_);
lean_ctor_set(v_reuseFailAlloc_3315_, 5, v___x_3267_);
lean_ctor_set(v_reuseFailAlloc_3315_, 6, v_recordedDeps_3259_);
lean_ctor_set(v_reuseFailAlloc_3315_, 7, v_messages_3260_);
lean_ctor_set(v_reuseFailAlloc_3315_, 8, v_infoState_3261_);
lean_ctor_set(v_reuseFailAlloc_3315_, 9, v_snapshotTasks_3262_);
v___x_3269_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v_mctx_3272_; lean_object* v_zetaDeltaFVarIds_3273_; lean_object* v_postponed_3274_; lean_object* v_diag_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3313_; 
v___x_3270_ = lean_st_ref_put(v___y_3244_, v___x_3269_);
v___x_3271_ = lean_st_ref_take(v___y_3242_);
v_mctx_3272_ = lean_ctor_get(v___x_3271_, 0);
v_zetaDeltaFVarIds_3273_ = lean_ctor_get(v___x_3271_, 2);
v_postponed_3274_ = lean_ctor_get(v___x_3271_, 3);
v_diag_3275_ = lean_ctor_get(v___x_3271_, 4);
v_isSharedCheck_3313_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3313_ == 0)
{
lean_object* v_unused_3314_; 
v_unused_3314_ = lean_ctor_get(v___x_3271_, 1);
lean_dec(v_unused_3314_);
v___x_3277_ = v___x_3271_;
v_isShared_3278_ = v_isSharedCheck_3313_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_diag_3275_);
lean_inc(v_postponed_3274_);
lean_inc(v_zetaDeltaFVarIds_3273_);
lean_inc(v_mctx_3272_);
lean_dec(v___x_3271_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3313_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v___x_3279_; lean_object* v___x_3281_; 
v___x_3279_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0);
if (v_isShared_3278_ == 0)
{
lean_ctor_set(v___x_3277_, 1, v___x_3279_);
v___x_3281_ = v___x_3277_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v_mctx_3272_);
lean_ctor_set(v_reuseFailAlloc_3312_, 1, v___x_3279_);
lean_ctor_set(v_reuseFailAlloc_3312_, 2, v_zetaDeltaFVarIds_3273_);
lean_ctor_set(v_reuseFailAlloc_3312_, 3, v_postponed_3274_);
lean_ctor_set(v_reuseFailAlloc_3312_, 4, v_diag_3275_);
v___x_3281_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
lean_object* v___x_3282_; lean_object* v_r_3283_; 
v___x_3282_ = lean_st_ref_put(v___y_3242_, v___x_3281_);
lean_inc(v___y_3244_);
lean_inc_ref(v___y_3243_);
lean_inc(v___y_3242_);
lean_inc_ref(v___y_3241_);
v_r_3283_ = lean_apply_5(v_x_3239_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, lean_box(0));
if (lean_obj_tag(v_r_3283_) == 0)
{
lean_object* v_a_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3300_; 
v_a_3284_ = lean_ctor_get(v_r_3283_, 0);
v_isSharedCheck_3300_ = !lean_is_exclusive(v_r_3283_);
if (v_isSharedCheck_3300_ == 0)
{
v___x_3286_ = v_r_3283_;
v_isShared_3287_ = v_isSharedCheck_3300_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_a_3284_);
lean_dec(v_r_3283_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3300_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3289_; 
lean_inc(v_a_3284_);
if (v_isShared_3287_ == 0)
{
lean_ctor_set_tag(v___x_3286_, 1);
v___x_3289_ = v___x_3286_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v_a_3284_);
v___x_3289_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
lean_object* v___x_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3297_; 
v___x_3290_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(v___y_3244_, v_isExporting_3251_, v___x_3267_, v___y_3242_, v___x_3279_, v___x_3289_);
lean_dec_ref(v___x_3289_);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3290_);
if (v_isSharedCheck_3297_ == 0)
{
lean_object* v_unused_3298_; 
v_unused_3298_ = lean_ctor_get(v___x_3290_, 0);
lean_dec(v_unused_3298_);
v___x_3292_ = v___x_3290_;
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
else
{
lean_dec(v___x_3290_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3295_; 
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 0, v_a_3284_);
v___x_3295_ = v___x_3292_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v_a_3284_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
}
}
}
}
}
else
{
lean_object* v_a_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3310_; 
v_a_3301_ = lean_ctor_get(v_r_3283_, 0);
lean_inc(v_a_3301_);
lean_dec_ref_known(v_r_3283_, 1);
v___x_3302_ = lean_box(0);
v___x_3303_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(v___y_3244_, v_isExporting_3251_, v___x_3267_, v___y_3242_, v___x_3279_, v___x_3302_);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3303_);
if (v_isSharedCheck_3310_ == 0)
{
lean_object* v_unused_3311_; 
v_unused_3311_ = lean_ctor_get(v___x_3303_, 0);
lean_dec(v_unused_3311_);
v___x_3305_ = v___x_3303_;
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
else
{
lean_dec(v___x_3303_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v___x_3308_; 
if (v_isShared_3306_ == 0)
{
lean_ctor_set_tag(v___x_3305_, 1);
lean_ctor_set(v___x_3305_, 0, v_a_3301_);
v___x_3308_ = v___x_3305_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_a_3301_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___boxed(lean_object* v_x_3320_, lean_object* v_isExporting_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_){
_start:
{
uint8_t v_isExporting_boxed_3327_; lean_object* v_res_3328_; 
v_isExporting_boxed_3327_ = lean_unbox(v_isExporting_3321_);
v_res_3328_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(v_x_3320_, v_isExporting_boxed_3327_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_);
lean_dec(v___y_3325_);
lean_dec_ref(v___y_3324_);
lean_dec(v___y_3323_);
lean_dec_ref(v___y_3322_);
return v_res_3328_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(lean_object* v_x_3329_, uint8_t v_when_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_){
_start:
{
if (v_when_3330_ == 0)
{
lean_object* v___x_3336_; 
lean_inc(v___y_3334_);
lean_inc_ref(v___y_3333_);
lean_inc(v___y_3332_);
lean_inc_ref(v___y_3331_);
v___x_3336_ = lean_apply_5(v_x_3329_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_, lean_box(0));
return v___x_3336_;
}
else
{
uint8_t v___x_3337_; lean_object* v___x_3338_; 
v___x_3337_ = 0;
v___x_3338_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(v_x_3329_, v___x_3337_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
return v___x_3338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg___boxed(lean_object* v_x_3339_, lean_object* v_when_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_){
_start:
{
uint8_t v_when_boxed_3346_; lean_object* v_res_3347_; 
v_when_boxed_3346_ = lean_unbox(v_when_3340_);
v_res_3347_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(v_x_3339_, v_when_boxed_3346_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
lean_dec(v___y_3344_);
lean_dec_ref(v___y_3343_);
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
return v_res_3347_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__0(lean_object* v_a_3348_, lean_object* v_a_3349_){
_start:
{
if (lean_obj_tag(v_a_3348_) == 0)
{
lean_object* v___x_3350_; 
v___x_3350_ = l_List_reverse___redArg(v_a_3349_);
return v___x_3350_;
}
else
{
lean_object* v_head_3351_; lean_object* v_tail_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3361_; 
v_head_3351_ = lean_ctor_get(v_a_3348_, 0);
v_tail_3352_ = lean_ctor_get(v_a_3348_, 1);
v_isSharedCheck_3361_ = !lean_is_exclusive(v_a_3348_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3354_ = v_a_3348_;
v_isShared_3355_ = v_isSharedCheck_3361_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_tail_3352_);
lean_inc(v_head_3351_);
lean_dec(v_a_3348_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3361_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v___x_3356_; lean_object* v___x_3358_; 
v___x_3356_ = l_Lean_mkLevelParam(v_head_3351_);
if (v_isShared_3355_ == 0)
{
lean_ctor_set(v___x_3354_, 1, v_a_3349_);
lean_ctor_set(v___x_3354_, 0, v___x_3356_);
v___x_3358_ = v___x_3354_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v___x_3356_);
lean_ctor_set(v_reuseFailAlloc_3360_, 1, v_a_3349_);
v___x_3358_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
v_a_3348_ = v_tail_3352_;
v_a_3349_ = v___x_3358_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0(lean_object* v_levelParams_3362_, lean_object* v_declName_3363_, lean_object* v_name_3364_, lean_object* v_xs_3365_, lean_object* v_body_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_){
_start:
{
lean_object* v___x_3372_; lean_object* v_us_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3372_ = lean_box(0);
lean_inc(v_levelParams_3362_);
v_us_3373_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__0(v_levelParams_3362_, v___x_3372_);
lean_inc(v_declName_3363_);
v___x_3374_ = l_Lean_mkConst(v_declName_3363_, v_us_3373_);
v___x_3375_ = l_Lean_mkAppN(v___x_3374_, v_xs_3365_);
v___x_3376_ = l_Lean_Meta_mkEq(v___x_3375_, v_body_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_object* v_a_3377_; lean_object* v___x_3378_; uint8_t v___x_3379_; lean_object* v___x_3380_; 
v_a_3377_ = lean_ctor_get(v___x_3376_, 0);
lean_inc_n(v_a_3377_, 2);
lean_dec_ref_known(v___x_3376_, 1);
v___x_3378_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___boxed), 7, 2);
lean_closure_set(v___x_3378_, 0, v_declName_3363_);
lean_closure_set(v___x_3378_, 1, v_a_3377_);
v___x_3379_ = 1;
v___x_3380_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(v___x_3378_, v___x_3379_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_);
if (lean_obj_tag(v___x_3380_) == 0)
{
lean_object* v_a_3381_; uint8_t v___x_3382_; uint8_t v___x_3383_; lean_object* v___x_3384_; 
v_a_3381_ = lean_ctor_get(v___x_3380_, 0);
lean_inc(v_a_3381_);
lean_dec_ref_known(v___x_3380_, 1);
v___x_3382_ = 0;
v___x_3383_ = 1;
v___x_3384_ = l_Lean_Meta_mkForallFVars(v_xs_3365_, v_a_3377_, v___x_3382_, v___x_3379_, v___x_3379_, v___x_3383_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v_a_3385_; lean_object* v___x_3386_; 
v_a_3385_ = lean_ctor_get(v___x_3384_, 0);
lean_inc(v_a_3385_);
lean_dec_ref_known(v___x_3384_, 1);
v___x_3386_ = l_Lean_Meta_letToHave(v_a_3385_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v_a_3387_; lean_object* v___x_3388_; 
v_a_3387_ = lean_ctor_get(v___x_3386_, 0);
lean_inc(v_a_3387_);
lean_dec_ref_known(v___x_3386_, 1);
v___x_3388_ = l_Lean_Meta_mkLambdaFVars(v_xs_3365_, v_a_3381_, v___x_3382_, v___x_3379_, v___x_3382_, v___x_3379_, v___x_3383_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_);
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_object* v_a_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; 
v_a_3389_ = lean_ctor_get(v___x_3388_, 0);
lean_inc(v_a_3389_);
lean_dec_ref_known(v___x_3388_, 1);
lean_inc_n(v_name_3364_, 2);
v___x_3390_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3390_, 0, v_name_3364_);
lean_ctor_set(v___x_3390_, 1, v_levelParams_3362_);
lean_ctor_set(v___x_3390_, 2, v_a_3387_);
v___x_3391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3391_, 0, v_name_3364_);
lean_ctor_set(v___x_3391_, 1, v___x_3372_);
v___x_3392_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3392_, 0, v___x_3390_);
lean_ctor_set(v___x_3392_, 1, v_a_3389_);
lean_ctor_set(v___x_3392_, 2, v___x_3391_);
v___x_3393_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3392_);
v___x_3394_ = l_Lean_addDecl(v___x_3393_, v___x_3382_, v___y_3369_, v___y_3370_);
if (lean_obj_tag(v___x_3394_) == 0)
{
lean_object* v___x_3395_; 
lean_dec_ref_known(v___x_3394_, 1);
v___x_3395_ = l_Lean_inferDefEqAttr(v_name_3364_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_);
return v___x_3395_;
}
else
{
lean_dec(v_name_3364_);
return v___x_3394_;
}
}
else
{
lean_object* v_a_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3403_; 
lean_dec(v_a_3387_);
lean_dec(v_name_3364_);
lean_dec(v_levelParams_3362_);
v_a_3396_ = lean_ctor_get(v___x_3388_, 0);
v_isSharedCheck_3403_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3398_ = v___x_3388_;
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_a_3396_);
lean_dec(v___x_3388_);
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
lean_dec(v_a_3381_);
lean_dec(v_name_3364_);
lean_dec(v_levelParams_3362_);
v_a_3404_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3406_ = v___x_3386_;
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_a_3404_);
lean_dec(v___x_3386_);
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
lean_dec(v_a_3381_);
lean_dec(v_name_3364_);
lean_dec(v_levelParams_3362_);
v_a_3412_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3419_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3414_ = v___x_3384_;
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_a_3412_);
lean_dec(v___x_3384_);
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
lean_dec(v_a_3377_);
lean_dec(v_name_3364_);
lean_dec(v_levelParams_3362_);
v_a_3420_ = lean_ctor_get(v___x_3380_, 0);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3422_ = v___x_3380_;
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_a_3420_);
lean_dec(v___x_3380_);
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
else
{
lean_object* v_a_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3435_; 
lean_dec(v_name_3364_);
lean_dec(v_declName_3363_);
lean_dec(v_levelParams_3362_);
v_a_3428_ = lean_ctor_get(v___x_3376_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3430_ = v___x_3376_;
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_a_3428_);
lean_dec(v___x_3376_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3433_; 
if (v_isShared_3431_ == 0)
{
v___x_3433_ = v___x_3430_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_a_3428_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
return v___x_3433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0___boxed(lean_object* v_levelParams_3436_, lean_object* v_declName_3437_, lean_object* v_name_3438_, lean_object* v_xs_3439_, lean_object* v_body_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_){
_start:
{
lean_object* v_res_3446_; 
v_res_3446_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0(v_levelParams_3436_, v_declName_3437_, v_name_3438_, v_xs_3439_, v_body_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
lean_dec(v___y_3444_);
lean_dec_ref(v___y_3443_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
lean_dec_ref(v_xs_3439_);
return v_res_3446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3(lean_object* v_o_3447_, lean_object* v_k_3448_, uint8_t v_v_3449_){
_start:
{
lean_object* v_map_3450_; uint8_t v_hasTrace_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3465_; 
v_map_3450_ = lean_ctor_get(v_o_3447_, 0);
v_hasTrace_3451_ = lean_ctor_get_uint8(v_o_3447_, sizeof(void*)*1);
v_isSharedCheck_3465_ = !lean_is_exclusive(v_o_3447_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3453_ = v_o_3447_;
v_isShared_3454_ = v_isSharedCheck_3465_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_map_3450_);
lean_dec(v_o_3447_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3465_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___x_3455_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3455_, 0, v_v_3449_);
lean_inc(v_k_3448_);
v___x_3456_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_3448_, v___x_3455_, v_map_3450_);
if (v_hasTrace_3451_ == 0)
{
lean_object* v___x_3457_; uint8_t v___x_3458_; lean_object* v___x_3460_; 
v___x_3457_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19));
v___x_3458_ = l_Lean_Name_isPrefixOf(v___x_3457_, v_k_3448_);
lean_dec(v_k_3448_);
if (v_isShared_3454_ == 0)
{
lean_ctor_set(v___x_3453_, 0, v___x_3456_);
v___x_3460_ = v___x_3453_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v___x_3456_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
lean_ctor_set_uint8(v___x_3460_, sizeof(void*)*1, v___x_3458_);
return v___x_3460_;
}
}
else
{
lean_object* v___x_3463_; 
lean_dec(v_k_3448_);
if (v_isShared_3454_ == 0)
{
lean_ctor_set(v___x_3453_, 0, v___x_3456_);
v___x_3463_ = v___x_3453_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v___x_3456_);
lean_ctor_set_uint8(v_reuseFailAlloc_3464_, sizeof(void*)*1, v_hasTrace_3451_);
v___x_3463_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
return v___x_3463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3___boxed(lean_object* v_o_3466_, lean_object* v_k_3467_, lean_object* v_v_3468_){
_start:
{
uint8_t v_v_boxed_3469_; lean_object* v_res_3470_; 
v_v_boxed_3469_ = lean_unbox(v_v_3468_);
v_res_3470_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3(v_o_3466_, v_k_3467_, v_v_boxed_3469_);
return v_res_3470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2(lean_object* v_opts_3471_, lean_object* v_opt_3472_, uint8_t v_val_3473_){
_start:
{
lean_object* v_name_3474_; lean_object* v___x_3475_; 
v_name_3474_ = lean_ctor_get(v_opt_3472_, 0);
lean_inc(v_name_3474_);
lean_dec_ref(v_opt_3472_);
v___x_3475_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3(v_opts_3471_, v_name_3474_, v_val_3473_);
return v___x_3475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2___boxed(lean_object* v_opts_3476_, lean_object* v_opt_3477_, lean_object* v_val_3478_){
_start:
{
uint8_t v_val_boxed_3479_; lean_object* v_res_3480_; 
v_val_boxed_3479_ = lean_unbox(v_val_3478_);
v_res_3480_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2(v_opts_3476_, v_opt_3477_, v_val_boxed_3479_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize(lean_object* v_declName_3481_, lean_object* v_info_3482_, lean_object* v_name_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_){
_start:
{
lean_object* v_toCold_3489_; lean_object* v_levelParams_3490_; lean_object* v_value_3491_; lean_object* v_currRecDepth_3492_; lean_object* v_ref_3493_; uint8_t v_suppressElabErrors_3494_; uint8_t v_isRecordingDeps_3495_; lean_object* v_fileName_3496_; lean_object* v_fileMap_3497_; lean_object* v_options_3498_; lean_object* v_currNamespace_3499_; lean_object* v_openDecls_3500_; lean_object* v_initHeartbeats_3501_; lean_object* v_maxHeartbeats_3502_; lean_object* v_quotContext_3503_; lean_object* v_currMacroScope_3504_; lean_object* v_cancelTk_x3f_3505_; lean_object* v_inheritedTraceOptions_3506_; lean_object* v___f_3507_; uint8_t v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; uint16_t v___x_3511_; lean_object* v_fileName_3513_; lean_object* v_fileMap_3514_; lean_object* v_currNamespace_3515_; lean_object* v_openDecls_3516_; lean_object* v_initHeartbeats_3517_; lean_object* v_maxHeartbeats_3518_; lean_object* v_quotContext_3519_; lean_object* v_currMacroScope_3520_; lean_object* v_cancelTk_x3f_3521_; lean_object* v_inheritedTraceOptions_3522_; lean_object* v_currRecDepth_3523_; lean_object* v_ref_3524_; uint8_t v_suppressElabErrors_3525_; uint8_t v_isRecordingDeps_3526_; lean_object* v___y_3527_; lean_object* v___x_3533_; uint8_t v___y_3535_; lean_object* v_env_3557_; uint8_t v___x_3558_; uint16_t v___x_3559_; uint16_t v___x_3560_; uint16_t v___x_3561_; uint8_t v___x_3562_; 
v_toCold_3489_ = lean_ctor_get(v_a_3486_, 0);
v_levelParams_3490_ = lean_ctor_get(v_info_3482_, 1);
lean_inc(v_levelParams_3490_);
v_value_3491_ = lean_ctor_get(v_info_3482_, 3);
lean_inc_ref(v_value_3491_);
lean_dec_ref(v_info_3482_);
v_currRecDepth_3492_ = lean_ctor_get(v_a_3486_, 1);
v_ref_3493_ = lean_ctor_get(v_a_3486_, 2);
v_suppressElabErrors_3494_ = lean_ctor_get_uint8(v_a_3486_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3495_ = lean_ctor_get_uint8(v_a_3486_, sizeof(void*)*3 + 3);
v_fileName_3496_ = lean_ctor_get(v_toCold_3489_, 0);
v_fileMap_3497_ = lean_ctor_get(v_toCold_3489_, 1);
v_options_3498_ = lean_ctor_get(v_toCold_3489_, 2);
v_currNamespace_3499_ = lean_ctor_get(v_toCold_3489_, 4);
v_openDecls_3500_ = lean_ctor_get(v_toCold_3489_, 5);
v_initHeartbeats_3501_ = lean_ctor_get(v_toCold_3489_, 6);
v_maxHeartbeats_3502_ = lean_ctor_get(v_toCold_3489_, 7);
v_quotContext_3503_ = lean_ctor_get(v_toCold_3489_, 8);
v_currMacroScope_3504_ = lean_ctor_get(v_toCold_3489_, 9);
v_cancelTk_x3f_3505_ = lean_ctor_get(v_toCold_3489_, 10);
v_inheritedTraceOptions_3506_ = lean_ctor_get(v_toCold_3489_, 11);
v___f_3507_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3507_, 0, v_levelParams_3490_);
lean_closure_set(v___f_3507_, 1, v_declName_3481_);
lean_closure_set(v___f_3507_, 2, v_name_3483_);
v___x_3508_ = 0;
v___x_3509_ = l_Lean_Meta_tactic_hygienic;
lean_inc_ref(v_options_3498_);
v___x_3510_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2(v_options_3498_, v___x_3509_, v___x_3508_);
v___x_3511_ = l_Lean_OptionFlags_ofOptions(v___x_3510_);
v___x_3533_ = lean_st_ref_get(v_a_3487_);
v_env_3557_ = lean_ctor_get(v___x_3533_, 0);
lean_inc_ref(v_env_3557_);
lean_dec(v___x_3533_);
v___x_3558_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3557_);
lean_dec_ref(v_env_3557_);
v___x_3559_ = 512;
v___x_3560_ = lean_uint16_land(v___x_3511_, v___x_3559_);
v___x_3561_ = 0;
v___x_3562_ = lean_uint16_dec_eq(v___x_3560_, v___x_3561_);
if (v___x_3562_ == 0)
{
if (v___x_3558_ == 0)
{
uint8_t v___x_3563_; 
v___x_3563_ = 1;
v___y_3535_ = v___x_3563_;
goto v___jp_3534_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_3506_);
lean_inc(v_cancelTk_x3f_3505_);
lean_inc(v_currMacroScope_3504_);
lean_inc(v_quotContext_3503_);
lean_inc(v_maxHeartbeats_3502_);
lean_inc(v_initHeartbeats_3501_);
lean_inc(v_openDecls_3500_);
lean_inc(v_currNamespace_3499_);
lean_inc_ref(v_fileMap_3497_);
lean_inc_ref(v_fileName_3496_);
v_fileName_3513_ = v_fileName_3496_;
v_fileMap_3514_ = v_fileMap_3497_;
v_currNamespace_3515_ = v_currNamespace_3499_;
v_openDecls_3516_ = v_openDecls_3500_;
v_initHeartbeats_3517_ = v_initHeartbeats_3501_;
v_maxHeartbeats_3518_ = v_maxHeartbeats_3502_;
v_quotContext_3519_ = v_quotContext_3503_;
v_currMacroScope_3520_ = v_currMacroScope_3504_;
v_cancelTk_x3f_3521_ = v_cancelTk_x3f_3505_;
v_inheritedTraceOptions_3522_ = v_inheritedTraceOptions_3506_;
v_currRecDepth_3523_ = v_currRecDepth_3492_;
v_ref_3524_ = v_ref_3493_;
v_suppressElabErrors_3525_ = v_suppressElabErrors_3494_;
v_isRecordingDeps_3526_ = v_isRecordingDeps_3495_;
v___y_3527_ = v_a_3487_;
goto v___jp_3512_;
}
}
else
{
if (v___x_3558_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_3506_);
lean_inc(v_cancelTk_x3f_3505_);
lean_inc(v_currMacroScope_3504_);
lean_inc(v_quotContext_3503_);
lean_inc(v_maxHeartbeats_3502_);
lean_inc(v_initHeartbeats_3501_);
lean_inc(v_openDecls_3500_);
lean_inc(v_currNamespace_3499_);
lean_inc_ref(v_fileMap_3497_);
lean_inc_ref(v_fileName_3496_);
v_fileName_3513_ = v_fileName_3496_;
v_fileMap_3514_ = v_fileMap_3497_;
v_currNamespace_3515_ = v_currNamespace_3499_;
v_openDecls_3516_ = v_openDecls_3500_;
v_initHeartbeats_3517_ = v_initHeartbeats_3501_;
v_maxHeartbeats_3518_ = v_maxHeartbeats_3502_;
v_quotContext_3519_ = v_quotContext_3503_;
v_currMacroScope_3520_ = v_currMacroScope_3504_;
v_cancelTk_x3f_3521_ = v_cancelTk_x3f_3505_;
v_inheritedTraceOptions_3522_ = v_inheritedTraceOptions_3506_;
v_currRecDepth_3523_ = v_currRecDepth_3492_;
v_ref_3524_ = v_ref_3493_;
v_suppressElabErrors_3525_ = v_suppressElabErrors_3494_;
v_isRecordingDeps_3526_ = v_isRecordingDeps_3495_;
v___y_3527_ = v_a_3487_;
goto v___jp_3512_;
}
else
{
v___y_3535_ = v___x_3508_;
goto v___jp_3534_;
}
}
v___jp_3512_:
{
lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; 
v___x_3528_ = l_Lean_maxRecDepth;
v___x_3529_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v___x_3510_, v___x_3528_);
v___x_3530_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3530_, 0, v_fileName_3513_);
lean_ctor_set(v___x_3530_, 1, v_fileMap_3514_);
lean_ctor_set(v___x_3530_, 2, v___x_3510_);
lean_ctor_set(v___x_3530_, 3, v___x_3529_);
lean_ctor_set(v___x_3530_, 4, v_currNamespace_3515_);
lean_ctor_set(v___x_3530_, 5, v_openDecls_3516_);
lean_ctor_set(v___x_3530_, 6, v_initHeartbeats_3517_);
lean_ctor_set(v___x_3530_, 7, v_maxHeartbeats_3518_);
lean_ctor_set(v___x_3530_, 8, v_quotContext_3519_);
lean_ctor_set(v___x_3530_, 9, v_currMacroScope_3520_);
lean_ctor_set(v___x_3530_, 10, v_cancelTk_x3f_3521_);
lean_ctor_set(v___x_3530_, 11, v_inheritedTraceOptions_3522_);
lean_inc(v_ref_3524_);
lean_inc(v_currRecDepth_3523_);
v___x_3531_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3531_, 0, v___x_3530_);
lean_ctor_set(v___x_3531_, 1, v_currRecDepth_3523_);
lean_ctor_set(v___x_3531_, 2, v_ref_3524_);
lean_ctor_set_uint16(v___x_3531_, sizeof(void*)*3, v___x_3511_);
lean_ctor_set_uint8(v___x_3531_, sizeof(void*)*3 + 2, v_suppressElabErrors_3525_);
lean_ctor_set_uint8(v___x_3531_, sizeof(void*)*3 + 3, v_isRecordingDeps_3526_);
v___x_3532_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(v_value_3491_, v___f_3507_, v___x_3508_, v_a_3484_, v_a_3485_, v___x_3531_, v___y_3527_);
lean_dec_ref_known(v___x_3531_, 3);
return v___x_3532_;
}
v___jp_3534_:
{
lean_object* v___x_3536_; lean_object* v_env_3537_; lean_object* v_nextMacroScope_3538_; lean_object* v_ngen_3539_; lean_object* v_auxDeclNGen_3540_; lean_object* v_traceState_3541_; lean_object* v_recordedDeps_3542_; lean_object* v_messages_3543_; lean_object* v_infoState_3544_; lean_object* v_snapshotTasks_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3555_; 
v___x_3536_ = lean_st_ref_take(v_a_3487_);
v_env_3537_ = lean_ctor_get(v___x_3536_, 0);
v_nextMacroScope_3538_ = lean_ctor_get(v___x_3536_, 1);
v_ngen_3539_ = lean_ctor_get(v___x_3536_, 2);
v_auxDeclNGen_3540_ = lean_ctor_get(v___x_3536_, 3);
v_traceState_3541_ = lean_ctor_get(v___x_3536_, 4);
v_recordedDeps_3542_ = lean_ctor_get(v___x_3536_, 6);
v_messages_3543_ = lean_ctor_get(v___x_3536_, 7);
v_infoState_3544_ = lean_ctor_get(v___x_3536_, 8);
v_snapshotTasks_3545_ = lean_ctor_get(v___x_3536_, 9);
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
lean_inc(v_snapshotTasks_3545_);
lean_inc(v_infoState_3544_);
lean_inc(v_messages_3543_);
lean_inc(v_recordedDeps_3542_);
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
v___x_3549_ = l_Lean_Kernel_enableDiag(v_env_3537_, v___y_3535_);
v___x_3550_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__1, &l_Lean_Elab_Structural_registerEqnsInfo___closed__1_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1);
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
lean_ctor_set(v_reuseFailAlloc_3554_, 6, v_recordedDeps_3542_);
lean_ctor_set(v_reuseFailAlloc_3554_, 7, v_messages_3543_);
lean_ctor_set(v_reuseFailAlloc_3554_, 8, v_infoState_3544_);
lean_ctor_set(v_reuseFailAlloc_3554_, 9, v_snapshotTasks_3545_);
v___x_3552_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
lean_object* v___x_3553_; 
v___x_3553_ = lean_st_ref_put(v_a_3487_, v___x_3552_);
lean_inc_ref(v_inheritedTraceOptions_3506_);
lean_inc(v_cancelTk_x3f_3505_);
lean_inc(v_currMacroScope_3504_);
lean_inc(v_quotContext_3503_);
lean_inc(v_maxHeartbeats_3502_);
lean_inc(v_initHeartbeats_3501_);
lean_inc(v_openDecls_3500_);
lean_inc(v_currNamespace_3499_);
lean_inc_ref(v_fileMap_3497_);
lean_inc_ref(v_fileName_3496_);
v_fileName_3513_ = v_fileName_3496_;
v_fileMap_3514_ = v_fileMap_3497_;
v_currNamespace_3515_ = v_currNamespace_3499_;
v_openDecls_3516_ = v_openDecls_3500_;
v_initHeartbeats_3517_ = v_initHeartbeats_3501_;
v_maxHeartbeats_3518_ = v_maxHeartbeats_3502_;
v_quotContext_3519_ = v_quotContext_3503_;
v_currMacroScope_3520_ = v_currMacroScope_3504_;
v_cancelTk_x3f_3521_ = v_cancelTk_x3f_3505_;
v_inheritedTraceOptions_3522_ = v_inheritedTraceOptions_3506_;
v_currRecDepth_3523_ = v_currRecDepth_3492_;
v_ref_3524_ = v_ref_3493_;
v_suppressElabErrors_3525_ = v_suppressElabErrors_3494_;
v_isRecordingDeps_3526_ = v_isRecordingDeps_3495_;
v___y_3527_ = v_a_3487_;
goto v___jp_3512_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___boxed(lean_object* v_declName_3564_, lean_object* v_info_3565_, lean_object* v_name_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_){
_start:
{
lean_object* v_res_3572_; 
v_res_3572_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize(v_declName_3564_, v_info_3565_, v_name_3566_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_);
lean_dec(v_a_3570_);
lean_dec_ref(v_a_3569_);
lean_dec(v_a_3568_);
lean_dec_ref(v_a_3567_);
return v_res_3572_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1(lean_object* v_00_u03b1_3573_, lean_object* v_x_3574_, uint8_t v_isExporting_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_){
_start:
{
lean_object* v___x_3581_; 
v___x_3581_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(v_x_3574_, v_isExporting_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_);
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___boxed(lean_object* v_00_u03b1_3582_, lean_object* v_x_3583_, lean_object* v_isExporting_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_){
_start:
{
uint8_t v_isExporting_boxed_3590_; lean_object* v_res_3591_; 
v_isExporting_boxed_3590_ = lean_unbox(v_isExporting_3584_);
v_res_3591_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1(v_00_u03b1_3582_, v_x_3583_, v_isExporting_boxed_3590_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec(v___y_3586_);
lean_dec_ref(v___y_3585_);
return v_res_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1(lean_object* v_00_u03b1_3592_, lean_object* v_x_3593_, uint8_t v_when_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_){
_start:
{
lean_object* v___x_3600_; 
v___x_3600_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(v_x_3593_, v_when_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_);
return v___x_3600_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___boxed(lean_object* v_00_u03b1_3601_, lean_object* v_x_3602_, lean_object* v_when_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_){
_start:
{
uint8_t v_when_boxed_3609_; lean_object* v_res_3610_; 
v_when_boxed_3609_ = lean_unbox(v_when_3603_);
v_res_3610_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1(v_00_u03b1_3601_, v_x_3602_, v_when_boxed_3609_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_);
lean_dec(v___y_3607_);
lean_dec_ref(v___y_3606_);
lean_dec(v___y_3605_);
lean_dec_ref(v___y_3604_);
return v_res_3610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq(lean_object* v_declName_3611_, lean_object* v_info_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_){
_start:
{
lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v_env_3620_; lean_object* v_declName_3621_; lean_object* v_declNames_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; 
v___x_3618_ = lean_box(0);
v___x_3619_ = lean_st_ref_get(v_a_3616_);
v_env_3620_ = lean_ctor_get(v___x_3619_, 0);
lean_inc_ref(v_env_3620_);
lean_dec(v___x_3619_);
v_declName_3621_ = lean_ctor_get(v_info_3612_, 0);
v_declNames_3622_ = lean_ctor_get(v_info_3612_, 5);
v___x_3623_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc(v_declName_3621_);
v___x_3624_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3620_, v_declName_3621_, v___x_3623_);
v___x_3625_ = lean_unsigned_to_nat(0u);
v___x_3626_ = lean_array_get(v___x_3618_, v_declNames_3622_, v___x_3625_);
lean_inc_n(v___x_3624_, 2);
lean_inc(v_declName_3611_);
v___x_3627_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___boxed), 8, 3);
lean_closure_set(v___x_3627_, 0, v_declName_3611_);
lean_closure_set(v___x_3627_, 1, v_info_3612_);
lean_closure_set(v___x_3627_, 2, v___x_3624_);
v___x_3628_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_3628_, 0, lean_box(0));
lean_closure_set(v___x_3628_, 1, v_declName_3611_);
lean_closure_set(v___x_3628_, 2, v___x_3627_);
v___x_3629_ = l_Lean_Meta_realizeConst(v___x_3626_, v___x_3624_, v___x_3628_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_);
if (lean_obj_tag(v___x_3629_) == 0)
{
lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3636_; 
v_isSharedCheck_3636_ = !lean_is_exclusive(v___x_3629_);
if (v_isSharedCheck_3636_ == 0)
{
lean_object* v_unused_3637_; 
v_unused_3637_ = lean_ctor_get(v___x_3629_, 0);
lean_dec(v_unused_3637_);
v___x_3631_ = v___x_3629_;
v_isShared_3632_ = v_isSharedCheck_3636_;
goto v_resetjp_3630_;
}
else
{
lean_dec(v___x_3629_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3636_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
lean_object* v___x_3634_; 
if (v_isShared_3632_ == 0)
{
lean_ctor_set(v___x_3631_, 0, v___x_3624_);
v___x_3634_ = v___x_3631_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v___x_3624_);
v___x_3634_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
return v___x_3634_;
}
}
}
else
{
lean_object* v_a_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3645_; 
lean_dec(v___x_3624_);
v_a_3638_ = lean_ctor_get(v___x_3629_, 0);
v_isSharedCheck_3645_ = !lean_is_exclusive(v___x_3629_);
if (v_isSharedCheck_3645_ == 0)
{
v___x_3640_ = v___x_3629_;
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_a_3638_);
lean_dec(v___x_3629_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v___x_3643_; 
if (v_isShared_3641_ == 0)
{
v___x_3643_ = v___x_3640_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v_a_3638_);
v___x_3643_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
return v___x_3643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq___boxed(lean_object* v_declName_3646_, lean_object* v_info_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_){
_start:
{
lean_object* v_res_3653_; 
v_res_3653_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq(v_declName_3646_, v_info_3647_, v_a_3648_, v_a_3649_, v_a_3650_, v_a_3651_);
lean_dec(v_a_3651_);
lean_dec_ref(v_a_3650_);
lean_dec(v_a_3649_);
lean_dec_ref(v_a_3648_);
return v_res_3653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f(lean_object* v_declName_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_){
_start:
{
lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v_env_3662_; lean_object* v___x_3663_; lean_object* v_toEnvExtension_3664_; lean_object* v_asyncMode_3665_; uint8_t v___x_3666_; lean_object* v___x_3667_; 
v___x_3660_ = l_Lean_Elab_Structural_instInhabitedEqnInfo_default;
v___x_3661_ = lean_st_ref_get(v_a_3658_);
v_env_3662_ = lean_ctor_get(v___x_3661_, 0);
lean_inc_ref(v_env_3662_);
lean_dec(v___x_3661_);
v___x_3663_ = l_Lean_Elab_Structural_eqnInfoExt;
v_toEnvExtension_3664_ = lean_ctor_get(v___x_3663_, 0);
v_asyncMode_3665_ = lean_ctor_get(v_toEnvExtension_3664_, 2);
v___x_3666_ = 0;
lean_inc(v_declName_3654_);
v___x_3667_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_3660_, v___x_3663_, v_env_3662_, v_declName_3654_, v_asyncMode_3665_, v___x_3666_);
if (lean_obj_tag(v___x_3667_) == 1)
{
lean_object* v_val_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3692_; 
v_val_3668_ = lean_ctor_get(v___x_3667_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3667_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3670_ = v___x_3667_;
v_isShared_3671_ = v_isSharedCheck_3692_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_val_3668_);
lean_dec(v___x_3667_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3692_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v___x_3672_; 
v___x_3672_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq(v_declName_3654_, v_val_3668_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_);
if (lean_obj_tag(v___x_3672_) == 0)
{
lean_object* v_a_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3683_; 
v_a_3673_ = lean_ctor_get(v___x_3672_, 0);
v_isSharedCheck_3683_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3675_ = v___x_3672_;
v_isShared_3676_ = v_isSharedCheck_3683_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_a_3673_);
lean_dec(v___x_3672_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3683_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v___x_3678_; 
if (v_isShared_3671_ == 0)
{
lean_ctor_set(v___x_3670_, 0, v_a_3673_);
v___x_3678_ = v___x_3670_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_a_3673_);
v___x_3678_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
lean_object* v___x_3680_; 
if (v_isShared_3676_ == 0)
{
lean_ctor_set(v___x_3675_, 0, v___x_3678_);
v___x_3680_ = v___x_3675_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v___x_3678_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
}
}
else
{
lean_object* v_a_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3691_; 
lean_del_object(v___x_3670_);
v_a_3684_ = lean_ctor_get(v___x_3672_, 0);
v_isSharedCheck_3691_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3686_ = v___x_3672_;
v_isShared_3687_ = v_isSharedCheck_3691_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_a_3684_);
lean_dec(v___x_3672_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3691_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v___x_3689_; 
if (v_isShared_3687_ == 0)
{
v___x_3689_ = v___x_3686_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_a_3684_);
v___x_3689_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
return v___x_3689_;
}
}
}
}
}
else
{
lean_object* v___x_3693_; lean_object* v___x_3694_; 
lean_dec(v___x_3667_);
lean_dec(v_declName_3654_);
v___x_3693_ = lean_box(0);
v___x_3694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3694_, 0, v___x_3693_);
return v___x_3694_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f___boxed(lean_object* v_declName_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_){
_start:
{
lean_object* v_res_3701_; 
v_res_3701_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f(v_declName_3695_, v_a_3696_, v_a_3697_, v_a_3698_, v_a_3699_);
lean_dec(v_a_3699_);
lean_dec_ref(v_a_3698_);
lean_dec(v_a_3697_);
lean_dec_ref(v_a_3696_);
return v_res_3701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(lean_object* v_declName_3702_, lean_object* v_a_3703_){
_start:
{
lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v_env_3707_; lean_object* v___x_3708_; lean_object* v_toEnvExtension_3709_; lean_object* v_asyncMode_3710_; uint8_t v___x_3711_; lean_object* v___x_3712_; 
v___x_3705_ = l_Lean_Elab_Structural_instInhabitedEqnInfo_default;
v___x_3706_ = lean_st_ref_get(v_a_3703_);
v_env_3707_ = lean_ctor_get(v___x_3706_, 0);
lean_inc_ref(v_env_3707_);
lean_dec(v___x_3706_);
v___x_3708_ = l_Lean_Elab_Structural_eqnInfoExt;
v_toEnvExtension_3709_ = lean_ctor_get(v___x_3708_, 0);
v_asyncMode_3710_ = lean_ctor_get(v_toEnvExtension_3709_, 2);
v___x_3711_ = 0;
v___x_3712_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_3705_, v___x_3708_, v_env_3707_, v_declName_3702_, v_asyncMode_3710_, v___x_3711_);
if (lean_obj_tag(v___x_3712_) == 1)
{
lean_object* v_val_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3722_; 
v_val_3713_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3715_ = v___x_3712_;
v_isShared_3716_ = v_isSharedCheck_3722_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_val_3713_);
lean_dec(v___x_3712_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3722_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v_recArgPos_3717_; lean_object* v___x_3719_; 
v_recArgPos_3717_ = lean_ctor_get(v_val_3713_, 4);
lean_inc(v_recArgPos_3717_);
lean_dec(v_val_3713_);
if (v_isShared_3716_ == 0)
{
lean_ctor_set(v___x_3715_, 0, v_recArgPos_3717_);
v___x_3719_ = v___x_3715_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_recArgPos_3717_);
v___x_3719_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
lean_object* v___x_3720_; 
v___x_3720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3720_, 0, v___x_3719_);
return v___x_3720_;
}
}
}
else
{
lean_object* v___x_3723_; lean_object* v___x_3724_; 
lean_dec(v___x_3712_);
v___x_3723_ = lean_box(0);
v___x_3724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3723_);
return v___x_3724_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg___boxed(lean_object* v_declName_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_){
_start:
{
lean_object* v_res_3728_; 
v_res_3728_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(v_declName_3725_, v_a_3726_);
lean_dec(v_a_3726_);
return v_res_3728_;
}
}
LEAN_EXPORT lean_object* lean_get_structural_rec_arg_pos(lean_object* v_declName_3729_, lean_object* v_a_3730_, lean_object* v_a_3731_){
_start:
{
lean_object* v___x_3733_; 
lean_dec_ref(v_a_3730_);
v___x_3733_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(v_declName_3729_, v_a_3731_);
lean_dec(v_a_3731_);
return v___x_3733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___boxed(lean_object* v_declName_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_){
_start:
{
lean_object* v_res_3738_; 
v_res_3738_ = lean_get_structural_rec_arg_pos(v_declName_3734_, v_a_3735_, v_a_3736_);
return v_res_3738_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; 
v___x_3796_ = lean_unsigned_to_nat(2295916746u);
v___x_3797_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__22_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_3798_ = l_Lean_Name_num___override(v___x_3797_, v___x_3796_);
return v___x_3798_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; 
v___x_3800_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__24_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_3801_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_3802_ = l_Lean_Name_str___override(v___x_3801_, v___x_3800_);
return v___x_3802_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; 
v___x_3804_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__26_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_3805_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_3806_ = l_Lean_Name_str___override(v___x_3805_, v___x_3804_);
return v___x_3806_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; 
v___x_3807_ = lean_unsigned_to_nat(2u);
v___x_3808_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_3809_ = l_Lean_Name_num___override(v___x_3808_, v___x_3807_);
return v___x_3809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3811_; lean_object* v___x_3812_; 
v___x_3811_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_3812_ = l_Lean_Meta_registerGetUnfoldEqnFn(v___x_3811_);
if (lean_obj_tag(v___x_3812_) == 0)
{
lean_object* v___x_3813_; uint8_t v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; 
lean_dec_ref_known(v___x_3812_, 1);
v___x_3813_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17));
v___x_3814_ = 0;
v___x_3815_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_3816_ = l_Lean_registerTraceClass(v___x_3813_, v___x_3814_, v___x_3815_);
return v___x_3816_;
}
else
{
return v___x_3812_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2____boxed(lean_object* v_a_3817_){
_start:
{
lean_object* v_res_3818_; 
v_res_3818_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_();
return v_res_3818_;
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
