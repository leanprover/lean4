// Lean compiler output
// Module: Lean.Elab.PreDefinition.PartialFixpoint.Main
// Imports: public import Lean.Elab.PreDefinition.MkInhabitant public import Lean.Elab.PreDefinition.Mutual public import Lean.Elab.PreDefinition.PartialFixpoint.Eqns public import Lean.Elab.Tactic.Monotonicity public import Lean.Meta.Order
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_toPartialOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedPartialFixpoint_default;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_Term_logUnassignedUsingErrorInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSorry(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_hasRecAppSyntax___boxed(lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_Lean_getRecAppSyntax_x3f(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_andList(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Meta_PProdN_mk(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_replace_expr(lean_object*, lean_object*);
lean_object* l_Lean_Meta_PProdN_reduceProjs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_betaReduce(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Elab_addAsAxiom___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_Monotonicity_solveMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapErrorImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_PProdN_proj(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Elab_Mutual_cleanPreDef(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkInstPiOfInstsForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Elab_isLatticeTheoretic(uint8_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkInhabitantFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_PProdN_pack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_mkPackedPPRodInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_PProdN_genMk___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFixOfMonFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAndCompilePartialRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Mutual_addPreDefAttributes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_FixedParamPerms_fixedArePrefix(lean_object*);
lean_object* l_Lean_Elab_getFixedParamPerms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedPreDefinition_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__0___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__1_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__1___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__0;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Lean.Elab.PreDefinition.PartialFixpoint.Main"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__0_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 81, .m_capacity = 81, .m_length = 80, .m_data = "_private.Lean.Elab.PreDefinition.PartialFixpoint.Main.0.Lean.Elab.replaceRecApps"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__1_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "assertion violation: recFnNames.size = fixedParamPerms.perms.size\n  "};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__3___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__0;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__1;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Expected lambda:"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "mkMonoPProd: unexpected type of"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__1;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__2_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__3_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "monotone"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__3_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__4_value),LEAN_SCALAR_PTR_LITERAL(61, 86, 242, 24, 111, 107, 219, 193)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__5_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PProd"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__6 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__6_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "monotone_mk"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__7 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__3_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__6_value),LEAN_SCALAR_PTR_LITERAL(141, 95, 229, 62, 87, 161, 97, 26)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__7_value),LEAN_SCALAR_PTR_LITERAL(238, 227, 132, 104, 89, 25, 150, 95)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__8 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__9;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__10;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__20___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Elab_partialFixpoint_spec__25___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__25___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__22___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9___closed__0_value;
static lean_once_cell_t l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9___closed__1;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9(lean_object*, lean_object*);
static const lean_closure_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_hasRecAppSyntax___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__0_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Cannot eliminate recursive call `"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__1 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__1_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__2;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "` enclosed in"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__3 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__3_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__4;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__5 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__5_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__6;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Elab.partialFixpoint"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__7 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__7_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "getRecAppSyntax\? failed"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__8 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__8_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__9;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Cannot eliminate recursive call in"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__10 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__10_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__11;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Tried to apply "};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__12 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__12_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__13;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = ", but failed.\nPossible cause: A missing `"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__14 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__14_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__15;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "MonoBind"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__16 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__16_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__3_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__17_value_aux_1),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__16_value),LEAN_SCALAR_PTR_LITERAL(150, 25, 7, 134, 163, 66, 53, 232)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__17 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__17_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "` instance.\nUse `set_option trace.Elab.Tactic.monotonicity true` to debug."};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__18 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__18_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__19;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__20;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Could not prove '"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__0_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__1;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "' to be monotone in its recursive calls:"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__2 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__2_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__3;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__4 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__4_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__5 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__5_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "partialFixpoint"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__6 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__6_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7_value_aux_0),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7_value_aux_1),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(21, 214, 78, 192, 157, 92, 193, 45)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__8 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__8_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__9 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__9_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "monotonicity proof for "};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__11 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__11_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__12;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__13 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__13_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__14;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__23(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__23___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "f"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___closed__0_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 68, 183, 24, 128, 148, 178, 23)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___closed__1 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___boxed(lean_object**);
static lean_once_cell_t l_Lean_Elab_partialFixpoint___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_partialFixpoint___lam__0___closed__0;
static const lean_closure_object l_Lean_Elab_partialFixpoint___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_partialFixpoint___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_partialFixpoint___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_partialFixpoint___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mutual"};
static const lean_object* l_Lean_Elab_partialFixpoint___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_partialFixpoint___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Elab_partialFixpoint___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_partialFixpoint___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(46, 227, 38, 90, 242, 200, 93, 238)}};
static const lean_object* l_Lean_Elab_partialFixpoint___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_partialFixpoint___lam__0___closed__3_value;
static const lean_string_object l_Lean_Elab_partialFixpoint___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "packedValue: "};
static const lean_object* l_Lean_Elab_partialFixpoint___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_partialFixpoint___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Elab_partialFixpoint___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_partialFixpoint___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_partialFixpoint___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_partialFixpoint___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27_spec__33(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27_spec__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__7___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "failed to compile definition '"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__0_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__1;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "' using `partial_fixpoint`"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__2 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__2_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__3;
static const lean_array_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__4 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__4_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Nonempty"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__5 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__5_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__6 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__6_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(142, 191, 110, 220, 210, 100, 152, 183)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__7_value_aux_0),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__6_value),LEAN_SCALAR_PTR_LITERAL(113, 209, 180, 93, 84, 117, 67, 110)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__7 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__7_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Classical"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__8 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__8_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ofNonempty"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__9 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__9_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__8_value),LEAN_SCALAR_PTR_LITERAL(40, 236, 220, 79, 38, 141, 161, 150)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__10_value_aux_0),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__9_value),LEAN_SCALAR_PTR_LITERAL(197, 41, 144, 91, 215, 43, 73, 12)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__10 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__10_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__11;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "FlatOrder"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__12 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__12_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instCCPO"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__13 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__13_value;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__4(lean_object*, lean_object*);
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "No CCPO instance found for "};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__0_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__1;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = ", trying inhabitation"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__2 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__2_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__3;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "CCPO"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__4 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__4_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__3_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__5_value_aux_1),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(19, 35, 8, 63, 189, 207, 68, 204)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__5 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__5_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "preDef.value: "};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__6 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__6_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__7;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = ", xs: "};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__8 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__8_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__9;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = ", _body: "};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__10 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__10_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__11;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__10___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ImplicationOrder"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__0_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "instCompleteLattice"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__1 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__1_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__3_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__2_value_aux_1),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(106, 240, 34, 128, 168, 240, 126, 19)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__2_value_aux_2),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(89, 9, 5, 228, 125, 57, 241, 212)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__2 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__2_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__3;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "`inductive_fixpoint` can be only used to define predicates"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__4 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__4_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__5;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "ReverseImplicationOrder"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__3_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__1_value_aux_1),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 161, 0, 6, 7, 21, 122, 42)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__1_value_aux_2),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(58, 218, 120, 132, 216, 84, 59, 130)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__1 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__1_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__2;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "`coinductive_fixpoint` can be only used to define predicates"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__3 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__3_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___closed__0_value;
static const lean_closure_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___closed__1 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__26_spec__31(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__26_spec__31___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__26(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__26___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_partialFixpoint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 116, .m_capacity = 116, .m_length = 115, .m_data = "assertion violation: preDefs.size = hints.size\n  -- We check if any fixpoints were defined lattice-theoretically\n  "};
static const lean_object* l_Lean_Elab_partialFixpoint___closed__0 = (const lean_object*)&l_Lean_Elab_partialFixpoint___closed__0_value;
static lean_once_cell_t l_Lean_Elab_partialFixpoint___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_partialFixpoint___closed__1;
static const lean_string_object l_Lean_Elab_partialFixpoint___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 218, .m_capacity = 218, .m_length = 213, .m_data = "assertion violation: hints.all fun x => isLatticeTheoretic x.fixpointType\n\n  -- For every function of type `∀ x y, r x y`, an CCPO instance\n  -- ∀ x y, CCPO (r x y), but crucially constructed using `instCCPOPi`\n  "};
static const lean_object* l_Lean_Elab_partialFixpoint___closed__2 = (const lean_object*)&l_Lean_Elab_partialFixpoint___closed__2_value;
static lean_once_cell_t l_Lean_Elab_partialFixpoint___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_partialFixpoint___closed__3;
static const lean_ctor_object l_Lean_Elab_partialFixpoint___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_Lean_Elab_partialFixpoint___boxed__const__1 = (const lean_object*)&l_Lean_Elab_partialFixpoint___boxed__const__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_partialFixpoint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_partialFixpoint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__22(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PreDefinition"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 172, 242, 185, 134, 214, 81, 182)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "PartialFixpoint"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__7_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__5_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(2, 13, 156, 207, 122, 14, 28, 133)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__7_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__7_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__8_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Main"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__8_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__8_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__9_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__7_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__8_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(175, 96, 209, 13, 184, 65, 254, 199)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__9_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__9_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__10_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__9_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(194, 168, 143, 49, 5, 114, 84, 87)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__10_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__10_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__11_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__11_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__11_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__12_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__10_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__11_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(55, 63, 80, 115, 56, 55, 131, 89)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__12_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__12_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__13_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__13_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__13_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__14_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__12_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__13_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(114, 0, 255, 206, 131, 161, 14, 13)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__14_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__14_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__15_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__14_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(243, 122, 71, 12, 44, 36, 157, 15)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__15_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__15_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__16_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__15_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(165, 120, 90, 26, 169, 90, 9, 167)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__16_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__16_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__17_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__16_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__4_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(14, 231, 67, 236, 91, 1, 141, 220)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__17_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__17_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__18_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__17_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__6_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(239, 128, 14, 179, 44, 110, 108, 17)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__18_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__18_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__19_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__18_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__8_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(54, 40, 28, 167, 73, 131, 219, 150)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__19_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__19_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__20_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__19_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1869300320) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(195, 94, 159, 117, 161, 139, 38, 203)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__20_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__20_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__21_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__21_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__21_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__22_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__20_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__21_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 109, 32, 139, 182, 114, 148, 178)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__22_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__22_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__24_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__22_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__23_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(124, 25, 54, 142, 91, 168, 16, 92)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__24_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__24_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__25_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__24_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(37, 21, 150, 201, 150, 88, 20, 42)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__25_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__25_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__0(lean_object* v_msg_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_){
_start:
{
lean_object* v___f_8_; lean_object* v___x_710__overap_9_; lean_object* v___x_10_; 
v___f_8_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__0___closed__0));
v___x_710__overap_9_ = lean_panic_fn_borrowed(v___f_8_, v_msg_2_);
lean_inc(v___y_6_);
lean_inc_ref(v___y_5_);
lean_inc(v___y_4_);
lean_inc_ref(v___y_3_);
v___x_10_ = lean_apply_5(v___x_710__overap_9_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, lean_box(0));
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__0___boxed(lean_object* v_msg_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__0(v_msg_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_);
lean_dec(v___y_15_);
lean_dec_ref(v___y_14_);
lean_dec(v___y_13_);
lean_dec_ref(v___y_12_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__1_spec__1_spec__2(lean_object* v_xs_18_, lean_object* v_v_19_, lean_object* v_i_20_){
_start:
{
lean_object* v___x_21_; uint8_t v___x_22_; 
v___x_21_ = lean_array_get_size(v_xs_18_);
v___x_22_ = lean_nat_dec_lt(v_i_20_, v___x_21_);
if (v___x_22_ == 0)
{
lean_object* v___x_23_; 
lean_dec(v_i_20_);
v___x_23_ = lean_box(0);
return v___x_23_;
}
else
{
lean_object* v___x_24_; uint8_t v___x_25_; 
v___x_24_ = lean_array_fget_borrowed(v_xs_18_, v_i_20_);
v___x_25_ = lean_name_eq(v___x_24_, v_v_19_);
if (v___x_25_ == 0)
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = lean_unsigned_to_nat(1u);
v___x_27_ = lean_nat_add(v_i_20_, v___x_26_);
lean_dec(v_i_20_);
v_i_20_ = v___x_27_;
goto _start;
}
else
{
lean_object* v___x_29_; 
v___x_29_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_29_, 0, v_i_20_);
return v___x_29_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__1_spec__1_spec__2___boxed(lean_object* v_xs_30_, lean_object* v_v_31_, lean_object* v_i_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__1_spec__1_spec__2(v_xs_30_, v_v_31_, v_i_32_);
lean_dec(v_v_31_);
lean_dec_ref(v_xs_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__1_spec__1(lean_object* v_xs_34_, lean_object* v_v_35_){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_unsigned_to_nat(0u);
v___x_37_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__1_spec__1_spec__2(v_xs_34_, v_v_35_, v___x_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__1_spec__1___boxed(lean_object* v_xs_38_, lean_object* v_v_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__1_spec__1(v_xs_38_, v_v_39_);
lean_dec(v_v_39_);
lean_dec_ref(v_xs_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__1(lean_object* v_xs_41_, lean_object* v_v_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__1_spec__1(v_xs_41_, v_v_42_);
if (lean_obj_tag(v___x_43_) == 0)
{
lean_object* v___x_44_; 
v___x_44_ = lean_box(0);
return v___x_44_;
}
else
{
lean_object* v_val_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_52_; 
v_val_45_ = lean_ctor_get(v___x_43_, 0);
v_isSharedCheck_52_ = !lean_is_exclusive(v___x_43_);
if (v_isSharedCheck_52_ == 0)
{
v___x_47_ = v___x_43_;
v_isShared_48_ = v_isSharedCheck_52_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_val_45_);
lean_dec(v___x_43_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_52_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_50_; 
if (v_isShared_48_ == 0)
{
v___x_50_ = v___x_47_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v_val_45_);
v___x_50_ = v_reuseFailAlloc_51_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
return v___x_50_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__1___boxed(lean_object* v_xs_53_, lean_object* v_v_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__1(v_xs_53_, v_v_54_);
lean_dec(v_v_54_);
lean_dec_ref(v_xs_53_);
return v_res_55_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__0(void){
_start:
{
lean_object* v___x_56_; lean_object* v_dummy_57_; 
v___x_56_ = lean_box(0);
v_dummy_57_ = l_Lean_Expr_sort___override(v___x_56_);
return v_dummy_57_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1(void){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Array_instInhabited(lean_box(0));
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0(lean_object* v_recFnNames_59_, lean_object* v_perms_60_, lean_object* v___x_61_, lean_object* v_a_62_, lean_object* v_f_63_, lean_object* v_e_64_){
_start:
{
lean_object* v___x_65_; uint8_t v___x_66_; 
v___x_65_ = l_Lean_Expr_getAppFn(v_e_64_);
v___x_66_ = l_Lean_Expr_isConst(v___x_65_);
if (v___x_66_ == 0)
{
lean_object* v___x_67_; 
lean_dec_ref(v___x_65_);
lean_dec_ref(v_e_64_);
lean_dec_ref(v_f_63_);
lean_dec_ref(v_a_62_);
v___x_67_ = lean_box(0);
return v___x_67_;
}
else
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = l_Lean_Expr_constName_x21(v___x_65_);
lean_dec_ref(v___x_65_);
v___x_69_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__1(v_recFnNames_59_, v___x_68_);
lean_dec(v___x_68_);
if (lean_obj_tag(v___x_69_) == 0)
{
lean_object* v___x_70_; 
lean_dec_ref(v_e_64_);
lean_dec_ref(v_f_63_);
lean_dec_ref(v_a_62_);
v___x_70_ = lean_box(0);
return v___x_70_;
}
else
{
lean_object* v_val_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_89_; 
v_val_71_ = lean_ctor_get(v___x_69_, 0);
v_isSharedCheck_89_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_89_ == 0)
{
v___x_73_ = v___x_69_;
v_isShared_74_ = v_isSharedCheck_89_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_val_71_);
lean_dec(v___x_69_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_89_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v_dummy_75_; lean_object* v_nargs_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_87_; 
v_dummy_75_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__0, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__0);
v_nargs_76_ = l_Lean_Expr_getAppNumArgs(v_e_64_);
lean_inc(v_nargs_76_);
v___x_77_ = lean_mk_array(v_nargs_76_, v_dummy_75_);
v___x_78_ = lean_unsigned_to_nat(1u);
v___x_79_ = lean_nat_sub(v_nargs_76_, v___x_78_);
lean_dec(v_nargs_76_);
v___x_80_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_64_, v___x_77_, v___x_79_);
v___x_81_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1);
v___x_82_ = lean_array_get_borrowed(v___x_81_, v_perms_60_, v_val_71_);
v___x_83_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v___x_82_, v___x_80_);
lean_dec_ref(v___x_80_);
v___x_84_ = l_Lean_Meta_PProdN_proj(v___x_61_, v_val_71_, v_a_62_, v_f_63_);
lean_dec(v_val_71_);
v___x_85_ = l_Lean_mkAppN(v___x_84_, v___x_83_);
lean_dec_ref(v___x_83_);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 0, v___x_85_);
v___x_87_ = v___x_73_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_85_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___boxed(lean_object* v_recFnNames_90_, lean_object* v_perms_91_, lean_object* v___x_92_, lean_object* v_a_93_, lean_object* v_f_94_, lean_object* v_e_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0(v_recFnNames_90_, v_perms_91_, v___x_92_, v_a_93_, v_f_94_, v_e_95_);
lean_dec(v___x_92_);
lean_dec_ref(v_perms_91_);
lean_dec_ref(v_recFnNames_90_);
return v_res_96_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__3(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_100_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__2));
v___x_101_ = lean_unsigned_to_nat(2u);
v___x_102_ = lean_unsigned_to_nat(25u);
v___x_103_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__1));
v___x_104_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__0));
v___x_105_ = l_mkPanicMessageWithDecl(v___x_104_, v___x_103_, v___x_102_, v___x_101_, v___x_100_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps(lean_object* v_recFnNames_106_, lean_object* v_fixedParamPerms_107_, lean_object* v_f_108_, lean_object* v_e_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
lean_object* v_perms_115_; lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v_perms_115_ = lean_ctor_get(v_fixedParamPerms_107_, 1);
lean_inc_ref(v_perms_115_);
lean_dec_ref(v_fixedParamPerms_107_);
v___x_116_ = lean_array_get_size(v_recFnNames_106_);
v___x_117_ = lean_array_get_size(v_perms_115_);
v___x_118_ = lean_nat_dec_eq(v___x_116_, v___x_117_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; lean_object* v___x_120_; 
lean_dec_ref(v_perms_115_);
lean_dec_ref(v_f_108_);
lean_dec_ref(v_recFnNames_106_);
v___x_119_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__3, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__3);
v___x_120_ = l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__0(v___x_119_, v_a_110_, v_a_111_, v_a_112_, v_a_113_);
return v___x_120_;
}
else
{
lean_object* v___x_121_; 
lean_inc(v_a_113_);
lean_inc_ref(v_a_112_);
lean_inc(v_a_111_);
lean_inc_ref(v_a_110_);
lean_inc_ref(v_f_108_);
v___x_121_ = lean_infer_type(v_f_108_, v_a_110_, v_a_111_, v_a_112_, v_a_113_);
if (lean_obj_tag(v___x_121_) == 0)
{
lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_131_; 
v_a_122_ = lean_ctor_get(v___x_121_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_131_ == 0)
{
v___x_124_ = v___x_121_;
v_isShared_125_ = v_isSharedCheck_131_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_dec(v___x_121_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_131_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___f_126_; lean_object* v___x_127_; lean_object* v___x_129_; 
v___f_126_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___boxed), 6, 5);
lean_closure_set(v___f_126_, 0, v_recFnNames_106_);
lean_closure_set(v___f_126_, 1, v_perms_115_);
lean_closure_set(v___f_126_, 2, v___x_116_);
lean_closure_set(v___f_126_, 3, v_a_122_);
lean_closure_set(v___f_126_, 4, v_f_108_);
v___x_127_ = lean_replace_expr(v___f_126_, v_e_109_);
lean_dec_ref(v___f_126_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 0, v___x_127_);
v___x_129_ = v___x_124_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_127_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
else
{
lean_dec_ref(v_perms_115_);
lean_dec_ref(v_f_108_);
lean_dec_ref(v_recFnNames_106_);
return v___x_121_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___boxed(lean_object* v_recFnNames_132_, lean_object* v_fixedParamPerms_133_, lean_object* v_f_134_, lean_object* v_e_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps(v_recFnNames_132_, v_fixedParamPerms_133_, v_f_134_, v_e_135_, v_a_136_, v_a_137_, v_a_138_, v_a_139_);
lean_dec(v_a_139_);
lean_dec_ref(v_a_138_);
lean_dec(v_a_137_);
lean_dec_ref(v_a_136_);
lean_dec_ref(v_e_135_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__1___redArg___lam__0(lean_object* v_k_142_, lean_object* v_b_143_, lean_object* v_c_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
lean_object* v___x_150_; 
lean_inc(v___y_148_);
lean_inc_ref(v___y_147_);
lean_inc(v___y_146_);
lean_inc_ref(v___y_145_);
v___x_150_ = lean_apply_7(v_k_142_, v_b_143_, v_c_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, lean_box(0));
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__1___redArg___lam__0___boxed(lean_object* v_k_151_, lean_object* v_b_152_, lean_object* v_c_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__1___redArg___lam__0(v_k_151_, v_b_152_, v_c_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_);
lean_dec(v___y_157_);
lean_dec_ref(v___y_156_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__1___redArg(lean_object* v_e_160_, lean_object* v_k_161_, uint8_t v_cleanupAnnotations_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
lean_object* v___f_168_; uint8_t v___x_169_; uint8_t v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___f_168_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_168_, 0, v_k_161_);
v___x_169_ = 1;
v___x_170_ = 0;
v___x_171_ = lean_box(0);
v___x_172_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_160_, v___x_169_, v___x_170_, v___x_169_, v___x_170_, v___x_171_, v___f_168_, v_cleanupAnnotations_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__1___redArg___boxed(lean_object* v_e_189_, lean_object* v_k_190_, lean_object* v_cleanupAnnotations_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_197_; lean_object* v_res_198_; 
v_cleanupAnnotations_boxed_197_ = lean_unbox(v_cleanupAnnotations_191_);
v_res_198_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__1___redArg(v_e_189_, v_k_190_, v_cleanupAnnotations_boxed_197_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__1(lean_object* v_00_u03b1_199_, lean_object* v_e_200_, lean_object* v_k_201_, uint8_t v_cleanupAnnotations_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__1___redArg(v_e_200_, v_k_201_, v_cleanupAnnotations_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__1___boxed(lean_object* v_00_u03b1_209_, lean_object* v_e_210_, lean_object* v_k_211_, lean_object* v_cleanupAnnotations_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_218_; lean_object* v_res_219_; 
v_cleanupAnnotations_boxed_218_ = lean_unbox(v_cleanupAnnotations_212_);
v_res_219_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__1(v_00_u03b1_209_, v_e_210_, v_k_211_, v_cleanupAnnotations_boxed_218_, v___y_213_, v___y_214_, v___y_215_, v___y_216_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__3___redArg(lean_object* v_e_220_, lean_object* v_maxFVars_221_, lean_object* v_k_222_, uint8_t v_cleanupAnnotations_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v___f_229_; uint8_t v___x_230_; uint8_t v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___f_229_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_229_, 0, v_k_222_);
v___x_230_ = 1;
v___x_231_ = 0;
v___x_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_232_, 0, v_maxFVars_221_);
v___x_233_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_220_, v___x_230_, v___x_231_, v___x_230_, v___x_231_, v___x_232_, v___f_229_, v_cleanupAnnotations_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_);
lean_dec_ref(v___x_232_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_241_; 
v_a_234_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_241_ == 0)
{
v___x_236_ = v___x_233_;
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_233_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_239_; 
if (v_isShared_237_ == 0)
{
v___x_239_ = v___x_236_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_234_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
else
{
lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_249_; 
v_a_242_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_249_ == 0)
{
v___x_244_ = v___x_233_;
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v___x_233_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_247_; 
if (v_isShared_245_ == 0)
{
v___x_247_ = v___x_244_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_a_242_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__3___redArg___boxed(lean_object* v_e_250_, lean_object* v_maxFVars_251_, lean_object* v_k_252_, lean_object* v_cleanupAnnotations_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_259_; lean_object* v_res_260_; 
v_cleanupAnnotations_boxed_259_ = lean_unbox(v_cleanupAnnotations_253_);
v_res_260_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__3___redArg(v_e_250_, v_maxFVars_251_, v_k_252_, v_cleanupAnnotations_boxed_259_, v___y_254_, v___y_255_, v___y_256_, v___y_257_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__3(lean_object* v_00_u03b1_261_, lean_object* v_e_262_, lean_object* v_maxFVars_263_, lean_object* v_k_264_, uint8_t v_cleanupAnnotations_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__3___redArg(v_e_262_, v_maxFVars_263_, v_k_264_, v_cleanupAnnotations_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__3___boxed(lean_object* v_00_u03b1_272_, lean_object* v_e_273_, lean_object* v_maxFVars_274_, lean_object* v_k_275_, lean_object* v_cleanupAnnotations_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_282_; lean_object* v_res_283_; 
v_cleanupAnnotations_boxed_282_ = lean_unbox(v_cleanupAnnotations_276_);
v_res_283_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__3(v_00_u03b1_272_, v_e_273_, v_maxFVars_274_, v_k_275_, v_cleanupAnnotations_boxed_282_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___lam__0(lean_object* v___x_284_, lean_object* v_a_285_, lean_object* v_e_286_){
_start:
{
uint8_t v___x_287_; 
v___x_287_ = lean_expr_eqv(v_e_286_, v___x_284_);
if (v___x_287_ == 0)
{
lean_object* v___x_288_; 
lean_dec_ref(v_a_285_);
v___x_288_ = lean_box(0);
return v___x_288_;
}
else
{
lean_object* v___x_289_; 
v___x_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_289_, 0, v_a_285_);
return v___x_289_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___lam__0___boxed(lean_object* v___x_290_, lean_object* v_a_291_, lean_object* v_e_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___lam__0(v___x_290_, v_a_291_, v_e_292_);
lean_dec_ref(v_e_292_);
lean_dec_ref(v___x_290_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___lam__1(lean_object* v___x_294_, lean_object* v___x_295_, lean_object* v_a_296_, lean_object* v_f_297_, lean_object* v_e_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v___x_304_; lean_object* v___f_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_304_ = lean_array_get_borrowed(v___x_294_, v_f_297_, v___x_295_);
lean_inc(v___x_304_);
v___f_305_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_305_, 0, v___x_304_);
lean_closure_set(v___f_305_, 1, v_a_296_);
v___x_306_ = lean_replace_expr(v___f_305_, v_e_298_);
lean_dec_ref(v___f_305_);
v___x_307_ = l_Lean_Meta_PProdN_reduceProjs(v___x_306_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v_a_308_; lean_object* v___x_309_; 
v_a_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_a_308_);
lean_dec_ref(v___x_307_);
v___x_309_ = l_Lean_Core_betaReduce(v_a_308_, v___y_301_, v___y_302_);
return v___x_309_;
}
else
{
return v___x_307_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___lam__1___boxed(lean_object* v___x_310_, lean_object* v___x_311_, lean_object* v_a_312_, lean_object* v_f_313_, lean_object* v_e_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___lam__1(v___x_310_, v___x_311_, v_a_312_, v_f_313_, v_e_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
lean_dec_ref(v_e_314_);
lean_dec_ref(v_f_313_);
lean_dec(v___x_311_);
lean_dec_ref(v___x_310_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__4___redArg(lean_object* v_as_321_, size_t v_i_322_, size_t v_stop_323_, lean_object* v_b_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
uint8_t v___x_328_; 
v___x_328_ = lean_usize_dec_eq(v_i_322_, v_stop_323_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = lean_array_uget_borrowed(v_as_321_, v_i_322_);
v___x_330_ = l_Lean_Elab_addAsAxiom___redArg(v___x_329_, v___y_325_, v___y_326_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; size_t v___x_332_; size_t v___x_333_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_a_331_);
lean_dec_ref(v___x_330_);
v___x_332_ = ((size_t)1ULL);
v___x_333_ = lean_usize_add(v_i_322_, v___x_332_);
v_i_322_ = v___x_333_;
v_b_324_ = v_a_331_;
goto _start;
}
else
{
return v___x_330_;
}
}
else
{
lean_object* v___x_335_; 
v___x_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_335_, 0, v_b_324_);
return v___x_335_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__4___redArg___boxed(lean_object* v_as_336_, lean_object* v_i_337_, lean_object* v_stop_338_, lean_object* v_b_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
size_t v_i_boxed_343_; size_t v_stop_boxed_344_; lean_object* v_res_345_; 
v_i_boxed_343_ = lean_unbox_usize(v_i_337_);
lean_dec(v_i_337_);
v_stop_boxed_344_ = lean_unbox_usize(v_stop_338_);
lean_dec(v_stop_338_);
v_res_345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__4___redArg(v_as_336_, v_i_boxed_343_, v_stop_boxed_344_, v_b_339_, v___y_340_, v___y_341_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec_ref(v_as_336_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__0(lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
if (lean_obj_tag(v_a_346_) == 0)
{
lean_object* v___x_348_; 
v___x_348_ = l_List_reverse___redArg(v_a_347_);
return v___x_348_;
}
else
{
lean_object* v_head_349_; lean_object* v_tail_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_359_; 
v_head_349_ = lean_ctor_get(v_a_346_, 0);
v_tail_350_ = lean_ctor_get(v_a_346_, 1);
v_isSharedCheck_359_ = !lean_is_exclusive(v_a_346_);
if (v_isSharedCheck_359_ == 0)
{
v___x_352_ = v_a_346_;
v_isShared_353_ = v_isSharedCheck_359_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_tail_350_);
lean_inc(v_head_349_);
lean_dec(v_a_346_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_359_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_354_; lean_object* v___x_356_; 
v___x_354_ = l_Lean_mkLevelParam(v_head_349_);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 1, v_a_347_);
lean_ctor_set(v___x_352_, 0, v___x_354_);
v___x_356_ = v___x_352_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_354_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v_a_347_);
v___x_356_ = v_reuseFailAlloc_358_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
v_a_346_ = v_tail_350_;
v_a_347_ = v___x_356_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___redArg___lam__0(lean_object* v___x_360_, lean_object* v___x_361_, lean_object* v_fixedArgs_362_, uint8_t v_isZero_363_, lean_object* v_xs_364_, lean_object* v_x_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v_levelParams_371_; lean_object* v_declName_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; uint8_t v___x_378_; uint8_t v___x_379_; lean_object* v___x_380_; 
v_levelParams_371_ = lean_ctor_get(v___x_360_, 1);
lean_inc(v_levelParams_371_);
v_declName_372_ = lean_ctor_get(v___x_360_, 3);
lean_inc(v_declName_372_);
lean_dec_ref(v___x_360_);
lean_inc_ref(v_xs_364_);
v___x_373_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v___x_361_, v_fixedArgs_362_, v_xs_364_);
v___x_374_ = lean_box(0);
v___x_375_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__0(v_levelParams_371_, v___x_374_);
v___x_376_ = l_Lean_Expr_const___override(v_declName_372_, v___x_375_);
v___x_377_ = l_Lean_mkAppN(v___x_376_, v___x_373_);
lean_dec_ref(v___x_373_);
v___x_378_ = 1;
v___x_379_ = 1;
v___x_380_ = l_Lean_Meta_mkLambdaFVars(v_xs_364_, v___x_377_, v_isZero_363_, v___x_378_, v___x_378_, v___x_378_, v___x_379_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
lean_dec_ref(v_xs_364_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___redArg___lam__0___boxed(lean_object* v___x_381_, lean_object* v___x_382_, lean_object* v_fixedArgs_383_, lean_object* v_isZero_384_, lean_object* v_xs_385_, lean_object* v_x_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
uint8_t v_isZero_boxed_392_; lean_object* v_res_393_; 
v_isZero_boxed_392_ = lean_unbox(v_isZero_384_);
v_res_393_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___redArg___lam__0(v___x_381_, v___x_382_, v_fixedArgs_383_, v_isZero_boxed_392_, v_xs_385_, v_x_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec_ref(v_x_386_);
lean_dec_ref(v_fixedArgs_383_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___redArg(lean_object* v_fixedParamPerms_394_, lean_object* v_fixedArgs_395_, lean_object* v_as_396_, lean_object* v_i_397_, lean_object* v_j_398_, lean_object* v_bs_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v_zero_405_; uint8_t v_isZero_406_; 
v_zero_405_ = lean_unsigned_to_nat(0u);
v_isZero_406_ = lean_nat_dec_eq(v_i_397_, v_zero_405_);
if (v_isZero_406_ == 1)
{
lean_object* v___x_407_; 
lean_dec(v_j_398_);
lean_dec(v_i_397_);
lean_dec_ref(v_fixedArgs_395_);
v___x_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_407_, 0, v_bs_399_);
return v___x_407_;
}
else
{
lean_object* v_perms_408_; lean_object* v___x_409_; lean_object* v_value_410_; lean_object* v___x_411_; lean_object* v_one_412_; lean_object* v_n_413_; lean_object* v___y_415_; lean_object* v___x_428_; lean_object* v___x_429_; 
v_perms_408_ = lean_ctor_get(v_fixedParamPerms_394_, 1);
v___x_409_ = lean_array_fget_borrowed(v_as_396_, v_j_398_);
v_value_410_ = lean_ctor_get(v___x_409_, 7);
v___x_411_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1);
v_one_412_ = lean_unsigned_to_nat(1u);
v_n_413_ = lean_nat_sub(v_i_397_, v_one_412_);
lean_dec(v_i_397_);
v___x_428_ = lean_array_get_borrowed(v___x_411_, v_perms_408_, v_j_398_);
lean_inc_ref(v_fixedArgs_395_);
lean_inc_ref(v_value_410_);
lean_inc(v___x_428_);
v___x_429_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_428_, v_value_410_, v_fixedArgs_395_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; lean_object* v___x_431_; lean_object* v___f_432_; lean_object* v___x_433_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_a_430_);
lean_dec_ref(v___x_429_);
v___x_431_ = lean_box(v_isZero_406_);
lean_inc_ref(v_fixedArgs_395_);
lean_inc(v___x_428_);
lean_inc(v___x_409_);
v___f_432_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_432_, 0, v___x_409_);
lean_closure_set(v___f_432_, 1, v___x_428_);
lean_closure_set(v___f_432_, 2, v_fixedArgs_395_);
lean_closure_set(v___f_432_, 3, v___x_431_);
v___x_433_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__1___redArg(v_a_430_, v___f_432_, v_isZero_406_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
v___y_415_ = v___x_433_;
goto v___jp_414_;
}
else
{
v___y_415_ = v___x_429_;
goto v___jp_414_;
}
v___jp_414_:
{
if (lean_obj_tag(v___y_415_) == 0)
{
lean_object* v_a_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v_a_416_ = lean_ctor_get(v___y_415_, 0);
lean_inc(v_a_416_);
lean_dec_ref(v___y_415_);
v___x_417_ = lean_nat_add(v_j_398_, v_one_412_);
lean_dec(v_j_398_);
v___x_418_ = lean_array_push(v_bs_399_, v_a_416_);
v_i_397_ = v_n_413_;
v_j_398_ = v___x_417_;
v_bs_399_ = v___x_418_;
goto _start;
}
else
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_427_; 
lean_dec(v_n_413_);
lean_dec_ref(v_bs_399_);
lean_dec(v_j_398_);
lean_dec_ref(v_fixedArgs_395_);
v_a_420_ = lean_ctor_get(v___y_415_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___y_415_);
if (v_isSharedCheck_427_ == 0)
{
v___x_422_ = v___y_415_;
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___y_415_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_425_; 
if (v_isShared_423_ == 0)
{
v___x_425_ = v___x_422_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_a_420_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___redArg___boxed(lean_object* v_fixedParamPerms_434_, lean_object* v_fixedArgs_435_, lean_object* v_as_436_, lean_object* v_i_437_, lean_object* v_j_438_, lean_object* v_bs_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___redArg(v_fixedParamPerms_434_, v_fixedArgs_435_, v_as_436_, v_i_437_, v_j_438_, v_bs_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec_ref(v_as_436_);
lean_dec_ref(v_fixedParamPerms_434_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___lam__2(lean_object* v___x_446_, lean_object* v_fixedParamPerms_447_, lean_object* v_fixedArgs_448_, lean_object* v_preDefs_449_, lean_object* v___x_450_, lean_object* v___x_451_, lean_object* v_F_452_, lean_object* v_k_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v___y_497_; uint8_t v___x_506_; 
v___x_506_ = lean_nat_dec_lt(v___x_450_, v___x_446_);
if (v___x_506_ == 0)
{
goto v___jp_459_;
}
else
{
lean_object* v___x_507_; uint8_t v___x_508_; 
v___x_507_ = lean_box(0);
v___x_508_ = lean_nat_dec_le(v___x_446_, v___x_446_);
if (v___x_508_ == 0)
{
if (v___x_506_ == 0)
{
goto v___jp_459_;
}
else
{
size_t v___x_509_; size_t v___x_510_; lean_object* v___x_511_; 
v___x_509_ = ((size_t)0ULL);
v___x_510_ = lean_usize_of_nat(v___x_446_);
v___x_511_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__4___redArg(v_preDefs_449_, v___x_509_, v___x_510_, v___x_507_, v___y_456_, v___y_457_);
v___y_497_ = v___x_511_;
goto v___jp_496_;
}
}
else
{
size_t v___x_512_; size_t v___x_513_; lean_object* v___x_514_; 
v___x_512_ = ((size_t)0ULL);
v___x_513_ = lean_usize_of_nat(v___x_446_);
v___x_514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__4___redArg(v_preDefs_449_, v___x_512_, v___x_513_, v___x_507_, v___y_456_, v___y_457_);
v___y_497_ = v___x_514_;
goto v___jp_496_;
}
}
v___jp_459_:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = lean_mk_empty_array_with_capacity(v___x_446_);
lean_inc(v___x_450_);
v___x_461_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___redArg(v_fixedParamPerms_447_, v_fixedArgs_448_, v_preDefs_449_, v___x_446_, v___x_450_, v___x_460_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v_a_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v_a_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_a_462_);
lean_dec_ref(v___x_461_);
v___x_463_ = l_Lean_Level_ofNat(v___x_450_);
v___x_464_ = l_Lean_Meta_PProdN_mk(v___x_463_, v_a_462_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; lean_object* v___f_466_; lean_object* v___x_467_; uint8_t v___x_468_; lean_object* v___x_469_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_a_465_);
lean_dec_ref(v___x_464_);
v___f_466_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_466_, 0, v___x_451_);
lean_closure_set(v___f_466_, 1, v___x_450_);
lean_closure_set(v___f_466_, 2, v_a_465_);
v___x_467_ = lean_unsigned_to_nat(1u);
v___x_468_ = 0;
v___x_469_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__3___redArg(v_F_452_, v___x_467_, v___f_466_, v___x_468_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; lean_object* v___x_471_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_a_470_);
lean_dec_ref(v___x_469_);
v___x_471_ = lean_apply_6(v_k_453_, v_a_470_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, lean_box(0));
return v___x_471_;
}
else
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec_ref(v_k_453_);
v_a_472_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_469_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_469_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_472_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
else
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec_ref(v_k_453_);
lean_dec_ref(v_F_452_);
lean_dec_ref(v___x_451_);
lean_dec(v___x_450_);
v_a_480_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___x_464_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_464_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_480_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
else
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec_ref(v_k_453_);
lean_dec_ref(v_F_452_);
lean_dec_ref(v___x_451_);
lean_dec(v___x_450_);
v_a_488_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_461_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_461_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_488_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
v___jp_496_:
{
if (lean_obj_tag(v___y_497_) == 0)
{
lean_dec_ref(v___y_497_);
goto v___jp_459_;
}
else
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec_ref(v_k_453_);
lean_dec_ref(v_F_452_);
lean_dec_ref(v___x_451_);
lean_dec(v___x_450_);
lean_dec_ref(v_fixedArgs_448_);
lean_dec(v___x_446_);
v_a_498_ = lean_ctor_get(v___y_497_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___y_497_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___y_497_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___y_497_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___lam__2___boxed(lean_object* v___x_515_, lean_object* v_fixedParamPerms_516_, lean_object* v_fixedArgs_517_, lean_object* v_preDefs_518_, lean_object* v___x_519_, lean_object* v___x_520_, lean_object* v_F_521_, lean_object* v_k_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___lam__2(v___x_515_, v_fixedParamPerms_516_, v_fixedArgs_517_, v_preDefs_518_, v___x_519_, v___x_520_, v_F_521_, v_k_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
lean_dec_ref(v_preDefs_518_);
lean_dec_ref(v_fixedParamPerms_516_);
return v_res_528_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_529_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__0);
v___x_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
return v___x_531_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__1);
v___x_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
return v___x_533_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__1);
v___x_535_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
lean_ctor_set(v___x_535_, 2, v___x_534_);
lean_ctor_set(v___x_535_, 3, v___x_534_);
lean_ctor_set(v___x_535_, 4, v___x_534_);
lean_ctor_set(v___x_535_, 5, v___x_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg(lean_object* v_env_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v___x_540_; lean_object* v_nextMacroScope_541_; lean_object* v_ngen_542_; lean_object* v_auxDeclNGen_543_; lean_object* v_traceState_544_; lean_object* v_messages_545_; lean_object* v_infoState_546_; lean_object* v_snapshotTasks_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_573_; 
v___x_540_ = lean_st_ref_take(v___y_538_);
v_nextMacroScope_541_ = lean_ctor_get(v___x_540_, 1);
v_ngen_542_ = lean_ctor_get(v___x_540_, 2);
v_auxDeclNGen_543_ = lean_ctor_get(v___x_540_, 3);
v_traceState_544_ = lean_ctor_get(v___x_540_, 4);
v_messages_545_ = lean_ctor_get(v___x_540_, 6);
v_infoState_546_ = lean_ctor_get(v___x_540_, 7);
v_snapshotTasks_547_ = lean_ctor_get(v___x_540_, 8);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_573_ == 0)
{
lean_object* v_unused_574_; lean_object* v_unused_575_; 
v_unused_574_ = lean_ctor_get(v___x_540_, 5);
lean_dec(v_unused_574_);
v_unused_575_ = lean_ctor_get(v___x_540_, 0);
lean_dec(v_unused_575_);
v___x_549_ = v___x_540_;
v_isShared_550_ = v_isSharedCheck_573_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_snapshotTasks_547_);
lean_inc(v_infoState_546_);
lean_inc(v_messages_545_);
lean_inc(v_traceState_544_);
lean_inc(v_auxDeclNGen_543_);
lean_inc(v_ngen_542_);
lean_inc(v_nextMacroScope_541_);
lean_dec(v___x_540_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_573_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_551_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 5, v___x_551_);
lean_ctor_set(v___x_549_, 0, v_env_536_);
v___x_553_ = v___x_549_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_env_536_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_nextMacroScope_541_);
lean_ctor_set(v_reuseFailAlloc_572_, 2, v_ngen_542_);
lean_ctor_set(v_reuseFailAlloc_572_, 3, v_auxDeclNGen_543_);
lean_ctor_set(v_reuseFailAlloc_572_, 4, v_traceState_544_);
lean_ctor_set(v_reuseFailAlloc_572_, 5, v___x_551_);
lean_ctor_set(v_reuseFailAlloc_572_, 6, v_messages_545_);
lean_ctor_set(v_reuseFailAlloc_572_, 7, v_infoState_546_);
lean_ctor_set(v_reuseFailAlloc_572_, 8, v_snapshotTasks_547_);
v___x_553_ = v_reuseFailAlloc_572_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v_mctx_556_; lean_object* v_zetaDeltaFVarIds_557_; lean_object* v_postponed_558_; lean_object* v_diag_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_570_; 
v___x_554_ = lean_st_ref_set(v___y_538_, v___x_553_);
v___x_555_ = lean_st_ref_take(v___y_537_);
v_mctx_556_ = lean_ctor_get(v___x_555_, 0);
v_zetaDeltaFVarIds_557_ = lean_ctor_get(v___x_555_, 2);
v_postponed_558_ = lean_ctor_get(v___x_555_, 3);
v_diag_559_ = lean_ctor_get(v___x_555_, 4);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_570_ == 0)
{
lean_object* v_unused_571_; 
v_unused_571_ = lean_ctor_get(v___x_555_, 1);
lean_dec(v_unused_571_);
v___x_561_ = v___x_555_;
v_isShared_562_ = v_isSharedCheck_570_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_diag_559_);
lean_inc(v_postponed_558_);
lean_inc(v_zetaDeltaFVarIds_557_);
lean_inc(v_mctx_556_);
lean_dec(v___x_555_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_570_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_563_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 1, v___x_563_);
v___x_565_ = v___x_561_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_mctx_556_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v___x_563_);
lean_ctor_set(v_reuseFailAlloc_569_, 2, v_zetaDeltaFVarIds_557_);
lean_ctor_set(v_reuseFailAlloc_569_, 3, v_postponed_558_);
lean_ctor_set(v_reuseFailAlloc_569_, 4, v_diag_559_);
v___x_565_ = v_reuseFailAlloc_569_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_566_ = lean_st_ref_set(v___y_537_, v___x_565_);
v___x_567_ = lean_box(0);
v___x_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
return v___x_568_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___boxed(lean_object* v_env_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg(v_env_576_, v___y_577_, v___y_578_);
lean_dec(v___y_578_);
lean_dec(v___y_577_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5___redArg(lean_object* v_env_581_, lean_object* v_x_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v___x_588_; lean_object* v_env_589_; lean_object* v_a_591_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_588_ = lean_st_ref_get(v___y_586_);
v_env_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc_ref(v_env_589_);
lean_dec(v___x_588_);
v___x_601_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg(v_env_581_, v___y_584_, v___y_586_);
lean_dec_ref(v___x_601_);
lean_inc(v___y_586_);
lean_inc_ref(v___y_585_);
lean_inc(v___y_584_);
lean_inc_ref(v___y_583_);
v___x_602_ = lean_apply_5(v_x_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, lean_box(0));
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; lean_object* v___x_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
lean_inc(v_a_603_);
lean_dec_ref(v___x_602_);
v___x_604_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg(v_env_589_, v___y_584_, v___y_586_);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_611_ == 0)
{
lean_object* v_unused_612_; 
v_unused_612_ = lean_ctor_get(v___x_604_, 0);
lean_dec(v_unused_612_);
v___x_606_ = v___x_604_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_dec(v___x_604_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 0, v_a_603_);
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_603_);
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
lean_object* v_a_613_; 
v_a_613_ = lean_ctor_get(v___x_602_, 0);
lean_inc(v_a_613_);
lean_dec_ref(v___x_602_);
v_a_591_ = v_a_613_;
goto v___jp_590_;
}
v___jp_590_:
{
lean_object* v___x_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
v___x_592_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg(v_env_589_, v___y_584_, v___y_586_);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_599_ == 0)
{
lean_object* v_unused_600_; 
v_unused_600_ = lean_ctor_get(v___x_592_, 0);
lean_dec(v_unused_600_);
v___x_594_ = v___x_592_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_dec(v___x_592_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
lean_ctor_set_tag(v___x_594_, 1);
lean_ctor_set(v___x_594_, 0, v_a_591_);
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_591_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5___redArg___boxed(lean_object* v_env_614_, lean_object* v_x_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5___redArg(v_env_614_, v_x_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6_spec__7(lean_object* v_msgData_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v___x_628_; lean_object* v_env_629_; lean_object* v___x_630_; lean_object* v_mctx_631_; lean_object* v_lctx_632_; lean_object* v_options_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_628_ = lean_st_ref_get(v___y_626_);
v_env_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc_ref(v_env_629_);
lean_dec(v___x_628_);
v___x_630_ = lean_st_ref_get(v___y_624_);
v_mctx_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc_ref(v_mctx_631_);
lean_dec(v___x_630_);
v_lctx_632_ = lean_ctor_get(v___y_623_, 2);
v_options_633_ = lean_ctor_get(v___y_625_, 2);
lean_inc_ref(v_options_633_);
lean_inc_ref(v_lctx_632_);
v___x_634_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_634_, 0, v_env_629_);
lean_ctor_set(v___x_634_, 1, v_mctx_631_);
lean_ctor_set(v___x_634_, 2, v_lctx_632_);
lean_ctor_set(v___x_634_, 3, v_options_633_);
v___x_635_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set(v___x_635_, 1, v_msgData_622_);
v___x_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6_spec__7___boxed(lean_object* v_msgData_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6_spec__7(v_msgData_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg(lean_object* v_msg_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
lean_object* v_ref_650_; lean_object* v___x_651_; lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_660_; 
v_ref_650_ = lean_ctor_get(v___y_647_, 5);
v___x_651_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6_spec__7(v_msg_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_);
v_a_652_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_660_ == 0)
{
v___x_654_ = v___x_651_;
v_isShared_655_ = v_isSharedCheck_660_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_651_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_660_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; lean_object* v___x_658_; 
lean_inc(v_ref_650_);
v___x_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_656_, 0, v_ref_650_);
lean_ctor_set(v___x_656_, 1, v_a_652_);
if (v_isShared_655_ == 0)
{
lean_ctor_set_tag(v___x_654_, 1);
lean_ctor_set(v___x_654_, 0, v___x_656_);
v___x_658_ = v___x_654_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_656_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg___boxed(lean_object* v_msg_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg(v_msg_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
return v_res_667_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___closed__1(void){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___closed__0));
v___x_670_ = l_Lean_stringToMessageData(v___x_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg(lean_object* v_preDefs_671_, lean_object* v_fixedParamPerms_672_, lean_object* v_fixedArgs_673_, lean_object* v_F_674_, lean_object* v_k_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_){
_start:
{
lean_object* v___x_681_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; uint8_t v___x_694_; 
v___x_681_ = l_Lean_instInhabitedExpr;
v___x_694_ = l_Lean_Expr_isLambda(v_F_674_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
lean_dec_ref(v_k_675_);
lean_dec_ref(v_fixedArgs_673_);
lean_dec_ref(v_fixedParamPerms_672_);
lean_dec_ref(v_preDefs_671_);
v___x_695_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___closed__1);
v___x_696_ = l_Lean_indentExpr(v_F_674_);
v___x_697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_695_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
v___x_698_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg(v___x_697_, v_a_676_, v_a_677_, v_a_678_, v_a_679_);
v_a_699_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_698_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_698_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_699_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
else
{
v___y_683_ = v_a_676_;
v___y_684_ = v_a_677_;
v___y_685_ = v_a_678_;
v___y_686_ = v_a_679_;
goto v___jp_682_;
}
v___jp_682_:
{
lean_object* v___x_687_; lean_object* v_env_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___f_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_687_ = lean_st_ref_get(v___y_686_);
v_env_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc_ref(v_env_688_);
lean_dec(v___x_687_);
v___x_689_ = lean_unsigned_to_nat(0u);
v___x_690_ = lean_array_get_size(v_preDefs_671_);
v___f_691_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___lam__2___boxed), 13, 8);
lean_closure_set(v___f_691_, 0, v___x_690_);
lean_closure_set(v___f_691_, 1, v_fixedParamPerms_672_);
lean_closure_set(v___f_691_, 2, v_fixedArgs_673_);
lean_closure_set(v___f_691_, 3, v_preDefs_671_);
lean_closure_set(v___f_691_, 4, v___x_689_);
lean_closure_set(v___f_691_, 5, v___x_681_);
lean_closure_set(v___f_691_, 6, v_F_674_);
lean_closure_set(v___f_691_, 7, v_k_675_);
v___x_692_ = l_Lean_Environment_unlockAsync(v_env_688_);
v___x_693_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5___redArg(v___x_692_, v___f_691_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
return v___x_693_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___boxed(lean_object* v_preDefs_707_, lean_object* v_fixedParamPerms_708_, lean_object* v_fixedArgs_709_, lean_object* v_F_710_, lean_object* v_k_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg(v_preDefs_707_, v_fixedParamPerms_708_, v_fixedArgs_709_, v_F_710_, v_k_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
lean_dec(v_a_715_);
lean_dec_ref(v_a_714_);
lean_dec(v_a_713_);
lean_dec_ref(v_a_712_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps(lean_object* v_00_u03b1_718_, lean_object* v_preDefs_719_, lean_object* v_fixedParamPerms_720_, lean_object* v_fixedArgs_721_, lean_object* v_F_722_, lean_object* v_k_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg(v_preDefs_719_, v_fixedParamPerms_720_, v_fixedArgs_721_, v_F_722_, v_k_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___boxed(lean_object* v_00_u03b1_730_, lean_object* v_preDefs_731_, lean_object* v_fixedParamPerms_732_, lean_object* v_fixedArgs_733_, lean_object* v_F_734_, lean_object* v_k_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps(v_00_u03b1_730_, v_preDefs_731_, v_fixedParamPerms_732_, v_fixedArgs_733_, v_F_734_, v_k_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_);
lean_dec(v_a_739_);
lean_dec_ref(v_a_738_);
lean_dec(v_a_737_);
lean_dec_ref(v_a_736_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2(lean_object* v_fixedParamPerms_742_, lean_object* v_fixedArgs_743_, lean_object* v_as_744_, lean_object* v_i_745_, lean_object* v_j_746_, lean_object* v_inv_747_, lean_object* v_bs_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___redArg(v_fixedParamPerms_742_, v_fixedArgs_743_, v_as_744_, v_i_745_, v_j_746_, v_bs_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___boxed(lean_object* v_fixedParamPerms_755_, lean_object* v_fixedArgs_756_, lean_object* v_as_757_, lean_object* v_i_758_, lean_object* v_j_759_, lean_object* v_inv_760_, lean_object* v_bs_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2(v_fixedParamPerms_755_, v_fixedArgs_756_, v_as_757_, v_i_758_, v_j_759_, v_inv_760_, v_bs_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec_ref(v_as_757_);
lean_dec_ref(v_fixedParamPerms_755_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__4(lean_object* v_as_768_, size_t v_i_769_, size_t v_stop_770_, lean_object* v_b_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__4___redArg(v_as_768_, v_i_769_, v_stop_770_, v_b_771_, v___y_774_, v___y_775_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__4___boxed(lean_object* v_as_778_, lean_object* v_i_779_, lean_object* v_stop_780_, lean_object* v_b_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
size_t v_i_boxed_787_; size_t v_stop_boxed_788_; lean_object* v_res_789_; 
v_i_boxed_787_ = lean_unbox_usize(v_i_779_);
lean_dec(v_i_779_);
v_stop_boxed_788_ = lean_unbox_usize(v_stop_780_);
lean_dec(v_stop_780_);
v_res_789_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__4(v_as_778_, v_i_boxed_787_, v_stop_boxed_788_, v_b_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec_ref(v_as_778_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5(lean_object* v_env_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg(v_env_790_, v___y_792_, v___y_794_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___boxed(lean_object* v_env_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5(v_env_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5(lean_object* v_00_u03b1_804_, lean_object* v_env_805_, lean_object* v_x_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5___redArg(v_env_805_, v_x_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5___boxed(lean_object* v_00_u03b1_813_, lean_object* v_env_814_, lean_object* v_x_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5(v_00_u03b1_813_, v_env_814_, v_x_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6(lean_object* v_00_u03b1_822_, lean_object* v_msg_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg(v_msg_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___boxed(lean_object* v_00_u03b1_830_, lean_object* v_msg_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6(v_00_u03b1_830_, v_msg_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
return v_res_837_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__1(void){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_839_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__0));
v___x_840_ = l_Lean_stringToMessageData(v___x_839_);
return v___x_840_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__9(void){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_855_ = lean_box(0);
v___x_856_ = lean_unsigned_to_nat(10u);
v___x_857_ = lean_mk_empty_array_with_capacity(v___x_856_);
v___x_858_ = lean_array_push(v___x_857_, v___x_855_);
return v___x_858_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__10(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_859_ = lean_box(0);
v___x_860_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__9, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__9);
v___x_861_ = lean_array_push(v___x_860_, v___x_859_);
return v___x_861_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__11(void){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_862_ = lean_box(0);
v___x_863_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__10, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__10);
v___x_864_ = lean_array_push(v___x_863_, v___x_862_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd(lean_object* v_x_865_, lean_object* v_x_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
lean_object* v_fst_872_; lean_object* v_snd_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_976_; 
v_fst_872_ = lean_ctor_get(v_x_865_, 0);
v_snd_873_ = lean_ctor_get(v_x_865_, 1);
v_isSharedCheck_976_ = !lean_is_exclusive(v_x_865_);
if (v_isSharedCheck_976_ == 0)
{
v___x_875_ = v_x_865_;
v_isShared_876_ = v_isSharedCheck_976_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_snd_873_);
lean_inc(v_fst_872_);
lean_dec(v_x_865_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_976_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v_fst_888_; lean_object* v_snd_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_975_; 
v_fst_888_ = lean_ctor_get(v_x_866_, 0);
v_snd_889_ = lean_ctor_get(v_x_866_, 1);
v_isSharedCheck_975_ = !lean_is_exclusive(v_x_866_);
if (v_isSharedCheck_975_ == 0)
{
v___x_891_ = v_x_866_;
v_isShared_892_ = v_isSharedCheck_975_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_snd_889_);
lean_inc(v_fst_888_);
lean_dec(v_x_866_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_975_;
goto v_resetjp_890_;
}
v___jp_877_:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_885_; 
v___x_882_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__1);
v___x_883_ = l_Lean_indentExpr(v_snd_873_);
if (v_isShared_876_ == 0)
{
lean_ctor_set_tag(v___x_875_, 7);
lean_ctor_set(v___x_875_, 1, v___x_883_);
lean_ctor_set(v___x_875_, 0, v___x_882_);
v___x_885_ = v___x_875_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v___x_883_);
v___x_885_ = v_reuseFailAlloc_887_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg(v___x_885_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
return v___x_886_;
}
}
v_resetjp_890_:
{
lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_897_; lean_object* v___x_902_; uint8_t v___x_903_; 
v___x_902_ = l_Lean_Expr_cleanupAnnotations(v_fst_872_);
v___x_903_ = l_Lean_Expr_isApp(v___x_902_);
if (v___x_903_ == 0)
{
lean_dec_ref(v___x_902_);
lean_del_object(v___x_891_);
lean_dec(v_snd_889_);
lean_dec(v_fst_888_);
v___y_878_ = v_a_867_;
v___y_879_ = v_a_868_;
v___y_880_ = v_a_869_;
v___y_881_ = v_a_870_;
goto v___jp_877_;
}
else
{
lean_object* v___x_904_; uint8_t v___x_905_; 
v___x_904_ = l_Lean_Expr_appFnCleanup___redArg(v___x_902_);
v___x_905_ = l_Lean_Expr_isApp(v___x_904_);
if (v___x_905_ == 0)
{
lean_dec_ref(v___x_904_);
lean_del_object(v___x_891_);
lean_dec(v_snd_889_);
lean_dec(v_fst_888_);
v___y_878_ = v_a_867_;
v___y_879_ = v_a_868_;
v___y_880_ = v_a_869_;
v___y_881_ = v_a_870_;
goto v___jp_877_;
}
else
{
lean_object* v_arg_906_; lean_object* v___x_907_; uint8_t v___x_908_; 
v_arg_906_ = lean_ctor_get(v___x_904_, 1);
lean_inc_ref(v_arg_906_);
v___x_907_ = l_Lean_Expr_appFnCleanup___redArg(v___x_904_);
v___x_908_ = l_Lean_Expr_isApp(v___x_907_);
if (v___x_908_ == 0)
{
lean_dec_ref(v___x_907_);
lean_dec_ref(v_arg_906_);
lean_del_object(v___x_891_);
lean_dec(v_snd_889_);
lean_dec(v_fst_888_);
v___y_878_ = v_a_867_;
v___y_879_ = v_a_868_;
v___y_880_ = v_a_869_;
v___y_881_ = v_a_870_;
goto v___jp_877_;
}
else
{
lean_object* v___x_909_; uint8_t v___x_910_; 
v___x_909_ = l_Lean_Expr_appFnCleanup___redArg(v___x_907_);
v___x_910_ = l_Lean_Expr_isApp(v___x_909_);
if (v___x_910_ == 0)
{
lean_dec_ref(v___x_909_);
lean_dec_ref(v_arg_906_);
lean_del_object(v___x_891_);
lean_dec(v_snd_889_);
lean_dec(v_fst_888_);
v___y_878_ = v_a_867_;
v___y_879_ = v_a_868_;
v___y_880_ = v_a_869_;
v___y_881_ = v_a_870_;
goto v___jp_877_;
}
else
{
lean_object* v_arg_911_; lean_object* v___x_912_; uint8_t v___x_913_; 
v_arg_911_ = lean_ctor_get(v___x_909_, 1);
lean_inc_ref(v_arg_911_);
v___x_912_ = l_Lean_Expr_appFnCleanup___redArg(v___x_909_);
v___x_913_ = l_Lean_Expr_isApp(v___x_912_);
if (v___x_913_ == 0)
{
lean_dec_ref(v___x_912_);
lean_dec_ref(v_arg_911_);
lean_dec_ref(v_arg_906_);
lean_del_object(v___x_891_);
lean_dec(v_snd_889_);
lean_dec(v_fst_888_);
v___y_878_ = v_a_867_;
v___y_879_ = v_a_868_;
v___y_880_ = v_a_869_;
v___y_881_ = v_a_870_;
goto v___jp_877_;
}
else
{
lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
v___x_914_ = l_Lean_Expr_appFnCleanup___redArg(v___x_912_);
v___x_915_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__5));
v___x_916_ = l_Lean_Expr_isConstOf(v___x_914_, v___x_915_);
lean_dec_ref(v___x_914_);
if (v___x_916_ == 0)
{
lean_dec_ref(v_arg_911_);
lean_dec_ref(v_arg_906_);
lean_del_object(v___x_891_);
lean_dec(v_snd_889_);
lean_dec(v_fst_888_);
v___y_878_ = v_a_867_;
v___y_879_ = v_a_868_;
v___y_880_ = v_a_869_;
v___y_881_ = v_a_870_;
goto v___jp_877_;
}
else
{
lean_object* v___x_917_; uint8_t v___x_918_; 
lean_del_object(v___x_875_);
v___x_917_ = l_Lean_Expr_cleanupAnnotations(v_fst_888_);
v___x_918_ = l_Lean_Expr_isApp(v___x_917_);
if (v___x_918_ == 0)
{
lean_dec_ref(v___x_917_);
lean_dec_ref(v_arg_911_);
lean_dec_ref(v_arg_906_);
lean_del_object(v___x_891_);
lean_dec(v_snd_873_);
v___y_894_ = v_a_867_;
v___y_895_ = v_a_868_;
v___y_896_ = v_a_869_;
v___y_897_ = v_a_870_;
goto v___jp_893_;
}
else
{
lean_object* v___x_919_; uint8_t v___x_920_; 
v___x_919_ = l_Lean_Expr_appFnCleanup___redArg(v___x_917_);
v___x_920_ = l_Lean_Expr_isApp(v___x_919_);
if (v___x_920_ == 0)
{
lean_dec_ref(v___x_919_);
lean_dec_ref(v_arg_911_);
lean_dec_ref(v_arg_906_);
lean_del_object(v___x_891_);
lean_dec(v_snd_873_);
v___y_894_ = v_a_867_;
v___y_895_ = v_a_868_;
v___y_896_ = v_a_869_;
v___y_897_ = v_a_870_;
goto v___jp_893_;
}
else
{
lean_object* v_arg_921_; lean_object* v___x_922_; uint8_t v___x_923_; 
v_arg_921_ = lean_ctor_get(v___x_919_, 1);
lean_inc_ref(v_arg_921_);
v___x_922_ = l_Lean_Expr_appFnCleanup___redArg(v___x_919_);
v___x_923_ = l_Lean_Expr_isApp(v___x_922_);
if (v___x_923_ == 0)
{
lean_dec_ref(v___x_922_);
lean_dec_ref(v_arg_921_);
lean_dec_ref(v_arg_911_);
lean_dec_ref(v_arg_906_);
lean_del_object(v___x_891_);
lean_dec(v_snd_873_);
v___y_894_ = v_a_867_;
v___y_895_ = v_a_868_;
v___y_896_ = v_a_869_;
v___y_897_ = v_a_870_;
goto v___jp_893_;
}
else
{
lean_object* v___x_924_; uint8_t v___x_925_; 
v___x_924_ = l_Lean_Expr_appFnCleanup___redArg(v___x_922_);
v___x_925_ = l_Lean_Expr_isApp(v___x_924_);
if (v___x_925_ == 0)
{
lean_dec_ref(v___x_924_);
lean_dec_ref(v_arg_921_);
lean_dec_ref(v_arg_911_);
lean_dec_ref(v_arg_906_);
lean_del_object(v___x_891_);
lean_dec(v_snd_873_);
v___y_894_ = v_a_867_;
v___y_895_ = v_a_868_;
v___y_896_ = v_a_869_;
v___y_897_ = v_a_870_;
goto v___jp_893_;
}
else
{
lean_object* v___x_926_; uint8_t v___x_927_; 
v___x_926_ = l_Lean_Expr_appFnCleanup___redArg(v___x_924_);
v___x_927_ = l_Lean_Expr_isApp(v___x_926_);
if (v___x_927_ == 0)
{
lean_dec_ref(v___x_926_);
lean_dec_ref(v_arg_921_);
lean_dec_ref(v_arg_911_);
lean_dec_ref(v_arg_906_);
lean_del_object(v___x_891_);
lean_dec(v_snd_873_);
v___y_894_ = v_a_867_;
v___y_895_ = v_a_868_;
v___y_896_ = v_a_869_;
v___y_897_ = v_a_870_;
goto v___jp_893_;
}
else
{
lean_object* v___x_928_; uint8_t v___x_929_; 
v___x_928_ = l_Lean_Expr_appFnCleanup___redArg(v___x_926_);
v___x_929_ = l_Lean_Expr_isConstOf(v___x_928_, v___x_915_);
lean_dec_ref(v___x_928_);
if (v___x_929_ == 0)
{
lean_dec_ref(v_arg_921_);
lean_dec_ref(v_arg_911_);
lean_dec_ref(v_arg_906_);
lean_del_object(v___x_891_);
lean_dec(v_snd_873_);
v___y_894_ = v_a_867_;
v___y_895_ = v_a_868_;
v___y_896_ = v_a_869_;
v___y_897_ = v_a_870_;
goto v___jp_893_;
}
else
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_930_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__8));
v___x_931_ = lean_box(0);
v___x_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_932_, 0, v_arg_906_);
v___x_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_933_, 0, v_arg_921_);
v___x_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_934_, 0, v_arg_911_);
v___x_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_935_, 0, v_snd_873_);
v___x_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_936_, 0, v_snd_889_);
v___x_937_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__11, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__11_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__11);
v___x_938_ = lean_array_push(v___x_937_, v___x_932_);
v___x_939_ = lean_array_push(v___x_938_, v___x_933_);
v___x_940_ = lean_array_push(v___x_939_, v___x_934_);
v___x_941_ = lean_array_push(v___x_940_, v___x_931_);
v___x_942_ = lean_array_push(v___x_941_, v___x_931_);
v___x_943_ = lean_array_push(v___x_942_, v___x_935_);
v___x_944_ = lean_array_push(v___x_943_, v___x_936_);
v___x_945_ = l_Lean_Meta_mkAppOptM(v___x_930_, v___x_944_, v_a_867_, v_a_868_, v_a_869_, v_a_870_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; lean_object* v___x_947_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
lean_inc_n(v_a_946_, 2);
lean_dec_ref(v___x_945_);
lean_inc(v_a_870_);
lean_inc_ref(v_a_869_);
lean_inc(v_a_868_);
lean_inc_ref(v_a_867_);
v___x_947_ = lean_infer_type(v_a_946_, v_a_867_, v_a_868_, v_a_869_, v_a_870_);
if (lean_obj_tag(v___x_947_) == 0)
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_958_; 
v_a_948_ = lean_ctor_get(v___x_947_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_958_ == 0)
{
v___x_950_ = v___x_947_;
v_isShared_951_ = v_isSharedCheck_958_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_947_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_958_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 1, v_a_946_);
lean_ctor_set(v___x_891_, 0, v_a_948_);
v___x_953_ = v___x_891_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_a_948_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_a_946_);
v___x_953_ = v_reuseFailAlloc_957_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
lean_object* v___x_955_; 
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 0, v___x_953_);
v___x_955_ = v___x_950_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v___x_953_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
else
{
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_966_; 
lean_dec(v_a_946_);
lean_del_object(v___x_891_);
v_a_959_ = lean_ctor_get(v___x_947_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_966_ == 0)
{
v___x_961_ = v___x_947_;
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_947_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_962_ == 0)
{
v___x_964_ = v___x_961_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_959_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
lean_del_object(v___x_891_);
v_a_967_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_945_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_945_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
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
}
}
}
}
v___jp_893_:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_898_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__1);
v___x_899_ = l_Lean_indentExpr(v_snd_889_);
v___x_900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_898_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg(v___x_900_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
return v___x_901_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___boxed(lean_object* v_x_977_, lean_object* v_x_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd(v_x_977_, v_x_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg___lam__0(lean_object* v_k_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v_b_988_, lean_object* v_c_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v___x_995_; 
lean_inc(v___y_993_);
lean_inc_ref(v___y_992_);
lean_inc(v___y_991_);
lean_inc_ref(v___y_990_);
lean_inc(v___y_987_);
lean_inc_ref(v___y_986_);
v___x_995_ = lean_apply_9(v_k_985_, v_b_988_, v_c_989_, v___y_986_, v___y_987_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, lean_box(0));
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg___lam__0___boxed(lean_object* v_k_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v_b_999_, lean_object* v_c_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg___lam__0(v_k_996_, v___y_997_, v___y_998_, v_b_999_, v_c_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg(lean_object* v_type_1007_, lean_object* v_k_1008_, uint8_t v_cleanupAnnotations_1009_, uint8_t v_whnfType_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v___f_1018_; lean_object* v___x_1019_; 
lean_inc(v___y_1012_);
lean_inc_ref(v___y_1011_);
v___f_1018_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1018_, 0, v_k_1008_);
lean_closure_set(v___f_1018_, 1, v___y_1011_);
lean_closure_set(v___f_1018_, 2, v___y_1012_);
v___x_1019_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1007_, v___f_1018_, v_cleanupAnnotations_1009_, v_whnfType_1010_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
if (lean_obj_tag(v___x_1019_) == 0)
{
return v___x_1019_;
}
else
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1027_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1022_ = v___x_1019_;
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_1019_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1025_; 
if (v_isShared_1023_ == 0)
{
v___x_1025_ = v___x_1022_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_a_1020_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg___boxed(lean_object* v_type_1028_, lean_object* v_k_1029_, lean_object* v_cleanupAnnotations_1030_, lean_object* v_whnfType_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1039_; uint8_t v_whnfType_boxed_1040_; lean_object* v_res_1041_; 
v_cleanupAnnotations_boxed_1039_ = lean_unbox(v_cleanupAnnotations_1030_);
v_whnfType_boxed_1040_ = lean_unbox(v_whnfType_1031_);
v_res_1041_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg(v_type_1028_, v_k_1029_, v_cleanupAnnotations_boxed_1039_, v_whnfType_boxed_1040_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3(lean_object* v_00_u03b1_1042_, lean_object* v_type_1043_, lean_object* v_k_1044_, uint8_t v_cleanupAnnotations_1045_, uint8_t v_whnfType_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg(v_type_1043_, v_k_1044_, v_cleanupAnnotations_1045_, v_whnfType_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___boxed(lean_object* v_00_u03b1_1055_, lean_object* v_type_1056_, lean_object* v_k_1057_, lean_object* v_cleanupAnnotations_1058_, lean_object* v_whnfType_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1067_; uint8_t v_whnfType_boxed_1068_; lean_object* v_res_1069_; 
v_cleanupAnnotations_boxed_1067_ = lean_unbox(v_cleanupAnnotations_1058_);
v_whnfType_boxed_1068_ = lean_unbox(v_whnfType_1059_);
v_res_1069_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3(v_00_u03b1_1055_, v_type_1056_, v_k_1057_, v_cleanupAnnotations_boxed_1067_, v_whnfType_boxed_1068_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5___redArg(lean_object* v_e_1070_, lean_object* v_k_1071_, uint8_t v_cleanupAnnotations_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v___f_1080_; uint8_t v___x_1081_; uint8_t v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
lean_inc(v___y_1074_);
lean_inc_ref(v___y_1073_);
v___f_1080_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1080_, 0, v_k_1071_);
lean_closure_set(v___f_1080_, 1, v___y_1073_);
lean_closure_set(v___f_1080_, 2, v___y_1074_);
v___x_1081_ = 1;
v___x_1082_ = 0;
v___x_1083_ = lean_box(0);
v___x_1084_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1070_, v___x_1081_, v___x_1082_, v___x_1081_, v___x_1082_, v___x_1083_, v___f_1080_, v_cleanupAnnotations_1072_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
if (lean_obj_tag(v___x_1084_) == 0)
{
return v___x_1084_;
}
else
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v___x_1084_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1084_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1085_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5___redArg___boxed(lean_object* v_e_1093_, lean_object* v_k_1094_, lean_object* v_cleanupAnnotations_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1103_; lean_object* v_res_1104_; 
v_cleanupAnnotations_boxed_1103_ = lean_unbox(v_cleanupAnnotations_1095_);
v_res_1104_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5___redArg(v_e_1093_, v_k_1094_, v_cleanupAnnotations_boxed_1103_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5(lean_object* v_00_u03b1_1105_, lean_object* v_e_1106_, lean_object* v_k_1107_, uint8_t v_cleanupAnnotations_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5___redArg(v_e_1106_, v_k_1107_, v_cleanupAnnotations_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5___boxed(lean_object* v_00_u03b1_1117_, lean_object* v_e_1118_, lean_object* v_k_1119_, lean_object* v_cleanupAnnotations_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1128_; lean_object* v_res_1129_; 
v_cleanupAnnotations_boxed_1128_ = lean_unbox(v_cleanupAnnotations_1120_);
v_res_1129_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5(v_00_u03b1_1117_, v_e_1118_, v_k_1119_, v_cleanupAnnotations_boxed_1128_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__8___redArg(lean_object* v_msg_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v___f_1136_; lean_object* v___x_41579__overap_1137_; lean_object* v___x_1138_; 
v___f_1136_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__0___closed__0));
v___x_41579__overap_1137_ = lean_panic_fn_borrowed(v___f_1136_, v_msg_1130_);
lean_inc(v___y_1134_);
lean_inc_ref(v___y_1133_);
lean_inc(v___y_1132_);
lean_inc_ref(v___y_1131_);
v___x_1138_ = lean_apply_5(v___x_41579__overap_1137_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, lean_box(0));
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__8___redArg___boxed(lean_object* v_msg_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_panic___at___00Lean_Elab_partialFixpoint_spec__8___redArg(v_msg_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__8(lean_object* v_00_u03b1_1146_, lean_object* v_msg_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = l_panic___at___00Lean_Elab_partialFixpoint_spec__8___redArg(v_msg_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__8___boxed(lean_object* v_00_u03b1_1154_, lean_object* v_msg_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_panic___at___00Lean_Elab_partialFixpoint_spec__8(v_00_u03b1_1154_, v_msg_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18___redArg(lean_object* v_e_1162_, lean_object* v___y_1163_){
_start:
{
uint8_t v___x_1165_; 
v___x_1165_ = l_Lean_Expr_hasMVar(v_e_1162_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; 
v___x_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1166_, 0, v_e_1162_);
return v___x_1166_;
}
else
{
lean_object* v___x_1167_; lean_object* v_mctx_1168_; lean_object* v___x_1169_; lean_object* v_fst_1170_; lean_object* v_snd_1171_; lean_object* v___x_1172_; lean_object* v_cache_1173_; lean_object* v_zetaDeltaFVarIds_1174_; lean_object* v_postponed_1175_; lean_object* v_diag_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1185_; 
v___x_1167_ = lean_st_ref_get(v___y_1163_);
v_mctx_1168_ = lean_ctor_get(v___x_1167_, 0);
lean_inc_ref(v_mctx_1168_);
lean_dec(v___x_1167_);
v___x_1169_ = l_Lean_instantiateMVarsCore(v_mctx_1168_, v_e_1162_);
v_fst_1170_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_fst_1170_);
v_snd_1171_ = lean_ctor_get(v___x_1169_, 1);
lean_inc(v_snd_1171_);
lean_dec_ref(v___x_1169_);
v___x_1172_ = lean_st_ref_take(v___y_1163_);
v_cache_1173_ = lean_ctor_get(v___x_1172_, 1);
v_zetaDeltaFVarIds_1174_ = lean_ctor_get(v___x_1172_, 2);
v_postponed_1175_ = lean_ctor_get(v___x_1172_, 3);
v_diag_1176_ = lean_ctor_get(v___x_1172_, 4);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1185_ == 0)
{
lean_object* v_unused_1186_; 
v_unused_1186_ = lean_ctor_get(v___x_1172_, 0);
lean_dec(v_unused_1186_);
v___x_1178_ = v___x_1172_;
v_isShared_1179_ = v_isSharedCheck_1185_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_diag_1176_);
lean_inc(v_postponed_1175_);
lean_inc(v_zetaDeltaFVarIds_1174_);
lean_inc(v_cache_1173_);
lean_dec(v___x_1172_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1185_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v_snd_1171_);
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_snd_1171_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_cache_1173_);
lean_ctor_set(v_reuseFailAlloc_1184_, 2, v_zetaDeltaFVarIds_1174_);
lean_ctor_set(v_reuseFailAlloc_1184_, 3, v_postponed_1175_);
lean_ctor_set(v_reuseFailAlloc_1184_, 4, v_diag_1176_);
v___x_1181_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = lean_st_ref_set(v___y_1163_, v___x_1181_);
v___x_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1183_, 0, v_fst_1170_);
return v___x_1183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18___redArg___boxed(lean_object* v_e_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18___redArg(v_e_1187_, v___y_1188_);
lean_dec(v___y_1188_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18(lean_object* v_e_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v___x_1199_; 
v___x_1199_ = l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18___redArg(v_e_1191_, v___y_1195_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18___boxed(lean_object* v_e_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18(v_e_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__20___redArg(lean_object* v_type_1209_, lean_object* v_maxFVars_x3f_1210_, lean_object* v_k_1211_, uint8_t v_cleanupAnnotations_1212_, uint8_t v_whnfType_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v___f_1221_; lean_object* v___x_1222_; 
lean_inc(v___y_1215_);
lean_inc_ref(v___y_1214_);
v___f_1221_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1221_, 0, v_k_1211_);
lean_closure_set(v___f_1221_, 1, v___y_1214_);
lean_closure_set(v___f_1221_, 2, v___y_1215_);
v___x_1222_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1209_, v_maxFVars_x3f_1210_, v___f_1221_, v_cleanupAnnotations_1212_, v_whnfType_1213_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
if (lean_obj_tag(v___x_1222_) == 0)
{
return v___x_1222_;
}
else
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___x_1222_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1222_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1223_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__20___redArg___boxed(lean_object* v_type_1231_, lean_object* v_maxFVars_x3f_1232_, lean_object* v_k_1233_, lean_object* v_cleanupAnnotations_1234_, lean_object* v_whnfType_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1243_; uint8_t v_whnfType_boxed_1244_; lean_object* v_res_1245_; 
v_cleanupAnnotations_boxed_1243_ = lean_unbox(v_cleanupAnnotations_1234_);
v_whnfType_boxed_1244_ = lean_unbox(v_whnfType_1235_);
v_res_1245_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__20___redArg(v_type_1231_, v_maxFVars_x3f_1232_, v_k_1233_, v_cleanupAnnotations_boxed_1243_, v_whnfType_boxed_1244_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__20(lean_object* v_00_u03b1_1246_, lean_object* v_type_1247_, lean_object* v_maxFVars_x3f_1248_, lean_object* v_k_1249_, uint8_t v_cleanupAnnotations_1250_, uint8_t v_whnfType_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__20___redArg(v_type_1247_, v_maxFVars_x3f_1248_, v_k_1249_, v_cleanupAnnotations_1250_, v_whnfType_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__20___boxed(lean_object* v_00_u03b1_1260_, lean_object* v_type_1261_, lean_object* v_maxFVars_x3f_1262_, lean_object* v_k_1263_, lean_object* v_cleanupAnnotations_1264_, lean_object* v_whnfType_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1273_; uint8_t v_whnfType_boxed_1274_; lean_object* v_res_1275_; 
v_cleanupAnnotations_boxed_1273_ = lean_unbox(v_cleanupAnnotations_1264_);
v_whnfType_boxed_1274_ = lean_unbox(v_whnfType_1265_);
v_res_1275_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__20(v_00_u03b1_1260_, v_type_1261_, v_maxFVars_x3f_1262_, v_k_1263_, v_cleanupAnnotations_boxed_1273_, v_whnfType_boxed_1274_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg___lam__0(lean_object* v_k_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v_b_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v___x_1285_; 
lean_inc(v___y_1283_);
lean_inc_ref(v___y_1282_);
lean_inc(v___y_1281_);
lean_inc_ref(v___y_1280_);
lean_inc(v___y_1278_);
lean_inc_ref(v___y_1277_);
v___x_1285_ = lean_apply_8(v_k_1276_, v_b_1279_, v___y_1277_, v___y_1278_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, lean_box(0));
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg___lam__0___boxed(lean_object* v_k_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v_b_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg___lam__0(v_k_1286_, v___y_1287_, v___y_1288_, v_b_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg(lean_object* v_perm_1296_, lean_object* v_type_1297_, lean_object* v_k_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v___f_1306_; lean_object* v___x_1307_; 
lean_inc(v___y_1300_);
lean_inc_ref(v___y_1299_);
v___f_1306_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1306_, 0, v_k_1298_);
lean_closure_set(v___f_1306_, 1, v___y_1299_);
lean_closure_set(v___f_1306_, 2, v___y_1300_);
v___x_1307_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_box(0), v_perm_1296_, v_type_1297_, v___f_1306_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
if (lean_obj_tag(v___x_1307_) == 0)
{
return v___x_1307_;
}
else
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1315_; 
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1310_ = v___x_1307_;
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1307_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1313_; 
if (v_isShared_1311_ == 0)
{
v___x_1313_ = v___x_1310_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_a_1308_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg___boxed(lean_object* v_perm_1316_, lean_object* v_type_1317_, lean_object* v_k_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg(v_perm_1316_, v_type_1317_, v_k_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24(lean_object* v_00_u03b1_1327_, lean_object* v_perm_1328_, lean_object* v_type_1329_, lean_object* v_k_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v___x_1338_; 
v___x_1338_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg(v_perm_1328_, v_type_1329_, v_k_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___boxed(lean_object* v_00_u03b1_1339_, lean_object* v_perm_1340_, lean_object* v_type_1341_, lean_object* v_k_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24(v_00_u03b1_1339_, v_perm_1340_, v_type_1341_, v_k_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
return v_res_1350_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_partialFixpoint_spec__25___closed__0(void){
_start:
{
lean_object* v___x_1351_; 
v___x_1351_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__25(lean_object* v_msg_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_47521__overap_1361_; lean_object* v___x_1362_; 
v___x_1360_ = lean_obj_once(&l_panic___at___00Lean_Elab_partialFixpoint_spec__25___closed__0, &l_panic___at___00Lean_Elab_partialFixpoint_spec__25___closed__0_once, _init_l_panic___at___00Lean_Elab_partialFixpoint_spec__25___closed__0);
v___x_47521__overap_1361_ = lean_panic_fn_borrowed(v___x_1360_, v_msg_1352_);
lean_inc(v___y_1358_);
lean_inc_ref(v___y_1357_);
lean_inc(v___y_1356_);
lean_inc_ref(v___y_1355_);
lean_inc(v___y_1354_);
lean_inc_ref(v___y_1353_);
v___x_1362_ = lean_apply_7(v___x_47521__overap_1361_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, lean_box(0));
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__25___boxed(lean_object* v_msg_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l_panic___at___00Lean_Elab_partialFixpoint_spec__25(v_msg_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
return v_res_1371_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1372_; double v___x_1373_; 
v___x_1372_ = lean_unsigned_to_nat(0u);
v___x_1373_ = lean_float_of_nat(v___x_1372_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg(lean_object* v_cls_1377_, lean_object* v_msg_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
lean_object* v_ref_1384_; lean_object* v___x_1385_; lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1430_; 
v_ref_1384_ = lean_ctor_get(v___y_1381_, 5);
v___x_1385_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6_spec__7(v_msg_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1388_ = v___x_1385_;
v_isShared_1389_ = v_isSharedCheck_1430_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1385_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1430_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1390_; lean_object* v_traceState_1391_; lean_object* v_env_1392_; lean_object* v_nextMacroScope_1393_; lean_object* v_ngen_1394_; lean_object* v_auxDeclNGen_1395_; lean_object* v_cache_1396_; lean_object* v_messages_1397_; lean_object* v_infoState_1398_; lean_object* v_snapshotTasks_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1429_; 
v___x_1390_ = lean_st_ref_take(v___y_1382_);
v_traceState_1391_ = lean_ctor_get(v___x_1390_, 4);
v_env_1392_ = lean_ctor_get(v___x_1390_, 0);
v_nextMacroScope_1393_ = lean_ctor_get(v___x_1390_, 1);
v_ngen_1394_ = lean_ctor_get(v___x_1390_, 2);
v_auxDeclNGen_1395_ = lean_ctor_get(v___x_1390_, 3);
v_cache_1396_ = lean_ctor_get(v___x_1390_, 5);
v_messages_1397_ = lean_ctor_get(v___x_1390_, 6);
v_infoState_1398_ = lean_ctor_get(v___x_1390_, 7);
v_snapshotTasks_1399_ = lean_ctor_get(v___x_1390_, 8);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1401_ = v___x_1390_;
v_isShared_1402_ = v_isSharedCheck_1429_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_snapshotTasks_1399_);
lean_inc(v_infoState_1398_);
lean_inc(v_messages_1397_);
lean_inc(v_cache_1396_);
lean_inc(v_traceState_1391_);
lean_inc(v_auxDeclNGen_1395_);
lean_inc(v_ngen_1394_);
lean_inc(v_nextMacroScope_1393_);
lean_inc(v_env_1392_);
lean_dec(v___x_1390_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1429_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
uint64_t v_tid_1403_; lean_object* v_traces_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1428_; 
v_tid_1403_ = lean_ctor_get_uint64(v_traceState_1391_, sizeof(void*)*1);
v_traces_1404_ = lean_ctor_get(v_traceState_1391_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_traceState_1391_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1406_ = v_traceState_1391_;
v_isShared_1407_ = v_isSharedCheck_1428_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_traces_1404_);
lean_dec(v_traceState_1391_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1428_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1408_; double v___x_1409_; uint8_t v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1418_; 
v___x_1408_ = lean_box(0);
v___x_1409_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__0);
v___x_1410_ = 0;
v___x_1411_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__1));
v___x_1412_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1412_, 0, v_cls_1377_);
lean_ctor_set(v___x_1412_, 1, v___x_1408_);
lean_ctor_set(v___x_1412_, 2, v___x_1411_);
lean_ctor_set_float(v___x_1412_, sizeof(void*)*3, v___x_1409_);
lean_ctor_set_float(v___x_1412_, sizeof(void*)*3 + 8, v___x_1409_);
lean_ctor_set_uint8(v___x_1412_, sizeof(void*)*3 + 16, v___x_1410_);
v___x_1413_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__2));
v___x_1414_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1412_);
lean_ctor_set(v___x_1414_, 1, v_a_1386_);
lean_ctor_set(v___x_1414_, 2, v___x_1413_);
lean_inc(v_ref_1384_);
v___x_1415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1415_, 0, v_ref_1384_);
lean_ctor_set(v___x_1415_, 1, v___x_1414_);
v___x_1416_ = l_Lean_PersistentArray_push___redArg(v_traces_1404_, v___x_1415_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 0, v___x_1416_);
v___x_1418_ = v___x_1406_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1416_);
lean_ctor_set_uint64(v_reuseFailAlloc_1427_, sizeof(void*)*1, v_tid_1403_);
v___x_1418_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
lean_object* v___x_1420_; 
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 4, v___x_1418_);
v___x_1420_ = v___x_1401_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_env_1392_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_nextMacroScope_1393_);
lean_ctor_set(v_reuseFailAlloc_1426_, 2, v_ngen_1394_);
lean_ctor_set(v_reuseFailAlloc_1426_, 3, v_auxDeclNGen_1395_);
lean_ctor_set(v_reuseFailAlloc_1426_, 4, v___x_1418_);
lean_ctor_set(v_reuseFailAlloc_1426_, 5, v_cache_1396_);
lean_ctor_set(v_reuseFailAlloc_1426_, 6, v_messages_1397_);
lean_ctor_set(v_reuseFailAlloc_1426_, 7, v_infoState_1398_);
lean_ctor_set(v_reuseFailAlloc_1426_, 8, v_snapshotTasks_1399_);
v___x_1420_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1424_; 
v___x_1421_ = lean_st_ref_set(v___y_1382_, v___x_1420_);
v___x_1422_ = lean_box(0);
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 0, v___x_1422_);
v___x_1424_ = v___x_1388_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1422_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___boxed(lean_object* v_cls_1431_, lean_object* v_msg_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg(v_cls_1431_, v_msg_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__22___redArg(size_t v_sz_1439_, size_t v_i_1440_, lean_object* v_bs_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
uint8_t v___x_1447_; 
v___x_1447_ = lean_usize_dec_lt(v_i_1440_, v_sz_1439_);
if (v___x_1447_ == 0)
{
lean_object* v___x_1448_; 
v___x_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1448_, 0, v_bs_1441_);
return v___x_1448_;
}
else
{
lean_object* v_v_1449_; lean_object* v___x_1450_; 
v_v_1449_ = lean_array_uget_borrowed(v_bs_1441_, v_i_1440_);
lean_inc(v_v_1449_);
v___x_1450_ = l_Lean_Elab_Mutual_cleanPreDef(v_v_1449_, v___x_1447_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1451_; lean_object* v___x_1452_; lean_object* v_bs_x27_1453_; size_t v___x_1454_; size_t v___x_1455_; lean_object* v___x_1456_; 
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_a_1451_);
lean_dec_ref(v___x_1450_);
v___x_1452_ = lean_unsigned_to_nat(0u);
v_bs_x27_1453_ = lean_array_uset(v_bs_1441_, v_i_1440_, v___x_1452_);
v___x_1454_ = ((size_t)1ULL);
v___x_1455_ = lean_usize_add(v_i_1440_, v___x_1454_);
v___x_1456_ = lean_array_uset(v_bs_x27_1453_, v_i_1440_, v_a_1451_);
v_i_1440_ = v___x_1455_;
v_bs_1441_ = v___x_1456_;
goto _start;
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
lean_dec_ref(v_bs_1441_);
v_a_1458_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1450_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1450_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__22___redArg___boxed(lean_object* v_sz_1466_, lean_object* v_i_1467_, lean_object* v_bs_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
size_t v_sz_boxed_1474_; size_t v_i_boxed_1475_; lean_object* v_res_1476_; 
v_sz_boxed_1474_ = lean_unbox_usize(v_sz_1466_);
lean_dec(v_sz_1466_);
v_i_boxed_1475_ = lean_unbox_usize(v_i_1467_);
lean_dec(v_i_1467_);
v_res_1476_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__22___redArg(v_sz_boxed_1474_, v_i_boxed_1475_, v_bs_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12___lam__0(lean_object* v_xs_1477_, lean_object* v_inst_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = l_Lean_Meta_mkInstPiOfInstsForall(v_xs_1477_, v_inst_1478_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12___lam__0___boxed(lean_object* v_xs_1487_, lean_object* v_inst_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12___lam__0(v_xs_1487_, v_inst_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12(size_t v_sz_1498_, size_t v_i_1499_, lean_object* v_bs_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
uint8_t v___x_1508_; 
v___x_1508_ = lean_usize_dec_lt(v_i_1499_, v_sz_1498_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1509_; 
v___x_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1509_, 0, v_bs_1500_);
return v___x_1509_;
}
else
{
lean_object* v___f_1510_; lean_object* v_v_1511_; uint8_t v___x_1512_; lean_object* v___x_1513_; 
v___f_1510_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12___closed__0));
v_v_1511_ = lean_array_uget_borrowed(v_bs_1500_, v_i_1499_);
v___x_1512_ = 0;
lean_inc(v_v_1511_);
v___x_1513_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5___redArg(v_v_1511_, v___f_1510_, v___x_1512_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v___x_1515_; lean_object* v_bs_x27_1516_; size_t v___x_1517_; size_t v___x_1518_; lean_object* v___x_1519_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
lean_inc(v_a_1514_);
lean_dec_ref(v___x_1513_);
v___x_1515_ = lean_unsigned_to_nat(0u);
v_bs_x27_1516_ = lean_array_uset(v_bs_1500_, v_i_1499_, v___x_1515_);
v___x_1517_ = ((size_t)1ULL);
v___x_1518_ = lean_usize_add(v_i_1499_, v___x_1517_);
v___x_1519_ = lean_array_uset(v_bs_x27_1516_, v_i_1499_, v_a_1514_);
v_i_1499_ = v___x_1518_;
v_bs_1500_ = v___x_1519_;
goto _start;
}
else
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1528_; 
lean_dec_ref(v_bs_1500_);
v_a_1521_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1523_ = v___x_1513_;
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1513_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12___boxed(lean_object* v_sz_1529_, lean_object* v_i_1530_, lean_object* v_bs_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
size_t v_sz_boxed_1539_; size_t v_i_boxed_1540_; lean_object* v_res_1541_; 
v_sz_boxed_1539_ = lean_unbox_usize(v_sz_1529_);
lean_dec(v_sz_1529_);
v_i_boxed_1540_ = lean_unbox_usize(v_i_1530_);
lean_dec(v_i_1530_);
v_res_1541_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12(v_sz_boxed_1539_, v_i_boxed_1540_, v_bs_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__10___redArg(lean_object* v___x_1542_, lean_object* v_fixedArgs_1543_, lean_object* v_as_1544_, lean_object* v_i_1545_, lean_object* v_j_1546_, lean_object* v_bs_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v_zero_1553_; uint8_t v_isZero_1554_; 
v_zero_1553_ = lean_unsigned_to_nat(0u);
v_isZero_1554_ = lean_nat_dec_eq(v_i_1545_, v_zero_1553_);
if (v_isZero_1554_ == 1)
{
lean_object* v___x_1555_; 
lean_dec(v_j_1546_);
lean_dec(v_i_1545_);
lean_dec_ref(v_fixedArgs_1543_);
v___x_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1555_, 0, v_bs_1547_);
return v___x_1555_;
}
else
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1556_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1);
v___x_1557_ = lean_array_fget_borrowed(v_as_1544_, v_j_1546_);
v___x_1558_ = lean_array_get_borrowed(v___x_1556_, v___x_1542_, v_j_1546_);
lean_inc_ref(v_fixedArgs_1543_);
lean_inc(v___x_1557_);
lean_inc(v___x_1558_);
v___x_1559_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_1558_, v___x_1557_, v_fixedArgs_1543_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v_a_1560_; lean_object* v_one_1561_; lean_object* v_n_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v_a_1560_ = lean_ctor_get(v___x_1559_, 0);
lean_inc(v_a_1560_);
lean_dec_ref(v___x_1559_);
v_one_1561_ = lean_unsigned_to_nat(1u);
v_n_1562_ = lean_nat_sub(v_i_1545_, v_one_1561_);
lean_dec(v_i_1545_);
v___x_1563_ = lean_nat_add(v_j_1546_, v_one_1561_);
lean_dec(v_j_1546_);
v___x_1564_ = lean_array_push(v_bs_1547_, v_a_1560_);
v_i_1545_ = v_n_1562_;
v_j_1546_ = v___x_1563_;
v_bs_1547_ = v___x_1564_;
goto _start;
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
lean_dec_ref(v_bs_1547_);
lean_dec(v_j_1546_);
lean_dec(v_i_1545_);
lean_dec_ref(v_fixedArgs_1543_);
v_a_1566_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1559_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1559_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1566_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__10___redArg___boxed(lean_object* v___x_1574_, lean_object* v_fixedArgs_1575_, lean_object* v_as_1576_, lean_object* v_i_1577_, lean_object* v_j_1578_, lean_object* v_bs_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__10___redArg(v___x_1574_, v_fixedArgs_1575_, v_as_1576_, v_i_1577_, v_j_1578_, v_bs_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec_ref(v_as_1576_);
lean_dec_ref(v___x_1574_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11___redArg(lean_object* v___x_1586_, lean_object* v_fixedArgs_1587_, lean_object* v_as_1588_, lean_object* v_i_1589_, lean_object* v_j_1590_, lean_object* v_bs_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v_zero_1597_; uint8_t v_isZero_1598_; 
v_zero_1597_ = lean_unsigned_to_nat(0u);
v_isZero_1598_ = lean_nat_dec_eq(v_i_1589_, v_zero_1597_);
if (v_isZero_1598_ == 1)
{
lean_object* v___x_1599_; 
lean_dec(v_j_1590_);
lean_dec(v_i_1589_);
lean_dec_ref(v_fixedArgs_1587_);
v___x_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1599_, 0, v_bs_1591_);
return v___x_1599_;
}
else
{
lean_object* v___x_1600_; lean_object* v_type_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1600_ = lean_array_fget_borrowed(v_as_1588_, v_j_1590_);
v_type_1601_ = lean_ctor_get(v___x_1600_, 6);
v___x_1602_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1);
v___x_1603_ = lean_array_get_borrowed(v___x_1602_, v___x_1586_, v_j_1590_);
lean_inc_ref(v_fixedArgs_1587_);
lean_inc_ref(v_type_1601_);
lean_inc(v___x_1603_);
v___x_1604_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v___x_1603_, v_type_1601_, v_fixedArgs_1587_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v_a_1605_; lean_object* v_one_1606_; lean_object* v_n_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_a_1605_);
lean_dec_ref(v___x_1604_);
v_one_1606_ = lean_unsigned_to_nat(1u);
v_n_1607_ = lean_nat_sub(v_i_1589_, v_one_1606_);
lean_dec(v_i_1589_);
v___x_1608_ = lean_nat_add(v_j_1590_, v_one_1606_);
lean_dec(v_j_1590_);
v___x_1609_ = lean_array_push(v_bs_1591_, v_a_1605_);
v_i_1589_ = v_n_1607_;
v_j_1590_ = v___x_1608_;
v_bs_1591_ = v___x_1609_;
goto _start;
}
else
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
lean_dec_ref(v_bs_1591_);
lean_dec(v_j_1590_);
lean_dec(v_i_1589_);
lean_dec_ref(v_fixedArgs_1587_);
v_a_1611_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1604_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1604_);
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
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11___redArg___boxed(lean_object* v___x_1619_, lean_object* v_fixedArgs_1620_, lean_object* v_as_1621_, lean_object* v_i_1622_, lean_object* v_j_1623_, lean_object* v_bs_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11___redArg(v___x_1619_, v_fixedArgs_1620_, v_as_1621_, v_i_1622_, v_j_1623_, v_bs_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec_ref(v_as_1621_);
lean_dec_ref(v___x_1619_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__2(lean_object* v___x_1631_, lean_object* v_e_1632_){
_start:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1633_ = l_Lean_indentD(v_e_1632_);
v___x_1634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1631_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__3(lean_object* v___f_1635_, lean_object* v___x_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Lean_Meta_Monotonicity_solveMono(v___f_1635_, v___x_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__3___boxed(lean_object* v___f_1643_, lean_object* v___x_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__3(v___f_1643_, v___x_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
return v_res_1650_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9___closed__1(void){
_start:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1652_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9___closed__0));
v___x_1653_ = l_Lean_stringToMessageData(v___x_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9(lean_object* v_a_1654_, lean_object* v_a_1655_){
_start:
{
if (lean_obj_tag(v_a_1654_) == 0)
{
lean_object* v___x_1656_; 
v___x_1656_ = l_List_reverse___redArg(v_a_1655_);
return v___x_1656_;
}
else
{
lean_object* v_head_1657_; lean_object* v_tail_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1671_; 
v_head_1657_ = lean_ctor_get(v_a_1654_, 0);
v_tail_1658_ = lean_ctor_get(v_a_1654_, 1);
v_isSharedCheck_1671_ = !lean_is_exclusive(v_a_1654_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1660_ = v_a_1654_;
v_isShared_1661_ = v_isSharedCheck_1671_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_tail_1658_);
lean_inc(v_head_1657_);
lean_dec(v_a_1654_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1671_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1662_; uint8_t v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1668_; 
v___x_1662_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9___closed__1, &l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9___closed__1);
v___x_1663_ = 0;
v___x_1664_ = l_Lean_MessageData_ofConstName(v_head_1657_, v___x_1663_);
v___x_1665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1662_);
lean_ctor_set(v___x_1665_, 1, v___x_1664_);
v___x_1666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1665_);
lean_ctor_set(v___x_1666_, 1, v___x_1662_);
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 1, v_a_1655_);
lean_ctor_set(v___x_1660_, 0, v___x_1666_);
v___x_1668_ = v___x_1660_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1666_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v_a_1655_);
v___x_1668_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
v_a_1654_ = v_tail_1658_;
v_a_1655_ = v___x_1668_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1674_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__1));
v___x_1675_ = l_Lean_stringToMessageData(v___x_1674_);
return v___x_1675_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1677_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__3));
v___x_1678_ = l_Lean_stringToMessageData(v___x_1677_);
return v___x_1678_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1680_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__5));
v___x_1681_ = l_Lean_stringToMessageData(v___x_1680_);
return v___x_1681_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1684_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__8));
v___x_1685_ = lean_unsigned_to_nat(52u);
v___x_1686_ = lean_unsigned_to_nat(148u);
v___x_1687_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__7));
v___x_1688_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__0));
v___x_1689_ = l_mkPanicMessageWithDecl(v___x_1688_, v___x_1687_, v___x_1686_, v___x_1685_, v___x_1684_);
return v___x_1689_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__11(void){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__10));
v___x_1692_ = l_Lean_stringToMessageData(v___x_1691_);
return v___x_1692_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__13(void){
_start:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1694_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__12));
v___x_1695_ = l_Lean_stringToMessageData(v___x_1694_);
return v___x_1695_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__15(void){
_start:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1697_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__14));
v___x_1698_ = l_Lean_stringToMessageData(v___x_1697_);
return v___x_1698_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__19(void){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1705_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__18));
v___x_1706_ = l_Lean_stringToMessageData(v___x_1705_);
return v___x_1706_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__20(void){
_start:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1707_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__1));
v___x_1708_ = l_Lean_stringToMessageData(v___x_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0(lean_object* v_monoThms_1709_, lean_object* v_t_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v___y_1717_; lean_object* v___x_1761_; lean_object* v___x_1762_; uint8_t v___x_1763_; 
v___x_1761_ = lean_array_get_size(v_monoThms_1709_);
v___x_1762_ = lean_unsigned_to_nat(0u);
v___x_1763_ = lean_nat_dec_eq(v___x_1761_, v___x_1762_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1764_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__13, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__13_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__13);
v___x_1765_ = lean_array_to_list(v_monoThms_1709_);
v___x_1766_ = lean_box(0);
v___x_1767_ = l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9(v___x_1765_, v___x_1766_);
v___x_1768_ = l_Lean_MessageData_andList(v___x_1767_);
v___x_1769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1764_);
lean_ctor_set(v___x_1769_, 1, v___x_1768_);
v___x_1770_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__15, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__15_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__15);
v___x_1771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1769_);
lean_ctor_set(v___x_1771_, 1, v___x_1770_);
v___x_1772_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__17));
v___x_1773_ = l_Lean_MessageData_ofConstName(v___x_1772_, v___x_1763_);
v___x_1774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1771_);
lean_ctor_set(v___x_1774_, 1, v___x_1773_);
v___x_1775_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__19, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__19_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__19);
v___x_1776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1774_);
lean_ctor_set(v___x_1776_, 1, v___x_1775_);
v___y_1717_ = v___x_1776_;
goto v___jp_1716_;
}
else
{
lean_object* v___x_1777_; 
lean_dec_ref(v_monoThms_1709_);
v___x_1777_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__20, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__20_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__20);
v___y_1717_ = v___x_1777_;
goto v___jp_1716_;
}
v___jp_1716_:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1718_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__0));
v___x_1719_ = lean_find_expr(v___x_1718_, v_t_1710_);
if (lean_obj_tag(v___x_1719_) == 1)
{
lean_object* v_val_1720_; lean_object* v___x_1721_; 
v_val_1720_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_val_1720_);
lean_dec_ref(v___x_1719_);
v___x_1721_ = l_Lean_getRecAppSyntax_x3f(v_val_1720_);
lean_dec(v_val_1720_);
if (lean_obj_tag(v___x_1721_) == 1)
{
lean_object* v_val_1722_; lean_object* v_fileName_1723_; lean_object* v_fileMap_1724_; lean_object* v_options_1725_; lean_object* v_currRecDepth_1726_; lean_object* v_maxRecDepth_1727_; lean_object* v_ref_1728_; lean_object* v_currNamespace_1729_; lean_object* v_openDecls_1730_; lean_object* v_initHeartbeats_1731_; lean_object* v_maxHeartbeats_1732_; lean_object* v_quotContext_1733_; lean_object* v_currMacroScope_1734_; uint8_t v_diag_1735_; lean_object* v_cancelTk_x3f_1736_; uint8_t v_suppressElabErrors_1737_; lean_object* v_inheritedTraceOptions_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v_ref_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v_val_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc_n(v_val_1722_, 2);
lean_dec_ref(v___x_1721_);
v_fileName_1723_ = lean_ctor_get(v___y_1713_, 0);
v_fileMap_1724_ = lean_ctor_get(v___y_1713_, 1);
v_options_1725_ = lean_ctor_get(v___y_1713_, 2);
v_currRecDepth_1726_ = lean_ctor_get(v___y_1713_, 3);
v_maxRecDepth_1727_ = lean_ctor_get(v___y_1713_, 4);
v_ref_1728_ = lean_ctor_get(v___y_1713_, 5);
v_currNamespace_1729_ = lean_ctor_get(v___y_1713_, 6);
v_openDecls_1730_ = lean_ctor_get(v___y_1713_, 7);
v_initHeartbeats_1731_ = lean_ctor_get(v___y_1713_, 8);
v_maxHeartbeats_1732_ = lean_ctor_get(v___y_1713_, 9);
v_quotContext_1733_ = lean_ctor_get(v___y_1713_, 10);
v_currMacroScope_1734_ = lean_ctor_get(v___y_1713_, 11);
v_diag_1735_ = lean_ctor_get_uint8(v___y_1713_, sizeof(void*)*14);
v_cancelTk_x3f_1736_ = lean_ctor_get(v___y_1713_, 12);
v_suppressElabErrors_1737_ = lean_ctor_get_uint8(v___y_1713_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1738_ = lean_ctor_get(v___y_1713_, 13);
v___x_1739_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__2, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__2_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__2);
v___x_1740_ = l_Lean_MessageData_ofSyntax(v_val_1722_);
v___x_1741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1739_);
lean_ctor_set(v___x_1741_, 1, v___x_1740_);
v___x_1742_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__4, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__4_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__4);
v___x_1743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1741_);
lean_ctor_set(v___x_1743_, 1, v___x_1742_);
v___x_1744_ = l_Lean_indentExpr(v_t_1710_);
v___x_1745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1743_);
lean_ctor_set(v___x_1745_, 1, v___x_1744_);
v___x_1746_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__6, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__6_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__6);
v___x_1747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1745_);
lean_ctor_set(v___x_1747_, 1, v___x_1746_);
v___x_1748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1747_);
lean_ctor_set(v___x_1748_, 1, v___y_1717_);
v_ref_1749_ = l_Lean_replaceRef(v_val_1722_, v_ref_1728_);
lean_dec(v_val_1722_);
lean_inc_ref(v_inheritedTraceOptions_1738_);
lean_inc(v_cancelTk_x3f_1736_);
lean_inc(v_currMacroScope_1734_);
lean_inc(v_quotContext_1733_);
lean_inc(v_maxHeartbeats_1732_);
lean_inc(v_initHeartbeats_1731_);
lean_inc(v_openDecls_1730_);
lean_inc(v_currNamespace_1729_);
lean_inc(v_maxRecDepth_1727_);
lean_inc(v_currRecDepth_1726_);
lean_inc_ref(v_options_1725_);
lean_inc_ref(v_fileMap_1724_);
lean_inc_ref(v_fileName_1723_);
v___x_1750_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1750_, 0, v_fileName_1723_);
lean_ctor_set(v___x_1750_, 1, v_fileMap_1724_);
lean_ctor_set(v___x_1750_, 2, v_options_1725_);
lean_ctor_set(v___x_1750_, 3, v_currRecDepth_1726_);
lean_ctor_set(v___x_1750_, 4, v_maxRecDepth_1727_);
lean_ctor_set(v___x_1750_, 5, v_ref_1749_);
lean_ctor_set(v___x_1750_, 6, v_currNamespace_1729_);
lean_ctor_set(v___x_1750_, 7, v_openDecls_1730_);
lean_ctor_set(v___x_1750_, 8, v_initHeartbeats_1731_);
lean_ctor_set(v___x_1750_, 9, v_maxHeartbeats_1732_);
lean_ctor_set(v___x_1750_, 10, v_quotContext_1733_);
lean_ctor_set(v___x_1750_, 11, v_currMacroScope_1734_);
lean_ctor_set(v___x_1750_, 12, v_cancelTk_x3f_1736_);
lean_ctor_set(v___x_1750_, 13, v_inheritedTraceOptions_1738_);
lean_ctor_set_uint8(v___x_1750_, sizeof(void*)*14, v_diag_1735_);
lean_ctor_set_uint8(v___x_1750_, sizeof(void*)*14 + 1, v_suppressElabErrors_1737_);
v___x_1751_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg(v___x_1748_, v___y_1711_, v___y_1712_, v___x_1750_, v___y_1714_);
lean_dec_ref(v___x_1750_);
return v___x_1751_;
}
else
{
lean_object* v___x_1752_; lean_object* v___x_1753_; 
lean_dec(v___x_1721_);
lean_dec_ref(v___y_1717_);
lean_dec_ref(v_t_1710_);
v___x_1752_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__9, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__9_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__9);
v___x_1753_ = l_panic___at___00Lean_Elab_partialFixpoint_spec__8___redArg(v___x_1752_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
return v___x_1753_;
}
}
else
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
lean_dec(v___x_1719_);
v___x_1754_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__11, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__11_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__11);
v___x_1755_ = l_Lean_indentExpr(v_t_1710_);
v___x_1756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1754_);
lean_ctor_set(v___x_1756_, 1, v___x_1755_);
v___x_1757_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__6, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__6_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__6);
v___x_1758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1756_);
lean_ctor_set(v___x_1758_, 1, v___x_1757_);
v___x_1759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
lean_ctor_set(v___x_1759_, 1, v___y_1717_);
v___x_1760_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg(v___x_1759_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
return v___x_1760_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___boxed(lean_object* v_monoThms_1778_, lean_object* v_t_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0(v_monoThms_1778_, v_t_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__1(lean_object* v_preDefs_1786_, lean_object* v_a_1787_, lean_object* v_fixedArgs_1788_, lean_object* v_00_u03b1_1789_, lean_object* v_f_1790_, lean_object* v_monoThms_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v___f_1797_; lean_object* v___x_1798_; 
v___f_1797_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1797_, 0, v_monoThms_1791_);
v___x_1798_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg(v_preDefs_1786_, v_a_1787_, v_fixedArgs_1788_, v_f_1790_, v___f_1797_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__1___boxed(lean_object* v_preDefs_1799_, lean_object* v_a_1800_, lean_object* v_fixedArgs_1801_, lean_object* v_00_u03b1_1802_, lean_object* v_f_1803_, lean_object* v_monoThms_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__1(v_preDefs_1799_, v_a_1800_, v_fixedArgs_1801_, v_00_u03b1_1802_, v_f_1803_, v_monoThms_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
return v_res_1810_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__1(void){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__0));
v___x_1813_ = l_Lean_stringToMessageData(v___x_1812_);
return v___x_1813_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__3(void){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__2));
v___x_1816_ = l_Lean_stringToMessageData(v___x_1815_);
return v___x_1816_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10(void){
_start:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1827_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7));
v___x_1828_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__9));
v___x_1829_ = l_Lean_Name_append(v___x_1828_, v___x_1827_);
return v___x_1829_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__12(void){
_start:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1831_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__11));
v___x_1832_ = l_Lean_stringToMessageData(v___x_1831_);
return v___x_1832_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__14(void){
_start:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1834_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__13));
v___x_1835_ = l_Lean_stringToMessageData(v___x_1834_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg(lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_hints_1841_, lean_object* v_preDefs_1842_, lean_object* v_a_1843_, lean_object* v_fixedArgs_1844_, lean_object* v_as_1845_, lean_object* v_i_1846_, lean_object* v_j_1847_, lean_object* v_bs_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v_zero_1856_; uint8_t v_isZero_1857_; 
v_zero_1856_ = lean_unsigned_to_nat(0u);
v_isZero_1857_ = lean_nat_dec_eq(v_i_1846_, v_zero_1856_);
if (v_isZero_1857_ == 1)
{
lean_object* v___x_1858_; 
lean_dec(v_j_1847_);
lean_dec(v_i_1846_);
lean_dec_ref(v_fixedArgs_1844_);
lean_dec_ref(v_a_1843_);
lean_dec_ref(v_preDefs_1842_);
lean_dec_ref(v_a_1840_);
lean_dec_ref(v_a_1839_);
v___x_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1858_, 0, v_bs_1848_);
return v___x_1858_;
}
else
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1859_ = l_Lean_instInhabitedExpr;
v___x_1860_ = lean_array_get_borrowed(v___x_1859_, v_a_1836_, v_j_1847_);
v___x_1861_ = lean_array_get_borrowed(v___x_1859_, v_a_1837_, v_j_1847_);
lean_inc(v___x_1860_);
v___x_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1860_);
lean_inc_ref(v___x_1862_);
lean_inc(v___x_1861_);
v___x_1863_ = l_Lean_Meta_toPartialOrder(v___x_1861_, v___x_1862_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v_a_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc(v_a_1864_);
lean_dec_ref(v___x_1863_);
v___x_1865_ = lean_array_get_borrowed(v___x_1859_, v_a_1838_, v_j_1847_);
v___x_1866_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__5));
lean_inc_ref(v_a_1839_);
v___x_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1867_, 0, v_a_1839_);
lean_inc_ref(v_a_1840_);
v___x_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1868_, 0, v_a_1840_);
v___x_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1869_, 0, v_a_1864_);
lean_inc(v___x_1865_);
v___x_1870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1865_);
v___x_1871_ = lean_unsigned_to_nat(5u);
v___x_1872_ = lean_mk_empty_array_with_capacity(v___x_1871_);
v___x_1873_ = lean_array_push(v___x_1872_, v___x_1867_);
v___x_1874_ = lean_array_push(v___x_1873_, v___x_1868_);
v___x_1875_ = lean_array_push(v___x_1874_, v___x_1862_);
v___x_1876_ = lean_array_push(v___x_1875_, v___x_1869_);
v___x_1877_ = lean_array_push(v___x_1876_, v___x_1870_);
v___x_1878_ = l_Lean_Meta_mkAppOptM(v___x_1866_, v___x_1877_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v_a_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v_term_x3f_1882_; lean_object* v_one_1883_; lean_object* v_n_1884_; lean_object* v_a_1886_; 
v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
lean_inc(v_a_1879_);
lean_dec_ref(v___x_1878_);
v___x_1880_ = l_Lean_Elab_instInhabitedPartialFixpoint_default;
v___x_1881_ = lean_array_get_borrowed(v___x_1880_, v_hints_1841_, v_j_1847_);
v_term_x3f_1882_ = lean_ctor_get(v___x_1881_, 1);
lean_inc(v_term_x3f_1882_);
v_one_1883_ = lean_unsigned_to_nat(1u);
v_n_1884_ = lean_nat_sub(v_i_1846_, v_one_1883_);
lean_dec(v_i_1846_);
if (lean_obj_tag(v_term_x3f_1882_) == 1)
{
lean_object* v_val_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1948_; 
v_val_1890_ = lean_ctor_get(v_term_x3f_1882_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v_term_x3f_1882_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1892_ = v_term_x3f_1882_;
v_isShared_1893_ = v_isSharedCheck_1948_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_val_1890_);
lean_dec(v_term_x3f_1882_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1948_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
uint8_t v___x_1894_; lean_object* v___x_1896_; 
v___x_1894_ = 1;
lean_inc(v_a_1879_);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 0, v_a_1879_);
v___x_1896_ = v___x_1892_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1879_);
v___x_1896_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; uint8_t v___x_1901_; lean_object* v___x_1902_; 
v___x_1897_ = lean_box(0);
v___x_1898_ = lean_box(v___x_1894_);
v___x_1899_ = lean_box(v___x_1894_);
v___x_1900_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_1900_, 0, v_val_1890_);
lean_closure_set(v___x_1900_, 1, v___x_1896_);
lean_closure_set(v___x_1900_, 2, v___x_1898_);
lean_closure_set(v___x_1900_, 3, v___x_1899_);
lean_closure_set(v___x_1900_, 4, v___x_1897_);
v___x_1901_ = 1;
v___x_1902_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1900_, v___x_1901_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; lean_object* v___x_1904_; lean_object* v_a_1905_; lean_object* v___x_1906_; 
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
lean_inc(v_a_1903_);
lean_dec_ref(v___x_1902_);
v___x_1904_ = l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18___redArg(v_a_1903_, v___y_1852_);
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
lean_inc_n(v_a_1905_, 2);
lean_dec_ref(v___x_1904_);
v___x_1906_ = l_Lean_Meta_getMVars(v_a_1905_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1908_; uint8_t v___x_1909_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
lean_inc(v_a_1907_);
lean_dec_ref(v___x_1906_);
v___x_1908_ = lean_array_get_size(v_a_1907_);
v___x_1909_ = lean_nat_dec_eq(v___x_1908_, v_zero_1856_);
if (v___x_1909_ == 0)
{
lean_object* v___x_1910_; 
lean_dec(v_a_1905_);
v___x_1910_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_1907_, v___x_1897_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
lean_dec(v_a_1907_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v___x_1911_; 
lean_dec_ref(v___x_1910_);
lean_inc(v_a_1879_);
v___x_1911_ = l_Lean_Meta_mkSorry(v_a_1879_, v___x_1894_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v___x_1913_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1912_);
lean_dec_ref(v___x_1911_);
v___x_1913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1913_, 0, v_a_1879_);
lean_ctor_set(v___x_1913_, 1, v_a_1912_);
v_a_1886_ = v___x_1913_;
goto v___jp_1885_;
}
else
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
lean_dec(v_n_1884_);
lean_dec(v_a_1879_);
lean_dec_ref(v_bs_1848_);
lean_dec(v_j_1847_);
lean_dec_ref(v_fixedArgs_1844_);
lean_dec_ref(v_a_1843_);
lean_dec_ref(v_preDefs_1842_);
lean_dec_ref(v_a_1840_);
lean_dec_ref(v_a_1839_);
v_a_1914_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1911_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1911_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
else
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
lean_dec(v_n_1884_);
lean_dec(v_a_1879_);
lean_dec_ref(v_bs_1848_);
lean_dec(v_j_1847_);
lean_dec_ref(v_fixedArgs_1844_);
lean_dec_ref(v_a_1843_);
lean_dec_ref(v_preDefs_1842_);
lean_dec_ref(v_a_1840_);
lean_dec_ref(v_a_1839_);
v_a_1922_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1910_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1910_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1922_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
else
{
lean_object* v___x_1930_; 
lean_dec(v_a_1907_);
v___x_1930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1930_, 0, v_a_1879_);
lean_ctor_set(v___x_1930_, 1, v_a_1905_);
v_a_1886_ = v___x_1930_;
goto v___jp_1885_;
}
}
else
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
lean_dec(v_a_1905_);
lean_dec(v_n_1884_);
lean_dec(v_a_1879_);
lean_dec_ref(v_bs_1848_);
lean_dec(v_j_1847_);
lean_dec_ref(v_fixedArgs_1844_);
lean_dec_ref(v_a_1843_);
lean_dec_ref(v_preDefs_1842_);
lean_dec_ref(v_a_1840_);
lean_dec_ref(v_a_1839_);
v_a_1931_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1906_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1906_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1931_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
lean_dec(v_n_1884_);
lean_dec(v_a_1879_);
lean_dec_ref(v_bs_1848_);
lean_dec(v_j_1847_);
lean_dec_ref(v_fixedArgs_1844_);
lean_dec_ref(v_a_1843_);
lean_dec_ref(v_preDefs_1842_);
lean_dec_ref(v_a_1840_);
lean_dec_ref(v_a_1839_);
v_a_1939_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1902_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1902_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
}
}
else
{
lean_object* v___x_1949_; lean_object* v___x_1950_; 
lean_dec(v_term_x3f_1882_);
v___x_1949_ = lean_box(0);
lean_inc(v_a_1879_);
v___x_1950_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1879_, v___x_1949_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v_a_1951_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___x_1962_; lean_object* v_declName_1963_; lean_object* v___f_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___f_1970_; lean_object* v___x_1971_; lean_object* v___f_1972_; lean_object* v___x_1973_; 
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
lean_inc(v_a_1951_);
lean_dec_ref(v___x_1950_);
v___x_1962_ = lean_array_fget_borrowed(v_as_1845_, v_j_1847_);
v_declName_1963_ = lean_ctor_get(v___x_1962_, 3);
lean_inc_ref(v_fixedArgs_1844_);
lean_inc_ref(v_a_1843_);
lean_inc_ref(v_preDefs_1842_);
v___f_1964_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__1___boxed), 11, 3);
lean_closure_set(v___f_1964_, 0, v_preDefs_1842_);
lean_closure_set(v___f_1964_, 1, v_a_1843_);
lean_closure_set(v___f_1964_, 2, v_fixedArgs_1844_);
v___x_1965_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__1, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__1_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__1);
lean_inc(v_declName_1963_);
v___x_1966_ = l_Lean_MessageData_ofName(v_declName_1963_);
lean_inc_ref(v___x_1966_);
v___x_1967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1965_);
lean_ctor_set(v___x_1967_, 1, v___x_1966_);
v___x_1968_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__3, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__3_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__3);
v___x_1969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1967_);
lean_ctor_set(v___x_1969_, 1, v___x_1968_);
v___f_1970_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1970_, 0, v___x_1969_);
v___x_1971_ = l_Lean_Expr_mvarId_x21(v_a_1951_);
v___f_1972_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__3___boxed), 7, 2);
lean_closure_set(v___f_1972_, 0, v___f_1964_);
lean_closure_set(v___f_1972_, 1, v___x_1971_);
v___x_1973_ = l_Lean_Meta_mapErrorImp___redArg(v___f_1972_, v___f_1970_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
if (lean_obj_tag(v___x_1973_) == 0)
{
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_options_1974_; uint8_t v_hasTrace_1975_; 
lean_dec_ref(v___x_1973_);
v_options_1974_ = lean_ctor_get(v___y_1853_, 2);
v_hasTrace_1975_ = lean_ctor_get_uint8(v_options_1974_, sizeof(void*)*1);
if (v_hasTrace_1975_ == 0)
{
lean_dec_ref(v___x_1966_);
v___y_1953_ = v___y_1849_;
v___y_1954_ = v___y_1850_;
v___y_1955_ = v___y_1851_;
v___y_1956_ = v___y_1852_;
v___y_1957_ = v___y_1853_;
v___y_1958_ = v___y_1854_;
goto v___jp_1952_;
}
else
{
lean_object* v_inheritedTraceOptions_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; uint8_t v___x_1979_; 
v_inheritedTraceOptions_1976_ = lean_ctor_get(v___y_1853_, 13);
v___x_1977_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7));
v___x_1978_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10);
v___x_1979_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1976_, v_options_1974_, v___x_1978_);
if (v___x_1979_ == 0)
{
lean_dec_ref(v___x_1966_);
v___y_1953_ = v___y_1849_;
v___y_1954_ = v___y_1850_;
v___y_1955_ = v___y_1851_;
v___y_1956_ = v___y_1852_;
v___y_1957_ = v___y_1853_;
v___y_1958_ = v___y_1854_;
goto v___jp_1952_;
}
else
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1980_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__12, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__12_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__12);
v___x_1981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1980_);
lean_ctor_set(v___x_1981_, 1, v___x_1966_);
v___x_1982_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__14, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__14_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__14);
v___x_1983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1981_);
lean_ctor_set(v___x_1983_, 1, v___x_1982_);
lean_inc(v_a_1951_);
v___x_1984_ = l_Lean_MessageData_ofExpr(v_a_1951_);
v___x_1985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1983_);
lean_ctor_set(v___x_1985_, 1, v___x_1984_);
v___x_1986_ = l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg(v___x_1977_, v___x_1985_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_dec_ref(v___x_1986_);
v___y_1953_ = v___y_1849_;
v___y_1954_ = v___y_1850_;
v___y_1955_ = v___y_1851_;
v___y_1956_ = v___y_1852_;
v___y_1957_ = v___y_1853_;
v___y_1958_ = v___y_1854_;
goto v___jp_1952_;
}
else
{
lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
lean_dec(v_a_1951_);
lean_dec(v_n_1884_);
lean_dec(v_a_1879_);
lean_dec_ref(v_bs_1848_);
lean_dec(v_j_1847_);
lean_dec_ref(v_fixedArgs_1844_);
lean_dec_ref(v_a_1843_);
lean_dec_ref(v_preDefs_1842_);
lean_dec_ref(v_a_1840_);
lean_dec_ref(v_a_1839_);
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1989_ = v___x_1986_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v___x_1986_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_a_1987_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
}
}
else
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2002_; 
lean_dec_ref(v___x_1966_);
lean_dec(v_a_1951_);
lean_dec(v_n_1884_);
lean_dec(v_a_1879_);
lean_dec_ref(v_bs_1848_);
lean_dec(v_j_1847_);
lean_dec_ref(v_fixedArgs_1844_);
lean_dec_ref(v_a_1843_);
lean_dec_ref(v_preDefs_1842_);
lean_dec_ref(v_a_1840_);
lean_dec_ref(v_a_1839_);
v_a_1995_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1997_ = v___x_1973_;
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1973_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1998_ == 0)
{
lean_ctor_set_tag(v___x_1997_, 1);
v___x_2000_ = v___x_1997_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1995_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
else
{
lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2010_; 
lean_dec_ref(v___x_1966_);
lean_dec(v_a_1951_);
lean_dec(v_n_1884_);
lean_dec(v_a_1879_);
lean_dec_ref(v_bs_1848_);
lean_dec(v_j_1847_);
lean_dec_ref(v_fixedArgs_1844_);
lean_dec_ref(v_a_1843_);
lean_dec_ref(v_preDefs_1842_);
lean_dec_ref(v_a_1840_);
lean_dec_ref(v_a_1839_);
v_a_2003_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_2005_ = v___x_1973_;
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v___x_1973_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2008_; 
if (v_isShared_2006_ == 0)
{
v___x_2008_ = v___x_2005_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_a_2003_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
v___jp_1952_:
{
lean_object* v___x_1959_; lean_object* v_a_1960_; lean_object* v___x_1961_; 
v___x_1959_ = l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18___redArg(v_a_1951_, v___y_1956_);
v_a_1960_ = lean_ctor_get(v___x_1959_, 0);
lean_inc(v_a_1960_);
lean_dec_ref(v___x_1959_);
v___x_1961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1961_, 0, v_a_1879_);
lean_ctor_set(v___x_1961_, 1, v_a_1960_);
v_a_1886_ = v___x_1961_;
goto v___jp_1885_;
}
}
else
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
lean_dec(v_n_1884_);
lean_dec(v_a_1879_);
lean_dec_ref(v_bs_1848_);
lean_dec(v_j_1847_);
lean_dec_ref(v_fixedArgs_1844_);
lean_dec_ref(v_a_1843_);
lean_dec_ref(v_preDefs_1842_);
lean_dec_ref(v_a_1840_);
lean_dec_ref(v_a_1839_);
v_a_2011_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2013_ = v___x_1950_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_1950_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2011_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
}
v___jp_1885_:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1887_ = lean_nat_add(v_j_1847_, v_one_1883_);
lean_dec(v_j_1847_);
v___x_1888_ = lean_array_push(v_bs_1848_, v_a_1886_);
v_i_1846_ = v_n_1884_;
v_j_1847_ = v___x_1887_;
v_bs_1848_ = v___x_1888_;
goto _start;
}
}
else
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2026_; 
lean_dec_ref(v_bs_1848_);
lean_dec(v_j_1847_);
lean_dec(v_i_1846_);
lean_dec_ref(v_fixedArgs_1844_);
lean_dec_ref(v_a_1843_);
lean_dec_ref(v_preDefs_1842_);
lean_dec_ref(v_a_1840_);
lean_dec_ref(v_a_1839_);
v_a_2019_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2021_ = v___x_1878_;
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_1878_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
if (v_isShared_2022_ == 0)
{
v___x_2024_ = v___x_2021_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_a_2019_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
else
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
lean_dec_ref(v___x_1862_);
lean_dec_ref(v_bs_1848_);
lean_dec(v_j_1847_);
lean_dec(v_i_1846_);
lean_dec_ref(v_fixedArgs_1844_);
lean_dec_ref(v_a_1843_);
lean_dec_ref(v_preDefs_1842_);
lean_dec_ref(v_a_1840_);
lean_dec_ref(v_a_1839_);
v_a_2027_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_1863_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_1863_);
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
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___boxed(lean_object** _args){
lean_object* v_a_2035_ = _args[0];
lean_object* v_a_2036_ = _args[1];
lean_object* v_a_2037_ = _args[2];
lean_object* v_a_2038_ = _args[3];
lean_object* v_a_2039_ = _args[4];
lean_object* v_hints_2040_ = _args[5];
lean_object* v_preDefs_2041_ = _args[6];
lean_object* v_a_2042_ = _args[7];
lean_object* v_fixedArgs_2043_ = _args[8];
lean_object* v_as_2044_ = _args[9];
lean_object* v_i_2045_ = _args[10];
lean_object* v_j_2046_ = _args[11];
lean_object* v_bs_2047_ = _args[12];
lean_object* v___y_2048_ = _args[13];
lean_object* v___y_2049_ = _args[14];
lean_object* v___y_2050_ = _args[15];
lean_object* v___y_2051_ = _args[16];
lean_object* v___y_2052_ = _args[17];
lean_object* v___y_2053_ = _args[18];
lean_object* v___y_2054_ = _args[19];
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg(v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_hints_2040_, v_preDefs_2041_, v_a_2042_, v_fixedArgs_2043_, v_as_2044_, v_i_2045_, v_j_2046_, v_bs_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec_ref(v_as_2044_);
lean_dec_ref(v_hints_2040_);
lean_dec_ref(v_a_2037_);
lean_dec_ref(v_a_2036_);
lean_dec_ref(v_a_2035_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19(lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_hints_2061_, lean_object* v_preDefs_2062_, lean_object* v_a_2063_, lean_object* v_fixedArgs_2064_, lean_object* v_as_2065_, lean_object* v_i_2066_, lean_object* v_j_2067_, lean_object* v_inv_2068_, lean_object* v_bs_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v___x_2077_; 
v___x_2077_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg(v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_, v_a_2060_, v_hints_2061_, v_preDefs_2062_, v_a_2063_, v_fixedArgs_2064_, v_as_2065_, v_i_2066_, v_j_2067_, v_bs_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___boxed(lean_object** _args){
lean_object* v_a_2078_ = _args[0];
lean_object* v_a_2079_ = _args[1];
lean_object* v_a_2080_ = _args[2];
lean_object* v_a_2081_ = _args[3];
lean_object* v_a_2082_ = _args[4];
lean_object* v_hints_2083_ = _args[5];
lean_object* v_preDefs_2084_ = _args[6];
lean_object* v_a_2085_ = _args[7];
lean_object* v_fixedArgs_2086_ = _args[8];
lean_object* v_as_2087_ = _args[9];
lean_object* v_i_2088_ = _args[10];
lean_object* v_j_2089_ = _args[11];
lean_object* v_inv_2090_ = _args[12];
lean_object* v_bs_2091_ = _args[13];
lean_object* v___y_2092_ = _args[14];
lean_object* v___y_2093_ = _args[15];
lean_object* v___y_2094_ = _args[16];
lean_object* v___y_2095_ = _args[17];
lean_object* v___y_2096_ = _args[18];
lean_object* v___y_2097_ = _args[19];
lean_object* v___y_2098_ = _args[20];
_start:
{
lean_object* v_res_2099_; 
v_res_2099_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19(v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_hints_2083_, v_preDefs_2084_, v_a_2085_, v_fixedArgs_2086_, v_as_2087_, v_i_2088_, v_j_2089_, v_inv_2090_, v_bs_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec_ref(v_as_2087_);
lean_dec_ref(v_hints_2083_);
lean_dec_ref(v_a_2080_);
lean_dec_ref(v_a_2079_);
lean_dec_ref(v_a_2078_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg___lam__0(lean_object* v___x_2100_, lean_object* v___x_2101_, lean_object* v___y_2102_, lean_object* v___x_2103_, lean_object* v_j_2104_, lean_object* v_a_2105_, uint8_t v_isZero_2106_, uint8_t v___x_2107_, uint8_t v___x_2108_, lean_object* v_ref_2109_, uint8_t v_kind_2110_, lean_object* v_levelParams_2111_, lean_object* v_modifiers_2112_, lean_object* v_declName_2113_, lean_object* v_binders_2114_, lean_object* v_numSectionVars_2115_, lean_object* v_type_2116_, lean_object* v_termination_2117_, lean_object* v_params_2118_, lean_object* v_x_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_){
_start:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2127_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v___x_2100_, v_params_2118_);
v___x_2128_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v___x_2100_, v_params_2118_);
v___x_2129_ = lean_box(0);
v___x_2130_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__0(v___x_2101_, v___x_2129_);
v___x_2131_ = l_Lean_mkConst(v___y_2102_, v___x_2130_);
v___x_2132_ = l_Lean_mkAppN(v___x_2131_, v___x_2127_);
lean_dec_ref(v___x_2127_);
v___x_2133_ = l_Lean_Meta_PProdN_proj(v___x_2103_, v_j_2104_, v_a_2105_, v___x_2132_);
v___x_2134_ = l_Lean_mkAppN(v___x_2133_, v___x_2128_);
lean_dec_ref(v___x_2128_);
v___x_2135_ = l_Lean_Meta_mkLambdaFVars(v_params_2118_, v___x_2134_, v_isZero_2106_, v___x_2107_, v___x_2107_, v___x_2107_, v___x_2108_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2144_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2138_ = v___x_2135_;
v_isShared_2139_ = v_isSharedCheck_2144_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2135_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2144_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2140_; lean_object* v___x_2142_; 
v___x_2140_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_2140_, 0, v_ref_2109_);
lean_ctor_set(v___x_2140_, 1, v_levelParams_2111_);
lean_ctor_set(v___x_2140_, 2, v_modifiers_2112_);
lean_ctor_set(v___x_2140_, 3, v_declName_2113_);
lean_ctor_set(v___x_2140_, 4, v_binders_2114_);
lean_ctor_set(v___x_2140_, 5, v_numSectionVars_2115_);
lean_ctor_set(v___x_2140_, 6, v_type_2116_);
lean_ctor_set(v___x_2140_, 7, v_a_2136_);
lean_ctor_set(v___x_2140_, 8, v_termination_2117_);
lean_ctor_set_uint8(v___x_2140_, sizeof(void*)*9, v_kind_2110_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v___x_2140_);
v___x_2142_ = v___x_2138_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2140_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
else
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2152_; 
lean_dec_ref(v_termination_2117_);
lean_dec_ref(v_type_2116_);
lean_dec(v_numSectionVars_2115_);
lean_dec(v_binders_2114_);
lean_dec(v_declName_2113_);
lean_dec_ref(v_modifiers_2112_);
lean_dec(v_levelParams_2111_);
lean_dec(v_ref_2109_);
v_a_2145_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2147_ = v___x_2135_;
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2135_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2150_; 
if (v_isShared_2148_ == 0)
{
v___x_2150_ = v___x_2147_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_a_2145_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_2153_ = _args[0];
lean_object* v___x_2154_ = _args[1];
lean_object* v___y_2155_ = _args[2];
lean_object* v___x_2156_ = _args[3];
lean_object* v_j_2157_ = _args[4];
lean_object* v_a_2158_ = _args[5];
lean_object* v_isZero_2159_ = _args[6];
lean_object* v___x_2160_ = _args[7];
lean_object* v___x_2161_ = _args[8];
lean_object* v_ref_2162_ = _args[9];
lean_object* v_kind_2163_ = _args[10];
lean_object* v_levelParams_2164_ = _args[11];
lean_object* v_modifiers_2165_ = _args[12];
lean_object* v_declName_2166_ = _args[13];
lean_object* v_binders_2167_ = _args[14];
lean_object* v_numSectionVars_2168_ = _args[15];
lean_object* v_type_2169_ = _args[16];
lean_object* v_termination_2170_ = _args[17];
lean_object* v_params_2171_ = _args[18];
lean_object* v_x_2172_ = _args[19];
lean_object* v___y_2173_ = _args[20];
lean_object* v___y_2174_ = _args[21];
lean_object* v___y_2175_ = _args[22];
lean_object* v___y_2176_ = _args[23];
lean_object* v___y_2177_ = _args[24];
lean_object* v___y_2178_ = _args[25];
lean_object* v___y_2179_ = _args[26];
_start:
{
uint8_t v_isZero_boxed_2180_; uint8_t v___x_56980__boxed_2181_; uint8_t v___x_56981__boxed_2182_; uint8_t v_kind_boxed_2183_; lean_object* v_res_2184_; 
v_isZero_boxed_2180_ = lean_unbox(v_isZero_2159_);
v___x_56980__boxed_2181_ = lean_unbox(v___x_2160_);
v___x_56981__boxed_2182_ = lean_unbox(v___x_2161_);
v_kind_boxed_2183_ = lean_unbox(v_kind_2163_);
v_res_2184_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg___lam__0(v___x_2153_, v___x_2154_, v___y_2155_, v___x_2156_, v_j_2157_, v_a_2158_, v_isZero_boxed_2180_, v___x_56980__boxed_2181_, v___x_56981__boxed_2182_, v_ref_2162_, v_kind_boxed_2183_, v_levelParams_2164_, v_modifiers_2165_, v_declName_2166_, v_binders_2167_, v_numSectionVars_2168_, v_type_2169_, v_termination_2170_, v_params_2171_, v_x_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec_ref(v_x_2172_);
lean_dec_ref(v_params_2171_);
lean_dec(v_j_2157_);
lean_dec(v___x_2156_);
lean_dec_ref(v___x_2153_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg(lean_object* v___x_2185_, lean_object* v___x_2186_, lean_object* v___y_2187_, lean_object* v___x_2188_, lean_object* v_a_2189_, lean_object* v_as_2190_, lean_object* v_i_2191_, lean_object* v_j_2192_, lean_object* v_bs_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
lean_object* v_zero_2201_; uint8_t v_isZero_2202_; 
v_zero_2201_ = lean_unsigned_to_nat(0u);
v_isZero_2202_ = lean_nat_dec_eq(v_i_2191_, v_zero_2201_);
if (v_isZero_2202_ == 1)
{
lean_object* v___x_2203_; 
lean_dec(v_j_2192_);
lean_dec(v_i_2191_);
lean_dec_ref(v_a_2189_);
lean_dec(v___x_2188_);
lean_dec(v___y_2187_);
lean_dec(v___x_2186_);
v___x_2203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2203_, 0, v_bs_2193_);
return v___x_2203_;
}
else
{
lean_object* v___x_2204_; lean_object* v_ref_2205_; uint8_t v_kind_2206_; lean_object* v_levelParams_2207_; lean_object* v_modifiers_2208_; lean_object* v_declName_2209_; lean_object* v_binders_2210_; lean_object* v_numSectionVars_2211_; lean_object* v_type_2212_; lean_object* v_termination_2213_; lean_object* v___x_2214_; uint8_t v___x_2215_; uint8_t v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___f_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2204_ = lean_array_fget_borrowed(v_as_2190_, v_j_2192_);
v_ref_2205_ = lean_ctor_get(v___x_2204_, 0);
v_kind_2206_ = lean_ctor_get_uint8(v___x_2204_, sizeof(void*)*9);
v_levelParams_2207_ = lean_ctor_get(v___x_2204_, 1);
v_modifiers_2208_ = lean_ctor_get(v___x_2204_, 2);
v_declName_2209_ = lean_ctor_get(v___x_2204_, 3);
v_binders_2210_ = lean_ctor_get(v___x_2204_, 4);
v_numSectionVars_2211_ = lean_ctor_get(v___x_2204_, 5);
v_type_2212_ = lean_ctor_get(v___x_2204_, 6);
v_termination_2213_ = lean_ctor_get(v___x_2204_, 8);
v___x_2214_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1);
v___x_2215_ = 1;
v___x_2216_ = 1;
v___x_2217_ = lean_array_get_borrowed(v___x_2214_, v___x_2185_, v_j_2192_);
v___x_2218_ = lean_box(v_isZero_2202_);
v___x_2219_ = lean_box(v___x_2215_);
v___x_2220_ = lean_box(v___x_2216_);
v___x_2221_ = lean_box(v_kind_2206_);
lean_inc_ref(v_termination_2213_);
lean_inc_ref_n(v_type_2212_, 2);
lean_inc(v_numSectionVars_2211_);
lean_inc(v_binders_2210_);
lean_inc(v_declName_2209_);
lean_inc_ref(v_modifiers_2208_);
lean_inc(v_levelParams_2207_);
lean_inc(v_ref_2205_);
lean_inc_ref(v_a_2189_);
lean_inc(v_j_2192_);
lean_inc(v___x_2188_);
lean_inc(v___y_2187_);
lean_inc(v___x_2186_);
lean_inc(v___x_2217_);
v___f_2222_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg___lam__0___boxed), 27, 18);
lean_closure_set(v___f_2222_, 0, v___x_2217_);
lean_closure_set(v___f_2222_, 1, v___x_2186_);
lean_closure_set(v___f_2222_, 2, v___y_2187_);
lean_closure_set(v___f_2222_, 3, v___x_2188_);
lean_closure_set(v___f_2222_, 4, v_j_2192_);
lean_closure_set(v___f_2222_, 5, v_a_2189_);
lean_closure_set(v___f_2222_, 6, v___x_2218_);
lean_closure_set(v___f_2222_, 7, v___x_2219_);
lean_closure_set(v___f_2222_, 8, v___x_2220_);
lean_closure_set(v___f_2222_, 9, v_ref_2205_);
lean_closure_set(v___f_2222_, 10, v___x_2221_);
lean_closure_set(v___f_2222_, 11, v_levelParams_2207_);
lean_closure_set(v___f_2222_, 12, v_modifiers_2208_);
lean_closure_set(v___f_2222_, 13, v_declName_2209_);
lean_closure_set(v___f_2222_, 14, v_binders_2210_);
lean_closure_set(v___f_2222_, 15, v_numSectionVars_2211_);
lean_closure_set(v___f_2222_, 16, v_type_2212_);
lean_closure_set(v___f_2222_, 17, v_termination_2213_);
v___x_2223_ = lean_array_get_size(v___x_2217_);
v___x_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2223_);
v___x_2225_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__20___redArg(v_type_2212_, v___x_2224_, v___f_2222_, v_isZero_2202_, v_isZero_2202_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
if (lean_obj_tag(v___x_2225_) == 0)
{
lean_object* v_a_2226_; lean_object* v_one_2227_; lean_object* v_n_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v_a_2226_ = lean_ctor_get(v___x_2225_, 0);
lean_inc(v_a_2226_);
lean_dec_ref(v___x_2225_);
v_one_2227_ = lean_unsigned_to_nat(1u);
v_n_2228_ = lean_nat_sub(v_i_2191_, v_one_2227_);
lean_dec(v_i_2191_);
v___x_2229_ = lean_nat_add(v_j_2192_, v_one_2227_);
lean_dec(v_j_2192_);
v___x_2230_ = lean_array_push(v_bs_2193_, v_a_2226_);
v_i_2191_ = v_n_2228_;
v_j_2192_ = v___x_2229_;
v_bs_2193_ = v___x_2230_;
goto _start;
}
else
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
lean_dec_ref(v_bs_2193_);
lean_dec(v_j_2192_);
lean_dec(v_i_2191_);
lean_dec_ref(v_a_2189_);
lean_dec(v___x_2188_);
lean_dec(v___y_2187_);
lean_dec(v___x_2186_);
v_a_2232_ = lean_ctor_get(v___x_2225_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2234_ = v___x_2225_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2225_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2237_; 
if (v_isShared_2235_ == 0)
{
v___x_2237_ = v___x_2234_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2232_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg___boxed(lean_object* v___x_2240_, lean_object* v___x_2241_, lean_object* v___y_2242_, lean_object* v___x_2243_, lean_object* v_a_2244_, lean_object* v_as_2245_, lean_object* v_i_2246_, lean_object* v_j_2247_, lean_object* v_bs_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg(v___x_2240_, v___x_2241_, v___y_2242_, v___x_2243_, v_a_2244_, v_as_2245_, v_i_2246_, v_j_2247_, v_bs_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec_ref(v_as_2245_);
lean_dec_ref(v___x_2240_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__23(size_t v_sz_2257_, size_t v_i_2258_, lean_object* v_bs_2259_){
_start:
{
uint8_t v___x_2260_; 
v___x_2260_ = lean_usize_dec_lt(v_i_2258_, v_sz_2257_);
if (v___x_2260_ == 0)
{
return v_bs_2259_;
}
else
{
lean_object* v_v_2261_; uint8_t v_fixpointType_2262_; lean_object* v___x_2263_; lean_object* v_bs_x27_2264_; size_t v___x_2265_; size_t v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v_v_2261_ = lean_array_uget_borrowed(v_bs_2259_, v_i_2258_);
v_fixpointType_2262_ = lean_ctor_get_uint8(v_v_2261_, sizeof(void*)*2);
v___x_2263_ = lean_unsigned_to_nat(0u);
v_bs_x27_2264_ = lean_array_uset(v_bs_2259_, v_i_2258_, v___x_2263_);
v___x_2265_ = ((size_t)1ULL);
v___x_2266_ = lean_usize_add(v_i_2258_, v___x_2265_);
v___x_2267_ = lean_box(v_fixpointType_2262_);
v___x_2268_ = lean_array_uset(v_bs_x27_2264_, v_i_2258_, v___x_2267_);
v_i_2258_ = v___x_2266_;
v_bs_2259_ = v___x_2268_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__23___boxed(lean_object* v_sz_2270_, lean_object* v_i_2271_, lean_object* v_bs_2272_){
_start:
{
size_t v_sz_boxed_2273_; size_t v_i_boxed_2274_; lean_object* v_res_2275_; 
v_sz_boxed_2273_ = lean_unbox_usize(v_sz_2270_);
lean_dec(v_sz_2270_);
v_i_boxed_2274_ = lean_unbox_usize(v_i_2271_);
lean_dec(v_i_2271_);
v_res_2275_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__23(v_sz_boxed_2273_, v_i_boxed_2274_, v_bs_2272_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg___lam__0(lean_object* v___y_2276_, uint8_t v_isExporting_2277_, lean_object* v___x_2278_, lean_object* v___y_2279_, lean_object* v___x_2280_, lean_object* v_a_x3f_2281_){
_start:
{
lean_object* v___x_2283_; lean_object* v_env_2284_; lean_object* v_nextMacroScope_2285_; lean_object* v_ngen_2286_; lean_object* v_auxDeclNGen_2287_; lean_object* v_traceState_2288_; lean_object* v_messages_2289_; lean_object* v_infoState_2290_; lean_object* v_snapshotTasks_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2316_; 
v___x_2283_ = lean_st_ref_take(v___y_2276_);
v_env_2284_ = lean_ctor_get(v___x_2283_, 0);
v_nextMacroScope_2285_ = lean_ctor_get(v___x_2283_, 1);
v_ngen_2286_ = lean_ctor_get(v___x_2283_, 2);
v_auxDeclNGen_2287_ = lean_ctor_get(v___x_2283_, 3);
v_traceState_2288_ = lean_ctor_get(v___x_2283_, 4);
v_messages_2289_ = lean_ctor_get(v___x_2283_, 6);
v_infoState_2290_ = lean_ctor_get(v___x_2283_, 7);
v_snapshotTasks_2291_ = lean_ctor_get(v___x_2283_, 8);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2316_ == 0)
{
lean_object* v_unused_2317_; 
v_unused_2317_ = lean_ctor_get(v___x_2283_, 5);
lean_dec(v_unused_2317_);
v___x_2293_ = v___x_2283_;
v_isShared_2294_ = v_isSharedCheck_2316_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_snapshotTasks_2291_);
lean_inc(v_infoState_2290_);
lean_inc(v_messages_2289_);
lean_inc(v_traceState_2288_);
lean_inc(v_auxDeclNGen_2287_);
lean_inc(v_ngen_2286_);
lean_inc(v_nextMacroScope_2285_);
lean_inc(v_env_2284_);
lean_dec(v___x_2283_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2316_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2295_; lean_object* v___x_2297_; 
v___x_2295_ = l_Lean_Environment_setExporting(v_env_2284_, v_isExporting_2277_);
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 5, v___x_2278_);
lean_ctor_set(v___x_2293_, 0, v___x_2295_);
v___x_2297_ = v___x_2293_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v___x_2295_);
lean_ctor_set(v_reuseFailAlloc_2315_, 1, v_nextMacroScope_2285_);
lean_ctor_set(v_reuseFailAlloc_2315_, 2, v_ngen_2286_);
lean_ctor_set(v_reuseFailAlloc_2315_, 3, v_auxDeclNGen_2287_);
lean_ctor_set(v_reuseFailAlloc_2315_, 4, v_traceState_2288_);
lean_ctor_set(v_reuseFailAlloc_2315_, 5, v___x_2278_);
lean_ctor_set(v_reuseFailAlloc_2315_, 6, v_messages_2289_);
lean_ctor_set(v_reuseFailAlloc_2315_, 7, v_infoState_2290_);
lean_ctor_set(v_reuseFailAlloc_2315_, 8, v_snapshotTasks_2291_);
v___x_2297_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v_mctx_2300_; lean_object* v_zetaDeltaFVarIds_2301_; lean_object* v_postponed_2302_; lean_object* v_diag_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2313_; 
v___x_2298_ = lean_st_ref_set(v___y_2276_, v___x_2297_);
v___x_2299_ = lean_st_ref_take(v___y_2279_);
v_mctx_2300_ = lean_ctor_get(v___x_2299_, 0);
v_zetaDeltaFVarIds_2301_ = lean_ctor_get(v___x_2299_, 2);
v_postponed_2302_ = lean_ctor_get(v___x_2299_, 3);
v_diag_2303_ = lean_ctor_get(v___x_2299_, 4);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2313_ == 0)
{
lean_object* v_unused_2314_; 
v_unused_2314_ = lean_ctor_get(v___x_2299_, 1);
lean_dec(v_unused_2314_);
v___x_2305_ = v___x_2299_;
v_isShared_2306_ = v_isSharedCheck_2313_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_diag_2303_);
lean_inc(v_postponed_2302_);
lean_inc(v_zetaDeltaFVarIds_2301_);
lean_inc(v_mctx_2300_);
lean_dec(v___x_2299_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2313_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2308_; 
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 1, v___x_2280_);
v___x_2308_ = v___x_2305_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_mctx_2300_);
lean_ctor_set(v_reuseFailAlloc_2312_, 1, v___x_2280_);
lean_ctor_set(v_reuseFailAlloc_2312_, 2, v_zetaDeltaFVarIds_2301_);
lean_ctor_set(v_reuseFailAlloc_2312_, 3, v_postponed_2302_);
lean_ctor_set(v_reuseFailAlloc_2312_, 4, v_diag_2303_);
v___x_2308_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2309_ = lean_st_ref_set(v___y_2279_, v___x_2308_);
v___x_2310_ = lean_box(0);
v___x_2311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2310_);
return v___x_2311_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg___lam__0___boxed(lean_object* v___y_2318_, lean_object* v_isExporting_2319_, lean_object* v___x_2320_, lean_object* v___y_2321_, lean_object* v___x_2322_, lean_object* v_a_x3f_2323_, lean_object* v___y_2324_){
_start:
{
uint8_t v_isExporting_boxed_2325_; lean_object* v_res_2326_; 
v_isExporting_boxed_2325_ = lean_unbox(v_isExporting_2319_);
v_res_2326_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg___lam__0(v___y_2318_, v_isExporting_boxed_2325_, v___x_2320_, v___y_2321_, v___x_2322_, v_a_x3f_2323_);
lean_dec(v_a_x3f_2323_);
lean_dec(v___y_2321_);
lean_dec(v___y_2318_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg(lean_object* v_x_2327_, uint8_t v_isExporting_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_){
_start:
{
lean_object* v___x_2336_; lean_object* v_env_2337_; uint8_t v_isExporting_2338_; lean_object* v___x_2339_; lean_object* v_env_2340_; lean_object* v_nextMacroScope_2341_; lean_object* v_ngen_2342_; lean_object* v_auxDeclNGen_2343_; lean_object* v_traceState_2344_; lean_object* v_messages_2345_; lean_object* v_infoState_2346_; lean_object* v_snapshotTasks_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2401_; 
v___x_2336_ = lean_st_ref_get(v___y_2334_);
v_env_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc_ref(v_env_2337_);
lean_dec(v___x_2336_);
v_isExporting_2338_ = lean_ctor_get_uint8(v_env_2337_, sizeof(void*)*8);
lean_dec_ref(v_env_2337_);
v___x_2339_ = lean_st_ref_take(v___y_2334_);
v_env_2340_ = lean_ctor_get(v___x_2339_, 0);
v_nextMacroScope_2341_ = lean_ctor_get(v___x_2339_, 1);
v_ngen_2342_ = lean_ctor_get(v___x_2339_, 2);
v_auxDeclNGen_2343_ = lean_ctor_get(v___x_2339_, 3);
v_traceState_2344_ = lean_ctor_get(v___x_2339_, 4);
v_messages_2345_ = lean_ctor_get(v___x_2339_, 6);
v_infoState_2346_ = lean_ctor_get(v___x_2339_, 7);
v_snapshotTasks_2347_ = lean_ctor_get(v___x_2339_, 8);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2401_ == 0)
{
lean_object* v_unused_2402_; 
v_unused_2402_ = lean_ctor_get(v___x_2339_, 5);
lean_dec(v_unused_2402_);
v___x_2349_ = v___x_2339_;
v_isShared_2350_ = v_isSharedCheck_2401_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_snapshotTasks_2347_);
lean_inc(v_infoState_2346_);
lean_inc(v_messages_2345_);
lean_inc(v_traceState_2344_);
lean_inc(v_auxDeclNGen_2343_);
lean_inc(v_ngen_2342_);
lean_inc(v_nextMacroScope_2341_);
lean_inc(v_env_2340_);
lean_dec(v___x_2339_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2401_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2354_; 
v___x_2351_ = l_Lean_Environment_setExporting(v_env_2340_, v_isExporting_2328_);
v___x_2352_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2);
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 5, v___x_2352_);
lean_ctor_set(v___x_2349_, 0, v___x_2351_);
v___x_2354_ = v___x_2349_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v___x_2351_);
lean_ctor_set(v_reuseFailAlloc_2400_, 1, v_nextMacroScope_2341_);
lean_ctor_set(v_reuseFailAlloc_2400_, 2, v_ngen_2342_);
lean_ctor_set(v_reuseFailAlloc_2400_, 3, v_auxDeclNGen_2343_);
lean_ctor_set(v_reuseFailAlloc_2400_, 4, v_traceState_2344_);
lean_ctor_set(v_reuseFailAlloc_2400_, 5, v___x_2352_);
lean_ctor_set(v_reuseFailAlloc_2400_, 6, v_messages_2345_);
lean_ctor_set(v_reuseFailAlloc_2400_, 7, v_infoState_2346_);
lean_ctor_set(v_reuseFailAlloc_2400_, 8, v_snapshotTasks_2347_);
v___x_2354_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v_mctx_2357_; lean_object* v_zetaDeltaFVarIds_2358_; lean_object* v_postponed_2359_; lean_object* v_diag_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2398_; 
v___x_2355_ = lean_st_ref_set(v___y_2334_, v___x_2354_);
v___x_2356_ = lean_st_ref_take(v___y_2332_);
v_mctx_2357_ = lean_ctor_get(v___x_2356_, 0);
v_zetaDeltaFVarIds_2358_ = lean_ctor_get(v___x_2356_, 2);
v_postponed_2359_ = lean_ctor_get(v___x_2356_, 3);
v_diag_2360_ = lean_ctor_get(v___x_2356_, 4);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2398_ == 0)
{
lean_object* v_unused_2399_; 
v_unused_2399_ = lean_ctor_get(v___x_2356_, 1);
lean_dec(v_unused_2399_);
v___x_2362_ = v___x_2356_;
v_isShared_2363_ = v_isSharedCheck_2398_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_diag_2360_);
lean_inc(v_postponed_2359_);
lean_inc(v_zetaDeltaFVarIds_2358_);
lean_inc(v_mctx_2357_);
lean_dec(v___x_2356_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2398_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2364_; lean_object* v___x_2366_; 
v___x_2364_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3);
if (v_isShared_2363_ == 0)
{
lean_ctor_set(v___x_2362_, 1, v___x_2364_);
v___x_2366_ = v___x_2362_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_mctx_2357_);
lean_ctor_set(v_reuseFailAlloc_2397_, 1, v___x_2364_);
lean_ctor_set(v_reuseFailAlloc_2397_, 2, v_zetaDeltaFVarIds_2358_);
lean_ctor_set(v_reuseFailAlloc_2397_, 3, v_postponed_2359_);
lean_ctor_set(v_reuseFailAlloc_2397_, 4, v_diag_2360_);
v___x_2366_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
lean_object* v___x_2367_; lean_object* v_r_2368_; 
v___x_2367_ = lean_st_ref_set(v___y_2332_, v___x_2366_);
lean_inc(v___y_2334_);
lean_inc_ref(v___y_2333_);
lean_inc(v___y_2332_);
lean_inc_ref(v___y_2331_);
lean_inc(v___y_2330_);
lean_inc_ref(v___y_2329_);
v_r_2368_ = lean_apply_7(v_x_2327_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, lean_box(0));
if (lean_obj_tag(v_r_2368_) == 0)
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2385_; 
v_a_2369_ = lean_ctor_get(v_r_2368_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v_r_2368_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2371_ = v_r_2368_;
v_isShared_2372_ = v_isSharedCheck_2385_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v_r_2368_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2385_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2374_; 
lean_inc(v_a_2369_);
if (v_isShared_2372_ == 0)
{
lean_ctor_set_tag(v___x_2371_, 1);
v___x_2374_ = v___x_2371_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v_a_2369_);
v___x_2374_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
lean_object* v___x_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2382_; 
v___x_2375_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg___lam__0(v___y_2334_, v_isExporting_2338_, v___x_2352_, v___y_2332_, v___x_2364_, v___x_2374_);
lean_dec_ref(v___x_2374_);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2382_ == 0)
{
lean_object* v_unused_2383_; 
v_unused_2383_ = lean_ctor_get(v___x_2375_, 0);
lean_dec(v_unused_2383_);
v___x_2377_ = v___x_2375_;
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
else
{
lean_dec(v___x_2375_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2380_; 
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 0, v_a_2369_);
v___x_2380_ = v___x_2377_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_a_2369_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
}
}
else
{
lean_object* v_a_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2395_; 
v_a_2386_ = lean_ctor_get(v_r_2368_, 0);
lean_inc(v_a_2386_);
lean_dec_ref(v_r_2368_);
v___x_2387_ = lean_box(0);
v___x_2388_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg___lam__0(v___y_2334_, v_isExporting_2338_, v___x_2352_, v___y_2332_, v___x_2364_, v___x_2387_);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2395_ == 0)
{
lean_object* v_unused_2396_; 
v_unused_2396_ = lean_ctor_get(v___x_2388_, 0);
lean_dec(v_unused_2396_);
v___x_2390_ = v___x_2388_;
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
else
{
lean_dec(v___x_2388_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2393_; 
if (v_isShared_2391_ == 0)
{
lean_ctor_set_tag(v___x_2390_, 1);
lean_ctor_set(v___x_2390_, 0, v_a_2386_);
v___x_2393_ = v___x_2390_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_a_2386_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg___boxed(lean_object* v_x_2403_, lean_object* v_isExporting_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
uint8_t v_isExporting_boxed_2412_; lean_object* v_res_2413_; 
v_isExporting_boxed_2412_ = lean_unbox(v_isExporting_2404_);
v_res_2413_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg(v_x_2403_, v_isExporting_boxed_2412_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17___redArg(lean_object* v_x_2414_, uint8_t v_when_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
if (v_when_2415_ == 0)
{
lean_object* v___x_2423_; 
lean_inc(v___y_2421_);
lean_inc_ref(v___y_2420_);
lean_inc(v___y_2419_);
lean_inc_ref(v___y_2418_);
lean_inc(v___y_2417_);
lean_inc_ref(v___y_2416_);
v___x_2423_ = lean_apply_7(v_x_2414_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, lean_box(0));
return v___x_2423_;
}
else
{
uint8_t v___x_2424_; lean_object* v___x_2425_; 
v___x_2424_ = 0;
v___x_2425_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg(v_x_2414_, v___x_2424_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
return v___x_2425_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17___redArg___boxed(lean_object* v_x_2426_, lean_object* v_when_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_){
_start:
{
uint8_t v_when_boxed_2435_; lean_object* v_res_2436_; 
v_when_boxed_2435_ = lean_unbox(v_when_2427_);
v_res_2436_ = l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17___redArg(v_x_2426_, v_when_boxed_2435_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_);
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2432_);
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16___redArg(lean_object* v_env_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
lean_object* v___x_2441_; lean_object* v_nextMacroScope_2442_; lean_object* v_ngen_2443_; lean_object* v_auxDeclNGen_2444_; lean_object* v_traceState_2445_; lean_object* v_messages_2446_; lean_object* v_infoState_2447_; lean_object* v_snapshotTasks_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2474_; 
v___x_2441_ = lean_st_ref_take(v___y_2439_);
v_nextMacroScope_2442_ = lean_ctor_get(v___x_2441_, 1);
v_ngen_2443_ = lean_ctor_get(v___x_2441_, 2);
v_auxDeclNGen_2444_ = lean_ctor_get(v___x_2441_, 3);
v_traceState_2445_ = lean_ctor_get(v___x_2441_, 4);
v_messages_2446_ = lean_ctor_get(v___x_2441_, 6);
v_infoState_2447_ = lean_ctor_get(v___x_2441_, 7);
v_snapshotTasks_2448_ = lean_ctor_get(v___x_2441_, 8);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2441_);
if (v_isSharedCheck_2474_ == 0)
{
lean_object* v_unused_2475_; lean_object* v_unused_2476_; 
v_unused_2475_ = lean_ctor_get(v___x_2441_, 5);
lean_dec(v_unused_2475_);
v_unused_2476_ = lean_ctor_get(v___x_2441_, 0);
lean_dec(v_unused_2476_);
v___x_2450_ = v___x_2441_;
v_isShared_2451_ = v_isSharedCheck_2474_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_snapshotTasks_2448_);
lean_inc(v_infoState_2447_);
lean_inc(v_messages_2446_);
lean_inc(v_traceState_2445_);
lean_inc(v_auxDeclNGen_2444_);
lean_inc(v_ngen_2443_);
lean_inc(v_nextMacroScope_2442_);
lean_dec(v___x_2441_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2474_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2452_; lean_object* v___x_2454_; 
v___x_2452_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2);
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 5, v___x_2452_);
lean_ctor_set(v___x_2450_, 0, v_env_2437_);
v___x_2454_ = v___x_2450_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_env_2437_);
lean_ctor_set(v_reuseFailAlloc_2473_, 1, v_nextMacroScope_2442_);
lean_ctor_set(v_reuseFailAlloc_2473_, 2, v_ngen_2443_);
lean_ctor_set(v_reuseFailAlloc_2473_, 3, v_auxDeclNGen_2444_);
lean_ctor_set(v_reuseFailAlloc_2473_, 4, v_traceState_2445_);
lean_ctor_set(v_reuseFailAlloc_2473_, 5, v___x_2452_);
lean_ctor_set(v_reuseFailAlloc_2473_, 6, v_messages_2446_);
lean_ctor_set(v_reuseFailAlloc_2473_, 7, v_infoState_2447_);
lean_ctor_set(v_reuseFailAlloc_2473_, 8, v_snapshotTasks_2448_);
v___x_2454_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v_mctx_2457_; lean_object* v_zetaDeltaFVarIds_2458_; lean_object* v_postponed_2459_; lean_object* v_diag_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2471_; 
v___x_2455_ = lean_st_ref_set(v___y_2439_, v___x_2454_);
v___x_2456_ = lean_st_ref_take(v___y_2438_);
v_mctx_2457_ = lean_ctor_get(v___x_2456_, 0);
v_zetaDeltaFVarIds_2458_ = lean_ctor_get(v___x_2456_, 2);
v_postponed_2459_ = lean_ctor_get(v___x_2456_, 3);
v_diag_2460_ = lean_ctor_get(v___x_2456_, 4);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2471_ == 0)
{
lean_object* v_unused_2472_; 
v_unused_2472_ = lean_ctor_get(v___x_2456_, 1);
lean_dec(v_unused_2472_);
v___x_2462_ = v___x_2456_;
v_isShared_2463_ = v_isSharedCheck_2471_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_diag_2460_);
lean_inc(v_postponed_2459_);
lean_inc(v_zetaDeltaFVarIds_2458_);
lean_inc(v_mctx_2457_);
lean_dec(v___x_2456_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2471_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2464_; lean_object* v___x_2466_; 
v___x_2464_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 1, v___x_2464_);
v___x_2466_ = v___x_2462_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_mctx_2457_);
lean_ctor_set(v_reuseFailAlloc_2470_, 1, v___x_2464_);
lean_ctor_set(v_reuseFailAlloc_2470_, 2, v_zetaDeltaFVarIds_2458_);
lean_ctor_set(v_reuseFailAlloc_2470_, 3, v_postponed_2459_);
lean_ctor_set(v_reuseFailAlloc_2470_, 4, v_diag_2460_);
v___x_2466_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2467_ = lean_st_ref_set(v___y_2438_, v___x_2466_);
v___x_2468_ = lean_box(0);
v___x_2469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2468_);
return v___x_2469_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16___redArg___boxed(lean_object* v_env_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
lean_object* v_res_2481_; 
v_res_2481_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16___redArg(v_env_2477_, v___y_2478_, v___y_2479_);
lean_dec(v___y_2479_);
lean_dec(v___y_2478_);
return v_res_2481_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14___redArg(lean_object* v_env_2482_, lean_object* v_x_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
lean_object* v___x_2491_; lean_object* v_env_2492_; lean_object* v_a_2494_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2491_ = lean_st_ref_get(v___y_2489_);
v_env_2492_ = lean_ctor_get(v___x_2491_, 0);
lean_inc_ref(v_env_2492_);
lean_dec(v___x_2491_);
v___x_2504_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16___redArg(v_env_2482_, v___y_2487_, v___y_2489_);
lean_dec_ref(v___x_2504_);
lean_inc(v___y_2489_);
lean_inc_ref(v___y_2488_);
lean_inc(v___y_2487_);
lean_inc_ref(v___y_2486_);
lean_inc(v___y_2485_);
lean_inc_ref(v___y_2484_);
v___x_2505_ = lean_apply_7(v_x_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, lean_box(0));
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v_a_2506_; lean_object* v___x_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2514_; 
v_a_2506_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_a_2506_);
lean_dec_ref(v___x_2505_);
v___x_2507_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16___redArg(v_env_2492_, v___y_2487_, v___y_2489_);
v_isSharedCheck_2514_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2514_ == 0)
{
lean_object* v_unused_2515_; 
v_unused_2515_ = lean_ctor_get(v___x_2507_, 0);
lean_dec(v_unused_2515_);
v___x_2509_ = v___x_2507_;
v_isShared_2510_ = v_isSharedCheck_2514_;
goto v_resetjp_2508_;
}
else
{
lean_dec(v___x_2507_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2514_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v___x_2512_; 
if (v_isShared_2510_ == 0)
{
lean_ctor_set(v___x_2509_, 0, v_a_2506_);
v___x_2512_ = v___x_2509_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v_a_2506_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
}
else
{
lean_object* v_a_2516_; 
v_a_2516_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_a_2516_);
lean_dec_ref(v___x_2505_);
v_a_2494_ = v_a_2516_;
goto v___jp_2493_;
}
v___jp_2493_:
{
lean_object* v___x_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2502_; 
v___x_2495_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16___redArg(v_env_2492_, v___y_2487_, v___y_2489_);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2502_ == 0)
{
lean_object* v_unused_2503_; 
v_unused_2503_ = lean_ctor_get(v___x_2495_, 0);
lean_dec(v_unused_2503_);
v___x_2497_ = v___x_2495_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_dec(v___x_2495_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2500_; 
if (v_isShared_2498_ == 0)
{
lean_ctor_set_tag(v___x_2497_, 1);
lean_ctor_set(v___x_2497_, 0, v_a_2494_);
v___x_2500_ = v___x_2497_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2494_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14___redArg___boxed(lean_object* v_env_2517_, lean_object* v_x_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
lean_object* v_res_2526_; 
v_res_2526_ = l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14___redArg(v_env_2517_, v_x_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13___redArg(lean_object* v_as_2527_, size_t v_i_2528_, size_t v_stop_2529_, lean_object* v_b_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_){
_start:
{
uint8_t v___x_2534_; 
v___x_2534_ = lean_usize_dec_eq(v_i_2528_, v_stop_2529_);
if (v___x_2534_ == 0)
{
lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2535_ = lean_array_uget_borrowed(v_as_2527_, v_i_2528_);
v___x_2536_ = l_Lean_Elab_addAsAxiom___redArg(v___x_2535_, v___y_2531_, v___y_2532_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v_a_2537_; size_t v___x_2538_; size_t v___x_2539_; 
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
lean_inc(v_a_2537_);
lean_dec_ref(v___x_2536_);
v___x_2538_ = ((size_t)1ULL);
v___x_2539_ = lean_usize_add(v_i_2528_, v___x_2538_);
v_i_2528_ = v___x_2539_;
v_b_2530_ = v_a_2537_;
goto _start;
}
else
{
return v___x_2536_;
}
}
else
{
lean_object* v___x_2541_; 
v___x_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2541_, 0, v_b_2530_);
return v___x_2541_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13___redArg___boxed(lean_object* v_as_2542_, lean_object* v_i_2543_, lean_object* v_stop_2544_, lean_object* v_b_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
size_t v_i_boxed_2549_; size_t v_stop_boxed_2550_; lean_object* v_res_2551_; 
v_i_boxed_2549_ = lean_unbox_usize(v_i_2543_);
lean_dec(v_i_2543_);
v_stop_boxed_2550_ = lean_unbox_usize(v_stop_2544_);
lean_dec(v_stop_2544_);
v_res_2551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13___redArg(v_as_2542_, v_i_boxed_2549_, v_stop_boxed_2550_, v_b_2545_, v___y_2546_, v___y_2547_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec_ref(v_as_2542_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__0(lean_object* v___x_2552_, lean_object* v___x_2553_, lean_object* v___x_2554_, lean_object* v_a_2555_, lean_object* v_f_2556_, lean_object* v_a_2557_, lean_object* v_preDefs_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_){
_start:
{
lean_object* v___y_2567_; uint8_t v___x_2577_; 
v___x_2577_ = lean_nat_dec_lt(v___x_2552_, v___x_2553_);
if (v___x_2577_ == 0)
{
lean_object* v___x_2578_; 
v___x_2578_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps(v___x_2554_, v_a_2555_, v_f_2556_, v_a_2557_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_);
return v___x_2578_;
}
else
{
lean_object* v___x_2579_; lean_object* v___x_2580_; uint8_t v___x_2581_; 
v___x_2579_ = lean_box(0);
v___x_2580_ = lean_array_get_size(v_preDefs_2558_);
v___x_2581_ = lean_nat_dec_le(v___x_2553_, v___x_2580_);
if (v___x_2581_ == 0)
{
uint8_t v___x_2582_; 
v___x_2582_ = lean_nat_dec_lt(v___x_2552_, v___x_2580_);
if (v___x_2582_ == 0)
{
lean_object* v___x_2583_; 
v___x_2583_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps(v___x_2554_, v_a_2555_, v_f_2556_, v_a_2557_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_);
return v___x_2583_;
}
else
{
size_t v___x_2584_; size_t v___x_2585_; lean_object* v___x_2586_; 
v___x_2584_ = ((size_t)0ULL);
v___x_2585_ = lean_usize_of_nat(v___x_2580_);
v___x_2586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13___redArg(v_preDefs_2558_, v___x_2584_, v___x_2585_, v___x_2579_, v___y_2563_, v___y_2564_);
v___y_2567_ = v___x_2586_;
goto v___jp_2566_;
}
}
else
{
size_t v___x_2587_; size_t v___x_2588_; lean_object* v___x_2589_; 
v___x_2587_ = ((size_t)0ULL);
v___x_2588_ = lean_usize_of_nat(v___x_2553_);
v___x_2589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13___redArg(v_preDefs_2558_, v___x_2587_, v___x_2588_, v___x_2579_, v___y_2563_, v___y_2564_);
v___y_2567_ = v___x_2589_;
goto v___jp_2566_;
}
}
v___jp_2566_:
{
if (lean_obj_tag(v___y_2567_) == 0)
{
lean_object* v___x_2568_; 
lean_dec_ref(v___y_2567_);
v___x_2568_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps(v___x_2554_, v_a_2555_, v_f_2556_, v_a_2557_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_);
return v___x_2568_;
}
else
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2576_; 
lean_dec_ref(v_f_2556_);
lean_dec_ref(v_a_2555_);
lean_dec_ref(v___x_2554_);
v_a_2569_ = lean_ctor_get(v___y_2567_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___y_2567_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2571_ = v___y_2567_;
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___y_2567_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2574_; 
if (v_isShared_2572_ == 0)
{
v___x_2574_ = v___x_2571_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2569_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__0___boxed(lean_object* v___x_2590_, lean_object* v___x_2591_, lean_object* v___x_2592_, lean_object* v_a_2593_, lean_object* v_f_2594_, lean_object* v_a_2595_, lean_object* v_preDefs_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__0(v___x_2590_, v___x_2591_, v___x_2592_, v_a_2593_, v_f_2594_, v_a_2595_, v_preDefs_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
lean_dec_ref(v_preDefs_2596_);
lean_dec_ref(v_a_2595_);
lean_dec(v___x_2591_);
lean_dec(v___x_2590_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__1(lean_object* v___x_2605_, lean_object* v___x_2606_, lean_object* v___x_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_preDefs_2610_, uint8_t v_isZero_2611_, lean_object* v_f_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
lean_object* v___x_2620_; lean_object* v_env_2621_; lean_object* v___f_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2620_ = lean_st_ref_get(v___y_2618_);
v_env_2621_ = lean_ctor_get(v___x_2620_, 0);
lean_inc_ref(v_env_2621_);
lean_dec(v___x_2620_);
lean_inc_ref(v_f_2612_);
v___f_2622_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2622_, 0, v___x_2605_);
lean_closure_set(v___f_2622_, 1, v___x_2606_);
lean_closure_set(v___f_2622_, 2, v___x_2607_);
lean_closure_set(v___f_2622_, 3, v_a_2608_);
lean_closure_set(v___f_2622_, 4, v_f_2612_);
lean_closure_set(v___f_2622_, 5, v_a_2609_);
lean_closure_set(v___f_2622_, 6, v_preDefs_2610_);
v___x_2623_ = l_Lean_Environment_unlockAsync(v_env_2621_);
v___x_2624_ = l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14___redArg(v___x_2623_, v___f_2622_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
if (lean_obj_tag(v___x_2624_) == 0)
{
lean_object* v_a_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; uint8_t v___x_2629_; uint8_t v___x_2630_; lean_object* v___x_2631_; 
v_a_2625_ = lean_ctor_get(v___x_2624_, 0);
lean_inc(v_a_2625_);
lean_dec_ref(v___x_2624_);
v___x_2626_ = lean_unsigned_to_nat(1u);
v___x_2627_ = lean_mk_empty_array_with_capacity(v___x_2626_);
v___x_2628_ = lean_array_push(v___x_2627_, v_f_2612_);
v___x_2629_ = 1;
v___x_2630_ = 1;
v___x_2631_ = l_Lean_Meta_mkLambdaFVars(v___x_2628_, v_a_2625_, v_isZero_2611_, v___x_2629_, v_isZero_2611_, v___x_2629_, v___x_2630_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
lean_dec_ref(v___x_2628_);
return v___x_2631_;
}
else
{
lean_dec_ref(v_f_2612_);
return v___x_2624_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__1___boxed(lean_object* v___x_2632_, lean_object* v___x_2633_, lean_object* v___x_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_preDefs_2637_, lean_object* v_isZero_2638_, lean_object* v_f_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
uint8_t v_isZero_boxed_2647_; lean_object* v_res_2648_; 
v_isZero_boxed_2647_ = lean_unbox(v_isZero_2638_);
v_res_2648_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__1(v___x_2632_, v___x_2633_, v___x_2634_, v_a_2635_, v_a_2636_, v_preDefs_2637_, v_isZero_boxed_2647_, v_f_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
return v_res_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg___lam__0(lean_object* v_k_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v_b_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
lean_object* v___x_2658_; 
lean_inc(v___y_2656_);
lean_inc_ref(v___y_2655_);
lean_inc(v___y_2654_);
lean_inc_ref(v___y_2653_);
lean_inc(v___y_2651_);
lean_inc_ref(v___y_2650_);
v___x_2658_ = lean_apply_8(v_k_2649_, v_b_2652_, v___y_2650_, v___y_2651_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, lean_box(0));
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg___lam__0___boxed(lean_object* v_k_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v_b_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_){
_start:
{
lean_object* v_res_2668_; 
v_res_2668_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg___lam__0(v_k_2659_, v___y_2660_, v___y_2661_, v_b_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
lean_dec(v___y_2661_);
lean_dec_ref(v___y_2660_);
return v_res_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg(lean_object* v_name_2669_, uint8_t v_bi_2670_, lean_object* v_type_2671_, lean_object* v_k_2672_, uint8_t v_kind_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
lean_object* v___f_2681_; lean_object* v___x_2682_; 
lean_inc(v___y_2675_);
lean_inc_ref(v___y_2674_);
v___f_2681_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2681_, 0, v_k_2672_);
lean_closure_set(v___f_2681_, 1, v___y_2674_);
lean_closure_set(v___f_2681_, 2, v___y_2675_);
v___x_2682_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2669_, v_bi_2670_, v_type_2671_, v___f_2681_, v_kind_2673_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_);
if (lean_obj_tag(v___x_2682_) == 0)
{
return v___x_2682_;
}
else
{
lean_object* v_a_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2690_; 
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2685_ = v___x_2682_;
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_a_2683_);
lean_dec(v___x_2682_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg___boxed(lean_object* v_name_2691_, lean_object* v_bi_2692_, lean_object* v_type_2693_, lean_object* v_k_2694_, lean_object* v_kind_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_){
_start:
{
uint8_t v_bi_boxed_2703_; uint8_t v_kind_boxed_2704_; lean_object* v_res_2705_; 
v_bi_boxed_2703_ = lean_unbox(v_bi_2692_);
v_kind_boxed_2704_ = lean_unbox(v_kind_2695_);
v_res_2705_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg(v_name_2691_, v_bi_boxed_2703_, v_type_2693_, v_k_2694_, v_kind_boxed_2704_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
lean_dec(v___y_2699_);
lean_dec_ref(v___y_2698_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
return v_res_2705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15___redArg(lean_object* v_name_2706_, lean_object* v_type_2707_, lean_object* v_k_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_){
_start:
{
uint8_t v___x_2716_; uint8_t v___x_2717_; lean_object* v___x_2718_; 
v___x_2716_ = 0;
v___x_2717_ = 0;
v___x_2718_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg(v_name_2706_, v___x_2716_, v_type_2707_, v_k_2708_, v___x_2717_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15___redArg___boxed(lean_object* v_name_2719_, lean_object* v_type_2720_, lean_object* v_k_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
lean_object* v_res_2729_; 
v_res_2729_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15___redArg(v_name_2719_, v_type_2720_, v_k_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg(lean_object* v___x_2733_, lean_object* v_fixedArgs_2734_, lean_object* v___x_2735_, lean_object* v_a_2736_, lean_object* v___x_2737_, lean_object* v_preDefs_2738_, lean_object* v_a_2739_, lean_object* v_as_2740_, lean_object* v_i_2741_, lean_object* v_j_2742_, lean_object* v_bs_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
lean_object* v_zero_2751_; uint8_t v_isZero_2752_; 
v_zero_2751_ = lean_unsigned_to_nat(0u);
v_isZero_2752_ = lean_nat_dec_eq(v_i_2741_, v_zero_2751_);
if (v_isZero_2752_ == 1)
{
lean_object* v___x_2753_; 
lean_dec(v_j_2742_);
lean_dec(v_i_2741_);
lean_dec_ref(v_a_2739_);
lean_dec_ref(v_preDefs_2738_);
lean_dec(v___x_2737_);
lean_dec_ref(v_a_2736_);
lean_dec_ref(v___x_2735_);
lean_dec_ref(v_fixedArgs_2734_);
v___x_2753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2753_, 0, v_bs_2743_);
return v___x_2753_;
}
else
{
lean_object* v___x_2754_; lean_object* v_value_2755_; lean_object* v___x_2756_; lean_object* v_one_2757_; lean_object* v_n_2758_; lean_object* v___y_2760_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2754_ = lean_array_fget_borrowed(v_as_2740_, v_j_2742_);
v_value_2755_ = lean_ctor_get(v___x_2754_, 7);
v___x_2756_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1);
v_one_2757_ = lean_unsigned_to_nat(1u);
v_n_2758_ = lean_nat_sub(v_i_2741_, v_one_2757_);
lean_dec(v_i_2741_);
v___x_2773_ = lean_array_get_borrowed(v___x_2756_, v___x_2733_, v_j_2742_);
lean_inc_ref(v_fixedArgs_2734_);
lean_inc_ref(v_value_2755_);
lean_inc(v___x_2773_);
v___x_2774_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_2773_, v_value_2755_, v_fixedArgs_2734_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
if (lean_obj_tag(v___x_2774_) == 0)
{
lean_object* v_a_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; 
v_a_2775_ = lean_ctor_get(v___x_2774_, 0);
lean_inc(v_a_2775_);
lean_dec_ref(v___x_2774_);
v___x_2776_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___closed__1));
v___x_2777_ = l_Lean_Core_mkFreshUserName(v___x_2776_, v___y_2748_, v___y_2749_);
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_object* v_a_2778_; lean_object* v___x_2779_; lean_object* v___f_2780_; lean_object* v___x_2781_; 
v_a_2778_ = lean_ctor_get(v___x_2777_, 0);
lean_inc(v_a_2778_);
lean_dec_ref(v___x_2777_);
v___x_2779_ = lean_box(v_isZero_2752_);
lean_inc_ref(v_preDefs_2738_);
lean_inc_ref(v_a_2736_);
lean_inc_ref(v___x_2735_);
lean_inc(v___x_2737_);
v___f_2780_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__1___boxed), 15, 7);
lean_closure_set(v___f_2780_, 0, v_zero_2751_);
lean_closure_set(v___f_2780_, 1, v___x_2737_);
lean_closure_set(v___f_2780_, 2, v___x_2735_);
lean_closure_set(v___f_2780_, 3, v_a_2736_);
lean_closure_set(v___f_2780_, 4, v_a_2775_);
lean_closure_set(v___f_2780_, 5, v_preDefs_2738_);
lean_closure_set(v___f_2780_, 6, v___x_2779_);
lean_inc_ref(v_a_2739_);
v___x_2781_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15___redArg(v_a_2778_, v_a_2739_, v___f_2780_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
v___y_2760_ = v___x_2781_;
goto v___jp_2759_;
}
else
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
lean_dec(v_a_2775_);
lean_dec(v_n_2758_);
lean_dec_ref(v_bs_2743_);
lean_dec(v_j_2742_);
lean_dec_ref(v_a_2739_);
lean_dec_ref(v_preDefs_2738_);
lean_dec(v___x_2737_);
lean_dec_ref(v_a_2736_);
lean_dec_ref(v___x_2735_);
lean_dec_ref(v_fixedArgs_2734_);
v_a_2782_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2784_ = v___x_2777_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2777_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2782_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
}
else
{
v___y_2760_ = v___x_2774_;
goto v___jp_2759_;
}
v___jp_2759_:
{
if (lean_obj_tag(v___y_2760_) == 0)
{
lean_object* v_a_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
v_a_2761_ = lean_ctor_get(v___y_2760_, 0);
lean_inc(v_a_2761_);
lean_dec_ref(v___y_2760_);
v___x_2762_ = lean_nat_add(v_j_2742_, v_one_2757_);
lean_dec(v_j_2742_);
v___x_2763_ = lean_array_push(v_bs_2743_, v_a_2761_);
v_i_2741_ = v_n_2758_;
v_j_2742_ = v___x_2762_;
v_bs_2743_ = v___x_2763_;
goto _start;
}
else
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2772_; 
lean_dec(v_n_2758_);
lean_dec_ref(v_bs_2743_);
lean_dec(v_j_2742_);
lean_dec_ref(v_a_2739_);
lean_dec_ref(v_preDefs_2738_);
lean_dec(v___x_2737_);
lean_dec_ref(v_a_2736_);
lean_dec_ref(v___x_2735_);
lean_dec_ref(v_fixedArgs_2734_);
v_a_2765_ = lean_ctor_get(v___y_2760_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___y_2760_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2767_ = v___y_2760_;
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___y_2760_);
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
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___boxed(lean_object** _args){
lean_object* v___x_2790_ = _args[0];
lean_object* v_fixedArgs_2791_ = _args[1];
lean_object* v___x_2792_ = _args[2];
lean_object* v_a_2793_ = _args[3];
lean_object* v___x_2794_ = _args[4];
lean_object* v_preDefs_2795_ = _args[5];
lean_object* v_a_2796_ = _args[6];
lean_object* v_as_2797_ = _args[7];
lean_object* v_i_2798_ = _args[8];
lean_object* v_j_2799_ = _args[9];
lean_object* v_bs_2800_ = _args[10];
lean_object* v___y_2801_ = _args[11];
lean_object* v___y_2802_ = _args[12];
lean_object* v___y_2803_ = _args[13];
lean_object* v___y_2804_ = _args[14];
lean_object* v___y_2805_ = _args[15];
lean_object* v___y_2806_ = _args[16];
lean_object* v___y_2807_ = _args[17];
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg(v___x_2790_, v_fixedArgs_2791_, v___x_2792_, v_a_2793_, v___x_2794_, v_preDefs_2795_, v_a_2796_, v_as_2797_, v_i_2798_, v_j_2799_, v_bs_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec_ref(v_as_2797_);
lean_dec_ref(v___x_2790_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16(lean_object* v___x_2809_, lean_object* v_fixedArgs_2810_, lean_object* v___x_2811_, lean_object* v_a_2812_, lean_object* v___x_2813_, lean_object* v_preDefs_2814_, lean_object* v_a_2815_, lean_object* v_as_2816_, lean_object* v_i_2817_, lean_object* v_j_2818_, lean_object* v_inv_2819_, lean_object* v_bs_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_){
_start:
{
lean_object* v___x_2828_; 
v___x_2828_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg(v___x_2809_, v_fixedArgs_2810_, v___x_2811_, v_a_2812_, v___x_2813_, v_preDefs_2814_, v_a_2815_, v_as_2816_, v_i_2817_, v_j_2818_, v_bs_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___boxed(lean_object** _args){
lean_object* v___x_2829_ = _args[0];
lean_object* v_fixedArgs_2830_ = _args[1];
lean_object* v___x_2831_ = _args[2];
lean_object* v_a_2832_ = _args[3];
lean_object* v___x_2833_ = _args[4];
lean_object* v_preDefs_2834_ = _args[5];
lean_object* v_a_2835_ = _args[6];
lean_object* v_as_2836_ = _args[7];
lean_object* v_i_2837_ = _args[8];
lean_object* v_j_2838_ = _args[9];
lean_object* v_inv_2839_ = _args[10];
lean_object* v_bs_2840_ = _args[11];
lean_object* v___y_2841_ = _args[12];
lean_object* v___y_2842_ = _args[13];
lean_object* v___y_2843_ = _args[14];
lean_object* v___y_2844_ = _args[15];
lean_object* v___y_2845_ = _args[16];
lean_object* v___y_2846_ = _args[17];
lean_object* v___y_2847_ = _args[18];
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16(v___x_2829_, v_fixedArgs_2830_, v___x_2831_, v_a_2832_, v___x_2833_, v_preDefs_2834_, v_a_2835_, v_as_2836_, v_i_2837_, v_j_2838_, v_inv_2839_, v_bs_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec_ref(v_as_2836_);
lean_dec_ref(v___x_2829_);
return v_res_2848_;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2849_ = l_Lean_instInhabitedExpr;
v___x_2850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2849_);
lean_ctor_set(v___x_2850_, 1, v___x_2849_);
return v___x_2850_;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2856_ = ((lean_object*)(l_Lean_Elab_partialFixpoint___lam__0___closed__4));
v___x_2857_ = l_Lean_stringToMessageData(v___x_2856_);
return v___x_2857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_partialFixpoint___lam__0(lean_object* v_a_2858_, lean_object* v_perms_2859_, lean_object* v___x_2860_, lean_object* v_preDefs_2861_, lean_object* v___x_2862_, lean_object* v___x_2863_, size_t v___x_2864_, lean_object* v___x_2865_, lean_object* v_a_2866_, uint8_t v___x_2867_, lean_object* v_hints_2868_, lean_object* v___x_2869_, lean_object* v_docCtx_2870_, size_t v_sz_2871_, lean_object* v_fixedArgs_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_){
_start:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2880_ = lean_array_get_size(v_a_2858_);
v___x_2881_ = lean_mk_empty_array_with_capacity(v___x_2880_);
lean_inc(v___x_2860_);
lean_inc_ref(v_fixedArgs_2872_);
v___x_2882_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__10___redArg(v_perms_2859_, v_fixedArgs_2872_, v_a_2858_, v___x_2880_, v___x_2860_, v___x_2881_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v_a_2883_; lean_object* v___x_2884_; 
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
lean_inc(v_a_2883_);
lean_dec_ref(v___x_2882_);
lean_inc_ref(v___x_2863_);
lean_inc(v___x_2860_);
lean_inc(v___x_2862_);
lean_inc_ref(v_fixedArgs_2872_);
v___x_2884_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11___redArg(v_perms_2859_, v_fixedArgs_2872_, v_preDefs_2861_, v___x_2862_, v___x_2860_, v___x_2863_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v_a_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
v_a_2885_ = lean_ctor_get(v___x_2884_, 0);
lean_inc_n(v_a_2885_, 2);
lean_dec_ref(v___x_2884_);
v___x_2886_ = l_Lean_Level_ofNat(v___x_2860_);
v___x_2887_ = l_Lean_Meta_PProdN_pack(v___x_2886_, v_a_2885_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v_a_2888_; size_t v_sz_2889_; lean_object* v___x_2890_; 
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
lean_inc(v_a_2888_);
lean_dec_ref(v___x_2887_);
v_sz_2889_ = lean_array_size(v_a_2883_);
v___x_2890_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12(v_sz_2889_, v___x_2864_, v_a_2883_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; lean_object* v___x_2892_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
lean_inc_n(v_a_2891_, 2);
lean_dec_ref(v___x_2890_);
v___x_2892_ = l_Lean_Meta_mkPackedPPRodInstance(v_a_2891_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v_a_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
lean_inc_n(v_a_2893_, 2);
lean_dec_ref(v___x_2892_);
v___x_2894_ = lean_box(0);
v___x_2895_ = l_Lean_Meta_toPartialOrder(v_a_2893_, v___x_2894_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
if (lean_obj_tag(v___x_2895_) == 0)
{
lean_object* v_a_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
v_a_2896_ = lean_ctor_get(v___x_2895_, 0);
lean_inc(v_a_2896_);
lean_dec_ref(v___x_2895_);
lean_inc(v___x_2860_);
lean_inc(v_a_2888_);
lean_inc_ref_n(v_preDefs_2861_, 2);
lean_inc_n(v___x_2862_, 2);
lean_inc_ref(v_a_2866_);
lean_inc_ref(v_fixedArgs_2872_);
lean_inc_ref(v_perms_2859_);
v___x_2897_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___boxed), 19, 12);
lean_closure_set(v___x_2897_, 0, v_perms_2859_);
lean_closure_set(v___x_2897_, 1, v_fixedArgs_2872_);
lean_closure_set(v___x_2897_, 2, v___x_2865_);
lean_closure_set(v___x_2897_, 3, v_a_2866_);
lean_closure_set(v___x_2897_, 4, v___x_2862_);
lean_closure_set(v___x_2897_, 5, v_preDefs_2861_);
lean_closure_set(v___x_2897_, 6, v_a_2888_);
lean_closure_set(v___x_2897_, 7, v_preDefs_2861_);
lean_closure_set(v___x_2897_, 8, v___x_2862_);
lean_closure_set(v___x_2897_, 9, v___x_2860_);
lean_closure_set(v___x_2897_, 10, lean_box(0));
lean_closure_set(v___x_2897_, 11, v___x_2863_);
v___x_2898_ = l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17___redArg(v___x_2897_, v___x_2867_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_object* v_a_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v_a_2899_ = lean_ctor_get(v___x_2898_, 0);
lean_inc(v_a_2899_);
lean_dec_ref(v___x_2898_);
v___x_2900_ = lean_mk_empty_array_with_capacity(v___x_2862_);
lean_inc_ref(v___x_2900_);
lean_inc(v___x_2860_);
lean_inc(v___x_2862_);
lean_inc_ref(v_fixedArgs_2872_);
lean_inc_ref(v_a_2866_);
lean_inc_ref_n(v_preDefs_2861_, 2);
lean_inc_ref(v_hints_2868_);
lean_inc(v_a_2888_);
v___x_2901_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___boxed), 21, 14);
lean_closure_set(v___x_2901_, 0, v_a_2885_);
lean_closure_set(v___x_2901_, 1, v_a_2891_);
lean_closure_set(v___x_2901_, 2, v_a_2899_);
lean_closure_set(v___x_2901_, 3, v_a_2888_);
lean_closure_set(v___x_2901_, 4, v_a_2896_);
lean_closure_set(v___x_2901_, 5, v_hints_2868_);
lean_closure_set(v___x_2901_, 6, v_preDefs_2861_);
lean_closure_set(v___x_2901_, 7, v_a_2866_);
lean_closure_set(v___x_2901_, 8, v_fixedArgs_2872_);
lean_closure_set(v___x_2901_, 9, v_preDefs_2861_);
lean_closure_set(v___x_2901_, 10, v___x_2862_);
lean_closure_set(v___x_2901_, 11, v___x_2860_);
lean_closure_set(v___x_2901_, 12, lean_box(0));
lean_closure_set(v___x_2901_, 13, v___x_2900_);
v___x_2902_ = l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17___redArg(v___x_2901_, v___x_2867_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
if (lean_obj_tag(v___x_2902_) == 0)
{
lean_object* v_a_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v_a_2903_ = lean_ctor_get(v___x_2902_, 0);
lean_inc(v_a_2903_);
lean_dec_ref(v___x_2902_);
v___x_2904_ = lean_obj_once(&l_Lean_Elab_partialFixpoint___lam__0___closed__0, &l_Lean_Elab_partialFixpoint___lam__0___closed__0_once, _init_l_Lean_Elab_partialFixpoint___lam__0___closed__0);
v___x_2905_ = ((lean_object*)(l_Lean_Elab_partialFixpoint___lam__0___closed__1));
v___x_2906_ = l_Lean_Meta_PProdN_genMk___redArg(v___x_2904_, v___x_2905_, v_a_2903_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
if (lean_obj_tag(v___x_2906_) == 0)
{
lean_object* v_a_2907_; lean_object* v_snd_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_3029_; 
v_a_2907_ = lean_ctor_get(v___x_2906_, 0);
lean_inc(v_a_2907_);
lean_dec_ref(v___x_2906_);
v_snd_2908_ = lean_ctor_get(v_a_2907_, 1);
v_isSharedCheck_3029_ = !lean_is_exclusive(v_a_2907_);
if (v_isSharedCheck_3029_ == 0)
{
lean_object* v_unused_3030_; 
v_unused_3030_ = lean_ctor_get(v_a_2907_, 0);
lean_dec(v_unused_3030_);
v___x_2910_ = v_a_2907_;
v_isShared_2911_ = v_isSharedCheck_3029_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_snd_2908_);
lean_dec(v_a_2907_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_3029_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2912_; 
lean_inc(v_a_2888_);
v___x_2912_ = l_Lean_Meta_mkFixOfMonFun(v_a_2888_, v_a_2893_, v_snd_2908_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_object* v_a_2913_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; uint8_t v___y_2994_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v_options_3009_; uint8_t v_hasTrace_3010_; 
v_a_2913_ = lean_ctor_get(v___x_2912_, 0);
lean_inc(v_a_2913_);
lean_dec_ref(v___x_2912_);
v_options_3009_ = lean_ctor_get(v___y_2877_, 2);
v_hasTrace_3010_ = lean_ctor_get_uint8(v_options_3009_, sizeof(void*)*1);
if (v_hasTrace_3010_ == 0)
{
lean_del_object(v___x_2910_);
v___y_3000_ = v___y_2873_;
v___y_3001_ = v___y_2874_;
v___y_3002_ = v___y_2875_;
v___y_3003_ = v___y_2876_;
v___y_3004_ = v___y_2877_;
v___y_3005_ = v___y_2878_;
goto v___jp_2999_;
}
else
{
lean_object* v_inheritedTraceOptions_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; uint8_t v___x_3014_; 
v_inheritedTraceOptions_3011_ = lean_ctor_get(v___y_2877_, 13);
v___x_3012_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7));
v___x_3013_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10);
v___x_3014_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3011_, v_options_3009_, v___x_3013_);
if (v___x_3014_ == 0)
{
lean_del_object(v___x_2910_);
v___y_3000_ = v___y_2873_;
v___y_3001_ = v___y_2874_;
v___y_3002_ = v___y_2875_;
v___y_3003_ = v___y_2876_;
v___y_3004_ = v___y_2877_;
v___y_3005_ = v___y_2878_;
goto v___jp_2999_;
}
else
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3018_; 
v___x_3015_ = lean_obj_once(&l_Lean_Elab_partialFixpoint___lam__0___closed__5, &l_Lean_Elab_partialFixpoint___lam__0___closed__5_once, _init_l_Lean_Elab_partialFixpoint___lam__0___closed__5);
lean_inc(v_a_2913_);
v___x_3016_ = l_Lean_MessageData_ofExpr(v_a_2913_);
if (v_isShared_2911_ == 0)
{
lean_ctor_set_tag(v___x_2910_, 7);
lean_ctor_set(v___x_2910_, 1, v___x_3016_);
lean_ctor_set(v___x_2910_, 0, v___x_3015_);
v___x_3018_ = v___x_2910_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v___x_3015_);
lean_ctor_set(v_reuseFailAlloc_3020_, 1, v___x_3016_);
v___x_3018_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
lean_object* v___x_3019_; 
v___x_3019_ = l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg(v___x_3012_, v___x_3018_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_dec_ref(v___x_3019_);
v___y_3000_ = v___y_2873_;
v___y_3001_ = v___y_2874_;
v___y_3002_ = v___y_2875_;
v___y_3003_ = v___y_2876_;
v___y_3004_ = v___y_2877_;
v___y_3005_ = v___y_2878_;
goto v___jp_2999_;
}
else
{
lean_dec(v_a_2913_);
lean_dec_ref(v___x_2900_);
lean_dec(v_a_2888_);
lean_dec_ref(v_fixedArgs_2872_);
lean_dec_ref(v_docCtx_2870_);
lean_dec_ref(v___x_2869_);
lean_dec_ref(v_hints_2868_);
lean_dec_ref(v_a_2866_);
lean_dec(v___x_2862_);
lean_dec_ref(v_preDefs_2861_);
lean_dec(v___x_2860_);
lean_dec_ref(v_perms_2859_);
return v___x_3019_;
}
}
}
}
v___jp_2914_:
{
uint8_t v___x_2922_; uint8_t v___x_2923_; lean_object* v___x_2924_; 
v___x_2922_ = 0;
v___x_2923_ = 1;
lean_inc(v_a_2888_);
v___x_2924_ = l_Lean_Meta_mkForallFVars(v_fixedArgs_2872_, v_a_2888_, v___x_2922_, v___x_2867_, v___x_2867_, v___x_2923_, v___y_2917_, v___y_2918_, v___y_2920_, v___y_2916_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v_a_2925_; lean_object* v___x_2926_; 
v_a_2925_ = lean_ctor_get(v___x_2924_, 0);
lean_inc(v_a_2925_);
lean_dec_ref(v___x_2924_);
v___x_2926_ = l_Lean_Meta_mkLambdaFVars(v_fixedArgs_2872_, v_a_2913_, v___x_2922_, v___x_2867_, v___x_2922_, v___x_2867_, v___x_2923_, v___y_2917_, v___y_2918_, v___y_2920_, v___y_2916_);
lean_dec_ref(v_fixedArgs_2872_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v_a_2927_; lean_object* v_ref_2928_; uint8_t v_kind_2929_; lean_object* v_levelParams_2930_; lean_object* v_modifiers_2931_; lean_object* v_binders_2932_; lean_object* v_numSectionVars_2933_; lean_object* v_termination_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2967_; 
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
lean_inc(v_a_2927_);
lean_dec_ref(v___x_2926_);
v_ref_2928_ = lean_ctor_get(v___x_2869_, 0);
v_kind_2929_ = lean_ctor_get_uint8(v___x_2869_, sizeof(void*)*9);
v_levelParams_2930_ = lean_ctor_get(v___x_2869_, 1);
v_modifiers_2931_ = lean_ctor_get(v___x_2869_, 2);
v_binders_2932_ = lean_ctor_get(v___x_2869_, 4);
v_numSectionVars_2933_ = lean_ctor_get(v___x_2869_, 5);
v_termination_2934_ = lean_ctor_get(v___x_2869_, 8);
v_isSharedCheck_2967_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2967_ == 0)
{
lean_object* v_unused_2968_; lean_object* v_unused_2969_; lean_object* v_unused_2970_; 
v_unused_2968_ = lean_ctor_get(v___x_2869_, 7);
lean_dec(v_unused_2968_);
v_unused_2969_ = lean_ctor_get(v___x_2869_, 6);
lean_dec(v_unused_2969_);
v_unused_2970_ = lean_ctor_get(v___x_2869_, 3);
lean_dec(v_unused_2970_);
v___x_2936_ = v___x_2869_;
v_isShared_2937_ = v_isSharedCheck_2967_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_termination_2934_);
lean_inc(v_numSectionVars_2933_);
lean_inc(v_binders_2932_);
lean_inc(v_modifiers_2931_);
lean_inc(v_levelParams_2930_);
lean_inc(v_ref_2928_);
lean_dec(v___x_2869_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2967_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2938_; 
lean_inc(v___x_2862_);
lean_inc(v___y_2921_);
lean_inc(v_levelParams_2930_);
v___x_2938_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg(v_perms_2859_, v_levelParams_2930_, v___y_2921_, v___x_2862_, v_a_2888_, v_preDefs_2861_, v___x_2862_, v___x_2860_, v___x_2900_, v___y_2919_, v___y_2915_, v___y_2917_, v___y_2918_, v___y_2920_, v___y_2916_);
lean_dec_ref(v_perms_2859_);
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_object* v_a_2939_; lean_object* v___x_2941_; 
v_a_2939_ = lean_ctor_get(v___x_2938_, 0);
lean_inc(v_a_2939_);
lean_dec_ref(v___x_2938_);
lean_inc(v___y_2921_);
if (v_isShared_2937_ == 0)
{
lean_ctor_set(v___x_2936_, 7, v_a_2927_);
lean_ctor_set(v___x_2936_, 6, v_a_2925_);
lean_ctor_set(v___x_2936_, 3, v___y_2921_);
v___x_2941_ = v___x_2936_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_ref_2928_);
lean_ctor_set(v_reuseFailAlloc_2958_, 1, v_levelParams_2930_);
lean_ctor_set(v_reuseFailAlloc_2958_, 2, v_modifiers_2931_);
lean_ctor_set(v_reuseFailAlloc_2958_, 3, v___y_2921_);
lean_ctor_set(v_reuseFailAlloc_2958_, 4, v_binders_2932_);
lean_ctor_set(v_reuseFailAlloc_2958_, 5, v_numSectionVars_2933_);
lean_ctor_set(v_reuseFailAlloc_2958_, 6, v_a_2925_);
lean_ctor_set(v_reuseFailAlloc_2958_, 7, v_a_2927_);
lean_ctor_set(v_reuseFailAlloc_2958_, 8, v_termination_2934_);
lean_ctor_set_uint8(v_reuseFailAlloc_2958_, sizeof(void*)*9, v_kind_2929_);
v___x_2941_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
lean_object* v___x_2942_; 
lean_inc_ref(v_preDefs_2861_);
lean_inc_ref(v_docCtx_2870_);
v___x_2942_ = l_Lean_Elab_Mutual_addPreDefsFromUnary(v_docCtx_2870_, v_preDefs_2861_, v_a_2939_, v___x_2941_, v___x_2867_, v___y_2919_, v___y_2915_, v___y_2917_, v___y_2918_, v___y_2920_, v___y_2916_);
lean_dec(v_a_2939_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v___x_2943_; 
lean_dec_ref(v___x_2942_);
lean_inc_ref(v_preDefs_2861_);
v___x_2943_ = l_Lean_Elab_addAndCompilePartialRec(v_docCtx_2870_, v_preDefs_2861_, v___y_2919_, v___y_2915_, v___y_2917_, v___y_2918_, v___y_2920_, v___y_2916_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v___x_2944_; 
lean_dec_ref(v___x_2943_);
v___x_2944_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__22___redArg(v_sz_2871_, v___x_2864_, v_preDefs_2861_, v___y_2917_, v___y_2918_, v___y_2920_, v___y_2916_);
if (lean_obj_tag(v___x_2944_) == 0)
{
lean_object* v_a_2945_; size_t v_sz_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
lean_inc_n(v_a_2945_, 2);
lean_dec_ref(v___x_2944_);
v_sz_2946_ = lean_array_size(v_hints_2868_);
v___x_2947_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__23(v_sz_2946_, v___x_2864_, v_hints_2868_);
v___x_2948_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo(v_a_2945_, v___y_2921_, v_a_2866_, v___x_2947_, v___y_2917_, v___y_2918_, v___y_2920_, v___y_2916_);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_object* v___x_2949_; 
lean_dec_ref(v___x_2948_);
v___x_2949_ = l_Lean_Elab_Mutual_addPreDefAttributes(v_a_2945_, v___y_2919_, v___y_2915_, v___y_2917_, v___y_2918_, v___y_2920_, v___y_2916_);
return v___x_2949_;
}
else
{
lean_dec(v_a_2945_);
return v___x_2948_;
}
}
else
{
lean_object* v_a_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2957_; 
lean_dec(v___y_2921_);
lean_dec_ref(v_hints_2868_);
lean_dec_ref(v_a_2866_);
v_a_2950_ = lean_ctor_get(v___x_2944_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2952_ = v___x_2944_;
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_a_2950_);
lean_dec(v___x_2944_);
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
else
{
lean_dec(v___y_2921_);
lean_dec_ref(v_hints_2868_);
lean_dec_ref(v_a_2866_);
lean_dec_ref(v_preDefs_2861_);
return v___x_2943_;
}
}
else
{
lean_dec(v___y_2921_);
lean_dec_ref(v_docCtx_2870_);
lean_dec_ref(v_hints_2868_);
lean_dec_ref(v_a_2866_);
lean_dec_ref(v_preDefs_2861_);
return v___x_2942_;
}
}
}
else
{
lean_object* v_a_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2966_; 
lean_del_object(v___x_2936_);
lean_dec_ref(v_termination_2934_);
lean_dec(v_numSectionVars_2933_);
lean_dec(v_binders_2932_);
lean_dec_ref(v_modifiers_2931_);
lean_dec(v_levelParams_2930_);
lean_dec(v_ref_2928_);
lean_dec(v_a_2927_);
lean_dec(v_a_2925_);
lean_dec(v___y_2921_);
lean_dec_ref(v_docCtx_2870_);
lean_dec_ref(v_hints_2868_);
lean_dec_ref(v_a_2866_);
lean_dec_ref(v_preDefs_2861_);
v_a_2959_ = lean_ctor_get(v___x_2938_, 0);
v_isSharedCheck_2966_ = !lean_is_exclusive(v___x_2938_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2961_ = v___x_2938_;
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_a_2959_);
lean_dec(v___x_2938_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2964_; 
if (v_isShared_2962_ == 0)
{
v___x_2964_ = v___x_2961_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_a_2959_);
v___x_2964_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
return v___x_2964_;
}
}
}
}
}
else
{
lean_object* v_a_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2978_; 
lean_dec(v_a_2925_);
lean_dec(v___y_2921_);
lean_dec_ref(v___x_2900_);
lean_dec(v_a_2888_);
lean_dec_ref(v_docCtx_2870_);
lean_dec_ref(v___x_2869_);
lean_dec_ref(v_hints_2868_);
lean_dec_ref(v_a_2866_);
lean_dec(v___x_2862_);
lean_dec_ref(v_preDefs_2861_);
lean_dec(v___x_2860_);
lean_dec_ref(v_perms_2859_);
v_a_2971_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2973_ = v___x_2926_;
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_a_2971_);
lean_dec(v___x_2926_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2976_; 
if (v_isShared_2974_ == 0)
{
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
return v___x_2976_;
}
}
}
}
else
{
lean_object* v_a_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2986_; 
lean_dec(v___y_2921_);
lean_dec(v_a_2913_);
lean_dec_ref(v___x_2900_);
lean_dec(v_a_2888_);
lean_dec_ref(v_fixedArgs_2872_);
lean_dec_ref(v_docCtx_2870_);
lean_dec_ref(v___x_2869_);
lean_dec_ref(v_hints_2868_);
lean_dec_ref(v_a_2866_);
lean_dec(v___x_2862_);
lean_dec_ref(v_preDefs_2861_);
lean_dec(v___x_2860_);
lean_dec_ref(v_perms_2859_);
v_a_2979_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2981_ = v___x_2924_;
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_a_2979_);
lean_dec(v___x_2924_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2984_; 
if (v_isShared_2982_ == 0)
{
v___x_2984_ = v___x_2981_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_a_2979_);
v___x_2984_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
return v___x_2984_;
}
}
}
}
v___jp_2987_:
{
if (v___y_2994_ == 0)
{
lean_object* v_declName_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
v_declName_2995_ = lean_ctor_get(v___x_2869_, 3);
v___x_2996_ = ((lean_object*)(l_Lean_Elab_partialFixpoint___lam__0___closed__3));
lean_inc(v_declName_2995_);
v___x_2997_ = l_Lean_Name_append(v_declName_2995_, v___x_2996_);
v___y_2915_ = v___y_2988_;
v___y_2916_ = v___y_2989_;
v___y_2917_ = v___y_2990_;
v___y_2918_ = v___y_2991_;
v___y_2919_ = v___y_2993_;
v___y_2920_ = v___y_2992_;
v___y_2921_ = v___x_2997_;
goto v___jp_2914_;
}
else
{
lean_object* v_declName_2998_; 
v_declName_2998_ = lean_ctor_get(v___x_2869_, 3);
lean_inc(v_declName_2998_);
v___y_2915_ = v___y_2988_;
v___y_2916_ = v___y_2989_;
v___y_2917_ = v___y_2990_;
v___y_2918_ = v___y_2991_;
v___y_2919_ = v___y_2993_;
v___y_2920_ = v___y_2992_;
v___y_2921_ = v_declName_2998_;
goto v___jp_2914_;
}
}
v___jp_2999_:
{
lean_object* v___x_3006_; uint8_t v___x_3007_; 
v___x_3006_ = lean_unsigned_to_nat(1u);
v___x_3007_ = lean_nat_dec_eq(v___x_2862_, v___x_3006_);
if (v___x_3007_ == 0)
{
v___y_2988_ = v___y_3001_;
v___y_2989_ = v___y_3005_;
v___y_2990_ = v___y_3002_;
v___y_2991_ = v___y_3003_;
v___y_2992_ = v___y_3004_;
v___y_2993_ = v___y_3000_;
v___y_2994_ = v___x_3007_;
goto v___jp_2987_;
}
else
{
uint8_t v___x_3008_; 
lean_inc_ref(v_a_2866_);
v___x_3008_ = l_Lean_Elab_FixedParamPerms_fixedArePrefix(v_a_2866_);
v___y_2988_ = v___y_3001_;
v___y_2989_ = v___y_3005_;
v___y_2990_ = v___y_3002_;
v___y_2991_ = v___y_3003_;
v___y_2992_ = v___y_3004_;
v___y_2993_ = v___y_3000_;
v___y_2994_ = v___x_3008_;
goto v___jp_2987_;
}
}
}
else
{
lean_object* v_a_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3028_; 
lean_del_object(v___x_2910_);
lean_dec_ref(v___x_2900_);
lean_dec(v_a_2888_);
lean_dec_ref(v_fixedArgs_2872_);
lean_dec_ref(v_docCtx_2870_);
lean_dec_ref(v___x_2869_);
lean_dec_ref(v_hints_2868_);
lean_dec_ref(v_a_2866_);
lean_dec(v___x_2862_);
lean_dec_ref(v_preDefs_2861_);
lean_dec(v___x_2860_);
lean_dec_ref(v_perms_2859_);
v_a_3021_ = lean_ctor_get(v___x_2912_, 0);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3023_ = v___x_2912_;
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_a_3021_);
lean_dec(v___x_2912_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v___x_3026_; 
if (v_isShared_3024_ == 0)
{
v___x_3026_ = v___x_3023_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_a_3021_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
}
}
}
else
{
lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3038_; 
lean_dec_ref(v___x_2900_);
lean_dec(v_a_2893_);
lean_dec(v_a_2888_);
lean_dec_ref(v_fixedArgs_2872_);
lean_dec_ref(v_docCtx_2870_);
lean_dec_ref(v___x_2869_);
lean_dec_ref(v_hints_2868_);
lean_dec_ref(v_a_2866_);
lean_dec(v___x_2862_);
lean_dec_ref(v_preDefs_2861_);
lean_dec(v___x_2860_);
lean_dec_ref(v_perms_2859_);
v_a_3031_ = lean_ctor_get(v___x_2906_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3033_ = v___x_2906_;
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v___x_2906_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3036_; 
if (v_isShared_3034_ == 0)
{
v___x_3036_ = v___x_3033_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_a_3031_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
}
}
else
{
lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3046_; 
lean_dec_ref(v___x_2900_);
lean_dec(v_a_2893_);
lean_dec(v_a_2888_);
lean_dec_ref(v_fixedArgs_2872_);
lean_dec_ref(v_docCtx_2870_);
lean_dec_ref(v___x_2869_);
lean_dec_ref(v_hints_2868_);
lean_dec_ref(v_a_2866_);
lean_dec(v___x_2862_);
lean_dec_ref(v_preDefs_2861_);
lean_dec(v___x_2860_);
lean_dec_ref(v_perms_2859_);
v_a_3039_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3041_ = v___x_2902_;
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_dec(v___x_2902_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3044_; 
if (v_isShared_3042_ == 0)
{
v___x_3044_ = v___x_3041_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_a_3039_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
return v___x_3044_;
}
}
}
}
else
{
lean_object* v_a_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3054_; 
lean_dec(v_a_2896_);
lean_dec(v_a_2893_);
lean_dec(v_a_2891_);
lean_dec(v_a_2888_);
lean_dec(v_a_2885_);
lean_dec_ref(v_fixedArgs_2872_);
lean_dec_ref(v_docCtx_2870_);
lean_dec_ref(v___x_2869_);
lean_dec_ref(v_hints_2868_);
lean_dec_ref(v_a_2866_);
lean_dec(v___x_2862_);
lean_dec_ref(v_preDefs_2861_);
lean_dec(v___x_2860_);
lean_dec_ref(v_perms_2859_);
v_a_3047_ = lean_ctor_get(v___x_2898_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3049_ = v___x_2898_;
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_a_3047_);
lean_dec(v___x_2898_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___x_3052_; 
if (v_isShared_3050_ == 0)
{
v___x_3052_ = v___x_3049_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_a_3047_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
}
else
{
lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3062_; 
lean_dec(v_a_2893_);
lean_dec(v_a_2891_);
lean_dec(v_a_2888_);
lean_dec(v_a_2885_);
lean_dec_ref(v_fixedArgs_2872_);
lean_dec_ref(v_docCtx_2870_);
lean_dec_ref(v___x_2869_);
lean_dec_ref(v_hints_2868_);
lean_dec_ref(v_a_2866_);
lean_dec_ref(v___x_2865_);
lean_dec_ref(v___x_2863_);
lean_dec(v___x_2862_);
lean_dec_ref(v_preDefs_2861_);
lean_dec(v___x_2860_);
lean_dec_ref(v_perms_2859_);
v_a_3055_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3057_ = v___x_2895_;
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_dec(v___x_2895_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3060_; 
if (v_isShared_3058_ == 0)
{
v___x_3060_ = v___x_3057_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3055_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
}
else
{
lean_object* v_a_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3070_; 
lean_dec(v_a_2891_);
lean_dec(v_a_2888_);
lean_dec(v_a_2885_);
lean_dec_ref(v_fixedArgs_2872_);
lean_dec_ref(v_docCtx_2870_);
lean_dec_ref(v___x_2869_);
lean_dec_ref(v_hints_2868_);
lean_dec_ref(v_a_2866_);
lean_dec_ref(v___x_2865_);
lean_dec_ref(v___x_2863_);
lean_dec(v___x_2862_);
lean_dec_ref(v_preDefs_2861_);
lean_dec(v___x_2860_);
lean_dec_ref(v_perms_2859_);
v_a_3063_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_3065_ = v___x_2892_;
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_a_3063_);
lean_dec(v___x_2892_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3068_; 
if (v_isShared_3066_ == 0)
{
v___x_3068_ = v___x_3065_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_a_3063_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
}
}
else
{
lean_object* v_a_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3078_; 
lean_dec(v_a_2888_);
lean_dec(v_a_2885_);
lean_dec_ref(v_fixedArgs_2872_);
lean_dec_ref(v_docCtx_2870_);
lean_dec_ref(v___x_2869_);
lean_dec_ref(v_hints_2868_);
lean_dec_ref(v_a_2866_);
lean_dec_ref(v___x_2865_);
lean_dec_ref(v___x_2863_);
lean_dec(v___x_2862_);
lean_dec_ref(v_preDefs_2861_);
lean_dec(v___x_2860_);
lean_dec_ref(v_perms_2859_);
v_a_3071_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3073_ = v___x_2890_;
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_a_3071_);
lean_dec(v___x_2890_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v___x_3076_; 
if (v_isShared_3074_ == 0)
{
v___x_3076_ = v___x_3073_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_a_3071_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
}
}
else
{
lean_object* v_a_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3086_; 
lean_dec(v_a_2885_);
lean_dec(v_a_2883_);
lean_dec_ref(v_fixedArgs_2872_);
lean_dec_ref(v_docCtx_2870_);
lean_dec_ref(v___x_2869_);
lean_dec_ref(v_hints_2868_);
lean_dec_ref(v_a_2866_);
lean_dec_ref(v___x_2865_);
lean_dec_ref(v___x_2863_);
lean_dec(v___x_2862_);
lean_dec_ref(v_preDefs_2861_);
lean_dec(v___x_2860_);
lean_dec_ref(v_perms_2859_);
v_a_3079_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3081_ = v___x_2887_;
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_a_3079_);
lean_dec(v___x_2887_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3084_; 
if (v_isShared_3082_ == 0)
{
v___x_3084_ = v___x_3081_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_a_3079_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
}
}
else
{
lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3094_; 
lean_dec(v_a_2883_);
lean_dec_ref(v_fixedArgs_2872_);
lean_dec_ref(v_docCtx_2870_);
lean_dec_ref(v___x_2869_);
lean_dec_ref(v_hints_2868_);
lean_dec_ref(v_a_2866_);
lean_dec_ref(v___x_2865_);
lean_dec_ref(v___x_2863_);
lean_dec(v___x_2862_);
lean_dec_ref(v_preDefs_2861_);
lean_dec(v___x_2860_);
lean_dec_ref(v_perms_2859_);
v_a_3087_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3089_ = v___x_2884_;
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v___x_2884_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3092_; 
if (v_isShared_3090_ == 0)
{
v___x_3092_ = v___x_3089_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_a_3087_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
}
else
{
lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3102_; 
lean_dec_ref(v_fixedArgs_2872_);
lean_dec_ref(v_docCtx_2870_);
lean_dec_ref(v___x_2869_);
lean_dec_ref(v_hints_2868_);
lean_dec_ref(v_a_2866_);
lean_dec_ref(v___x_2865_);
lean_dec_ref(v___x_2863_);
lean_dec(v___x_2862_);
lean_dec_ref(v_preDefs_2861_);
lean_dec(v___x_2860_);
lean_dec_ref(v_perms_2859_);
v_a_3095_ = lean_ctor_get(v___x_2882_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3097_ = v___x_2882_;
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v___x_2882_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3100_; 
if (v_isShared_3098_ == 0)
{
v___x_3100_ = v___x_3097_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_a_3095_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_partialFixpoint___lam__0___boxed(lean_object** _args){
lean_object* v_a_3103_ = _args[0];
lean_object* v_perms_3104_ = _args[1];
lean_object* v___x_3105_ = _args[2];
lean_object* v_preDefs_3106_ = _args[3];
lean_object* v___x_3107_ = _args[4];
lean_object* v___x_3108_ = _args[5];
lean_object* v___x_3109_ = _args[6];
lean_object* v___x_3110_ = _args[7];
lean_object* v_a_3111_ = _args[8];
lean_object* v___x_3112_ = _args[9];
lean_object* v_hints_3113_ = _args[10];
lean_object* v___x_3114_ = _args[11];
lean_object* v_docCtx_3115_ = _args[12];
lean_object* v_sz_3116_ = _args[13];
lean_object* v_fixedArgs_3117_ = _args[14];
lean_object* v___y_3118_ = _args[15];
lean_object* v___y_3119_ = _args[16];
lean_object* v___y_3120_ = _args[17];
lean_object* v___y_3121_ = _args[18];
lean_object* v___y_3122_ = _args[19];
lean_object* v___y_3123_ = _args[20];
lean_object* v___y_3124_ = _args[21];
_start:
{
size_t v___x_58014__boxed_3125_; uint8_t v___x_58017__boxed_3126_; size_t v_sz_boxed_3127_; lean_object* v_res_3128_; 
v___x_58014__boxed_3125_ = lean_unbox_usize(v___x_3109_);
lean_dec(v___x_3109_);
v___x_58017__boxed_3126_ = lean_unbox(v___x_3112_);
v_sz_boxed_3127_ = lean_unbox_usize(v_sz_3116_);
lean_dec(v_sz_3116_);
v_res_3128_ = l_Lean_Elab_partialFixpoint___lam__0(v_a_3103_, v_perms_3104_, v___x_3105_, v_preDefs_3106_, v___x_3107_, v___x_3108_, v___x_58014__boxed_3125_, v___x_3110_, v_a_3111_, v___x_58017__boxed_3126_, v_hints_3113_, v___x_3114_, v_docCtx_3115_, v_sz_boxed_3127_, v_fixedArgs_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_);
lean_dec(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec_ref(v_a_3103_);
return v_res_3128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0_spec__0(lean_object* v_as_3129_, size_t v_i_3130_, size_t v_stop_3131_, lean_object* v_b_3132_){
_start:
{
lean_object* v___y_3134_; uint8_t v___x_3138_; 
v___x_3138_ = lean_usize_dec_eq(v_i_3130_, v_stop_3131_);
if (v___x_3138_ == 0)
{
lean_object* v___x_3139_; lean_object* v_termination_3140_; lean_object* v_partialFixpoint_x3f_3141_; 
v___x_3139_ = lean_array_uget_borrowed(v_as_3129_, v_i_3130_);
v_termination_3140_ = lean_ctor_get(v___x_3139_, 8);
v_partialFixpoint_x3f_3141_ = lean_ctor_get(v_termination_3140_, 3);
if (lean_obj_tag(v_partialFixpoint_x3f_3141_) == 0)
{
v___y_3134_ = v_b_3132_;
goto v___jp_3133_;
}
else
{
lean_object* v_val_3142_; lean_object* v___x_3143_; 
v_val_3142_ = lean_ctor_get(v_partialFixpoint_x3f_3141_, 0);
lean_inc(v_val_3142_);
v___x_3143_ = lean_array_push(v_b_3132_, v_val_3142_);
v___y_3134_ = v___x_3143_;
goto v___jp_3133_;
}
}
else
{
return v_b_3132_;
}
v___jp_3133_:
{
size_t v___x_3135_; size_t v___x_3136_; 
v___x_3135_ = ((size_t)1ULL);
v___x_3136_ = lean_usize_add(v_i_3130_, v___x_3135_);
v_i_3130_ = v___x_3136_;
v_b_3132_ = v___y_3134_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0_spec__0___boxed(lean_object* v_as_3144_, lean_object* v_i_3145_, lean_object* v_stop_3146_, lean_object* v_b_3147_){
_start:
{
size_t v_i_boxed_3148_; size_t v_stop_boxed_3149_; lean_object* v_res_3150_; 
v_i_boxed_3148_ = lean_unbox_usize(v_i_3145_);
lean_dec(v_i_3145_);
v_stop_boxed_3149_ = lean_unbox_usize(v_stop_3146_);
lean_dec(v_stop_3146_);
v_res_3150_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0_spec__0(v_as_3144_, v_i_boxed_3148_, v_stop_boxed_3149_, v_b_3147_);
lean_dec_ref(v_as_3144_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0(lean_object* v_as_3153_, lean_object* v_start_3154_, lean_object* v_stop_3155_){
_start:
{
lean_object* v___x_3156_; uint8_t v___x_3157_; 
v___x_3156_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0___closed__0));
v___x_3157_ = lean_nat_dec_lt(v_start_3154_, v_stop_3155_);
if (v___x_3157_ == 0)
{
return v___x_3156_;
}
else
{
lean_object* v___x_3158_; uint8_t v___x_3159_; 
v___x_3158_ = lean_array_get_size(v_as_3153_);
v___x_3159_ = lean_nat_dec_le(v_stop_3155_, v___x_3158_);
if (v___x_3159_ == 0)
{
uint8_t v___x_3160_; 
v___x_3160_ = lean_nat_dec_lt(v_start_3154_, v___x_3158_);
if (v___x_3160_ == 0)
{
return v___x_3156_;
}
else
{
size_t v___x_3161_; size_t v___x_3162_; lean_object* v___x_3163_; 
v___x_3161_ = lean_usize_of_nat(v_start_3154_);
v___x_3162_ = lean_usize_of_nat(v___x_3158_);
v___x_3163_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0_spec__0(v_as_3153_, v___x_3161_, v___x_3162_, v___x_3156_);
return v___x_3163_;
}
}
else
{
size_t v___x_3164_; size_t v___x_3165_; lean_object* v___x_3166_; 
v___x_3164_ = lean_usize_of_nat(v_start_3154_);
v___x_3165_ = lean_usize_of_nat(v_stop_3155_);
v___x_3166_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0_spec__0(v_as_3153_, v___x_3164_, v___x_3165_, v___x_3156_);
return v___x_3166_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0___boxed(lean_object* v_as_3167_, lean_object* v_start_3168_, lean_object* v_stop_3169_){
_start:
{
lean_object* v_res_3170_; 
v_res_3170_ = l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0(v_as_3167_, v_start_3168_, v_stop_3169_);
lean_dec(v_stop_3169_);
lean_dec(v_start_3168_);
lean_dec_ref(v_as_3167_);
return v_res_3170_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27_spec__33(uint8_t v___x_3171_, lean_object* v_as_3172_, size_t v_i_3173_, size_t v_stop_3174_){
_start:
{
uint8_t v___x_3175_; 
v___x_3175_ = lean_usize_dec_eq(v_i_3173_, v_stop_3174_);
if (v___x_3175_ == 0)
{
lean_object* v___x_3176_; uint8_t v_fixpointType_3177_; uint8_t v___x_3178_; uint8_t v___y_3180_; uint8_t v___x_3184_; 
v___x_3176_ = lean_array_uget_borrowed(v_as_3172_, v_i_3173_);
v_fixpointType_3177_ = lean_ctor_get_uint8(v___x_3176_, sizeof(void*)*2);
v___x_3178_ = 1;
v___x_3184_ = l_Lean_Elab_isLatticeTheoretic(v_fixpointType_3177_);
if (v___x_3184_ == 0)
{
v___y_3180_ = v___x_3171_;
goto v___jp_3179_;
}
else
{
v___y_3180_ = v___x_3175_;
goto v___jp_3179_;
}
v___jp_3179_:
{
if (v___y_3180_ == 0)
{
size_t v___x_3181_; size_t v___x_3182_; 
v___x_3181_ = ((size_t)1ULL);
v___x_3182_ = lean_usize_add(v_i_3173_, v___x_3181_);
v_i_3173_ = v___x_3182_;
goto _start;
}
else
{
return v___x_3178_;
}
}
}
else
{
uint8_t v___x_3185_; 
v___x_3185_ = 0;
return v___x_3185_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27_spec__33___boxed(lean_object* v___x_3186_, lean_object* v_as_3187_, lean_object* v_i_3188_, lean_object* v_stop_3189_){
_start:
{
uint8_t v___x_58540__boxed_3190_; size_t v_i_boxed_3191_; size_t v_stop_boxed_3192_; uint8_t v_res_3193_; lean_object* v_r_3194_; 
v___x_58540__boxed_3190_ = lean_unbox(v___x_3186_);
v_i_boxed_3191_ = lean_unbox_usize(v_i_3188_);
lean_dec(v_i_3188_);
v_stop_boxed_3192_ = lean_unbox_usize(v_stop_3189_);
lean_dec(v_stop_3189_);
v_res_3193_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27_spec__33(v___x_58540__boxed_3190_, v_as_3187_, v_i_boxed_3191_, v_stop_boxed_3192_);
lean_dec_ref(v_as_3187_);
v_r_3194_ = lean_box(v_res_3193_);
return v_r_3194_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27(uint8_t v___x_3195_, lean_object* v_as_3196_, size_t v_i_3197_, size_t v_stop_3198_){
_start:
{
uint8_t v___x_3199_; 
v___x_3199_ = lean_usize_dec_eq(v_i_3197_, v_stop_3198_);
if (v___x_3199_ == 0)
{
lean_object* v___x_3200_; uint8_t v_fixpointType_3201_; uint8_t v___x_3202_; uint8_t v___y_3204_; uint8_t v___x_3208_; 
v___x_3200_ = lean_array_uget_borrowed(v_as_3196_, v_i_3197_);
v_fixpointType_3201_ = lean_ctor_get_uint8(v___x_3200_, sizeof(void*)*2);
v___x_3202_ = 1;
v___x_3208_ = l_Lean_Elab_isLatticeTheoretic(v_fixpointType_3201_);
if (v___x_3208_ == 0)
{
v___y_3204_ = v___x_3195_;
goto v___jp_3203_;
}
else
{
v___y_3204_ = v___x_3199_;
goto v___jp_3203_;
}
v___jp_3203_:
{
if (v___y_3204_ == 0)
{
size_t v___x_3205_; size_t v___x_3206_; uint8_t v___x_3207_; 
v___x_3205_ = ((size_t)1ULL);
v___x_3206_ = lean_usize_add(v_i_3197_, v___x_3205_);
v___x_3207_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27_spec__33(v___x_3195_, v_as_3196_, v___x_3206_, v_stop_3198_);
return v___x_3207_;
}
else
{
return v___x_3202_;
}
}
}
else
{
uint8_t v___x_3209_; 
v___x_3209_ = 0;
return v___x_3209_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27___boxed(lean_object* v___x_3210_, lean_object* v_as_3211_, lean_object* v_i_3212_, lean_object* v_stop_3213_){
_start:
{
uint8_t v___x_58563__boxed_3214_; size_t v_i_boxed_3215_; size_t v_stop_boxed_3216_; uint8_t v_res_3217_; lean_object* v_r_3218_; 
v___x_58563__boxed_3214_ = lean_unbox(v___x_3210_);
v_i_boxed_3215_ = lean_unbox_usize(v_i_3212_);
lean_dec(v_i_3212_);
v_stop_boxed_3216_ = lean_unbox_usize(v_stop_3213_);
lean_dec(v_stop_3213_);
v_res_3217_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27(v___x_58563__boxed_3214_, v_as_3211_, v_i_boxed_3215_, v_stop_boxed_3216_);
lean_dec_ref(v_as_3211_);
v_r_3218_ = lean_box(v_res_3217_);
return v_r_3218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__7(size_t v_sz_3219_, size_t v_i_3220_, lean_object* v_bs_3221_){
_start:
{
uint8_t v___x_3222_; 
v___x_3222_ = lean_usize_dec_lt(v_i_3220_, v_sz_3219_);
if (v___x_3222_ == 0)
{
return v_bs_3221_;
}
else
{
lean_object* v_v_3223_; lean_object* v_declName_3224_; lean_object* v___x_3225_; lean_object* v_bs_x27_3226_; size_t v___x_3227_; size_t v___x_3228_; lean_object* v___x_3229_; 
v_v_3223_ = lean_array_uget_borrowed(v_bs_3221_, v_i_3220_);
v_declName_3224_ = lean_ctor_get(v_v_3223_, 3);
lean_inc(v_declName_3224_);
v___x_3225_ = lean_unsigned_to_nat(0u);
v_bs_x27_3226_ = lean_array_uset(v_bs_3221_, v_i_3220_, v___x_3225_);
v___x_3227_ = ((size_t)1ULL);
v___x_3228_ = lean_usize_add(v_i_3220_, v___x_3227_);
v___x_3229_ = lean_array_uset(v_bs_x27_3226_, v_i_3220_, v_declName_3224_);
v_i_3220_ = v___x_3228_;
v_bs_3221_ = v___x_3229_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__7___boxed(lean_object* v_sz_3231_, lean_object* v_i_3232_, lean_object* v_bs_3233_){
_start:
{
size_t v_sz_boxed_3234_; size_t v_i_boxed_3235_; lean_object* v_res_3236_; 
v_sz_boxed_3234_ = lean_unbox_usize(v_sz_3231_);
lean_dec(v_sz_3231_);
v_i_boxed_3235_ = lean_unbox_usize(v_i_3232_);
lean_dec(v_i_3232_);
v_res_3236_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__7(v_sz_boxed_3234_, v_i_boxed_3235_, v_bs_3233_);
return v_res_3236_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3238_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__0));
v___x_3239_ = l_Lean_stringToMessageData(v___x_3238_);
return v___x_3239_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_3241_; lean_object* v___x_3242_; 
v___x_3241_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__2));
v___x_3242_ = l_Lean_stringToMessageData(v___x_3241_);
return v___x_3242_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__11(void){
_start:
{
lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
v___x_3255_ = lean_box(0);
v___x_3256_ = lean_unsigned_to_nat(2u);
v___x_3257_ = lean_mk_empty_array_with_capacity(v___x_3256_);
v___x_3258_ = lean_array_push(v___x_3257_, v___x_3255_);
return v___x_3258_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2(lean_object* v_declName_3261_, lean_object* v_type_3262_, lean_object* v_xs_3263_, lean_object* v___x_3264_, lean_object* v___x_3265_, lean_object* v_____r_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_){
_start:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3274_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__1, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__1_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__1);
v___x_3275_ = l_Lean_MessageData_ofName(v_declName_3261_);
v___x_3276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3274_);
lean_ctor_set(v___x_3276_, 1, v___x_3275_);
v___x_3277_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__3, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__3_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__3);
v___x_3278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3278_, 0, v___x_3276_);
lean_ctor_set(v___x_3278_, 1, v___x_3277_);
v___x_3279_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__4));
v___x_3280_ = l_Lean_Elab_mkInhabitantFor(v___x_3278_, v___x_3279_, v_type_3262_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_);
if (lean_obj_tag(v___x_3280_) == 0)
{
lean_object* v_a_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
v_a_3281_ = lean_ctor_get(v___x_3280_, 0);
lean_inc(v_a_3281_);
lean_dec_ref(v___x_3280_);
v___x_3282_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__7));
v___x_3283_ = l_Lean_mkAppN(v_a_3281_, v_xs_3263_);
v___x_3284_ = lean_unsigned_to_nat(1u);
v___x_3285_ = lean_mk_empty_array_with_capacity(v___x_3284_);
v___x_3286_ = lean_array_push(v___x_3285_, v___x_3283_);
v___x_3287_ = l_Lean_Meta_mkAppM(v___x_3282_, v___x_3286_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_);
if (lean_obj_tag(v___x_3287_) == 0)
{
lean_object* v_a_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3312_; 
v_a_3288_ = lean_ctor_get(v___x_3287_, 0);
v_isSharedCheck_3312_ = !lean_is_exclusive(v___x_3287_);
if (v_isSharedCheck_3312_ == 0)
{
v___x_3290_ = v___x_3287_;
v_isShared_3291_ = v_isSharedCheck_3312_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_a_3288_);
lean_dec(v___x_3287_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3312_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3292_; lean_object* v___x_3294_; 
v___x_3292_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__10));
if (v_isShared_3291_ == 0)
{
lean_ctor_set_tag(v___x_3290_, 1);
v___x_3294_ = v___x_3290_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v_a_3288_);
v___x_3294_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; 
v___x_3295_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__11, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__11_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__11);
v___x_3296_ = lean_array_push(v___x_3295_, v___x_3294_);
v___x_3297_ = l_Lean_Meta_mkAppOptM(v___x_3292_, v___x_3296_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_);
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_object* v_a_3298_; lean_object* v___x_3300_; uint8_t v_isShared_3301_; uint8_t v_isSharedCheck_3310_; 
v_a_3298_ = lean_ctor_get(v___x_3297_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3297_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3300_ = v___x_3297_;
v_isShared_3301_ = v_isSharedCheck_3310_;
goto v_resetjp_3299_;
}
else
{
lean_inc(v_a_3298_);
lean_dec(v___x_3297_);
v___x_3300_ = lean_box(0);
v_isShared_3301_ = v_isSharedCheck_3310_;
goto v_resetjp_3299_;
}
v_resetjp_3299_:
{
lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3306_; 
v___x_3302_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__12));
v___x_3303_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__13));
v___x_3304_ = l_Lean_Name_mkStr4(v___x_3264_, v___x_3265_, v___x_3302_, v___x_3303_);
if (v_isShared_3301_ == 0)
{
lean_ctor_set_tag(v___x_3300_, 1);
v___x_3306_ = v___x_3300_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_a_3298_);
v___x_3306_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
lean_object* v___x_3307_; lean_object* v___x_3308_; 
v___x_3307_ = lean_array_push(v___x_3295_, v___x_3306_);
v___x_3308_ = l_Lean_Meta_mkAppOptM(v___x_3304_, v___x_3307_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_);
return v___x_3308_;
}
}
}
else
{
lean_dec_ref(v___x_3265_);
lean_dec_ref(v___x_3264_);
return v___x_3297_;
}
}
}
}
else
{
lean_dec_ref(v___x_3265_);
lean_dec_ref(v___x_3264_);
return v___x_3287_;
}
}
else
{
lean_dec_ref(v___x_3265_);
lean_dec_ref(v___x_3264_);
return v___x_3280_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___boxed(lean_object* v_declName_3313_, lean_object* v_type_3314_, lean_object* v_xs_3315_, lean_object* v___x_3316_, lean_object* v___x_3317_, lean_object* v_____r_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_){
_start:
{
lean_object* v_res_3326_; 
v_res_3326_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2(v_declName_3313_, v_type_3314_, v_xs_3315_, v___x_3316_, v___x_3317_, v_____r_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
lean_dec(v___y_3324_);
lean_dec_ref(v___y_3323_);
lean_dec(v___y_3322_);
lean_dec_ref(v___y_3321_);
lean_dec(v___y_3320_);
lean_dec_ref(v___y_3319_);
lean_dec_ref(v_xs_3315_);
return v_res_3326_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__4(lean_object* v_a_3327_, lean_object* v_a_3328_){
_start:
{
if (lean_obj_tag(v_a_3327_) == 0)
{
lean_object* v___x_3329_; 
v___x_3329_ = l_List_reverse___redArg(v_a_3328_);
return v___x_3329_;
}
else
{
lean_object* v_head_3330_; lean_object* v_tail_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3340_; 
v_head_3330_ = lean_ctor_get(v_a_3327_, 0);
v_tail_3331_ = lean_ctor_get(v_a_3327_, 1);
v_isSharedCheck_3340_ = !lean_is_exclusive(v_a_3327_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3333_ = v_a_3327_;
v_isShared_3334_ = v_isSharedCheck_3340_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_tail_3331_);
lean_inc(v_head_3330_);
lean_dec(v_a_3327_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3340_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
lean_object* v___x_3335_; lean_object* v___x_3337_; 
v___x_3335_ = l_Lean_MessageData_ofExpr(v_head_3330_);
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 1, v_a_3328_);
lean_ctor_set(v___x_3333_, 0, v___x_3335_);
v___x_3337_ = v___x_3333_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v___x_3335_);
lean_ctor_set(v_reuseFailAlloc_3339_, 1, v_a_3328_);
v___x_3337_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
v_a_3327_ = v_tail_3331_;
v_a_3328_ = v___x_3337_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_3342_; lean_object* v___x_3343_; 
v___x_3342_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__0));
v___x_3343_ = l_Lean_stringToMessageData(v___x_3342_);
return v___x_3343_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__3(void){
_start:
{
lean_object* v___x_3345_; lean_object* v___x_3346_; 
v___x_3345_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__2));
v___x_3346_ = l_Lean_stringToMessageData(v___x_3345_);
return v___x_3346_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__7(void){
_start:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; 
v___x_3353_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__6));
v___x_3354_ = l_Lean_stringToMessageData(v___x_3353_);
return v___x_3354_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__9(void){
_start:
{
lean_object* v___x_3356_; lean_object* v___x_3357_; 
v___x_3356_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__8));
v___x_3357_ = l_Lean_stringToMessageData(v___x_3356_);
return v___x_3357_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__11(void){
_start:
{
lean_object* v___x_3359_; lean_object* v___x_3360_; 
v___x_3359_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__10));
v___x_3360_ = l_Lean_stringToMessageData(v___x_3359_);
return v___x_3360_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3(uint8_t v_isZero_3361_, lean_object* v_declName_3362_, lean_object* v_type_3363_, uint8_t v_fixpointType_3364_, lean_object* v___f_3365_, lean_object* v___f_3366_, lean_object* v_value_3367_, lean_object* v_xs_3368_, lean_object* v___body_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
lean_object* v_inst_3378_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v_options_3403_; lean_object* v_inheritedTraceOptions_3404_; uint8_t v_hasTrace_3405_; lean_object* v_cls_3406_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; uint8_t v___y_3416_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; 
v_options_3403_ = lean_ctor_get(v___y_3374_, 2);
v_inheritedTraceOptions_3404_ = lean_ctor_get(v___y_3374_, 13);
v_hasTrace_3405_ = lean_ctor_get_uint8(v_options_3403_, sizeof(void*)*1);
v_cls_3406_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7));
if (v_hasTrace_3405_ == 0)
{
lean_dec_ref(v___body_3369_);
lean_dec_ref(v_value_3367_);
v___y_3452_ = v___y_3370_;
v___y_3453_ = v___y_3371_;
v___y_3454_ = v___y_3372_;
v___y_3455_ = v___y_3373_;
v___y_3456_ = v___y_3374_;
v___y_3457_ = v___y_3375_;
goto v___jp_3451_;
}
else
{
lean_object* v___x_3477_; uint8_t v___x_3478_; 
v___x_3477_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10);
v___x_3478_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3404_, v_options_3403_, v___x_3477_);
if (v___x_3478_ == 0)
{
lean_dec_ref(v___body_3369_);
lean_dec_ref(v_value_3367_);
v___y_3452_ = v___y_3370_;
v___y_3453_ = v___y_3371_;
v___y_3454_ = v___y_3372_;
v___y_3455_ = v___y_3373_;
v___y_3456_ = v___y_3374_;
v___y_3457_ = v___y_3375_;
goto v___jp_3451_;
}
else
{
lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; 
v___x_3479_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__7, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__7_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__7);
v___x_3480_ = l_Lean_MessageData_ofExpr(v_value_3367_);
v___x_3481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3479_);
lean_ctor_set(v___x_3481_, 1, v___x_3480_);
v___x_3482_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__9, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__9_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__9);
v___x_3483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3481_);
lean_ctor_set(v___x_3483_, 1, v___x_3482_);
lean_inc_ref(v_xs_3368_);
v___x_3484_ = lean_array_to_list(v_xs_3368_);
v___x_3485_ = lean_box(0);
v___x_3486_ = l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__4(v___x_3484_, v___x_3485_);
v___x_3487_ = l_Lean_MessageData_ofList(v___x_3486_);
v___x_3488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3483_);
lean_ctor_set(v___x_3488_, 1, v___x_3487_);
v___x_3489_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__11, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__11_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__11);
v___x_3490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3488_);
lean_ctor_set(v___x_3490_, 1, v___x_3489_);
v___x_3491_ = l_Lean_MessageData_ofExpr(v___body_3369_);
v___x_3492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3492_, 0, v___x_3490_);
lean_ctor_set(v___x_3492_, 1, v___x_3491_);
v___x_3493_ = l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg(v_cls_3406_, v___x_3492_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_dec_ref(v___x_3493_);
v___y_3452_ = v___y_3370_;
v___y_3453_ = v___y_3371_;
v___y_3454_ = v___y_3372_;
v___y_3455_ = v___y_3373_;
v___y_3456_ = v___y_3374_;
v___y_3457_ = v___y_3375_;
goto v___jp_3451_;
}
else
{
lean_object* v_a_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3501_; 
lean_dec_ref(v_xs_3368_);
lean_dec_ref(v___f_3366_);
lean_dec_ref(v___f_3365_);
lean_dec_ref(v_type_3363_);
lean_dec(v_declName_3362_);
v_a_3494_ = lean_ctor_get(v___x_3493_, 0);
v_isSharedCheck_3501_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3496_ = v___x_3493_;
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_a_3494_);
lean_dec(v___x_3493_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3499_; 
if (v_isShared_3497_ == 0)
{
v___x_3499_ = v___x_3496_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v_a_3494_);
v___x_3499_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
return v___x_3499_;
}
}
}
}
}
v___jp_3377_:
{
uint8_t v___x_3383_; uint8_t v___x_3384_; lean_object* v___x_3385_; 
v___x_3383_ = 1;
v___x_3384_ = 1;
v___x_3385_ = l_Lean_Meta_mkLambdaFVars(v_xs_3368_, v_inst_3378_, v_isZero_3361_, v___x_3383_, v_isZero_3361_, v___x_3383_, v___x_3384_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_);
lean_dec_ref(v_xs_3368_);
return v___x_3385_;
}
v___jp_3386_:
{
if (lean_obj_tag(v___y_3391_) == 0)
{
lean_object* v_a_3392_; 
v_a_3392_ = lean_ctor_get(v___y_3391_, 0);
lean_inc(v_a_3392_);
lean_dec_ref(v___y_3391_);
v_inst_3378_ = v_a_3392_;
v___y_3379_ = v___y_3388_;
v___y_3380_ = v___y_3390_;
v___y_3381_ = v___y_3387_;
v___y_3382_ = v___y_3389_;
goto v___jp_3377_;
}
else
{
lean_dec_ref(v_xs_3368_);
return v___y_3391_;
}
}
v___jp_3393_:
{
lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3401_ = lean_box(0);
lean_inc(v___y_3396_);
lean_inc_ref(v___y_3394_);
lean_inc(v___y_3400_);
lean_inc_ref(v___y_3395_);
lean_inc(v___y_3399_);
lean_inc_ref(v___y_3397_);
v___x_3402_ = lean_apply_8(v___y_3398_, v___x_3401_, v___y_3397_, v___y_3399_, v___y_3395_, v___y_3400_, v___y_3394_, v___y_3396_, lean_box(0));
v___y_3387_ = v___y_3394_;
v___y_3388_ = v___y_3395_;
v___y_3389_ = v___y_3396_;
v___y_3390_ = v___y_3400_;
v___y_3391_ = v___x_3402_;
goto v___jp_3386_;
}
v___jp_3407_:
{
if (v___y_3416_ == 0)
{
lean_object* v_options_3417_; uint8_t v_hasTrace_3418_; 
lean_dec_ref(v___y_3411_);
v_options_3417_ = lean_ctor_get(v___y_3409_, 2);
v_hasTrace_3418_ = lean_ctor_get_uint8(v_options_3417_, sizeof(void*)*1);
if (v_hasTrace_3418_ == 0)
{
lean_dec(v_declName_3362_);
v___y_3394_ = v___y_3409_;
v___y_3395_ = v___y_3408_;
v___y_3396_ = v___y_3410_;
v___y_3397_ = v___y_3413_;
v___y_3398_ = v___y_3412_;
v___y_3399_ = v___y_3414_;
v___y_3400_ = v___y_3415_;
goto v___jp_3393_;
}
else
{
lean_object* v_inheritedTraceOptions_3419_; lean_object* v___x_3420_; uint8_t v___x_3421_; 
v_inheritedTraceOptions_3419_ = lean_ctor_get(v___y_3409_, 13);
v___x_3420_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10);
v___x_3421_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3419_, v_options_3417_, v___x_3420_);
if (v___x_3421_ == 0)
{
lean_dec(v_declName_3362_);
v___y_3394_ = v___y_3409_;
v___y_3395_ = v___y_3408_;
v___y_3396_ = v___y_3410_;
v___y_3397_ = v___y_3413_;
v___y_3398_ = v___y_3412_;
v___y_3399_ = v___y_3414_;
v___y_3400_ = v___y_3415_;
goto v___jp_3393_;
}
else
{
lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3422_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__1, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__1_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__1);
v___x_3423_ = l_Lean_MessageData_ofName(v_declName_3362_);
v___x_3424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3422_);
lean_ctor_set(v___x_3424_, 1, v___x_3423_);
v___x_3425_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__3, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__3_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__3);
v___x_3426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3424_);
lean_ctor_set(v___x_3426_, 1, v___x_3425_);
v___x_3427_ = l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg(v_cls_3406_, v___x_3426_, v___y_3408_, v___y_3415_, v___y_3409_, v___y_3410_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v_a_3428_; lean_object* v___x_3429_; 
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
lean_inc(v_a_3428_);
lean_dec_ref(v___x_3427_);
lean_inc(v___y_3410_);
lean_inc_ref(v___y_3409_);
lean_inc(v___y_3415_);
lean_inc_ref(v___y_3408_);
lean_inc(v___y_3414_);
lean_inc_ref(v___y_3413_);
v___x_3429_ = lean_apply_8(v___y_3412_, v_a_3428_, v___y_3413_, v___y_3414_, v___y_3408_, v___y_3415_, v___y_3409_, v___y_3410_, lean_box(0));
v___y_3387_ = v___y_3409_;
v___y_3388_ = v___y_3408_;
v___y_3389_ = v___y_3410_;
v___y_3390_ = v___y_3415_;
v___y_3391_ = v___x_3429_;
goto v___jp_3386_;
}
else
{
lean_object* v_a_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3437_; 
lean_dec_ref(v___y_3412_);
lean_dec_ref(v_xs_3368_);
v_a_3430_ = lean_ctor_get(v___x_3427_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3432_ = v___x_3427_;
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_a_3430_);
lean_dec(v___x_3427_);
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
}
else
{
lean_dec_ref(v___y_3412_);
lean_dec_ref(v_xs_3368_);
lean_dec(v_declName_3362_);
return v___y_3411_;
}
}
v___jp_3438_:
{
if (lean_obj_tag(v___y_3446_) == 0)
{
lean_object* v_a_3447_; 
lean_dec_ref(v___y_3443_);
lean_dec(v_declName_3362_);
v_a_3447_ = lean_ctor_get(v___y_3446_, 0);
lean_inc(v_a_3447_);
lean_dec_ref(v___y_3446_);
v_inst_3378_ = v_a_3447_;
v___y_3379_ = v___y_3440_;
v___y_3380_ = v___y_3445_;
v___y_3381_ = v___y_3439_;
v___y_3382_ = v___y_3441_;
goto v___jp_3377_;
}
else
{
lean_object* v_a_3448_; uint8_t v___x_3449_; 
v_a_3448_ = lean_ctor_get(v___y_3446_, 0);
v___x_3449_ = l_Lean_Exception_isInterrupt(v_a_3448_);
if (v___x_3449_ == 0)
{
uint8_t v___x_3450_; 
lean_inc(v_a_3448_);
v___x_3450_ = l_Lean_Exception_isRuntime(v_a_3448_);
v___y_3408_ = v___y_3440_;
v___y_3409_ = v___y_3439_;
v___y_3410_ = v___y_3441_;
v___y_3411_ = v___y_3446_;
v___y_3412_ = v___y_3443_;
v___y_3413_ = v___y_3442_;
v___y_3414_ = v___y_3444_;
v___y_3415_ = v___y_3445_;
v___y_3416_ = v___x_3450_;
goto v___jp_3407_;
}
else
{
v___y_3408_ = v___y_3440_;
v___y_3409_ = v___y_3439_;
v___y_3410_ = v___y_3441_;
v___y_3411_ = v___y_3446_;
v___y_3412_ = v___y_3443_;
v___y_3413_ = v___y_3442_;
v___y_3414_ = v___y_3444_;
v___y_3415_ = v___y_3445_;
v___y_3416_ = v___x_3449_;
goto v___jp_3407_;
}
}
}
v___jp_3451_:
{
lean_object* v___x_3458_; 
lean_inc_ref(v_type_3363_);
v___x_3458_ = l_Lean_Meta_instantiateForall(v_type_3363_, v_xs_3368_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
if (lean_obj_tag(v___x_3458_) == 0)
{
switch(v_fixpointType_3364_)
{
case 0:
{
lean_object* v_a_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___f_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; 
lean_dec_ref(v___f_3366_);
lean_dec_ref(v___f_3365_);
v_a_3459_ = lean_ctor_get(v___x_3458_, 0);
lean_inc(v_a_3459_);
lean_dec_ref(v___x_3458_);
v___x_3460_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__2));
v___x_3461_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__3));
lean_inc_ref(v_xs_3368_);
lean_inc(v_declName_3362_);
v___f_3462_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___boxed), 13, 5);
lean_closure_set(v___f_3462_, 0, v_declName_3362_);
lean_closure_set(v___f_3462_, 1, v_type_3363_);
lean_closure_set(v___f_3462_, 2, v_xs_3368_);
lean_closure_set(v___f_3462_, 3, v___x_3460_);
lean_closure_set(v___f_3462_, 4, v___x_3461_);
v___x_3463_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__5));
v___x_3464_ = lean_unsigned_to_nat(1u);
v___x_3465_ = lean_mk_empty_array_with_capacity(v___x_3464_);
v___x_3466_ = lean_array_push(v___x_3465_, v_a_3459_);
v___x_3467_ = l_Lean_Meta_mkAppM(v___x_3463_, v___x_3466_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
if (lean_obj_tag(v___x_3467_) == 0)
{
lean_object* v_a_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
v_a_3468_ = lean_ctor_get(v___x_3467_, 0);
lean_inc(v_a_3468_);
lean_dec_ref(v___x_3467_);
v___x_3469_ = lean_box(0);
v___x_3470_ = l_Lean_Meta_synthInstance(v_a_3468_, v___x_3469_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
v___y_3439_ = v___y_3456_;
v___y_3440_ = v___y_3454_;
v___y_3441_ = v___y_3457_;
v___y_3442_ = v___y_3452_;
v___y_3443_ = v___f_3462_;
v___y_3444_ = v___y_3453_;
v___y_3445_ = v___y_3455_;
v___y_3446_ = v___x_3470_;
goto v___jp_3438_;
}
else
{
v___y_3439_ = v___y_3456_;
v___y_3440_ = v___y_3454_;
v___y_3441_ = v___y_3457_;
v___y_3442_ = v___y_3452_;
v___y_3443_ = v___f_3462_;
v___y_3444_ = v___y_3453_;
v___y_3445_ = v___y_3455_;
v___y_3446_ = v___x_3467_;
goto v___jp_3438_;
}
}
case 1:
{
lean_object* v_a_3471_; lean_object* v___x_3472_; 
lean_dec_ref(v___f_3366_);
lean_dec_ref(v_type_3363_);
lean_dec(v_declName_3362_);
v_a_3471_ = lean_ctor_get(v___x_3458_, 0);
lean_inc(v_a_3471_);
lean_dec_ref(v___x_3458_);
v___x_3472_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg(v_a_3471_, v___f_3365_, v_isZero_3361_, v_isZero_3361_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
if (lean_obj_tag(v___x_3472_) == 0)
{
lean_object* v_a_3473_; 
v_a_3473_ = lean_ctor_get(v___x_3472_, 0);
lean_inc(v_a_3473_);
lean_dec_ref(v___x_3472_);
v_inst_3378_ = v_a_3473_;
v___y_3379_ = v___y_3454_;
v___y_3380_ = v___y_3455_;
v___y_3381_ = v___y_3456_;
v___y_3382_ = v___y_3457_;
goto v___jp_3377_;
}
else
{
lean_dec_ref(v_xs_3368_);
return v___x_3472_;
}
}
default: 
{
lean_object* v_a_3474_; lean_object* v___x_3475_; 
lean_dec_ref(v___f_3365_);
lean_dec_ref(v_type_3363_);
lean_dec(v_declName_3362_);
v_a_3474_ = lean_ctor_get(v___x_3458_, 0);
lean_inc(v_a_3474_);
lean_dec_ref(v___x_3458_);
v___x_3475_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg(v_a_3474_, v___f_3366_, v_isZero_3361_, v_isZero_3361_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
if (lean_obj_tag(v___x_3475_) == 0)
{
lean_object* v_a_3476_; 
v_a_3476_ = lean_ctor_get(v___x_3475_, 0);
lean_inc(v_a_3476_);
lean_dec_ref(v___x_3475_);
v_inst_3378_ = v_a_3476_;
v___y_3379_ = v___y_3454_;
v___y_3380_ = v___y_3455_;
v___y_3381_ = v___y_3456_;
v___y_3382_ = v___y_3457_;
goto v___jp_3377_;
}
else
{
lean_dec_ref(v_xs_3368_);
return v___x_3475_;
}
}
}
}
else
{
lean_dec_ref(v_xs_3368_);
lean_dec_ref(v___f_3366_);
lean_dec_ref(v___f_3365_);
lean_dec_ref(v_type_3363_);
lean_dec(v_declName_3362_);
return v___x_3458_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___boxed(lean_object* v_isZero_3502_, lean_object* v_declName_3503_, lean_object* v_type_3504_, lean_object* v_fixpointType_3505_, lean_object* v___f_3506_, lean_object* v___f_3507_, lean_object* v_value_3508_, lean_object* v_xs_3509_, lean_object* v___body_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_){
_start:
{
uint8_t v_isZero_boxed_3518_; uint8_t v_fixpointType_boxed_3519_; lean_object* v_res_3520_; 
v_isZero_boxed_3518_ = lean_unbox(v_isZero_3502_);
v_fixpointType_boxed_3519_ = lean_unbox(v_fixpointType_3505_);
v_res_3520_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3(v_isZero_boxed_3518_, v_declName_3503_, v_type_3504_, v_fixpointType_boxed_3519_, v___f_3506_, v___f_3507_, v_value_3508_, v_xs_3509_, v___body_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_);
lean_dec(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
return v_res_3520_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__0(void){
_start:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3521_ = lean_box(1);
v___x_3522_ = l_Lean_MessageData_ofFormat(v___x_3521_);
return v___x_3522_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__3(void){
_start:
{
lean_object* v___x_3526_; lean_object* v___x_3527_; 
v___x_3526_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__2));
v___x_3527_ = l_Lean_MessageData_ofFormat(v___x_3526_);
return v___x_3527_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11(lean_object* v_x_3528_, lean_object* v_x_3529_){
_start:
{
if (lean_obj_tag(v_x_3529_) == 0)
{
return v_x_3528_;
}
else
{
lean_object* v_head_3530_; lean_object* v_tail_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3553_; 
v_head_3530_ = lean_ctor_get(v_x_3529_, 0);
v_tail_3531_ = lean_ctor_get(v_x_3529_, 1);
v_isSharedCheck_3553_ = !lean_is_exclusive(v_x_3529_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3533_ = v_x_3529_;
v_isShared_3534_ = v_isSharedCheck_3553_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_tail_3531_);
lean_inc(v_head_3530_);
lean_dec(v_x_3529_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3553_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v_before_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3551_; 
v_before_3535_ = lean_ctor_get(v_head_3530_, 0);
v_isSharedCheck_3551_ = !lean_is_exclusive(v_head_3530_);
if (v_isSharedCheck_3551_ == 0)
{
lean_object* v_unused_3552_; 
v_unused_3552_ = lean_ctor_get(v_head_3530_, 1);
lean_dec(v_unused_3552_);
v___x_3537_ = v_head_3530_;
v_isShared_3538_ = v_isSharedCheck_3551_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_before_3535_);
lean_dec(v_head_3530_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3551_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3539_; lean_object* v___x_3541_; 
v___x_3539_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__0);
if (v_isShared_3538_ == 0)
{
lean_ctor_set_tag(v___x_3537_, 7);
lean_ctor_set(v___x_3537_, 1, v___x_3539_);
lean_ctor_set(v___x_3537_, 0, v_x_3528_);
v___x_3541_ = v___x_3537_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v_x_3528_);
lean_ctor_set(v_reuseFailAlloc_3550_, 1, v___x_3539_);
v___x_3541_ = v_reuseFailAlloc_3550_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
lean_object* v___x_3542_; lean_object* v___x_3544_; 
v___x_3542_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__3);
if (v_isShared_3534_ == 0)
{
lean_ctor_set_tag(v___x_3533_, 7);
lean_ctor_set(v___x_3533_, 1, v___x_3542_);
lean_ctor_set(v___x_3533_, 0, v___x_3541_);
v___x_3544_ = v___x_3533_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v___x_3541_);
lean_ctor_set(v_reuseFailAlloc_3549_, 1, v___x_3542_);
v___x_3544_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; 
v___x_3545_ = l_Lean_MessageData_ofSyntax(v_before_3535_);
v___x_3546_ = l_Lean_indentD(v___x_3545_);
v___x_3547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3547_, 0, v___x_3544_);
lean_ctor_set(v___x_3547_, 1, v___x_3546_);
v_x_3528_ = v___x_3547_;
v_x_3529_ = v_tail_3531_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__10(lean_object* v_opts_3554_, lean_object* v_opt_3555_){
_start:
{
lean_object* v_name_3556_; lean_object* v_defValue_3557_; lean_object* v_map_3558_; lean_object* v___x_3559_; 
v_name_3556_ = lean_ctor_get(v_opt_3555_, 0);
v_defValue_3557_ = lean_ctor_get(v_opt_3555_, 1);
v_map_3558_ = lean_ctor_get(v_opts_3554_, 0);
v___x_3559_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3558_, v_name_3556_);
if (lean_obj_tag(v___x_3559_) == 0)
{
uint8_t v___x_3560_; 
v___x_3560_ = lean_unbox(v_defValue_3557_);
return v___x_3560_;
}
else
{
lean_object* v_val_3561_; 
v_val_3561_ = lean_ctor_get(v___x_3559_, 0);
lean_inc(v_val_3561_);
lean_dec_ref(v___x_3559_);
if (lean_obj_tag(v_val_3561_) == 1)
{
uint8_t v_v_3562_; 
v_v_3562_ = lean_ctor_get_uint8(v_val_3561_, 0);
lean_dec_ref(v_val_3561_);
return v_v_3562_;
}
else
{
uint8_t v___x_3563_; 
lean_dec(v_val_3561_);
v___x_3563_ = lean_unbox(v_defValue_3557_);
return v___x_3563_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__10___boxed(lean_object* v_opts_3564_, lean_object* v_opt_3565_){
_start:
{
uint8_t v_res_3566_; lean_object* v_r_3567_; 
v_res_3566_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__10(v_opts_3564_, v_opt_3565_);
lean_dec_ref(v_opt_3565_);
lean_dec_ref(v_opts_3564_);
v_r_3567_ = lean_box(v_res_3566_);
return v_r_3567_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3571_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__1));
v___x_3572_ = l_Lean_MessageData_ofFormat(v___x_3571_);
return v___x_3572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg(lean_object* v_msgData_3573_, lean_object* v_macroStack_3574_, lean_object* v___y_3575_){
_start:
{
lean_object* v_options_3577_; lean_object* v___x_3578_; uint8_t v___x_3579_; 
v_options_3577_ = lean_ctor_get(v___y_3575_, 2);
v___x_3578_ = l_Lean_Elab_pp_macroStack;
v___x_3579_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__10(v_options_3577_, v___x_3578_);
if (v___x_3579_ == 0)
{
lean_object* v___x_3580_; 
lean_dec(v_macroStack_3574_);
v___x_3580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3580_, 0, v_msgData_3573_);
return v___x_3580_;
}
else
{
if (lean_obj_tag(v_macroStack_3574_) == 0)
{
lean_object* v___x_3581_; 
v___x_3581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3581_, 0, v_msgData_3573_);
return v___x_3581_;
}
else
{
lean_object* v_head_3582_; lean_object* v_after_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3598_; 
v_head_3582_ = lean_ctor_get(v_macroStack_3574_, 0);
lean_inc(v_head_3582_);
v_after_3583_ = lean_ctor_get(v_head_3582_, 1);
v_isSharedCheck_3598_ = !lean_is_exclusive(v_head_3582_);
if (v_isSharedCheck_3598_ == 0)
{
lean_object* v_unused_3599_; 
v_unused_3599_ = lean_ctor_get(v_head_3582_, 0);
lean_dec(v_unused_3599_);
v___x_3585_ = v_head_3582_;
v_isShared_3586_ = v_isSharedCheck_3598_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_after_3583_);
lean_dec(v_head_3582_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3598_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3587_; lean_object* v___x_3589_; 
v___x_3587_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__0);
if (v_isShared_3586_ == 0)
{
lean_ctor_set_tag(v___x_3585_, 7);
lean_ctor_set(v___x_3585_, 1, v___x_3587_);
lean_ctor_set(v___x_3585_, 0, v_msgData_3573_);
v___x_3589_ = v___x_3585_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_msgData_3573_);
lean_ctor_set(v_reuseFailAlloc_3597_, 1, v___x_3587_);
v___x_3589_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v_msgData_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; 
v___x_3590_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__2);
v___x_3591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3591_, 0, v___x_3589_);
lean_ctor_set(v___x_3591_, 1, v___x_3590_);
v___x_3592_ = l_Lean_MessageData_ofSyntax(v_after_3583_);
v___x_3593_ = l_Lean_indentD(v___x_3592_);
v_msgData_3594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_3594_, 0, v___x_3591_);
lean_ctor_set(v_msgData_3594_, 1, v___x_3593_);
v___x_3595_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11(v_msgData_3594_, v_macroStack_3574_);
v___x_3596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3596_, 0, v___x_3595_);
return v___x_3596_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_3600_, lean_object* v_macroStack_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg(v_msgData_3600_, v_macroStack_3601_, v___y_3602_);
lean_dec_ref(v___y_3602_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___redArg(lean_object* v_msg_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_){
_start:
{
lean_object* v_ref_3613_; lean_object* v___x_3614_; lean_object* v_a_3615_; lean_object* v_macroStack_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v_a_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3627_; 
v_ref_3613_ = lean_ctor_get(v___y_3610_, 5);
v___x_3614_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6_spec__7(v_msg_3605_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_);
v_a_3615_ = lean_ctor_get(v___x_3614_, 0);
lean_inc(v_a_3615_);
lean_dec_ref(v___x_3614_);
v_macroStack_3616_ = lean_ctor_get(v___y_3606_, 1);
v___x_3617_ = l_Lean_Elab_getBetterRef(v_ref_3613_, v_macroStack_3616_);
lean_inc(v_macroStack_3616_);
v___x_3618_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg(v_a_3615_, v_macroStack_3616_, v___y_3610_);
v_a_3619_ = lean_ctor_get(v___x_3618_, 0);
v_isSharedCheck_3627_ = !lean_is_exclusive(v___x_3618_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3621_ = v___x_3618_;
v_isShared_3622_ = v_isSharedCheck_3627_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_a_3619_);
lean_dec(v___x_3618_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3627_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3623_; lean_object* v___x_3625_; 
v___x_3623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3623_, 0, v___x_3617_);
lean_ctor_set(v___x_3623_, 1, v_a_3619_);
if (v_isShared_3622_ == 0)
{
lean_ctor_set_tag(v___x_3621_, 1);
lean_ctor_set(v___x_3621_, 0, v___x_3623_);
v___x_3625_ = v___x_3621_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v___x_3623_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___redArg___boxed(lean_object* v_msg_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_){
_start:
{
lean_object* v_res_3636_; 
v_res_3636_ = l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___redArg(v_msg_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_);
lean_dec(v___y_3634_);
lean_dec_ref(v___y_3633_);
lean_dec(v___y_3632_);
lean_dec_ref(v___y_3631_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
return v_res_3636_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3644_ = lean_box(0);
v___x_3645_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__2));
v___x_3646_ = l_Lean_mkConst(v___x_3645_, v___x_3644_);
return v___x_3646_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__5(void){
_start:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3648_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__4));
v___x_3649_ = l_Lean_stringToMessageData(v___x_3648_);
return v___x_3649_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1(lean_object* v_xs_3650_, lean_object* v_e_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_){
_start:
{
uint8_t v___x_3662_; 
v___x_3662_ = l_Lean_Expr_isProp(v_e_3651_);
if (v___x_3662_ == 0)
{
lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v_a_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3672_; 
lean_dec_ref(v_xs_3650_);
v___x_3663_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__5, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__5_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__5);
v___x_3664_ = l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___redArg(v___x_3663_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_);
v_a_3665_ = lean_ctor_get(v___x_3664_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v___x_3664_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3667_ = v___x_3664_;
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_a_3665_);
lean_dec(v___x_3664_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3672_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v___x_3670_; 
if (v_isShared_3668_ == 0)
{
v___x_3670_ = v___x_3667_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_a_3665_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
return v___x_3670_;
}
}
}
else
{
goto v___jp_3659_;
}
v___jp_3659_:
{
lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3660_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__3, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__3_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__3);
v___x_3661_ = l_Lean_Meta_mkInstPiOfInstsForall(v_xs_3650_, v___x_3660_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_);
return v___x_3661_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___boxed(lean_object* v_xs_3673_, lean_object* v_e_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_){
_start:
{
lean_object* v_res_3682_; 
v_res_3682_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1(v_xs_3673_, v_e_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
lean_dec(v___y_3680_);
lean_dec_ref(v___y_3679_);
lean_dec(v___y_3678_);
lean_dec_ref(v___y_3677_);
lean_dec(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec_ref(v_e_3674_);
return v_res_3682_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; 
v___x_3689_ = lean_box(0);
v___x_3690_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__1));
v___x_3691_ = l_Lean_mkConst(v___x_3690_, v___x_3689_);
return v___x_3691_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3693_; lean_object* v___x_3694_; 
v___x_3693_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__3));
v___x_3694_ = l_Lean_stringToMessageData(v___x_3693_);
return v___x_3694_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0(lean_object* v_xs_3695_, lean_object* v_e_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_){
_start:
{
uint8_t v___x_3707_; 
v___x_3707_ = l_Lean_Expr_isProp(v_e_3696_);
if (v___x_3707_ == 0)
{
lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v_a_3710_; lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3717_; 
lean_dec_ref(v_xs_3695_);
v___x_3708_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__4, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__4_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__4);
v___x_3709_ = l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___redArg(v___x_3708_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_);
v_a_3710_ = lean_ctor_get(v___x_3709_, 0);
v_isSharedCheck_3717_ = !lean_is_exclusive(v___x_3709_);
if (v_isSharedCheck_3717_ == 0)
{
v___x_3712_ = v___x_3709_;
v_isShared_3713_ = v_isSharedCheck_3717_;
goto v_resetjp_3711_;
}
else
{
lean_inc(v_a_3710_);
lean_dec(v___x_3709_);
v___x_3712_ = lean_box(0);
v_isShared_3713_ = v_isSharedCheck_3717_;
goto v_resetjp_3711_;
}
v_resetjp_3711_:
{
lean_object* v___x_3715_; 
if (v_isShared_3713_ == 0)
{
v___x_3715_ = v___x_3712_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v_a_3710_);
v___x_3715_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
return v___x_3715_;
}
}
}
else
{
goto v___jp_3704_;
}
v___jp_3704_:
{
lean_object* v___x_3705_; lean_object* v___x_3706_; 
v___x_3705_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__2, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__2_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__2);
v___x_3706_ = l_Lean_Meta_mkInstPiOfInstsForall(v_xs_3695_, v___x_3705_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_);
return v___x_3706_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___boxed(lean_object* v_xs_3718_, lean_object* v_e_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_){
_start:
{
lean_object* v_res_3727_; 
v_res_3727_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0(v_xs_3718_, v_e_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_);
lean_dec(v___y_3725_);
lean_dec_ref(v___y_3724_);
lean_dec(v___y_3723_);
lean_dec_ref(v___y_3722_);
lean_dec(v___y_3721_);
lean_dec_ref(v___y_3720_);
lean_dec_ref(v_e_3719_);
return v_res_3727_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg(lean_object* v_hints_3730_, lean_object* v_as_3731_, lean_object* v_i_3732_, lean_object* v_j_3733_, lean_object* v_bs_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_){
_start:
{
lean_object* v_zero_3742_; uint8_t v_isZero_3743_; 
v_zero_3742_ = lean_unsigned_to_nat(0u);
v_isZero_3743_ = lean_nat_dec_eq(v_i_3732_, v_zero_3742_);
if (v_isZero_3743_ == 1)
{
lean_object* v___x_3744_; 
lean_dec(v_j_3733_);
lean_dec(v_i_3732_);
v___x_3744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3744_, 0, v_bs_3734_);
return v___x_3744_;
}
else
{
lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v_ref_3747_; uint8_t v_fixpointType_3748_; lean_object* v___x_3749_; lean_object* v_declName_3750_; lean_object* v_type_3751_; lean_object* v_value_3752_; lean_object* v_fileName_3753_; lean_object* v_fileMap_3754_; lean_object* v_options_3755_; lean_object* v_currRecDepth_3756_; lean_object* v_maxRecDepth_3757_; lean_object* v_ref_3758_; lean_object* v_currNamespace_3759_; lean_object* v_openDecls_3760_; lean_object* v_initHeartbeats_3761_; lean_object* v_maxHeartbeats_3762_; lean_object* v_quotContext_3763_; lean_object* v_currMacroScope_3764_; uint8_t v_diag_3765_; lean_object* v_cancelTk_x3f_3766_; uint8_t v_suppressElabErrors_3767_; lean_object* v_inheritedTraceOptions_3768_; lean_object* v___f_3769_; lean_object* v___f_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___f_3773_; lean_object* v_ref_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; 
v___x_3745_ = l_Lean_Elab_instInhabitedPartialFixpoint_default;
v___x_3746_ = lean_array_get_borrowed(v___x_3745_, v_hints_3730_, v_j_3733_);
v_ref_3747_ = lean_ctor_get(v___x_3746_, 0);
v_fixpointType_3748_ = lean_ctor_get_uint8(v___x_3746_, sizeof(void*)*2);
v___x_3749_ = lean_array_fget_borrowed(v_as_3731_, v_j_3733_);
v_declName_3750_ = lean_ctor_get(v___x_3749_, 3);
v_type_3751_ = lean_ctor_get(v___x_3749_, 6);
v_value_3752_ = lean_ctor_get(v___x_3749_, 7);
v_fileName_3753_ = lean_ctor_get(v___y_3739_, 0);
v_fileMap_3754_ = lean_ctor_get(v___y_3739_, 1);
v_options_3755_ = lean_ctor_get(v___y_3739_, 2);
v_currRecDepth_3756_ = lean_ctor_get(v___y_3739_, 3);
v_maxRecDepth_3757_ = lean_ctor_get(v___y_3739_, 4);
v_ref_3758_ = lean_ctor_get(v___y_3739_, 5);
v_currNamespace_3759_ = lean_ctor_get(v___y_3739_, 6);
v_openDecls_3760_ = lean_ctor_get(v___y_3739_, 7);
v_initHeartbeats_3761_ = lean_ctor_get(v___y_3739_, 8);
v_maxHeartbeats_3762_ = lean_ctor_get(v___y_3739_, 9);
v_quotContext_3763_ = lean_ctor_get(v___y_3739_, 10);
v_currMacroScope_3764_ = lean_ctor_get(v___y_3739_, 11);
v_diag_3765_ = lean_ctor_get_uint8(v___y_3739_, sizeof(void*)*14);
v_cancelTk_x3f_3766_ = lean_ctor_get(v___y_3739_, 12);
v_suppressElabErrors_3767_ = lean_ctor_get_uint8(v___y_3739_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3768_ = lean_ctor_get(v___y_3739_, 13);
v___f_3769_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___closed__0));
v___f_3770_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___closed__1));
v___x_3771_ = lean_box(v_isZero_3743_);
v___x_3772_ = lean_box(v_fixpointType_3748_);
lean_inc_ref_n(v_value_3752_, 2);
lean_inc_ref(v_type_3751_);
lean_inc(v_declName_3750_);
v___f_3773_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___boxed), 16, 7);
lean_closure_set(v___f_3773_, 0, v___x_3771_);
lean_closure_set(v___f_3773_, 1, v_declName_3750_);
lean_closure_set(v___f_3773_, 2, v_type_3751_);
lean_closure_set(v___f_3773_, 3, v___x_3772_);
lean_closure_set(v___f_3773_, 4, v___f_3769_);
lean_closure_set(v___f_3773_, 5, v___f_3770_);
lean_closure_set(v___f_3773_, 6, v_value_3752_);
v_ref_3774_ = l_Lean_replaceRef(v_ref_3747_, v_ref_3758_);
lean_inc_ref(v_inheritedTraceOptions_3768_);
lean_inc(v_cancelTk_x3f_3766_);
lean_inc(v_currMacroScope_3764_);
lean_inc(v_quotContext_3763_);
lean_inc(v_maxHeartbeats_3762_);
lean_inc(v_initHeartbeats_3761_);
lean_inc(v_openDecls_3760_);
lean_inc(v_currNamespace_3759_);
lean_inc(v_maxRecDepth_3757_);
lean_inc(v_currRecDepth_3756_);
lean_inc_ref(v_options_3755_);
lean_inc_ref(v_fileMap_3754_);
lean_inc_ref(v_fileName_3753_);
v___x_3775_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3775_, 0, v_fileName_3753_);
lean_ctor_set(v___x_3775_, 1, v_fileMap_3754_);
lean_ctor_set(v___x_3775_, 2, v_options_3755_);
lean_ctor_set(v___x_3775_, 3, v_currRecDepth_3756_);
lean_ctor_set(v___x_3775_, 4, v_maxRecDepth_3757_);
lean_ctor_set(v___x_3775_, 5, v_ref_3774_);
lean_ctor_set(v___x_3775_, 6, v_currNamespace_3759_);
lean_ctor_set(v___x_3775_, 7, v_openDecls_3760_);
lean_ctor_set(v___x_3775_, 8, v_initHeartbeats_3761_);
lean_ctor_set(v___x_3775_, 9, v_maxHeartbeats_3762_);
lean_ctor_set(v___x_3775_, 10, v_quotContext_3763_);
lean_ctor_set(v___x_3775_, 11, v_currMacroScope_3764_);
lean_ctor_set(v___x_3775_, 12, v_cancelTk_x3f_3766_);
lean_ctor_set(v___x_3775_, 13, v_inheritedTraceOptions_3768_);
lean_ctor_set_uint8(v___x_3775_, sizeof(void*)*14, v_diag_3765_);
lean_ctor_set_uint8(v___x_3775_, sizeof(void*)*14 + 1, v_suppressElabErrors_3767_);
v___x_3776_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5___redArg(v_value_3752_, v___f_3773_, v_isZero_3743_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___x_3775_, v___y_3740_);
lean_dec_ref(v___x_3775_);
if (lean_obj_tag(v___x_3776_) == 0)
{
lean_object* v_a_3777_; lean_object* v_one_3778_; lean_object* v_n_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; 
v_a_3777_ = lean_ctor_get(v___x_3776_, 0);
lean_inc(v_a_3777_);
lean_dec_ref(v___x_3776_);
v_one_3778_ = lean_unsigned_to_nat(1u);
v_n_3779_ = lean_nat_sub(v_i_3732_, v_one_3778_);
lean_dec(v_i_3732_);
v___x_3780_ = lean_nat_add(v_j_3733_, v_one_3778_);
lean_dec(v_j_3733_);
v___x_3781_ = lean_array_push(v_bs_3734_, v_a_3777_);
v_i_3732_ = v_n_3779_;
v_j_3733_ = v___x_3780_;
v_bs_3734_ = v___x_3781_;
goto _start;
}
else
{
lean_object* v_a_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3790_; 
lean_dec_ref(v_bs_3734_);
lean_dec(v_j_3733_);
lean_dec(v_i_3732_);
v_a_3783_ = lean_ctor_get(v___x_3776_, 0);
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3776_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3785_ = v___x_3776_;
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_a_3783_);
lean_dec(v___x_3776_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3788_; 
if (v_isShared_3786_ == 0)
{
v___x_3788_ = v___x_3785_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_a_3783_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___boxed(lean_object* v_hints_3791_, lean_object* v_as_3792_, lean_object* v_i_3793_, lean_object* v_j_3794_, lean_object* v_bs_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_){
_start:
{
lean_object* v_res_3803_; 
v_res_3803_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg(v_hints_3791_, v_as_3792_, v_i_3793_, v_j_3794_, v_bs_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_);
lean_dec(v___y_3801_);
lean_dec_ref(v___y_3800_);
lean_dec(v___y_3799_);
lean_dec_ref(v___y_3798_);
lean_dec(v___y_3797_);
lean_dec_ref(v___y_3796_);
lean_dec_ref(v_as_3792_);
lean_dec_ref(v_hints_3791_);
return v_res_3803_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__26_spec__31(lean_object* v_as_3804_, size_t v_i_3805_, size_t v_stop_3806_){
_start:
{
uint8_t v___x_3807_; 
v___x_3807_ = lean_usize_dec_eq(v_i_3805_, v_stop_3806_);
if (v___x_3807_ == 0)
{
lean_object* v___x_3808_; uint8_t v_fixpointType_3809_; uint8_t v___x_3810_; 
v___x_3808_ = lean_array_uget_borrowed(v_as_3804_, v_i_3805_);
v_fixpointType_3809_ = lean_ctor_get_uint8(v___x_3808_, sizeof(void*)*2);
v___x_3810_ = l_Lean_Elab_isLatticeTheoretic(v_fixpointType_3809_);
if (v___x_3810_ == 0)
{
size_t v___x_3811_; size_t v___x_3812_; 
v___x_3811_ = ((size_t)1ULL);
v___x_3812_ = lean_usize_add(v_i_3805_, v___x_3811_);
v_i_3805_ = v___x_3812_;
goto _start;
}
else
{
return v___x_3810_;
}
}
else
{
uint8_t v___x_3814_; 
v___x_3814_ = 0;
return v___x_3814_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__26_spec__31___boxed(lean_object* v_as_3815_, lean_object* v_i_3816_, lean_object* v_stop_3817_){
_start:
{
size_t v_i_boxed_3818_; size_t v_stop_boxed_3819_; uint8_t v_res_3820_; lean_object* v_r_3821_; 
v_i_boxed_3818_ = lean_unbox_usize(v_i_3816_);
lean_dec(v_i_3816_);
v_stop_boxed_3819_ = lean_unbox_usize(v_stop_3817_);
lean_dec(v_stop_3817_);
v_res_3820_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__26_spec__31(v_as_3815_, v_i_boxed_3818_, v_stop_boxed_3819_);
lean_dec_ref(v_as_3815_);
v_r_3821_ = lean_box(v_res_3820_);
return v_r_3821_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__26(lean_object* v_as_3822_, size_t v_i_3823_, size_t v_stop_3824_){
_start:
{
uint8_t v___x_3825_; 
v___x_3825_ = lean_usize_dec_eq(v_i_3823_, v_stop_3824_);
if (v___x_3825_ == 0)
{
lean_object* v___x_3826_; uint8_t v_fixpointType_3827_; uint8_t v___x_3828_; 
v___x_3826_ = lean_array_uget_borrowed(v_as_3822_, v_i_3823_);
v_fixpointType_3827_ = lean_ctor_get_uint8(v___x_3826_, sizeof(void*)*2);
v___x_3828_ = l_Lean_Elab_isLatticeTheoretic(v_fixpointType_3827_);
if (v___x_3828_ == 0)
{
size_t v___x_3829_; size_t v___x_3830_; uint8_t v___x_3831_; 
v___x_3829_ = ((size_t)1ULL);
v___x_3830_ = lean_usize_add(v_i_3823_, v___x_3829_);
v___x_3831_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__26_spec__31(v_as_3822_, v___x_3830_, v_stop_3824_);
return v___x_3831_;
}
else
{
return v___x_3828_;
}
}
else
{
uint8_t v___x_3832_; 
v___x_3832_ = 0;
return v___x_3832_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__26___boxed(lean_object* v_as_3833_, lean_object* v_i_3834_, lean_object* v_stop_3835_){
_start:
{
size_t v_i_boxed_3836_; size_t v_stop_boxed_3837_; uint8_t v_res_3838_; lean_object* v_r_3839_; 
v_i_boxed_3836_ = lean_unbox_usize(v_i_3834_);
lean_dec(v_i_3834_);
v_stop_boxed_3837_ = lean_unbox_usize(v_stop_3835_);
lean_dec(v_stop_3835_);
v_res_3838_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__26(v_as_3833_, v_i_boxed_3836_, v_stop_boxed_3837_);
lean_dec_ref(v_as_3833_);
v_r_3839_ = lean_box(v_res_3838_);
return v_r_3839_;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___closed__1(void){
_start:
{
lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; 
v___x_3841_ = ((lean_object*)(l_Lean_Elab_partialFixpoint___closed__0));
v___x_3842_ = lean_unsigned_to_nat(2u);
v___x_3843_ = lean_unsigned_to_nat(82u);
v___x_3844_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__7));
v___x_3845_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__0));
v___x_3846_ = l_mkPanicMessageWithDecl(v___x_3845_, v___x_3844_, v___x_3843_, v___x_3842_, v___x_3841_);
return v___x_3846_;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___closed__3(void){
_start:
{
lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; 
v___x_3848_ = ((lean_object*)(l_Lean_Elab_partialFixpoint___closed__2));
v___x_3849_ = lean_unsigned_to_nat(4u);
v___x_3850_ = lean_unsigned_to_nat(86u);
v___x_3851_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__7));
v___x_3852_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__0));
v___x_3853_ = l_mkPanicMessageWithDecl(v___x_3852_, v___x_3851_, v___x_3850_, v___x_3849_, v___x_3848_);
return v___x_3853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_partialFixpoint(lean_object* v_docCtx_3856_, lean_object* v_preDefs_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_){
_start:
{
lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v_hints_3867_; lean_object* v___x_3868_; uint8_t v___x_3869_; lean_object* v___y_3871_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; 
v___x_3865_ = lean_unsigned_to_nat(0u);
v___x_3866_ = lean_array_get_size(v_preDefs_3857_);
v_hints_3867_ = l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0(v_preDefs_3857_, v___x_3865_, v___x_3866_);
v___x_3868_ = lean_array_get_size(v_hints_3867_);
v___x_3869_ = lean_nat_dec_eq(v___x_3866_, v___x_3868_);
if (v___x_3869_ == 0)
{
lean_object* v___x_3912_; lean_object* v___x_3913_; 
lean_dec_ref(v_hints_3867_);
lean_dec_ref(v_preDefs_3857_);
lean_dec_ref(v_docCtx_3856_);
v___x_3912_ = lean_obj_once(&l_Lean_Elab_partialFixpoint___closed__1, &l_Lean_Elab_partialFixpoint___closed__1_once, _init_l_Lean_Elab_partialFixpoint___closed__1);
v___x_3913_ = l_panic___at___00Lean_Elab_partialFixpoint_spec__25(v___x_3912_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_);
return v___x_3913_;
}
else
{
uint8_t v___x_3914_; 
v___x_3914_ = lean_nat_dec_lt(v___x_3865_, v___x_3868_);
if (v___x_3914_ == 0)
{
v___y_3871_ = v_a_3858_;
v___y_3872_ = v_a_3859_;
v___y_3873_ = v_a_3860_;
v___y_3874_ = v_a_3861_;
v___y_3875_ = v_a_3862_;
v___y_3876_ = v_a_3863_;
goto v___jp_3870_;
}
else
{
if (v___x_3914_ == 0)
{
v___y_3871_ = v_a_3858_;
v___y_3872_ = v_a_3859_;
v___y_3873_ = v_a_3860_;
v___y_3874_ = v_a_3861_;
v___y_3875_ = v_a_3862_;
v___y_3876_ = v_a_3863_;
goto v___jp_3870_;
}
else
{
size_t v___x_3915_; size_t v___x_3916_; uint8_t v___x_3917_; 
v___x_3915_ = ((size_t)0ULL);
v___x_3916_ = lean_usize_of_nat(v___x_3868_);
v___x_3917_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__26(v_hints_3867_, v___x_3915_, v___x_3916_);
if (v___x_3917_ == 0)
{
v___y_3871_ = v_a_3858_;
v___y_3872_ = v_a_3859_;
v___y_3873_ = v_a_3860_;
v___y_3874_ = v_a_3861_;
v___y_3875_ = v_a_3862_;
v___y_3876_ = v_a_3863_;
goto v___jp_3870_;
}
else
{
if (v___x_3914_ == 0)
{
v___y_3871_ = v_a_3858_;
v___y_3872_ = v_a_3859_;
v___y_3873_ = v_a_3860_;
v___y_3874_ = v_a_3861_;
v___y_3875_ = v_a_3862_;
v___y_3876_ = v_a_3863_;
goto v___jp_3870_;
}
else
{
if (v___x_3914_ == 0)
{
v___y_3871_ = v_a_3858_;
v___y_3872_ = v_a_3859_;
v___y_3873_ = v_a_3860_;
v___y_3874_ = v_a_3861_;
v___y_3875_ = v_a_3862_;
v___y_3876_ = v_a_3863_;
goto v___jp_3870_;
}
else
{
uint8_t v___x_3918_; 
v___x_3918_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27(v___x_3917_, v_hints_3867_, v___x_3915_, v___x_3916_);
if (v___x_3918_ == 0)
{
v___y_3871_ = v_a_3858_;
v___y_3872_ = v_a_3859_;
v___y_3873_ = v_a_3860_;
v___y_3874_ = v_a_3861_;
v___y_3875_ = v_a_3862_;
v___y_3876_ = v_a_3863_;
goto v___jp_3870_;
}
else
{
lean_object* v___x_3919_; lean_object* v___x_3920_; 
lean_dec_ref(v_hints_3867_);
lean_dec_ref(v_preDefs_3857_);
lean_dec_ref(v_docCtx_3856_);
v___x_3919_ = lean_obj_once(&l_Lean_Elab_partialFixpoint___closed__3, &l_Lean_Elab_partialFixpoint___closed__3_once, _init_l_Lean_Elab_partialFixpoint___closed__3);
v___x_3920_ = l_panic___at___00Lean_Elab_partialFixpoint_spec__25(v___x_3919_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_);
return v___x_3920_;
}
}
}
}
}
}
}
v___jp_3870_:
{
lean_object* v___x_3877_; lean_object* v___x_3878_; 
v___x_3877_ = lean_mk_empty_array_with_capacity(v___x_3866_);
lean_inc_ref(v___x_3877_);
v___x_3878_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg(v_hints_3867_, v_preDefs_3857_, v___x_3866_, v___x_3865_, v___x_3877_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_);
if (lean_obj_tag(v___x_3878_) == 0)
{
lean_object* v_a_3879_; size_t v_sz_3880_; size_t v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; 
v_a_3879_ = lean_ctor_get(v___x_3878_, 0);
lean_inc(v_a_3879_);
lean_dec_ref(v___x_3878_);
v_sz_3880_ = lean_array_size(v_preDefs_3857_);
v___x_3881_ = ((size_t)0ULL);
lean_inc_ref_n(v_preDefs_3857_, 2);
v___x_3882_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__7(v_sz_3880_, v___x_3881_, v_preDefs_3857_);
v___x_3883_ = l_Lean_Elab_getFixedParamPerms(v_preDefs_3857_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_);
if (lean_obj_tag(v___x_3883_) == 0)
{
lean_object* v_a_3884_; lean_object* v_perms_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v_type_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___f_3894_; lean_object* v___x_3895_; 
v_a_3884_ = lean_ctor_get(v___x_3883_, 0);
lean_inc(v_a_3884_);
lean_dec_ref(v___x_3883_);
v_perms_3885_ = lean_ctor_get(v_a_3884_, 1);
lean_inc_ref(v_perms_3885_);
v___x_3886_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_3887_ = lean_array_get(v___x_3886_, v_preDefs_3857_, v___x_3865_);
v_type_3888_ = lean_ctor_get(v___x_3887_, 6);
lean_inc_ref(v_type_3888_);
v___x_3889_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1);
v___x_3890_ = lean_array_get(v___x_3889_, v_perms_3885_, v___x_3865_);
v___x_3891_ = ((lean_object*)(l_Lean_Elab_partialFixpoint___boxed__const__1));
v___x_3892_ = lean_box(v___x_3869_);
v___x_3893_ = lean_box_usize(v_sz_3880_);
v___f_3894_ = lean_alloc_closure((void*)(l_Lean_Elab_partialFixpoint___lam__0___boxed), 22, 14);
lean_closure_set(v___f_3894_, 0, v_a_3879_);
lean_closure_set(v___f_3894_, 1, v_perms_3885_);
lean_closure_set(v___f_3894_, 2, v___x_3865_);
lean_closure_set(v___f_3894_, 3, v_preDefs_3857_);
lean_closure_set(v___f_3894_, 4, v___x_3866_);
lean_closure_set(v___f_3894_, 5, v___x_3877_);
lean_closure_set(v___f_3894_, 6, v___x_3891_);
lean_closure_set(v___f_3894_, 7, v___x_3882_);
lean_closure_set(v___f_3894_, 8, v_a_3884_);
lean_closure_set(v___f_3894_, 9, v___x_3892_);
lean_closure_set(v___f_3894_, 10, v_hints_3867_);
lean_closure_set(v___f_3894_, 11, v___x_3887_);
lean_closure_set(v___f_3894_, 12, v_docCtx_3856_);
lean_closure_set(v___f_3894_, 13, v___x_3893_);
v___x_3895_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg(v___x_3890_, v_type_3888_, v___f_3894_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_);
return v___x_3895_;
}
else
{
lean_object* v_a_3896_; lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3903_; 
lean_dec_ref(v___x_3882_);
lean_dec(v_a_3879_);
lean_dec_ref(v___x_3877_);
lean_dec_ref(v_hints_3867_);
lean_dec_ref(v_preDefs_3857_);
lean_dec_ref(v_docCtx_3856_);
v_a_3896_ = lean_ctor_get(v___x_3883_, 0);
v_isSharedCheck_3903_ = !lean_is_exclusive(v___x_3883_);
if (v_isSharedCheck_3903_ == 0)
{
v___x_3898_ = v___x_3883_;
v_isShared_3899_ = v_isSharedCheck_3903_;
goto v_resetjp_3897_;
}
else
{
lean_inc(v_a_3896_);
lean_dec(v___x_3883_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3903_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
lean_object* v___x_3901_; 
if (v_isShared_3899_ == 0)
{
v___x_3901_ = v___x_3898_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v_a_3896_);
v___x_3901_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3900_;
}
v_reusejp_3900_:
{
return v___x_3901_;
}
}
}
}
else
{
lean_object* v_a_3904_; lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3911_; 
lean_dec_ref(v___x_3877_);
lean_dec_ref(v_hints_3867_);
lean_dec_ref(v_preDefs_3857_);
lean_dec_ref(v_docCtx_3856_);
v_a_3904_ = lean_ctor_get(v___x_3878_, 0);
v_isSharedCheck_3911_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3911_ == 0)
{
v___x_3906_ = v___x_3878_;
v_isShared_3907_ = v_isSharedCheck_3911_;
goto v_resetjp_3905_;
}
else
{
lean_inc(v_a_3904_);
lean_dec(v___x_3878_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3911_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
lean_object* v___x_3909_; 
if (v_isShared_3907_ == 0)
{
v___x_3909_ = v___x_3906_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v_a_3904_);
v___x_3909_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
return v___x_3909_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_partialFixpoint___boxed(lean_object* v_docCtx_3921_, lean_object* v_preDefs_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_){
_start:
{
lean_object* v_res_3930_; 
v_res_3930_ = l_Lean_Elab_partialFixpoint(v_docCtx_3921_, v_preDefs_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_);
lean_dec(v_a_3928_);
lean_dec_ref(v_a_3927_);
lean_dec(v_a_3926_);
lean_dec_ref(v_a_3925_);
lean_dec(v_a_3924_);
lean_dec_ref(v_a_3923_);
return v_res_3930_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1(lean_object* v_00_u03b1_3931_, lean_object* v_msg_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_){
_start:
{
lean_object* v___x_3940_; 
v___x_3940_ = l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___redArg(v_msg_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_);
return v___x_3940_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___boxed(lean_object* v_00_u03b1_3941_, lean_object* v_msg_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_){
_start:
{
lean_object* v_res_3950_; 
v_res_3950_ = l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1(v_00_u03b1_3941_, v_msg_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_);
lean_dec(v___y_3948_);
lean_dec_ref(v___y_3947_);
lean_dec(v___y_3946_);
lean_dec_ref(v___y_3945_);
lean_dec(v___y_3944_);
lean_dec_ref(v___y_3943_);
return v_res_3950_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2(lean_object* v_cls_3951_, lean_object* v_msg_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_){
_start:
{
lean_object* v___x_3960_; 
v___x_3960_ = l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg(v_cls_3951_, v_msg_3952_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_);
return v___x_3960_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___boxed(lean_object* v_cls_3961_, lean_object* v_msg_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_){
_start:
{
lean_object* v_res_3970_; 
v_res_3970_ = l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2(v_cls_3961_, v_msg_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_);
lean_dec(v___y_3968_);
lean_dec_ref(v___y_3967_);
lean_dec(v___y_3966_);
lean_dec_ref(v___y_3965_);
lean_dec(v___y_3964_);
lean_dec_ref(v___y_3963_);
return v_res_3970_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6(lean_object* v_hints_3971_, lean_object* v_as_3972_, lean_object* v_i_3973_, lean_object* v_j_3974_, lean_object* v_inv_3975_, lean_object* v_bs_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_){
_start:
{
lean_object* v___x_3984_; 
v___x_3984_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg(v_hints_3971_, v_as_3972_, v_i_3973_, v_j_3974_, v_bs_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_);
return v___x_3984_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___boxed(lean_object* v_hints_3985_, lean_object* v_as_3986_, lean_object* v_i_3987_, lean_object* v_j_3988_, lean_object* v_inv_3989_, lean_object* v_bs_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_){
_start:
{
lean_object* v_res_3998_; 
v_res_3998_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6(v_hints_3985_, v_as_3986_, v_i_3987_, v_j_3988_, v_inv_3989_, v_bs_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_);
lean_dec(v___y_3996_);
lean_dec_ref(v___y_3995_);
lean_dec(v___y_3994_);
lean_dec_ref(v___y_3993_);
lean_dec(v___y_3992_);
lean_dec_ref(v___y_3991_);
lean_dec_ref(v_as_3986_);
lean_dec_ref(v_hints_3985_);
return v_res_3998_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__10(lean_object* v___x_3999_, lean_object* v_fixedArgs_4000_, lean_object* v_as_4001_, lean_object* v_i_4002_, lean_object* v_j_4003_, lean_object* v_inv_4004_, lean_object* v_bs_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_){
_start:
{
lean_object* v___x_4013_; 
v___x_4013_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__10___redArg(v___x_3999_, v_fixedArgs_4000_, v_as_4001_, v_i_4002_, v_j_4003_, v_bs_4005_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_);
return v___x_4013_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__10___boxed(lean_object* v___x_4014_, lean_object* v_fixedArgs_4015_, lean_object* v_as_4016_, lean_object* v_i_4017_, lean_object* v_j_4018_, lean_object* v_inv_4019_, lean_object* v_bs_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_){
_start:
{
lean_object* v_res_4028_; 
v_res_4028_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__10(v___x_4014_, v_fixedArgs_4015_, v_as_4016_, v_i_4017_, v_j_4018_, v_inv_4019_, v_bs_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_);
lean_dec(v___y_4026_);
lean_dec_ref(v___y_4025_);
lean_dec(v___y_4024_);
lean_dec_ref(v___y_4023_);
lean_dec(v___y_4022_);
lean_dec_ref(v___y_4021_);
lean_dec_ref(v_as_4016_);
lean_dec_ref(v___x_4014_);
return v_res_4028_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11(lean_object* v___x_4029_, lean_object* v_fixedArgs_4030_, lean_object* v_as_4031_, lean_object* v_i_4032_, lean_object* v_j_4033_, lean_object* v_inv_4034_, lean_object* v_bs_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_){
_start:
{
lean_object* v___x_4043_; 
v___x_4043_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11___redArg(v___x_4029_, v_fixedArgs_4030_, v_as_4031_, v_i_4032_, v_j_4033_, v_bs_4035_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_);
return v___x_4043_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11___boxed(lean_object* v___x_4044_, lean_object* v_fixedArgs_4045_, lean_object* v_as_4046_, lean_object* v_i_4047_, lean_object* v_j_4048_, lean_object* v_inv_4049_, lean_object* v_bs_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_){
_start:
{
lean_object* v_res_4058_; 
v_res_4058_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11(v___x_4044_, v_fixedArgs_4045_, v_as_4046_, v_i_4047_, v_j_4048_, v_inv_4049_, v_bs_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_);
lean_dec(v___y_4056_);
lean_dec_ref(v___y_4055_);
lean_dec(v___y_4054_);
lean_dec_ref(v___y_4053_);
lean_dec(v___y_4052_);
lean_dec_ref(v___y_4051_);
lean_dec_ref(v_as_4046_);
lean_dec_ref(v___x_4044_);
return v_res_4058_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13(lean_object* v_as_4059_, size_t v_i_4060_, size_t v_stop_4061_, lean_object* v_b_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_){
_start:
{
lean_object* v___x_4070_; 
v___x_4070_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13___redArg(v_as_4059_, v_i_4060_, v_stop_4061_, v_b_4062_, v___y_4067_, v___y_4068_);
return v___x_4070_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13___boxed(lean_object* v_as_4071_, lean_object* v_i_4072_, lean_object* v_stop_4073_, lean_object* v_b_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_){
_start:
{
size_t v_i_boxed_4082_; size_t v_stop_boxed_4083_; lean_object* v_res_4084_; 
v_i_boxed_4082_ = lean_unbox_usize(v_i_4072_);
lean_dec(v_i_4072_);
v_stop_boxed_4083_ = lean_unbox_usize(v_stop_4073_);
lean_dec(v_stop_4073_);
v_res_4084_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13(v_as_4071_, v_i_boxed_4082_, v_stop_boxed_4083_, v_b_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
lean_dec(v___y_4080_);
lean_dec_ref(v___y_4079_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec_ref(v___y_4075_);
lean_dec_ref(v_as_4071_);
return v_res_4084_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16(lean_object* v_env_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_){
_start:
{
lean_object* v___x_4093_; 
v___x_4093_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16___redArg(v_env_4085_, v___y_4089_, v___y_4091_);
return v___x_4093_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16___boxed(lean_object* v_env_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_){
_start:
{
lean_object* v_res_4102_; 
v_res_4102_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16(v_env_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
lean_dec(v___y_4100_);
lean_dec_ref(v___y_4099_);
lean_dec(v___y_4098_);
lean_dec_ref(v___y_4097_);
lean_dec(v___y_4096_);
lean_dec_ref(v___y_4095_);
return v_res_4102_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14(lean_object* v_00_u03b1_4103_, lean_object* v_env_4104_, lean_object* v_x_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_){
_start:
{
lean_object* v___x_4113_; 
v___x_4113_ = l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14___redArg(v_env_4104_, v_x_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_);
return v___x_4113_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14___boxed(lean_object* v_00_u03b1_4114_, lean_object* v_env_4115_, lean_object* v_x_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_){
_start:
{
lean_object* v_res_4124_; 
v_res_4124_ = l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14(v_00_u03b1_4114_, v_env_4115_, v_x_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_);
lean_dec(v___y_4122_);
lean_dec_ref(v___y_4121_);
lean_dec(v___y_4120_);
lean_dec_ref(v___y_4119_);
lean_dec(v___y_4118_);
lean_dec_ref(v___y_4117_);
return v_res_4124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18(lean_object* v_00_u03b1_4125_, lean_object* v_name_4126_, uint8_t v_bi_4127_, lean_object* v_type_4128_, lean_object* v_k_4129_, uint8_t v_kind_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_){
_start:
{
lean_object* v___x_4138_; 
v___x_4138_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg(v_name_4126_, v_bi_4127_, v_type_4128_, v_k_4129_, v_kind_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_);
return v___x_4138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___boxed(lean_object* v_00_u03b1_4139_, lean_object* v_name_4140_, lean_object* v_bi_4141_, lean_object* v_type_4142_, lean_object* v_k_4143_, lean_object* v_kind_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_){
_start:
{
uint8_t v_bi_boxed_4152_; uint8_t v_kind_boxed_4153_; lean_object* v_res_4154_; 
v_bi_boxed_4152_ = lean_unbox(v_bi_4141_);
v_kind_boxed_4153_ = lean_unbox(v_kind_4144_);
v_res_4154_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18(v_00_u03b1_4139_, v_name_4140_, v_bi_boxed_4152_, v_type_4142_, v_k_4143_, v_kind_boxed_4153_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_);
lean_dec(v___y_4150_);
lean_dec_ref(v___y_4149_);
lean_dec(v___y_4148_);
lean_dec_ref(v___y_4147_);
lean_dec(v___y_4146_);
lean_dec_ref(v___y_4145_);
return v_res_4154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15(lean_object* v_00_u03b1_4155_, lean_object* v_name_4156_, lean_object* v_type_4157_, lean_object* v_k_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_){
_start:
{
lean_object* v___x_4166_; 
v___x_4166_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15___redArg(v_name_4156_, v_type_4157_, v_k_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_);
return v___x_4166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15___boxed(lean_object* v_00_u03b1_4167_, lean_object* v_name_4168_, lean_object* v_type_4169_, lean_object* v_k_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_){
_start:
{
lean_object* v_res_4178_; 
v_res_4178_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15(v_00_u03b1_4167_, v_name_4168_, v_type_4169_, v_k_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_);
lean_dec(v___y_4176_);
lean_dec_ref(v___y_4175_);
lean_dec(v___y_4174_);
lean_dec_ref(v___y_4173_);
lean_dec(v___y_4172_);
lean_dec_ref(v___y_4171_);
return v_res_4178_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21(lean_object* v_00_u03b1_4179_, lean_object* v_x_4180_, uint8_t v_isExporting_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_){
_start:
{
lean_object* v___x_4189_; 
v___x_4189_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg(v_x_4180_, v_isExporting_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_);
return v___x_4189_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___boxed(lean_object* v_00_u03b1_4190_, lean_object* v_x_4191_, lean_object* v_isExporting_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_){
_start:
{
uint8_t v_isExporting_boxed_4200_; lean_object* v_res_4201_; 
v_isExporting_boxed_4200_ = lean_unbox(v_isExporting_4192_);
v_res_4201_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21(v_00_u03b1_4190_, v_x_4191_, v_isExporting_boxed_4200_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_);
lean_dec(v___y_4198_);
lean_dec_ref(v___y_4197_);
lean_dec(v___y_4196_);
lean_dec_ref(v___y_4195_);
lean_dec(v___y_4194_);
lean_dec_ref(v___y_4193_);
return v_res_4201_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17(lean_object* v_00_u03b1_4202_, lean_object* v_x_4203_, uint8_t v_when_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_){
_start:
{
lean_object* v___x_4212_; 
v___x_4212_ = l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17___redArg(v_x_4203_, v_when_4204_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_);
return v___x_4212_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17___boxed(lean_object* v_00_u03b1_4213_, lean_object* v_x_4214_, lean_object* v_when_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_){
_start:
{
uint8_t v_when_boxed_4223_; lean_object* v_res_4224_; 
v_when_boxed_4223_ = lean_unbox(v_when_4215_);
v_res_4224_ = l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17(v_00_u03b1_4213_, v_x_4214_, v_when_boxed_4223_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_);
lean_dec(v___y_4221_);
lean_dec_ref(v___y_4220_);
lean_dec(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec_ref(v___y_4216_);
return v_res_4224_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21(lean_object* v___x_4225_, lean_object* v___x_4226_, lean_object* v___y_4227_, lean_object* v___x_4228_, lean_object* v_a_4229_, lean_object* v_as_4230_, lean_object* v_i_4231_, lean_object* v_j_4232_, lean_object* v_inv_4233_, lean_object* v_bs_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_){
_start:
{
lean_object* v___x_4242_; 
v___x_4242_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg(v___x_4225_, v___x_4226_, v___y_4227_, v___x_4228_, v_a_4229_, v_as_4230_, v_i_4231_, v_j_4232_, v_bs_4234_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_);
return v___x_4242_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21___boxed(lean_object** _args){
lean_object* v___x_4243_ = _args[0];
lean_object* v___x_4244_ = _args[1];
lean_object* v___y_4245_ = _args[2];
lean_object* v___x_4246_ = _args[3];
lean_object* v_a_4247_ = _args[4];
lean_object* v_as_4248_ = _args[5];
lean_object* v_i_4249_ = _args[6];
lean_object* v_j_4250_ = _args[7];
lean_object* v_inv_4251_ = _args[8];
lean_object* v_bs_4252_ = _args[9];
lean_object* v___y_4253_ = _args[10];
lean_object* v___y_4254_ = _args[11];
lean_object* v___y_4255_ = _args[12];
lean_object* v___y_4256_ = _args[13];
lean_object* v___y_4257_ = _args[14];
lean_object* v___y_4258_ = _args[15];
lean_object* v___y_4259_ = _args[16];
_start:
{
lean_object* v_res_4260_; 
v_res_4260_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21(v___x_4243_, v___x_4244_, v___y_4245_, v___x_4246_, v_a_4247_, v_as_4248_, v_i_4249_, v_j_4250_, v_inv_4251_, v_bs_4252_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
lean_dec(v___y_4258_);
lean_dec_ref(v___y_4257_);
lean_dec(v___y_4256_);
lean_dec_ref(v___y_4255_);
lean_dec(v___y_4254_);
lean_dec_ref(v___y_4253_);
lean_dec_ref(v_as_4248_);
lean_dec_ref(v___x_4243_);
return v_res_4260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__22(size_t v_sz_4261_, size_t v_i_4262_, lean_object* v_bs_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_){
_start:
{
lean_object* v___x_4271_; 
v___x_4271_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__22___redArg(v_sz_4261_, v_i_4262_, v_bs_4263_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_);
return v___x_4271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__22___boxed(lean_object* v_sz_4272_, lean_object* v_i_4273_, lean_object* v_bs_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_){
_start:
{
size_t v_sz_boxed_4282_; size_t v_i_boxed_4283_; lean_object* v_res_4284_; 
v_sz_boxed_4282_ = lean_unbox_usize(v_sz_4272_);
lean_dec(v_sz_4272_);
v_i_boxed_4283_ = lean_unbox_usize(v_i_4273_);
lean_dec(v_i_4273_);
v_res_4284_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__22(v_sz_boxed_4282_, v_i_boxed_4283_, v_bs_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_);
lean_dec(v___y_4280_);
lean_dec_ref(v___y_4279_);
lean_dec(v___y_4278_);
lean_dec_ref(v___y_4277_);
lean_dec(v___y_4276_);
lean_dec_ref(v___y_4275_);
return v_res_4284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2(lean_object* v_msgData_4285_, lean_object* v_macroStack_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_){
_start:
{
lean_object* v___x_4294_; 
v___x_4294_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg(v_msgData_4285_, v_macroStack_4286_, v___y_4291_);
return v___x_4294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___boxed(lean_object* v_msgData_4295_, lean_object* v_macroStack_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_){
_start:
{
lean_object* v_res_4304_; 
v_res_4304_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2(v_msgData_4295_, v_macroStack_4296_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_);
lean_dec(v___y_4302_);
lean_dec_ref(v___y_4301_);
lean_dec(v___y_4300_);
lean_dec_ref(v___y_4299_);
lean_dec(v___y_4298_);
lean_dec_ref(v___y_4297_);
return v_res_4304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4368_; uint8_t v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; 
v___x_4368_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7));
v___x_4369_ = 0;
v___x_4370_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__25_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_));
v___x_4371_ = l_Lean_registerTraceClass(v___x_4368_, v___x_4369_, v___x_4370_);
return v___x_4371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2____boxed(lean_object* v_a_4372_){
_start:
{
lean_object* v_res_4373_; 
v_res_4373_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_();
return v_res_4373_;
}
}
lean_object* runtime_initialize_Lean_Elab_PreDefinition_MkInhabitant(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_Mutual(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Monotonicity(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Order(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Main(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_PreDefinition_MkInhabitant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_Mutual(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Monotonicity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Main(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_PreDefinition_MkInhabitant(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_Mutual(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Monotonicity(uint8_t builtin);
lean_object* initialize_Lean_Meta_Order(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_PartialFixpoint_Main(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_PreDefinition_MkInhabitant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Mutual(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Monotonicity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_PreDefinition_PartialFixpoint_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_PreDefinition_PartialFixpoint_Main(builtin);
}
#ifdef __cplusplus
}
#endif
