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
lean_object* v___x_540_; lean_object* v_nextMacroScope_541_; lean_object* v_ngen_542_; lean_object* v_auxDeclNGen_543_; lean_object* v_traceState_544_; lean_object* v_messages_545_; lean_object* v_infoState_546_; lean_object* v_snapshotTasks_547_; lean_object* v_newDecls_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_574_; 
v___x_540_ = lean_st_ref_take(v___y_538_);
v_nextMacroScope_541_ = lean_ctor_get(v___x_540_, 1);
v_ngen_542_ = lean_ctor_get(v___x_540_, 2);
v_auxDeclNGen_543_ = lean_ctor_get(v___x_540_, 3);
v_traceState_544_ = lean_ctor_get(v___x_540_, 4);
v_messages_545_ = lean_ctor_get(v___x_540_, 6);
v_infoState_546_ = lean_ctor_get(v___x_540_, 7);
v_snapshotTasks_547_ = lean_ctor_get(v___x_540_, 8);
v_newDecls_548_ = lean_ctor_get(v___x_540_, 9);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_574_ == 0)
{
lean_object* v_unused_575_; lean_object* v_unused_576_; 
v_unused_575_ = lean_ctor_get(v___x_540_, 5);
lean_dec(v_unused_575_);
v_unused_576_ = lean_ctor_get(v___x_540_, 0);
lean_dec(v_unused_576_);
v___x_550_ = v___x_540_;
v_isShared_551_ = v_isSharedCheck_574_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_newDecls_548_);
lean_inc(v_snapshotTasks_547_);
lean_inc(v_infoState_546_);
lean_inc(v_messages_545_);
lean_inc(v_traceState_544_);
lean_inc(v_auxDeclNGen_543_);
lean_inc(v_ngen_542_);
lean_inc(v_nextMacroScope_541_);
lean_dec(v___x_540_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_574_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; lean_object* v___x_554_; 
v___x_552_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 5, v___x_552_);
lean_ctor_set(v___x_550_, 0, v_env_536_);
v___x_554_ = v___x_550_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_env_536_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v_nextMacroScope_541_);
lean_ctor_set(v_reuseFailAlloc_573_, 2, v_ngen_542_);
lean_ctor_set(v_reuseFailAlloc_573_, 3, v_auxDeclNGen_543_);
lean_ctor_set(v_reuseFailAlloc_573_, 4, v_traceState_544_);
lean_ctor_set(v_reuseFailAlloc_573_, 5, v___x_552_);
lean_ctor_set(v_reuseFailAlloc_573_, 6, v_messages_545_);
lean_ctor_set(v_reuseFailAlloc_573_, 7, v_infoState_546_);
lean_ctor_set(v_reuseFailAlloc_573_, 8, v_snapshotTasks_547_);
lean_ctor_set(v_reuseFailAlloc_573_, 9, v_newDecls_548_);
v___x_554_ = v_reuseFailAlloc_573_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v_mctx_557_; lean_object* v_zetaDeltaFVarIds_558_; lean_object* v_postponed_559_; lean_object* v_diag_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_571_; 
v___x_555_ = lean_st_ref_set(v___y_538_, v___x_554_);
v___x_556_ = lean_st_ref_take(v___y_537_);
v_mctx_557_ = lean_ctor_get(v___x_556_, 0);
v_zetaDeltaFVarIds_558_ = lean_ctor_get(v___x_556_, 2);
v_postponed_559_ = lean_ctor_get(v___x_556_, 3);
v_diag_560_ = lean_ctor_get(v___x_556_, 4);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_571_ == 0)
{
lean_object* v_unused_572_; 
v_unused_572_ = lean_ctor_get(v___x_556_, 1);
lean_dec(v_unused_572_);
v___x_562_ = v___x_556_;
v_isShared_563_ = v_isSharedCheck_571_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_diag_560_);
lean_inc(v_postponed_559_);
lean_inc(v_zetaDeltaFVarIds_558_);
lean_inc(v_mctx_557_);
lean_dec(v___x_556_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_571_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_564_; lean_object* v___x_566_; 
v___x_564_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 1, v___x_564_);
v___x_566_ = v___x_562_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_mctx_557_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v___x_564_);
lean_ctor_set(v_reuseFailAlloc_570_, 2, v_zetaDeltaFVarIds_558_);
lean_ctor_set(v_reuseFailAlloc_570_, 3, v_postponed_559_);
lean_ctor_set(v_reuseFailAlloc_570_, 4, v_diag_560_);
v___x_566_ = v_reuseFailAlloc_570_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_567_ = lean_st_ref_set(v___y_537_, v___x_566_);
v___x_568_ = lean_box(0);
v___x_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
return v___x_569_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___boxed(lean_object* v_env_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg(v_env_577_, v___y_578_, v___y_579_);
lean_dec(v___y_579_);
lean_dec(v___y_578_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5___redArg(lean_object* v_env_582_, lean_object* v_x_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
lean_object* v___x_589_; lean_object* v_env_590_; lean_object* v_a_592_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_589_ = lean_st_ref_get(v___y_587_);
v_env_590_ = lean_ctor_get(v___x_589_, 0);
lean_inc_ref(v_env_590_);
lean_dec(v___x_589_);
v___x_602_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg(v_env_582_, v___y_585_, v___y_587_);
lean_dec_ref(v___x_602_);
lean_inc(v___y_587_);
lean_inc_ref(v___y_586_);
lean_inc(v___y_585_);
lean_inc_ref(v___y_584_);
v___x_603_ = lean_apply_5(v_x_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, lean_box(0));
if (lean_obj_tag(v___x_603_) == 0)
{
lean_object* v_a_604_; lean_object* v___x_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_612_; 
v_a_604_ = lean_ctor_get(v___x_603_, 0);
lean_inc(v_a_604_);
lean_dec_ref(v___x_603_);
v___x_605_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg(v_env_590_, v___y_585_, v___y_587_);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_612_ == 0)
{
lean_object* v_unused_613_; 
v_unused_613_ = lean_ctor_get(v___x_605_, 0);
lean_dec(v_unused_613_);
v___x_607_ = v___x_605_;
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
else
{
lean_dec(v___x_605_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v_a_604_);
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_a_604_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
else
{
lean_object* v_a_614_; 
v_a_614_ = lean_ctor_get(v___x_603_, 0);
lean_inc(v_a_614_);
lean_dec_ref(v___x_603_);
v_a_592_ = v_a_614_;
goto v___jp_591_;
}
v___jp_591_:
{
lean_object* v___x_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_600_; 
v___x_593_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg(v_env_590_, v___y_585_, v___y_587_);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_600_ == 0)
{
lean_object* v_unused_601_; 
v_unused_601_ = lean_ctor_get(v___x_593_, 0);
lean_dec(v_unused_601_);
v___x_595_ = v___x_593_;
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
else
{
lean_dec(v___x_593_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
lean_ctor_set_tag(v___x_595_, 1);
lean_ctor_set(v___x_595_, 0, v_a_592_);
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_a_592_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5___redArg___boxed(lean_object* v_env_615_, lean_object* v_x_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5___redArg(v_env_615_, v_x_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6_spec__7(lean_object* v_msgData_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
lean_object* v___x_629_; lean_object* v_env_630_; lean_object* v___x_631_; lean_object* v_mctx_632_; lean_object* v_lctx_633_; lean_object* v_options_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_629_ = lean_st_ref_get(v___y_627_);
v_env_630_ = lean_ctor_get(v___x_629_, 0);
lean_inc_ref(v_env_630_);
lean_dec(v___x_629_);
v___x_631_ = lean_st_ref_get(v___y_625_);
v_mctx_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc_ref(v_mctx_632_);
lean_dec(v___x_631_);
v_lctx_633_ = lean_ctor_get(v___y_624_, 2);
v_options_634_ = lean_ctor_get(v___y_626_, 2);
lean_inc_ref(v_options_634_);
lean_inc_ref(v_lctx_633_);
v___x_635_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_635_, 0, v_env_630_);
lean_ctor_set(v___x_635_, 1, v_mctx_632_);
lean_ctor_set(v___x_635_, 2, v_lctx_633_);
lean_ctor_set(v___x_635_, 3, v_options_634_);
v___x_636_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
lean_ctor_set(v___x_636_, 1, v_msgData_623_);
v___x_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6_spec__7___boxed(lean_object* v_msgData_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6_spec__7(v_msgData_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg(lean_object* v_msg_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v_ref_651_; lean_object* v___x_652_; lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_661_; 
v_ref_651_ = lean_ctor_get(v___y_648_, 5);
v___x_652_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6_spec__7(v_msg_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
v_a_653_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_661_ == 0)
{
v___x_655_ = v___x_652_;
v_isShared_656_ = v_isSharedCheck_661_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_652_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_661_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_657_; lean_object* v___x_659_; 
lean_inc(v_ref_651_);
v___x_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_657_, 0, v_ref_651_);
lean_ctor_set(v___x_657_, 1, v_a_653_);
if (v_isShared_656_ == 0)
{
lean_ctor_set_tag(v___x_655_, 1);
lean_ctor_set(v___x_655_, 0, v___x_657_);
v___x_659_ = v___x_655_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_657_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg___boxed(lean_object* v_msg_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg(v_msg_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
return v_res_668_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___closed__1(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___closed__0));
v___x_671_ = l_Lean_stringToMessageData(v___x_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg(lean_object* v_preDefs_672_, lean_object* v_fixedParamPerms_673_, lean_object* v_fixedArgs_674_, lean_object* v_F_675_, lean_object* v_k_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_){
_start:
{
lean_object* v___x_682_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; uint8_t v___x_695_; 
v___x_682_ = l_Lean_instInhabitedExpr;
v___x_695_ = l_Lean_Expr_isLambda(v_F_675_);
if (v___x_695_ == 0)
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
lean_dec_ref(v_k_676_);
lean_dec_ref(v_fixedArgs_674_);
lean_dec_ref(v_fixedParamPerms_673_);
lean_dec_ref(v_preDefs_672_);
v___x_696_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___closed__1);
v___x_697_ = l_Lean_indentExpr(v_F_675_);
v___x_698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_696_);
lean_ctor_set(v___x_698_, 1, v___x_697_);
v___x_699_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg(v___x_698_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
v_a_700_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_699_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_699_);
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
else
{
v___y_684_ = v_a_677_;
v___y_685_ = v_a_678_;
v___y_686_ = v_a_679_;
v___y_687_ = v_a_680_;
goto v___jp_683_;
}
v___jp_683_:
{
lean_object* v___x_688_; lean_object* v_env_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___f_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_688_ = lean_st_ref_get(v___y_687_);
v_env_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc_ref(v_env_689_);
lean_dec(v___x_688_);
v___x_690_ = lean_unsigned_to_nat(0u);
v___x_691_ = lean_array_get_size(v_preDefs_672_);
v___f_692_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___lam__2___boxed), 13, 8);
lean_closure_set(v___f_692_, 0, v___x_691_);
lean_closure_set(v___f_692_, 1, v_fixedParamPerms_673_);
lean_closure_set(v___f_692_, 2, v_fixedArgs_674_);
lean_closure_set(v___f_692_, 3, v_preDefs_672_);
lean_closure_set(v___f_692_, 4, v___x_690_);
lean_closure_set(v___f_692_, 5, v___x_682_);
lean_closure_set(v___f_692_, 6, v_F_675_);
lean_closure_set(v___f_692_, 7, v_k_676_);
v___x_693_ = l_Lean_Environment_unlockAsync(v_env_689_);
v___x_694_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5___redArg(v___x_693_, v___f_692_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
return v___x_694_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___boxed(lean_object* v_preDefs_708_, lean_object* v_fixedParamPerms_709_, lean_object* v_fixedArgs_710_, lean_object* v_F_711_, lean_object* v_k_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg(v_preDefs_708_, v_fixedParamPerms_709_, v_fixedArgs_710_, v_F_711_, v_k_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
lean_dec_ref(v_a_713_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps(lean_object* v_00_u03b1_719_, lean_object* v_preDefs_720_, lean_object* v_fixedParamPerms_721_, lean_object* v_fixedArgs_722_, lean_object* v_F_723_, lean_object* v_k_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg(v_preDefs_720_, v_fixedParamPerms_721_, v_fixedArgs_722_, v_F_723_, v_k_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___boxed(lean_object* v_00_u03b1_731_, lean_object* v_preDefs_732_, lean_object* v_fixedParamPerms_733_, lean_object* v_fixedArgs_734_, lean_object* v_F_735_, lean_object* v_k_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps(v_00_u03b1_731_, v_preDefs_732_, v_fixedParamPerms_733_, v_fixedArgs_734_, v_F_735_, v_k_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_);
lean_dec(v_a_740_);
lean_dec_ref(v_a_739_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2(lean_object* v_fixedParamPerms_743_, lean_object* v_fixedArgs_744_, lean_object* v_as_745_, lean_object* v_i_746_, lean_object* v_j_747_, lean_object* v_inv_748_, lean_object* v_bs_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___redArg(v_fixedParamPerms_743_, v_fixedArgs_744_, v_as_745_, v_i_746_, v_j_747_, v_bs_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___boxed(lean_object* v_fixedParamPerms_756_, lean_object* v_fixedArgs_757_, lean_object* v_as_758_, lean_object* v_i_759_, lean_object* v_j_760_, lean_object* v_inv_761_, lean_object* v_bs_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2(v_fixedParamPerms_756_, v_fixedArgs_757_, v_as_758_, v_i_759_, v_j_760_, v_inv_761_, v_bs_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec_ref(v_as_758_);
lean_dec_ref(v_fixedParamPerms_756_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__4(lean_object* v_as_769_, size_t v_i_770_, size_t v_stop_771_, lean_object* v_b_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__4___redArg(v_as_769_, v_i_770_, v_stop_771_, v_b_772_, v___y_775_, v___y_776_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__4___boxed(lean_object* v_as_779_, lean_object* v_i_780_, lean_object* v_stop_781_, lean_object* v_b_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
size_t v_i_boxed_788_; size_t v_stop_boxed_789_; lean_object* v_res_790_; 
v_i_boxed_788_ = lean_unbox_usize(v_i_780_);
lean_dec(v_i_780_);
v_stop_boxed_789_ = lean_unbox_usize(v_stop_781_);
lean_dec(v_stop_781_);
v_res_790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__4(v_as_779_, v_i_boxed_788_, v_stop_boxed_789_, v_b_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec_ref(v_as_779_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5(lean_object* v_env_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg(v_env_791_, v___y_793_, v___y_795_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___boxed(lean_object* v_env_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5(v_env_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5(lean_object* v_00_u03b1_805_, lean_object* v_env_806_, lean_object* v_x_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5___redArg(v_env_806_, v_x_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5___boxed(lean_object* v_00_u03b1_814_, lean_object* v_env_815_, lean_object* v_x_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5(v_00_u03b1_814_, v_env_815_, v_x_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6(lean_object* v_00_u03b1_823_, lean_object* v_msg_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg(v_msg_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___boxed(lean_object* v_00_u03b1_831_, lean_object* v_msg_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6(v_00_u03b1_831_, v_msg_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
return v_res_838_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__1(void){
_start:
{
lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_840_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__0));
v___x_841_ = l_Lean_stringToMessageData(v___x_840_);
return v___x_841_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__9(void){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_856_ = lean_box(0);
v___x_857_ = lean_unsigned_to_nat(10u);
v___x_858_ = lean_mk_empty_array_with_capacity(v___x_857_);
v___x_859_ = lean_array_push(v___x_858_, v___x_856_);
return v___x_859_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__10(void){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_860_ = lean_box(0);
v___x_861_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__9, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__9);
v___x_862_ = lean_array_push(v___x_861_, v___x_860_);
return v___x_862_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__11(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_863_ = lean_box(0);
v___x_864_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__10, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__10);
v___x_865_ = lean_array_push(v___x_864_, v___x_863_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd(lean_object* v_x_866_, lean_object* v_x_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_){
_start:
{
lean_object* v_fst_873_; lean_object* v_snd_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_977_; 
v_fst_873_ = lean_ctor_get(v_x_866_, 0);
v_snd_874_ = lean_ctor_get(v_x_866_, 1);
v_isSharedCheck_977_ = !lean_is_exclusive(v_x_866_);
if (v_isSharedCheck_977_ == 0)
{
v___x_876_ = v_x_866_;
v_isShared_877_ = v_isSharedCheck_977_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_snd_874_);
lean_inc(v_fst_873_);
lean_dec(v_x_866_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_977_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v_fst_889_; lean_object* v_snd_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_976_; 
v_fst_889_ = lean_ctor_get(v_x_867_, 0);
v_snd_890_ = lean_ctor_get(v_x_867_, 1);
v_isSharedCheck_976_ = !lean_is_exclusive(v_x_867_);
if (v_isSharedCheck_976_ == 0)
{
v___x_892_ = v_x_867_;
v_isShared_893_ = v_isSharedCheck_976_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_snd_890_);
lean_inc(v_fst_889_);
lean_dec(v_x_867_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_976_;
goto v_resetjp_891_;
}
v___jp_878_:
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_883_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__1);
v___x_884_ = l_Lean_indentExpr(v_snd_874_);
if (v_isShared_877_ == 0)
{
lean_ctor_set_tag(v___x_876_, 7);
lean_ctor_set(v___x_876_, 1, v___x_884_);
lean_ctor_set(v___x_876_, 0, v___x_883_);
v___x_886_ = v___x_876_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v___x_884_);
v___x_886_ = v_reuseFailAlloc_888_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_887_; 
v___x_887_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg(v___x_886_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
return v___x_887_;
}
}
v_resetjp_891_:
{
lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_897_; lean_object* v___y_898_; lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_903_ = l_Lean_Expr_cleanupAnnotations(v_fst_873_);
v___x_904_ = l_Lean_Expr_isApp(v___x_903_);
if (v___x_904_ == 0)
{
lean_dec_ref(v___x_903_);
lean_del_object(v___x_892_);
lean_dec(v_snd_890_);
lean_dec(v_fst_889_);
v___y_879_ = v_a_868_;
v___y_880_ = v_a_869_;
v___y_881_ = v_a_870_;
v___y_882_ = v_a_871_;
goto v___jp_878_;
}
else
{
lean_object* v___x_905_; uint8_t v___x_906_; 
v___x_905_ = l_Lean_Expr_appFnCleanup___redArg(v___x_903_);
v___x_906_ = l_Lean_Expr_isApp(v___x_905_);
if (v___x_906_ == 0)
{
lean_dec_ref(v___x_905_);
lean_del_object(v___x_892_);
lean_dec(v_snd_890_);
lean_dec(v_fst_889_);
v___y_879_ = v_a_868_;
v___y_880_ = v_a_869_;
v___y_881_ = v_a_870_;
v___y_882_ = v_a_871_;
goto v___jp_878_;
}
else
{
lean_object* v_arg_907_; lean_object* v___x_908_; uint8_t v___x_909_; 
v_arg_907_ = lean_ctor_get(v___x_905_, 1);
lean_inc_ref(v_arg_907_);
v___x_908_ = l_Lean_Expr_appFnCleanup___redArg(v___x_905_);
v___x_909_ = l_Lean_Expr_isApp(v___x_908_);
if (v___x_909_ == 0)
{
lean_dec_ref(v___x_908_);
lean_dec_ref(v_arg_907_);
lean_del_object(v___x_892_);
lean_dec(v_snd_890_);
lean_dec(v_fst_889_);
v___y_879_ = v_a_868_;
v___y_880_ = v_a_869_;
v___y_881_ = v_a_870_;
v___y_882_ = v_a_871_;
goto v___jp_878_;
}
else
{
lean_object* v___x_910_; uint8_t v___x_911_; 
v___x_910_ = l_Lean_Expr_appFnCleanup___redArg(v___x_908_);
v___x_911_ = l_Lean_Expr_isApp(v___x_910_);
if (v___x_911_ == 0)
{
lean_dec_ref(v___x_910_);
lean_dec_ref(v_arg_907_);
lean_del_object(v___x_892_);
lean_dec(v_snd_890_);
lean_dec(v_fst_889_);
v___y_879_ = v_a_868_;
v___y_880_ = v_a_869_;
v___y_881_ = v_a_870_;
v___y_882_ = v_a_871_;
goto v___jp_878_;
}
else
{
lean_object* v_arg_912_; lean_object* v___x_913_; uint8_t v___x_914_; 
v_arg_912_ = lean_ctor_get(v___x_910_, 1);
lean_inc_ref(v_arg_912_);
v___x_913_ = l_Lean_Expr_appFnCleanup___redArg(v___x_910_);
v___x_914_ = l_Lean_Expr_isApp(v___x_913_);
if (v___x_914_ == 0)
{
lean_dec_ref(v___x_913_);
lean_dec_ref(v_arg_912_);
lean_dec_ref(v_arg_907_);
lean_del_object(v___x_892_);
lean_dec(v_snd_890_);
lean_dec(v_fst_889_);
v___y_879_ = v_a_868_;
v___y_880_ = v_a_869_;
v___y_881_ = v_a_870_;
v___y_882_ = v_a_871_;
goto v___jp_878_;
}
else
{
lean_object* v___x_915_; lean_object* v___x_916_; uint8_t v___x_917_; 
v___x_915_ = l_Lean_Expr_appFnCleanup___redArg(v___x_913_);
v___x_916_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__5));
v___x_917_ = l_Lean_Expr_isConstOf(v___x_915_, v___x_916_);
lean_dec_ref(v___x_915_);
if (v___x_917_ == 0)
{
lean_dec_ref(v_arg_912_);
lean_dec_ref(v_arg_907_);
lean_del_object(v___x_892_);
lean_dec(v_snd_890_);
lean_dec(v_fst_889_);
v___y_879_ = v_a_868_;
v___y_880_ = v_a_869_;
v___y_881_ = v_a_870_;
v___y_882_ = v_a_871_;
goto v___jp_878_;
}
else
{
lean_object* v___x_918_; uint8_t v___x_919_; 
lean_del_object(v___x_876_);
v___x_918_ = l_Lean_Expr_cleanupAnnotations(v_fst_889_);
v___x_919_ = l_Lean_Expr_isApp(v___x_918_);
if (v___x_919_ == 0)
{
lean_dec_ref(v___x_918_);
lean_dec_ref(v_arg_912_);
lean_dec_ref(v_arg_907_);
lean_del_object(v___x_892_);
lean_dec(v_snd_874_);
v___y_895_ = v_a_868_;
v___y_896_ = v_a_869_;
v___y_897_ = v_a_870_;
v___y_898_ = v_a_871_;
goto v___jp_894_;
}
else
{
lean_object* v___x_920_; uint8_t v___x_921_; 
v___x_920_ = l_Lean_Expr_appFnCleanup___redArg(v___x_918_);
v___x_921_ = l_Lean_Expr_isApp(v___x_920_);
if (v___x_921_ == 0)
{
lean_dec_ref(v___x_920_);
lean_dec_ref(v_arg_912_);
lean_dec_ref(v_arg_907_);
lean_del_object(v___x_892_);
lean_dec(v_snd_874_);
v___y_895_ = v_a_868_;
v___y_896_ = v_a_869_;
v___y_897_ = v_a_870_;
v___y_898_ = v_a_871_;
goto v___jp_894_;
}
else
{
lean_object* v_arg_922_; lean_object* v___x_923_; uint8_t v___x_924_; 
v_arg_922_ = lean_ctor_get(v___x_920_, 1);
lean_inc_ref(v_arg_922_);
v___x_923_ = l_Lean_Expr_appFnCleanup___redArg(v___x_920_);
v___x_924_ = l_Lean_Expr_isApp(v___x_923_);
if (v___x_924_ == 0)
{
lean_dec_ref(v___x_923_);
lean_dec_ref(v_arg_922_);
lean_dec_ref(v_arg_912_);
lean_dec_ref(v_arg_907_);
lean_del_object(v___x_892_);
lean_dec(v_snd_874_);
v___y_895_ = v_a_868_;
v___y_896_ = v_a_869_;
v___y_897_ = v_a_870_;
v___y_898_ = v_a_871_;
goto v___jp_894_;
}
else
{
lean_object* v___x_925_; uint8_t v___x_926_; 
v___x_925_ = l_Lean_Expr_appFnCleanup___redArg(v___x_923_);
v___x_926_ = l_Lean_Expr_isApp(v___x_925_);
if (v___x_926_ == 0)
{
lean_dec_ref(v___x_925_);
lean_dec_ref(v_arg_922_);
lean_dec_ref(v_arg_912_);
lean_dec_ref(v_arg_907_);
lean_del_object(v___x_892_);
lean_dec(v_snd_874_);
v___y_895_ = v_a_868_;
v___y_896_ = v_a_869_;
v___y_897_ = v_a_870_;
v___y_898_ = v_a_871_;
goto v___jp_894_;
}
else
{
lean_object* v___x_927_; uint8_t v___x_928_; 
v___x_927_ = l_Lean_Expr_appFnCleanup___redArg(v___x_925_);
v___x_928_ = l_Lean_Expr_isApp(v___x_927_);
if (v___x_928_ == 0)
{
lean_dec_ref(v___x_927_);
lean_dec_ref(v_arg_922_);
lean_dec_ref(v_arg_912_);
lean_dec_ref(v_arg_907_);
lean_del_object(v___x_892_);
lean_dec(v_snd_874_);
v___y_895_ = v_a_868_;
v___y_896_ = v_a_869_;
v___y_897_ = v_a_870_;
v___y_898_ = v_a_871_;
goto v___jp_894_;
}
else
{
lean_object* v___x_929_; uint8_t v___x_930_; 
v___x_929_ = l_Lean_Expr_appFnCleanup___redArg(v___x_927_);
v___x_930_ = l_Lean_Expr_isConstOf(v___x_929_, v___x_916_);
lean_dec_ref(v___x_929_);
if (v___x_930_ == 0)
{
lean_dec_ref(v_arg_922_);
lean_dec_ref(v_arg_912_);
lean_dec_ref(v_arg_907_);
lean_del_object(v___x_892_);
lean_dec(v_snd_874_);
v___y_895_ = v_a_868_;
v___y_896_ = v_a_869_;
v___y_897_ = v_a_870_;
v___y_898_ = v_a_871_;
goto v___jp_894_;
}
else
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_931_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__8));
v___x_932_ = lean_box(0);
v___x_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_933_, 0, v_arg_907_);
v___x_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_934_, 0, v_arg_922_);
v___x_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_935_, 0, v_arg_912_);
v___x_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_936_, 0, v_snd_874_);
v___x_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_937_, 0, v_snd_890_);
v___x_938_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__11, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__11_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__11);
v___x_939_ = lean_array_push(v___x_938_, v___x_933_);
v___x_940_ = lean_array_push(v___x_939_, v___x_934_);
v___x_941_ = lean_array_push(v___x_940_, v___x_935_);
v___x_942_ = lean_array_push(v___x_941_, v___x_932_);
v___x_943_ = lean_array_push(v___x_942_, v___x_932_);
v___x_944_ = lean_array_push(v___x_943_, v___x_936_);
v___x_945_ = lean_array_push(v___x_944_, v___x_937_);
v___x_946_ = l_Lean_Meta_mkAppOptM(v___x_931_, v___x_945_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; lean_object* v___x_948_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc_n(v_a_947_, 2);
lean_dec_ref(v___x_946_);
lean_inc(v_a_871_);
lean_inc_ref(v_a_870_);
lean_inc(v_a_869_);
lean_inc_ref(v_a_868_);
v___x_948_ = lean_infer_type(v_a_947_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_959_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_959_ == 0)
{
v___x_951_ = v___x_948_;
v_isShared_952_ = v_isSharedCheck_959_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_948_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_959_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 1, v_a_947_);
lean_ctor_set(v___x_892_, 0, v_a_949_);
v___x_954_ = v___x_892_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_949_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_a_947_);
v___x_954_ = v_reuseFailAlloc_958_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
lean_object* v___x_956_; 
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 0, v___x_954_);
v___x_956_ = v___x_951_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_954_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
else
{
lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_967_; 
lean_dec(v_a_947_);
lean_del_object(v___x_892_);
v_a_960_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_967_ == 0)
{
v___x_962_ = v___x_948_;
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_948_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_965_; 
if (v_isShared_963_ == 0)
{
v___x_965_ = v___x_962_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_960_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
else
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_975_; 
lean_del_object(v___x_892_);
v_a_968_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_975_ == 0)
{
v___x_970_ = v___x_946_;
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_946_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_a_968_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
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
v___jp_894_:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_899_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__1);
v___x_900_ = l_Lean_indentExpr(v_snd_890_);
v___x_901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_899_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
v___x_902_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg(v___x_901_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
return v___x_902_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___boxed(lean_object* v_x_978_, lean_object* v_x_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd(v_x_978_, v_x_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
lean_dec(v_a_983_);
lean_dec_ref(v_a_982_);
lean_dec(v_a_981_);
lean_dec_ref(v_a_980_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg___lam__0(lean_object* v_k_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v_b_989_, lean_object* v_c_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v___x_996_; 
lean_inc(v___y_994_);
lean_inc_ref(v___y_993_);
lean_inc(v___y_992_);
lean_inc_ref(v___y_991_);
lean_inc(v___y_988_);
lean_inc_ref(v___y_987_);
v___x_996_ = lean_apply_9(v_k_986_, v_b_989_, v_c_990_, v___y_987_, v___y_988_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, lean_box(0));
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg___lam__0___boxed(lean_object* v_k_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v_b_1000_, lean_object* v_c_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg___lam__0(v_k_997_, v___y_998_, v___y_999_, v_b_1000_, v_c_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg(lean_object* v_type_1008_, lean_object* v_k_1009_, uint8_t v_cleanupAnnotations_1010_, uint8_t v_whnfType_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v___f_1019_; lean_object* v___x_1020_; 
lean_inc(v___y_1013_);
lean_inc_ref(v___y_1012_);
v___f_1019_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1019_, 0, v_k_1009_);
lean_closure_set(v___f_1019_, 1, v___y_1012_);
lean_closure_set(v___f_1019_, 2, v___y_1013_);
v___x_1020_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1008_, v___f_1019_, v_cleanupAnnotations_1010_, v_whnfType_1011_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
if (lean_obj_tag(v___x_1020_) == 0)
{
return v___x_1020_;
}
else
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_1020_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1020_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg___boxed(lean_object* v_type_1029_, lean_object* v_k_1030_, lean_object* v_cleanupAnnotations_1031_, lean_object* v_whnfType_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1040_; uint8_t v_whnfType_boxed_1041_; lean_object* v_res_1042_; 
v_cleanupAnnotations_boxed_1040_ = lean_unbox(v_cleanupAnnotations_1031_);
v_whnfType_boxed_1041_ = lean_unbox(v_whnfType_1032_);
v_res_1042_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg(v_type_1029_, v_k_1030_, v_cleanupAnnotations_boxed_1040_, v_whnfType_boxed_1041_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3(lean_object* v_00_u03b1_1043_, lean_object* v_type_1044_, lean_object* v_k_1045_, uint8_t v_cleanupAnnotations_1046_, uint8_t v_whnfType_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg(v_type_1044_, v_k_1045_, v_cleanupAnnotations_1046_, v_whnfType_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___boxed(lean_object* v_00_u03b1_1056_, lean_object* v_type_1057_, lean_object* v_k_1058_, lean_object* v_cleanupAnnotations_1059_, lean_object* v_whnfType_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1068_; uint8_t v_whnfType_boxed_1069_; lean_object* v_res_1070_; 
v_cleanupAnnotations_boxed_1068_ = lean_unbox(v_cleanupAnnotations_1059_);
v_whnfType_boxed_1069_ = lean_unbox(v_whnfType_1060_);
v_res_1070_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3(v_00_u03b1_1056_, v_type_1057_, v_k_1058_, v_cleanupAnnotations_boxed_1068_, v_whnfType_boxed_1069_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5___redArg(lean_object* v_e_1071_, lean_object* v_k_1072_, uint8_t v_cleanupAnnotations_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v___f_1081_; uint8_t v___x_1082_; uint8_t v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
lean_inc(v___y_1075_);
lean_inc_ref(v___y_1074_);
v___f_1081_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1081_, 0, v_k_1072_);
lean_closure_set(v___f_1081_, 1, v___y_1074_);
lean_closure_set(v___f_1081_, 2, v___y_1075_);
v___x_1082_ = 1;
v___x_1083_ = 0;
v___x_1084_ = lean_box(0);
v___x_1085_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1071_, v___x_1082_, v___x_1083_, v___x_1082_, v___x_1083_, v___x_1084_, v___f_1081_, v_cleanupAnnotations_1073_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
if (lean_obj_tag(v___x_1085_) == 0)
{
return v___x_1085_;
}
else
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1088_ = v___x_1085_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1085_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1086_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5___redArg___boxed(lean_object* v_e_1094_, lean_object* v_k_1095_, lean_object* v_cleanupAnnotations_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1104_; lean_object* v_res_1105_; 
v_cleanupAnnotations_boxed_1104_ = lean_unbox(v_cleanupAnnotations_1096_);
v_res_1105_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5___redArg(v_e_1094_, v_k_1095_, v_cleanupAnnotations_boxed_1104_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5(lean_object* v_00_u03b1_1106_, lean_object* v_e_1107_, lean_object* v_k_1108_, uint8_t v_cleanupAnnotations_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v___x_1117_; 
v___x_1117_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5___redArg(v_e_1107_, v_k_1108_, v_cleanupAnnotations_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5___boxed(lean_object* v_00_u03b1_1118_, lean_object* v_e_1119_, lean_object* v_k_1120_, lean_object* v_cleanupAnnotations_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1129_; lean_object* v_res_1130_; 
v_cleanupAnnotations_boxed_1129_ = lean_unbox(v_cleanupAnnotations_1121_);
v_res_1130_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5(v_00_u03b1_1118_, v_e_1119_, v_k_1120_, v_cleanupAnnotations_boxed_1129_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__8___redArg(lean_object* v_msg_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v___f_1137_; lean_object* v___x_41605__overap_1138_; lean_object* v___x_1139_; 
v___f_1137_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__0___closed__0));
v___x_41605__overap_1138_ = lean_panic_fn_borrowed(v___f_1137_, v_msg_1131_);
lean_inc(v___y_1135_);
lean_inc_ref(v___y_1134_);
lean_inc(v___y_1133_);
lean_inc_ref(v___y_1132_);
v___x_1139_ = lean_apply_5(v___x_41605__overap_1138_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, lean_box(0));
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__8___redArg___boxed(lean_object* v_msg_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_panic___at___00Lean_Elab_partialFixpoint_spec__8___redArg(v_msg_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__8(lean_object* v_00_u03b1_1147_, lean_object* v_msg_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = l_panic___at___00Lean_Elab_partialFixpoint_spec__8___redArg(v_msg_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__8___boxed(lean_object* v_00_u03b1_1155_, lean_object* v_msg_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_panic___at___00Lean_Elab_partialFixpoint_spec__8(v_00_u03b1_1155_, v_msg_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18___redArg(lean_object* v_e_1163_, lean_object* v___y_1164_){
_start:
{
uint8_t v___x_1166_; 
v___x_1166_ = l_Lean_Expr_hasMVar(v_e_1163_);
if (v___x_1166_ == 0)
{
lean_object* v___x_1167_; 
v___x_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1167_, 0, v_e_1163_);
return v___x_1167_;
}
else
{
lean_object* v___x_1168_; lean_object* v_mctx_1169_; lean_object* v___x_1170_; lean_object* v_fst_1171_; lean_object* v_snd_1172_; lean_object* v___x_1173_; lean_object* v_cache_1174_; lean_object* v_zetaDeltaFVarIds_1175_; lean_object* v_postponed_1176_; lean_object* v_diag_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1186_; 
v___x_1168_ = lean_st_ref_get(v___y_1164_);
v_mctx_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc_ref(v_mctx_1169_);
lean_dec(v___x_1168_);
v___x_1170_ = l_Lean_instantiateMVarsCore(v_mctx_1169_, v_e_1163_);
v_fst_1171_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_fst_1171_);
v_snd_1172_ = lean_ctor_get(v___x_1170_, 1);
lean_inc(v_snd_1172_);
lean_dec_ref(v___x_1170_);
v___x_1173_ = lean_st_ref_take(v___y_1164_);
v_cache_1174_ = lean_ctor_get(v___x_1173_, 1);
v_zetaDeltaFVarIds_1175_ = lean_ctor_get(v___x_1173_, 2);
v_postponed_1176_ = lean_ctor_get(v___x_1173_, 3);
v_diag_1177_ = lean_ctor_get(v___x_1173_, 4);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1186_ == 0)
{
lean_object* v_unused_1187_; 
v_unused_1187_ = lean_ctor_get(v___x_1173_, 0);
lean_dec(v_unused_1187_);
v___x_1179_ = v___x_1173_;
v_isShared_1180_ = v_isSharedCheck_1186_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_diag_1177_);
lean_inc(v_postponed_1176_);
lean_inc(v_zetaDeltaFVarIds_1175_);
lean_inc(v_cache_1174_);
lean_dec(v___x_1173_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1186_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 0, v_snd_1172_);
v___x_1182_ = v___x_1179_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_snd_1172_);
lean_ctor_set(v_reuseFailAlloc_1185_, 1, v_cache_1174_);
lean_ctor_set(v_reuseFailAlloc_1185_, 2, v_zetaDeltaFVarIds_1175_);
lean_ctor_set(v_reuseFailAlloc_1185_, 3, v_postponed_1176_);
lean_ctor_set(v_reuseFailAlloc_1185_, 4, v_diag_1177_);
v___x_1182_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1183_ = lean_st_ref_set(v___y_1164_, v___x_1182_);
v___x_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1184_, 0, v_fst_1171_);
return v___x_1184_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18___redArg___boxed(lean_object* v_e_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18___redArg(v_e_1188_, v___y_1189_);
lean_dec(v___y_1189_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18(lean_object* v_e_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18___redArg(v_e_1192_, v___y_1196_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18___boxed(lean_object* v_e_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18(v_e_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__20___redArg(lean_object* v_type_1210_, lean_object* v_maxFVars_x3f_1211_, lean_object* v_k_1212_, uint8_t v_cleanupAnnotations_1213_, uint8_t v_whnfType_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v___f_1222_; lean_object* v___x_1223_; 
lean_inc(v___y_1216_);
lean_inc_ref(v___y_1215_);
v___f_1222_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1222_, 0, v_k_1212_);
lean_closure_set(v___f_1222_, 1, v___y_1215_);
lean_closure_set(v___f_1222_, 2, v___y_1216_);
v___x_1223_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1210_, v_maxFVars_x3f_1211_, v___f_1222_, v_cleanupAnnotations_1213_, v_whnfType_1214_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_);
if (lean_obj_tag(v___x_1223_) == 0)
{
return v___x_1223_;
}
else
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1231_; 
v_a_1224_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1226_ = v___x_1223_;
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v___x_1223_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1229_; 
if (v_isShared_1227_ == 0)
{
v___x_1229_ = v___x_1226_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_a_1224_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__20___redArg___boxed(lean_object* v_type_1232_, lean_object* v_maxFVars_x3f_1233_, lean_object* v_k_1234_, lean_object* v_cleanupAnnotations_1235_, lean_object* v_whnfType_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1244_; uint8_t v_whnfType_boxed_1245_; lean_object* v_res_1246_; 
v_cleanupAnnotations_boxed_1244_ = lean_unbox(v_cleanupAnnotations_1235_);
v_whnfType_boxed_1245_ = lean_unbox(v_whnfType_1236_);
v_res_1246_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__20___redArg(v_type_1232_, v_maxFVars_x3f_1233_, v_k_1234_, v_cleanupAnnotations_boxed_1244_, v_whnfType_boxed_1245_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__20(lean_object* v_00_u03b1_1247_, lean_object* v_type_1248_, lean_object* v_maxFVars_x3f_1249_, lean_object* v_k_1250_, uint8_t v_cleanupAnnotations_1251_, uint8_t v_whnfType_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v___x_1260_; 
v___x_1260_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__20___redArg(v_type_1248_, v_maxFVars_x3f_1249_, v_k_1250_, v_cleanupAnnotations_1251_, v_whnfType_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__20___boxed(lean_object* v_00_u03b1_1261_, lean_object* v_type_1262_, lean_object* v_maxFVars_x3f_1263_, lean_object* v_k_1264_, lean_object* v_cleanupAnnotations_1265_, lean_object* v_whnfType_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1274_; uint8_t v_whnfType_boxed_1275_; lean_object* v_res_1276_; 
v_cleanupAnnotations_boxed_1274_ = lean_unbox(v_cleanupAnnotations_1265_);
v_whnfType_boxed_1275_ = lean_unbox(v_whnfType_1266_);
v_res_1276_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__20(v_00_u03b1_1261_, v_type_1262_, v_maxFVars_x3f_1263_, v_k_1264_, v_cleanupAnnotations_boxed_1274_, v_whnfType_boxed_1275_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg___lam__0(lean_object* v_k_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v_b_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v___x_1286_; 
lean_inc(v___y_1284_);
lean_inc_ref(v___y_1283_);
lean_inc(v___y_1282_);
lean_inc_ref(v___y_1281_);
lean_inc(v___y_1279_);
lean_inc_ref(v___y_1278_);
v___x_1286_ = lean_apply_8(v_k_1277_, v_b_1280_, v___y_1278_, v___y_1279_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, lean_box(0));
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg___lam__0___boxed(lean_object* v_k_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v_b_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg___lam__0(v_k_1287_, v___y_1288_, v___y_1289_, v_b_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg(lean_object* v_perm_1297_, lean_object* v_type_1298_, lean_object* v_k_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v___f_1307_; lean_object* v___x_1308_; 
lean_inc(v___y_1301_);
lean_inc_ref(v___y_1300_);
v___f_1307_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1307_, 0, v_k_1299_);
lean_closure_set(v___f_1307_, 1, v___y_1300_);
lean_closure_set(v___f_1307_, 2, v___y_1301_);
v___x_1308_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_box(0), v_perm_1297_, v_type_1298_, v___f_1307_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
if (lean_obj_tag(v___x_1308_) == 0)
{
return v___x_1308_;
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___x_1308_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1308_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1309_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg___boxed(lean_object* v_perm_1317_, lean_object* v_type_1318_, lean_object* v_k_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg(v_perm_1317_, v_type_1318_, v_k_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24(lean_object* v_00_u03b1_1328_, lean_object* v_perm_1329_, lean_object* v_type_1330_, lean_object* v_k_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_){
_start:
{
lean_object* v___x_1339_; 
v___x_1339_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg(v_perm_1329_, v_type_1330_, v_k_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___boxed(lean_object* v_00_u03b1_1340_, lean_object* v_perm_1341_, lean_object* v_type_1342_, lean_object* v_k_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24(v_00_u03b1_1340_, v_perm_1341_, v_type_1342_, v_k_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
return v_res_1351_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_partialFixpoint_spec__25___closed__0(void){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__25(lean_object* v_msg_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_47548__overap_1362_; lean_object* v___x_1363_; 
v___x_1361_ = lean_obj_once(&l_panic___at___00Lean_Elab_partialFixpoint_spec__25___closed__0, &l_panic___at___00Lean_Elab_partialFixpoint_spec__25___closed__0_once, _init_l_panic___at___00Lean_Elab_partialFixpoint_spec__25___closed__0);
v___x_47548__overap_1362_ = lean_panic_fn_borrowed(v___x_1361_, v_msg_1353_);
lean_inc(v___y_1359_);
lean_inc_ref(v___y_1358_);
lean_inc(v___y_1357_);
lean_inc_ref(v___y_1356_);
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
v___x_1363_ = lean_apply_7(v___x_47548__overap_1362_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, lean_box(0));
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__25___boxed(lean_object* v_msg_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_panic___at___00Lean_Elab_partialFixpoint_spec__25(v_msg_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
return v_res_1372_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1373_; double v___x_1374_; 
v___x_1373_ = lean_unsigned_to_nat(0u);
v___x_1374_ = lean_float_of_nat(v___x_1373_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg(lean_object* v_cls_1378_, lean_object* v_msg_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v_ref_1385_; lean_object* v___x_1386_; lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1432_; 
v_ref_1385_ = lean_ctor_get(v___y_1382_, 5);
v___x_1386_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6_spec__7(v_msg_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1389_ = v___x_1386_;
v_isShared_1390_ = v_isSharedCheck_1432_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1386_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1432_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1391_; lean_object* v_traceState_1392_; lean_object* v_env_1393_; lean_object* v_nextMacroScope_1394_; lean_object* v_ngen_1395_; lean_object* v_auxDeclNGen_1396_; lean_object* v_cache_1397_; lean_object* v_messages_1398_; lean_object* v_infoState_1399_; lean_object* v_snapshotTasks_1400_; lean_object* v_newDecls_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1431_; 
v___x_1391_ = lean_st_ref_take(v___y_1383_);
v_traceState_1392_ = lean_ctor_get(v___x_1391_, 4);
v_env_1393_ = lean_ctor_get(v___x_1391_, 0);
v_nextMacroScope_1394_ = lean_ctor_get(v___x_1391_, 1);
v_ngen_1395_ = lean_ctor_get(v___x_1391_, 2);
v_auxDeclNGen_1396_ = lean_ctor_get(v___x_1391_, 3);
v_cache_1397_ = lean_ctor_get(v___x_1391_, 5);
v_messages_1398_ = lean_ctor_get(v___x_1391_, 6);
v_infoState_1399_ = lean_ctor_get(v___x_1391_, 7);
v_snapshotTasks_1400_ = lean_ctor_get(v___x_1391_, 8);
v_newDecls_1401_ = lean_ctor_get(v___x_1391_, 9);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1403_ = v___x_1391_;
v_isShared_1404_ = v_isSharedCheck_1431_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_newDecls_1401_);
lean_inc(v_snapshotTasks_1400_);
lean_inc(v_infoState_1399_);
lean_inc(v_messages_1398_);
lean_inc(v_cache_1397_);
lean_inc(v_traceState_1392_);
lean_inc(v_auxDeclNGen_1396_);
lean_inc(v_ngen_1395_);
lean_inc(v_nextMacroScope_1394_);
lean_inc(v_env_1393_);
lean_dec(v___x_1391_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1431_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
uint64_t v_tid_1405_; lean_object* v_traces_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1430_; 
v_tid_1405_ = lean_ctor_get_uint64(v_traceState_1392_, sizeof(void*)*1);
v_traces_1406_ = lean_ctor_get(v_traceState_1392_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v_traceState_1392_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1408_ = v_traceState_1392_;
v_isShared_1409_ = v_isSharedCheck_1430_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_traces_1406_);
lean_dec(v_traceState_1392_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1430_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1410_; double v___x_1411_; uint8_t v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1420_; 
v___x_1410_ = lean_box(0);
v___x_1411_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__0);
v___x_1412_ = 0;
v___x_1413_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__1));
v___x_1414_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1414_, 0, v_cls_1378_);
lean_ctor_set(v___x_1414_, 1, v___x_1410_);
lean_ctor_set(v___x_1414_, 2, v___x_1413_);
lean_ctor_set_float(v___x_1414_, sizeof(void*)*3, v___x_1411_);
lean_ctor_set_float(v___x_1414_, sizeof(void*)*3 + 8, v___x_1411_);
lean_ctor_set_uint8(v___x_1414_, sizeof(void*)*3 + 16, v___x_1412_);
v___x_1415_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__2));
v___x_1416_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1414_);
lean_ctor_set(v___x_1416_, 1, v_a_1387_);
lean_ctor_set(v___x_1416_, 2, v___x_1415_);
lean_inc(v_ref_1385_);
v___x_1417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1417_, 0, v_ref_1385_);
lean_ctor_set(v___x_1417_, 1, v___x_1416_);
v___x_1418_ = l_Lean_PersistentArray_push___redArg(v_traces_1406_, v___x_1417_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1418_);
v___x_1420_ = v___x_1408_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1418_);
lean_ctor_set_uint64(v_reuseFailAlloc_1429_, sizeof(void*)*1, v_tid_1405_);
v___x_1420_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
lean_object* v___x_1422_; 
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 4, v___x_1420_);
v___x_1422_ = v___x_1403_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_env_1393_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v_nextMacroScope_1394_);
lean_ctor_set(v_reuseFailAlloc_1428_, 2, v_ngen_1395_);
lean_ctor_set(v_reuseFailAlloc_1428_, 3, v_auxDeclNGen_1396_);
lean_ctor_set(v_reuseFailAlloc_1428_, 4, v___x_1420_);
lean_ctor_set(v_reuseFailAlloc_1428_, 5, v_cache_1397_);
lean_ctor_set(v_reuseFailAlloc_1428_, 6, v_messages_1398_);
lean_ctor_set(v_reuseFailAlloc_1428_, 7, v_infoState_1399_);
lean_ctor_set(v_reuseFailAlloc_1428_, 8, v_snapshotTasks_1400_);
lean_ctor_set(v_reuseFailAlloc_1428_, 9, v_newDecls_1401_);
v___x_1422_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1426_; 
v___x_1423_ = lean_st_ref_set(v___y_1383_, v___x_1422_);
v___x_1424_ = lean_box(0);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1424_);
v___x_1426_ = v___x_1389_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1424_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___boxed(lean_object* v_cls_1433_, lean_object* v_msg_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg(v_cls_1433_, v_msg_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__22___redArg(size_t v_sz_1441_, size_t v_i_1442_, lean_object* v_bs_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
uint8_t v___x_1449_; 
v___x_1449_ = lean_usize_dec_lt(v_i_1442_, v_sz_1441_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1450_; 
v___x_1450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1450_, 0, v_bs_1443_);
return v___x_1450_;
}
else
{
lean_object* v_v_1451_; lean_object* v___x_1452_; 
v_v_1451_ = lean_array_uget_borrowed(v_bs_1443_, v_i_1442_);
lean_inc(v_v_1451_);
v___x_1452_ = l_Lean_Elab_Mutual_cleanPreDef(v_v_1451_, v___x_1449_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v_a_1453_; lean_object* v___x_1454_; lean_object* v_bs_x27_1455_; size_t v___x_1456_; size_t v___x_1457_; lean_object* v___x_1458_; 
v_a_1453_ = lean_ctor_get(v___x_1452_, 0);
lean_inc(v_a_1453_);
lean_dec_ref(v___x_1452_);
v___x_1454_ = lean_unsigned_to_nat(0u);
v_bs_x27_1455_ = lean_array_uset(v_bs_1443_, v_i_1442_, v___x_1454_);
v___x_1456_ = ((size_t)1ULL);
v___x_1457_ = lean_usize_add(v_i_1442_, v___x_1456_);
v___x_1458_ = lean_array_uset(v_bs_x27_1455_, v_i_1442_, v_a_1453_);
v_i_1442_ = v___x_1457_;
v_bs_1443_ = v___x_1458_;
goto _start;
}
else
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
lean_dec_ref(v_bs_1443_);
v_a_1460_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1452_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1452_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__22___redArg___boxed(lean_object* v_sz_1468_, lean_object* v_i_1469_, lean_object* v_bs_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
size_t v_sz_boxed_1476_; size_t v_i_boxed_1477_; lean_object* v_res_1478_; 
v_sz_boxed_1476_ = lean_unbox_usize(v_sz_1468_);
lean_dec(v_sz_1468_);
v_i_boxed_1477_ = lean_unbox_usize(v_i_1469_);
lean_dec(v_i_1469_);
v_res_1478_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__22___redArg(v_sz_boxed_1476_, v_i_boxed_1477_, v_bs_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12___lam__0(lean_object* v_xs_1479_, lean_object* v_inst_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = l_Lean_Meta_mkInstPiOfInstsForall(v_xs_1479_, v_inst_1480_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12___lam__0___boxed(lean_object* v_xs_1489_, lean_object* v_inst_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12___lam__0(v_xs_1489_, v_inst_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12(size_t v_sz_1500_, size_t v_i_1501_, lean_object* v_bs_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
uint8_t v___x_1510_; 
v___x_1510_ = lean_usize_dec_lt(v_i_1501_, v_sz_1500_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1511_; 
v___x_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1511_, 0, v_bs_1502_);
return v___x_1511_;
}
else
{
lean_object* v___f_1512_; lean_object* v_v_1513_; uint8_t v___x_1514_; lean_object* v___x_1515_; 
v___f_1512_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12___closed__0));
v_v_1513_ = lean_array_uget_borrowed(v_bs_1502_, v_i_1501_);
v___x_1514_ = 0;
lean_inc(v_v_1513_);
v___x_1515_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5___redArg(v_v_1513_, v___f_1512_, v___x_1514_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v_a_1516_; lean_object* v___x_1517_; lean_object* v_bs_x27_1518_; size_t v___x_1519_; size_t v___x_1520_; lean_object* v___x_1521_; 
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_a_1516_);
lean_dec_ref(v___x_1515_);
v___x_1517_ = lean_unsigned_to_nat(0u);
v_bs_x27_1518_ = lean_array_uset(v_bs_1502_, v_i_1501_, v___x_1517_);
v___x_1519_ = ((size_t)1ULL);
v___x_1520_ = lean_usize_add(v_i_1501_, v___x_1519_);
v___x_1521_ = lean_array_uset(v_bs_x27_1518_, v_i_1501_, v_a_1516_);
v_i_1501_ = v___x_1520_;
v_bs_1502_ = v___x_1521_;
goto _start;
}
else
{
lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1530_; 
lean_dec_ref(v_bs_1502_);
v_a_1523_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1525_ = v___x_1515_;
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v___x_1515_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
if (v_isShared_1526_ == 0)
{
v___x_1528_ = v___x_1525_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_a_1523_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12___boxed(lean_object* v_sz_1531_, lean_object* v_i_1532_, lean_object* v_bs_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
size_t v_sz_boxed_1541_; size_t v_i_boxed_1542_; lean_object* v_res_1543_; 
v_sz_boxed_1541_ = lean_unbox_usize(v_sz_1531_);
lean_dec(v_sz_1531_);
v_i_boxed_1542_ = lean_unbox_usize(v_i_1532_);
lean_dec(v_i_1532_);
v_res_1543_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12(v_sz_boxed_1541_, v_i_boxed_1542_, v_bs_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__10___redArg(lean_object* v___x_1544_, lean_object* v_fixedArgs_1545_, lean_object* v_as_1546_, lean_object* v_i_1547_, lean_object* v_j_1548_, lean_object* v_bs_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v_zero_1555_; uint8_t v_isZero_1556_; 
v_zero_1555_ = lean_unsigned_to_nat(0u);
v_isZero_1556_ = lean_nat_dec_eq(v_i_1547_, v_zero_1555_);
if (v_isZero_1556_ == 1)
{
lean_object* v___x_1557_; 
lean_dec(v_j_1548_);
lean_dec(v_i_1547_);
lean_dec_ref(v_fixedArgs_1545_);
v___x_1557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1557_, 0, v_bs_1549_);
return v___x_1557_;
}
else
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1558_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1);
v___x_1559_ = lean_array_fget_borrowed(v_as_1546_, v_j_1548_);
v___x_1560_ = lean_array_get_borrowed(v___x_1558_, v___x_1544_, v_j_1548_);
lean_inc_ref(v_fixedArgs_1545_);
lean_inc(v___x_1559_);
lean_inc(v___x_1560_);
v___x_1561_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_1560_, v___x_1559_, v_fixedArgs_1545_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; lean_object* v_one_1563_; lean_object* v_n_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_a_1562_);
lean_dec_ref(v___x_1561_);
v_one_1563_ = lean_unsigned_to_nat(1u);
v_n_1564_ = lean_nat_sub(v_i_1547_, v_one_1563_);
lean_dec(v_i_1547_);
v___x_1565_ = lean_nat_add(v_j_1548_, v_one_1563_);
lean_dec(v_j_1548_);
v___x_1566_ = lean_array_push(v_bs_1549_, v_a_1562_);
v_i_1547_ = v_n_1564_;
v_j_1548_ = v___x_1565_;
v_bs_1549_ = v___x_1566_;
goto _start;
}
else
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
lean_dec_ref(v_bs_1549_);
lean_dec(v_j_1548_);
lean_dec(v_i_1547_);
lean_dec_ref(v_fixedArgs_1545_);
v_a_1568_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1570_ = v___x_1561_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1561_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__10___redArg___boxed(lean_object* v___x_1576_, lean_object* v_fixedArgs_1577_, lean_object* v_as_1578_, lean_object* v_i_1579_, lean_object* v_j_1580_, lean_object* v_bs_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__10___redArg(v___x_1576_, v_fixedArgs_1577_, v_as_1578_, v_i_1579_, v_j_1580_, v_bs_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec_ref(v_as_1578_);
lean_dec_ref(v___x_1576_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11___redArg(lean_object* v___x_1588_, lean_object* v_fixedArgs_1589_, lean_object* v_as_1590_, lean_object* v_i_1591_, lean_object* v_j_1592_, lean_object* v_bs_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v_zero_1599_; uint8_t v_isZero_1600_; 
v_zero_1599_ = lean_unsigned_to_nat(0u);
v_isZero_1600_ = lean_nat_dec_eq(v_i_1591_, v_zero_1599_);
if (v_isZero_1600_ == 1)
{
lean_object* v___x_1601_; 
lean_dec(v_j_1592_);
lean_dec(v_i_1591_);
lean_dec_ref(v_fixedArgs_1589_);
v___x_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1601_, 0, v_bs_1593_);
return v___x_1601_;
}
else
{
lean_object* v___x_1602_; lean_object* v_type_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1602_ = lean_array_fget_borrowed(v_as_1590_, v_j_1592_);
v_type_1603_ = lean_ctor_get(v___x_1602_, 6);
v___x_1604_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1);
v___x_1605_ = lean_array_get_borrowed(v___x_1604_, v___x_1588_, v_j_1592_);
lean_inc_ref(v_fixedArgs_1589_);
lean_inc_ref(v_type_1603_);
lean_inc(v___x_1605_);
v___x_1606_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v___x_1605_, v_type_1603_, v_fixedArgs_1589_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v_a_1607_; lean_object* v_one_1608_; lean_object* v_n_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
v_a_1607_ = lean_ctor_get(v___x_1606_, 0);
lean_inc(v_a_1607_);
lean_dec_ref(v___x_1606_);
v_one_1608_ = lean_unsigned_to_nat(1u);
v_n_1609_ = lean_nat_sub(v_i_1591_, v_one_1608_);
lean_dec(v_i_1591_);
v___x_1610_ = lean_nat_add(v_j_1592_, v_one_1608_);
lean_dec(v_j_1592_);
v___x_1611_ = lean_array_push(v_bs_1593_, v_a_1607_);
v_i_1591_ = v_n_1609_;
v_j_1592_ = v___x_1610_;
v_bs_1593_ = v___x_1611_;
goto _start;
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
lean_dec_ref(v_bs_1593_);
lean_dec(v_j_1592_);
lean_dec(v_i_1591_);
lean_dec_ref(v_fixedArgs_1589_);
v_a_1613_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___x_1606_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1606_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1618_; 
if (v_isShared_1616_ == 0)
{
v___x_1618_ = v___x_1615_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11___redArg___boxed(lean_object* v___x_1621_, lean_object* v_fixedArgs_1622_, lean_object* v_as_1623_, lean_object* v_i_1624_, lean_object* v_j_1625_, lean_object* v_bs_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11___redArg(v___x_1621_, v_fixedArgs_1622_, v_as_1623_, v_i_1624_, v_j_1625_, v_bs_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec_ref(v_as_1623_);
lean_dec_ref(v___x_1621_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__2(lean_object* v___x_1633_, lean_object* v_e_1634_){
_start:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1635_ = l_Lean_indentD(v_e_1634_);
v___x_1636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1633_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__3(lean_object* v___f_1637_, lean_object* v___x_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l_Lean_Meta_Monotonicity_solveMono(v___f_1637_, v___x_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__3___boxed(lean_object* v___f_1645_, lean_object* v___x_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__3(v___f_1645_, v___x_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
return v_res_1652_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9___closed__1(void){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1654_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9___closed__0));
v___x_1655_ = l_Lean_stringToMessageData(v___x_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9(lean_object* v_a_1656_, lean_object* v_a_1657_){
_start:
{
if (lean_obj_tag(v_a_1656_) == 0)
{
lean_object* v___x_1658_; 
v___x_1658_ = l_List_reverse___redArg(v_a_1657_);
return v___x_1658_;
}
else
{
lean_object* v_head_1659_; lean_object* v_tail_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1673_; 
v_head_1659_ = lean_ctor_get(v_a_1656_, 0);
v_tail_1660_ = lean_ctor_get(v_a_1656_, 1);
v_isSharedCheck_1673_ = !lean_is_exclusive(v_a_1656_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1662_ = v_a_1656_;
v_isShared_1663_ = v_isSharedCheck_1673_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_tail_1660_);
lean_inc(v_head_1659_);
lean_dec(v_a_1656_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1673_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1664_; uint8_t v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1670_; 
v___x_1664_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9___closed__1, &l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9___closed__1);
v___x_1665_ = 0;
v___x_1666_ = l_Lean_MessageData_ofConstName(v_head_1659_, v___x_1665_);
v___x_1667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1664_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
v___x_1668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1667_);
lean_ctor_set(v___x_1668_, 1, v___x_1664_);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 1, v_a_1657_);
lean_ctor_set(v___x_1662_, 0, v___x_1668_);
v___x_1670_ = v___x_1662_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1668_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v_a_1657_);
v___x_1670_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
v_a_1656_ = v_tail_1660_;
v_a_1657_ = v___x_1670_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__1));
v___x_1677_ = l_Lean_stringToMessageData(v___x_1676_);
return v___x_1677_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__3));
v___x_1680_ = l_Lean_stringToMessageData(v___x_1679_);
return v___x_1680_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1682_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__5));
v___x_1683_ = l_Lean_stringToMessageData(v___x_1682_);
return v___x_1683_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1686_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__8));
v___x_1687_ = lean_unsigned_to_nat(52u);
v___x_1688_ = lean_unsigned_to_nat(148u);
v___x_1689_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__7));
v___x_1690_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__0));
v___x_1691_ = l_mkPanicMessageWithDecl(v___x_1690_, v___x_1689_, v___x_1688_, v___x_1687_, v___x_1686_);
return v___x_1691_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__11(void){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1693_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__10));
v___x_1694_ = l_Lean_stringToMessageData(v___x_1693_);
return v___x_1694_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__13(void){
_start:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1696_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__12));
v___x_1697_ = l_Lean_stringToMessageData(v___x_1696_);
return v___x_1697_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__15(void){
_start:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1699_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__14));
v___x_1700_ = l_Lean_stringToMessageData(v___x_1699_);
return v___x_1700_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__19(void){
_start:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1707_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__18));
v___x_1708_ = l_Lean_stringToMessageData(v___x_1707_);
return v___x_1708_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__20(void){
_start:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__1));
v___x_1710_ = l_Lean_stringToMessageData(v___x_1709_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0(lean_object* v_monoThms_1711_, lean_object* v_t_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v___y_1719_; lean_object* v___x_1763_; lean_object* v___x_1764_; uint8_t v___x_1765_; 
v___x_1763_ = lean_array_get_size(v_monoThms_1711_);
v___x_1764_ = lean_unsigned_to_nat(0u);
v___x_1765_ = lean_nat_dec_eq(v___x_1763_, v___x_1764_);
if (v___x_1765_ == 0)
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1766_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__13, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__13_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__13);
v___x_1767_ = lean_array_to_list(v_monoThms_1711_);
v___x_1768_ = lean_box(0);
v___x_1769_ = l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9(v___x_1767_, v___x_1768_);
v___x_1770_ = l_Lean_MessageData_andList(v___x_1769_);
v___x_1771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1766_);
lean_ctor_set(v___x_1771_, 1, v___x_1770_);
v___x_1772_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__15, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__15_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__15);
v___x_1773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1771_);
lean_ctor_set(v___x_1773_, 1, v___x_1772_);
v___x_1774_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__17));
v___x_1775_ = l_Lean_MessageData_ofConstName(v___x_1774_, v___x_1765_);
v___x_1776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1773_);
lean_ctor_set(v___x_1776_, 1, v___x_1775_);
v___x_1777_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__19, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__19_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__19);
v___x_1778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1776_);
lean_ctor_set(v___x_1778_, 1, v___x_1777_);
v___y_1719_ = v___x_1778_;
goto v___jp_1718_;
}
else
{
lean_object* v___x_1779_; 
lean_dec_ref(v_monoThms_1711_);
v___x_1779_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__20, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__20_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__20);
v___y_1719_ = v___x_1779_;
goto v___jp_1718_;
}
v___jp_1718_:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1720_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__0));
v___x_1721_ = lean_find_expr(v___x_1720_, v_t_1712_);
if (lean_obj_tag(v___x_1721_) == 1)
{
lean_object* v_val_1722_; lean_object* v___x_1723_; 
v_val_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_val_1722_);
lean_dec_ref(v___x_1721_);
v___x_1723_ = l_Lean_getRecAppSyntax_x3f(v_val_1722_);
lean_dec(v_val_1722_);
if (lean_obj_tag(v___x_1723_) == 1)
{
lean_object* v_val_1724_; lean_object* v_fileName_1725_; lean_object* v_fileMap_1726_; lean_object* v_options_1727_; lean_object* v_currRecDepth_1728_; lean_object* v_maxRecDepth_1729_; lean_object* v_ref_1730_; lean_object* v_currNamespace_1731_; lean_object* v_openDecls_1732_; lean_object* v_initHeartbeats_1733_; lean_object* v_maxHeartbeats_1734_; lean_object* v_quotContext_1735_; lean_object* v_currMacroScope_1736_; uint8_t v_diag_1737_; lean_object* v_cancelTk_x3f_1738_; uint8_t v_suppressElabErrors_1739_; lean_object* v_inheritedTraceOptions_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v_ref_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v_val_1724_ = lean_ctor_get(v___x_1723_, 0);
lean_inc_n(v_val_1724_, 2);
lean_dec_ref(v___x_1723_);
v_fileName_1725_ = lean_ctor_get(v___y_1715_, 0);
v_fileMap_1726_ = lean_ctor_get(v___y_1715_, 1);
v_options_1727_ = lean_ctor_get(v___y_1715_, 2);
v_currRecDepth_1728_ = lean_ctor_get(v___y_1715_, 3);
v_maxRecDepth_1729_ = lean_ctor_get(v___y_1715_, 4);
v_ref_1730_ = lean_ctor_get(v___y_1715_, 5);
v_currNamespace_1731_ = lean_ctor_get(v___y_1715_, 6);
v_openDecls_1732_ = lean_ctor_get(v___y_1715_, 7);
v_initHeartbeats_1733_ = lean_ctor_get(v___y_1715_, 8);
v_maxHeartbeats_1734_ = lean_ctor_get(v___y_1715_, 9);
v_quotContext_1735_ = lean_ctor_get(v___y_1715_, 10);
v_currMacroScope_1736_ = lean_ctor_get(v___y_1715_, 11);
v_diag_1737_ = lean_ctor_get_uint8(v___y_1715_, sizeof(void*)*14);
v_cancelTk_x3f_1738_ = lean_ctor_get(v___y_1715_, 12);
v_suppressElabErrors_1739_ = lean_ctor_get_uint8(v___y_1715_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1740_ = lean_ctor_get(v___y_1715_, 13);
v___x_1741_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__2, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__2_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__2);
v___x_1742_ = l_Lean_MessageData_ofSyntax(v_val_1724_);
v___x_1743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1741_);
lean_ctor_set(v___x_1743_, 1, v___x_1742_);
v___x_1744_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__4, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__4_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__4);
v___x_1745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1743_);
lean_ctor_set(v___x_1745_, 1, v___x_1744_);
v___x_1746_ = l_Lean_indentExpr(v_t_1712_);
v___x_1747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1745_);
lean_ctor_set(v___x_1747_, 1, v___x_1746_);
v___x_1748_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__6, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__6_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__6);
v___x_1749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1747_);
lean_ctor_set(v___x_1749_, 1, v___x_1748_);
v___x_1750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1749_);
lean_ctor_set(v___x_1750_, 1, v___y_1719_);
v_ref_1751_ = l_Lean_replaceRef(v_val_1724_, v_ref_1730_);
lean_dec(v_val_1724_);
lean_inc_ref(v_inheritedTraceOptions_1740_);
lean_inc(v_cancelTk_x3f_1738_);
lean_inc(v_currMacroScope_1736_);
lean_inc(v_quotContext_1735_);
lean_inc(v_maxHeartbeats_1734_);
lean_inc(v_initHeartbeats_1733_);
lean_inc(v_openDecls_1732_);
lean_inc(v_currNamespace_1731_);
lean_inc(v_maxRecDepth_1729_);
lean_inc(v_currRecDepth_1728_);
lean_inc_ref(v_options_1727_);
lean_inc_ref(v_fileMap_1726_);
lean_inc_ref(v_fileName_1725_);
v___x_1752_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1752_, 0, v_fileName_1725_);
lean_ctor_set(v___x_1752_, 1, v_fileMap_1726_);
lean_ctor_set(v___x_1752_, 2, v_options_1727_);
lean_ctor_set(v___x_1752_, 3, v_currRecDepth_1728_);
lean_ctor_set(v___x_1752_, 4, v_maxRecDepth_1729_);
lean_ctor_set(v___x_1752_, 5, v_ref_1751_);
lean_ctor_set(v___x_1752_, 6, v_currNamespace_1731_);
lean_ctor_set(v___x_1752_, 7, v_openDecls_1732_);
lean_ctor_set(v___x_1752_, 8, v_initHeartbeats_1733_);
lean_ctor_set(v___x_1752_, 9, v_maxHeartbeats_1734_);
lean_ctor_set(v___x_1752_, 10, v_quotContext_1735_);
lean_ctor_set(v___x_1752_, 11, v_currMacroScope_1736_);
lean_ctor_set(v___x_1752_, 12, v_cancelTk_x3f_1738_);
lean_ctor_set(v___x_1752_, 13, v_inheritedTraceOptions_1740_);
lean_ctor_set_uint8(v___x_1752_, sizeof(void*)*14, v_diag_1737_);
lean_ctor_set_uint8(v___x_1752_, sizeof(void*)*14 + 1, v_suppressElabErrors_1739_);
v___x_1753_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg(v___x_1750_, v___y_1713_, v___y_1714_, v___x_1752_, v___y_1716_);
lean_dec_ref(v___x_1752_);
return v___x_1753_;
}
else
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
lean_dec(v___x_1723_);
lean_dec_ref(v___y_1719_);
lean_dec_ref(v_t_1712_);
v___x_1754_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__9, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__9_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__9);
v___x_1755_ = l_panic___at___00Lean_Elab_partialFixpoint_spec__8___redArg(v___x_1754_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
return v___x_1755_;
}
}
else
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
lean_dec(v___x_1721_);
v___x_1756_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__11, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__11_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__11);
v___x_1757_ = l_Lean_indentExpr(v_t_1712_);
v___x_1758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1756_);
lean_ctor_set(v___x_1758_, 1, v___x_1757_);
v___x_1759_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__6, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__6_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__6);
v___x_1760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1758_);
lean_ctor_set(v___x_1760_, 1, v___x_1759_);
v___x_1761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1760_);
lean_ctor_set(v___x_1761_, 1, v___y_1719_);
v___x_1762_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg(v___x_1761_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
return v___x_1762_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___boxed(lean_object* v_monoThms_1780_, lean_object* v_t_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0(v_monoThms_1780_, v_t_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__1(lean_object* v_preDefs_1788_, lean_object* v_a_1789_, lean_object* v_fixedArgs_1790_, lean_object* v_00_u03b1_1791_, lean_object* v_f_1792_, lean_object* v_monoThms_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v___f_1799_; lean_object* v___x_1800_; 
v___f_1799_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1799_, 0, v_monoThms_1793_);
v___x_1800_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg(v_preDefs_1788_, v_a_1789_, v_fixedArgs_1790_, v_f_1792_, v___f_1799_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__1___boxed(lean_object* v_preDefs_1801_, lean_object* v_a_1802_, lean_object* v_fixedArgs_1803_, lean_object* v_00_u03b1_1804_, lean_object* v_f_1805_, lean_object* v_monoThms_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__1(v_preDefs_1801_, v_a_1802_, v_fixedArgs_1803_, v_00_u03b1_1804_, v_f_1805_, v_monoThms_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
return v_res_1812_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__1(void){
_start:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1814_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__0));
v___x_1815_ = l_Lean_stringToMessageData(v___x_1814_);
return v___x_1815_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__3(void){
_start:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1817_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__2));
v___x_1818_ = l_Lean_stringToMessageData(v___x_1817_);
return v___x_1818_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10(void){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1829_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7));
v___x_1830_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__9));
v___x_1831_ = l_Lean_Name_append(v___x_1830_, v___x_1829_);
return v___x_1831_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__12(void){
_start:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1833_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__11));
v___x_1834_ = l_Lean_stringToMessageData(v___x_1833_);
return v___x_1834_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__14(void){
_start:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1836_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__13));
v___x_1837_ = l_Lean_stringToMessageData(v___x_1836_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg(lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_hints_1843_, lean_object* v_preDefs_1844_, lean_object* v_a_1845_, lean_object* v_fixedArgs_1846_, lean_object* v_as_1847_, lean_object* v_i_1848_, lean_object* v_j_1849_, lean_object* v_bs_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v_zero_1858_; uint8_t v_isZero_1859_; 
v_zero_1858_ = lean_unsigned_to_nat(0u);
v_isZero_1859_ = lean_nat_dec_eq(v_i_1848_, v_zero_1858_);
if (v_isZero_1859_ == 1)
{
lean_object* v___x_1860_; 
lean_dec(v_j_1849_);
lean_dec(v_i_1848_);
lean_dec_ref(v_fixedArgs_1846_);
lean_dec_ref(v_a_1845_);
lean_dec_ref(v_preDefs_1844_);
lean_dec_ref(v_a_1842_);
lean_dec_ref(v_a_1841_);
v___x_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1860_, 0, v_bs_1850_);
return v___x_1860_;
}
else
{
lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1861_ = l_Lean_instInhabitedExpr;
v___x_1862_ = lean_array_get_borrowed(v___x_1861_, v_a_1838_, v_j_1849_);
v___x_1863_ = lean_array_get_borrowed(v___x_1861_, v_a_1839_, v_j_1849_);
lean_inc(v___x_1862_);
v___x_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1862_);
lean_inc_ref(v___x_1864_);
lean_inc(v___x_1863_);
v___x_1865_ = l_Lean_Meta_toPartialOrder(v___x_1863_, v___x_1864_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v_a_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc(v_a_1866_);
lean_dec_ref(v___x_1865_);
v___x_1867_ = lean_array_get_borrowed(v___x_1861_, v_a_1840_, v_j_1849_);
v___x_1868_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__5));
lean_inc_ref(v_a_1841_);
v___x_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1869_, 0, v_a_1841_);
lean_inc_ref(v_a_1842_);
v___x_1870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1870_, 0, v_a_1842_);
v___x_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1871_, 0, v_a_1866_);
lean_inc(v___x_1867_);
v___x_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1867_);
v___x_1873_ = lean_unsigned_to_nat(5u);
v___x_1874_ = lean_mk_empty_array_with_capacity(v___x_1873_);
v___x_1875_ = lean_array_push(v___x_1874_, v___x_1869_);
v___x_1876_ = lean_array_push(v___x_1875_, v___x_1870_);
v___x_1877_ = lean_array_push(v___x_1876_, v___x_1864_);
v___x_1878_ = lean_array_push(v___x_1877_, v___x_1871_);
v___x_1879_ = lean_array_push(v___x_1878_, v___x_1872_);
v___x_1880_ = l_Lean_Meta_mkAppOptM(v___x_1868_, v___x_1879_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v_term_x3f_1884_; lean_object* v_one_1885_; lean_object* v_n_1886_; lean_object* v_a_1888_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
lean_inc(v_a_1881_);
lean_dec_ref(v___x_1880_);
v___x_1882_ = l_Lean_Elab_instInhabitedPartialFixpoint_default;
v___x_1883_ = lean_array_get_borrowed(v___x_1882_, v_hints_1843_, v_j_1849_);
v_term_x3f_1884_ = lean_ctor_get(v___x_1883_, 1);
lean_inc(v_term_x3f_1884_);
v_one_1885_ = lean_unsigned_to_nat(1u);
v_n_1886_ = lean_nat_sub(v_i_1848_, v_one_1885_);
lean_dec(v_i_1848_);
if (lean_obj_tag(v_term_x3f_1884_) == 1)
{
lean_object* v_val_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1950_; 
v_val_1892_ = lean_ctor_get(v_term_x3f_1884_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v_term_x3f_1884_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1894_ = v_term_x3f_1884_;
v_isShared_1895_ = v_isSharedCheck_1950_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_val_1892_);
lean_dec(v_term_x3f_1884_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1950_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
uint8_t v___x_1896_; lean_object* v___x_1898_; 
v___x_1896_ = 1;
lean_inc(v_a_1881_);
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 0, v_a_1881_);
v___x_1898_ = v___x_1894_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1881_);
v___x_1898_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; uint8_t v___x_1903_; lean_object* v___x_1904_; 
v___x_1899_ = lean_box(0);
v___x_1900_ = lean_box(v___x_1896_);
v___x_1901_ = lean_box(v___x_1896_);
v___x_1902_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_1902_, 0, v_val_1892_);
lean_closure_set(v___x_1902_, 1, v___x_1898_);
lean_closure_set(v___x_1902_, 2, v___x_1900_);
lean_closure_set(v___x_1902_, 3, v___x_1901_);
lean_closure_set(v___x_1902_, 4, v___x_1899_);
v___x_1903_ = 1;
v___x_1904_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_1902_, v___x_1903_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1906_; lean_object* v_a_1907_; lean_object* v___x_1908_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
lean_inc(v_a_1905_);
lean_dec_ref(v___x_1904_);
v___x_1906_ = l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18___redArg(v_a_1905_, v___y_1854_);
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
lean_inc_n(v_a_1907_, 2);
lean_dec_ref(v___x_1906_);
v___x_1908_ = l_Lean_Meta_getMVars(v_a_1907_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; lean_object* v___x_1910_; uint8_t v___x_1911_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_a_1909_);
lean_dec_ref(v___x_1908_);
v___x_1910_ = lean_array_get_size(v_a_1909_);
v___x_1911_ = lean_nat_dec_eq(v___x_1910_, v_zero_1858_);
if (v___x_1911_ == 0)
{
lean_object* v___x_1912_; 
lean_dec(v_a_1907_);
v___x_1912_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_1909_, v___x_1899_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
lean_dec(v_a_1909_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v___x_1913_; 
lean_dec_ref(v___x_1912_);
lean_inc(v_a_1881_);
v___x_1913_ = l_Lean_Meta_mkSorry(v_a_1881_, v___x_1896_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v___x_1915_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_a_1914_);
lean_dec_ref(v___x_1913_);
v___x_1915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1915_, 0, v_a_1881_);
lean_ctor_set(v___x_1915_, 1, v_a_1914_);
v_a_1888_ = v___x_1915_;
goto v___jp_1887_;
}
else
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1923_; 
lean_dec(v_n_1886_);
lean_dec(v_a_1881_);
lean_dec_ref(v_bs_1850_);
lean_dec(v_j_1849_);
lean_dec_ref(v_fixedArgs_1846_);
lean_dec_ref(v_a_1845_);
lean_dec_ref(v_preDefs_1844_);
lean_dec_ref(v_a_1842_);
lean_dec_ref(v_a_1841_);
v_a_1916_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1918_ = v___x_1913_;
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1913_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1919_ == 0)
{
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1916_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
else
{
lean_object* v_a_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1931_; 
lean_dec(v_n_1886_);
lean_dec(v_a_1881_);
lean_dec_ref(v_bs_1850_);
lean_dec(v_j_1849_);
lean_dec_ref(v_fixedArgs_1846_);
lean_dec_ref(v_a_1845_);
lean_dec_ref(v_preDefs_1844_);
lean_dec_ref(v_a_1842_);
lean_dec_ref(v_a_1841_);
v_a_1924_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1926_ = v___x_1912_;
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_a_1924_);
lean_dec(v___x_1912_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1929_; 
if (v_isShared_1927_ == 0)
{
v___x_1929_ = v___x_1926_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_a_1924_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
}
else
{
lean_object* v___x_1932_; 
lean_dec(v_a_1909_);
v___x_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1932_, 0, v_a_1881_);
lean_ctor_set(v___x_1932_, 1, v_a_1907_);
v_a_1888_ = v___x_1932_;
goto v___jp_1887_;
}
}
else
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
lean_dec(v_a_1907_);
lean_dec(v_n_1886_);
lean_dec(v_a_1881_);
lean_dec_ref(v_bs_1850_);
lean_dec(v_j_1849_);
lean_dec_ref(v_fixedArgs_1846_);
lean_dec_ref(v_a_1845_);
lean_dec_ref(v_preDefs_1844_);
lean_dec_ref(v_a_1842_);
lean_dec_ref(v_a_1841_);
v_a_1933_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1908_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1908_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
lean_dec(v_n_1886_);
lean_dec(v_a_1881_);
lean_dec_ref(v_bs_1850_);
lean_dec(v_j_1849_);
lean_dec_ref(v_fixedArgs_1846_);
lean_dec_ref(v_a_1845_);
lean_dec_ref(v_preDefs_1844_);
lean_dec_ref(v_a_1842_);
lean_dec_ref(v_a_1841_);
v_a_1941_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1904_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1904_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
}
}
else
{
lean_object* v___x_1951_; lean_object* v___x_1952_; 
lean_dec(v_term_x3f_1884_);
v___x_1951_ = lean_box(0);
lean_inc(v_a_1881_);
v___x_1952_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1881_, v___x_1951_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v_a_1953_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___x_1964_; lean_object* v_declName_1965_; lean_object* v___f_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___f_1972_; lean_object* v___x_1973_; lean_object* v___f_1974_; lean_object* v___x_1975_; 
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_a_1953_);
lean_dec_ref(v___x_1952_);
v___x_1964_ = lean_array_fget_borrowed(v_as_1847_, v_j_1849_);
v_declName_1965_ = lean_ctor_get(v___x_1964_, 3);
lean_inc_ref(v_fixedArgs_1846_);
lean_inc_ref(v_a_1845_);
lean_inc_ref(v_preDefs_1844_);
v___f_1966_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__1___boxed), 11, 3);
lean_closure_set(v___f_1966_, 0, v_preDefs_1844_);
lean_closure_set(v___f_1966_, 1, v_a_1845_);
lean_closure_set(v___f_1966_, 2, v_fixedArgs_1846_);
v___x_1967_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__1, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__1_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__1);
lean_inc(v_declName_1965_);
v___x_1968_ = l_Lean_MessageData_ofName(v_declName_1965_);
lean_inc_ref(v___x_1968_);
v___x_1969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1967_);
lean_ctor_set(v___x_1969_, 1, v___x_1968_);
v___x_1970_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__3, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__3_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__3);
v___x_1971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1969_);
lean_ctor_set(v___x_1971_, 1, v___x_1970_);
v___f_1972_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__2), 2, 1);
lean_closure_set(v___f_1972_, 0, v___x_1971_);
v___x_1973_ = l_Lean_Expr_mvarId_x21(v_a_1953_);
v___f_1974_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__3___boxed), 7, 2);
lean_closure_set(v___f_1974_, 0, v___f_1966_);
lean_closure_set(v___f_1974_, 1, v___x_1973_);
v___x_1975_ = l_Lean_Meta_mapErrorImp___redArg(v___f_1974_, v___f_1972_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
if (lean_obj_tag(v___x_1975_) == 0)
{
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v_options_1976_; uint8_t v_hasTrace_1977_; 
lean_dec_ref(v___x_1975_);
v_options_1976_ = lean_ctor_get(v___y_1855_, 2);
v_hasTrace_1977_ = lean_ctor_get_uint8(v_options_1976_, sizeof(void*)*1);
if (v_hasTrace_1977_ == 0)
{
lean_dec_ref(v___x_1968_);
v___y_1955_ = v___y_1851_;
v___y_1956_ = v___y_1852_;
v___y_1957_ = v___y_1853_;
v___y_1958_ = v___y_1854_;
v___y_1959_ = v___y_1855_;
v___y_1960_ = v___y_1856_;
goto v___jp_1954_;
}
else
{
lean_object* v_inheritedTraceOptions_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; uint8_t v___x_1981_; 
v_inheritedTraceOptions_1978_ = lean_ctor_get(v___y_1855_, 13);
v___x_1979_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7));
v___x_1980_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10);
v___x_1981_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1978_, v_options_1976_, v___x_1980_);
if (v___x_1981_ == 0)
{
lean_dec_ref(v___x_1968_);
v___y_1955_ = v___y_1851_;
v___y_1956_ = v___y_1852_;
v___y_1957_ = v___y_1853_;
v___y_1958_ = v___y_1854_;
v___y_1959_ = v___y_1855_;
v___y_1960_ = v___y_1856_;
goto v___jp_1954_;
}
else
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1982_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__12, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__12_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__12);
v___x_1983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1982_);
lean_ctor_set(v___x_1983_, 1, v___x_1968_);
v___x_1984_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__14, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__14_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__14);
v___x_1985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1983_);
lean_ctor_set(v___x_1985_, 1, v___x_1984_);
lean_inc(v_a_1953_);
v___x_1986_ = l_Lean_MessageData_ofExpr(v_a_1953_);
v___x_1987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1985_);
lean_ctor_set(v___x_1987_, 1, v___x_1986_);
v___x_1988_ = l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg(v___x_1979_, v___x_1987_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_dec_ref(v___x_1988_);
v___y_1955_ = v___y_1851_;
v___y_1956_ = v___y_1852_;
v___y_1957_ = v___y_1853_;
v___y_1958_ = v___y_1854_;
v___y_1959_ = v___y_1855_;
v___y_1960_ = v___y_1856_;
goto v___jp_1954_;
}
else
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_1996_; 
lean_dec(v_a_1953_);
lean_dec(v_n_1886_);
lean_dec(v_a_1881_);
lean_dec_ref(v_bs_1850_);
lean_dec(v_j_1849_);
lean_dec_ref(v_fixedArgs_1846_);
lean_dec_ref(v_a_1845_);
lean_dec_ref(v_preDefs_1844_);
lean_dec_ref(v_a_1842_);
lean_dec_ref(v_a_1841_);
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1991_ = v___x_1988_;
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1988_);
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
}
else
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2004_; 
lean_dec_ref(v___x_1968_);
lean_dec(v_a_1953_);
lean_dec(v_n_1886_);
lean_dec(v_a_1881_);
lean_dec_ref(v_bs_1850_);
lean_dec(v_j_1849_);
lean_dec_ref(v_fixedArgs_1846_);
lean_dec_ref(v_a_1845_);
lean_dec_ref(v_preDefs_1844_);
lean_dec_ref(v_a_1842_);
lean_dec_ref(v_a_1841_);
v_a_1997_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1999_ = v___x_1975_;
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1975_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
if (v_isShared_2000_ == 0)
{
lean_ctor_set_tag(v___x_1999_, 1);
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
else
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2012_; 
lean_dec_ref(v___x_1968_);
lean_dec(v_a_1953_);
lean_dec(v_n_1886_);
lean_dec(v_a_1881_);
lean_dec_ref(v_bs_1850_);
lean_dec(v_j_1849_);
lean_dec_ref(v_fixedArgs_1846_);
lean_dec_ref(v_a_1845_);
lean_dec_ref(v_preDefs_1844_);
lean_dec_ref(v_a_1842_);
lean_dec_ref(v_a_1841_);
v_a_2005_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2007_ = v___x_1975_;
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_1975_);
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
v___jp_1954_:
{
lean_object* v___x_1961_; lean_object* v_a_1962_; lean_object* v___x_1963_; 
v___x_1961_ = l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18___redArg(v_a_1953_, v___y_1958_);
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
lean_inc(v_a_1962_);
lean_dec_ref(v___x_1961_);
v___x_1963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1963_, 0, v_a_1881_);
lean_ctor_set(v___x_1963_, 1, v_a_1962_);
v_a_1888_ = v___x_1963_;
goto v___jp_1887_;
}
}
else
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
lean_dec(v_n_1886_);
lean_dec(v_a_1881_);
lean_dec_ref(v_bs_1850_);
lean_dec(v_j_1849_);
lean_dec_ref(v_fixedArgs_1846_);
lean_dec_ref(v_a_1845_);
lean_dec_ref(v_preDefs_1844_);
lean_dec_ref(v_a_1842_);
lean_dec_ref(v_a_1841_);
v_a_2013_ = lean_ctor_get(v___x_1952_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_1952_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_1952_);
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
v___jp_1887_:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1889_ = lean_nat_add(v_j_1849_, v_one_1885_);
lean_dec(v_j_1849_);
v___x_1890_ = lean_array_push(v_bs_1850_, v_a_1888_);
v_i_1848_ = v_n_1886_;
v_j_1849_ = v___x_1889_;
v_bs_1850_ = v___x_1890_;
goto _start;
}
}
else
{
lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2028_; 
lean_dec_ref(v_bs_1850_);
lean_dec(v_j_1849_);
lean_dec(v_i_1848_);
lean_dec_ref(v_fixedArgs_1846_);
lean_dec_ref(v_a_1845_);
lean_dec_ref(v_preDefs_1844_);
lean_dec_ref(v_a_1842_);
lean_dec_ref(v_a_1841_);
v_a_2021_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2023_ = v___x_1880_;
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_dec(v___x_1880_);
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
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_dec_ref(v___x_1864_);
lean_dec_ref(v_bs_1850_);
lean_dec(v_j_1849_);
lean_dec(v_i_1848_);
lean_dec_ref(v_fixedArgs_1846_);
lean_dec_ref(v_a_1845_);
lean_dec_ref(v_preDefs_1844_);
lean_dec_ref(v_a_1842_);
lean_dec_ref(v_a_1841_);
v_a_2029_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_1865_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_1865_);
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
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___boxed(lean_object** _args){
lean_object* v_a_2037_ = _args[0];
lean_object* v_a_2038_ = _args[1];
lean_object* v_a_2039_ = _args[2];
lean_object* v_a_2040_ = _args[3];
lean_object* v_a_2041_ = _args[4];
lean_object* v_hints_2042_ = _args[5];
lean_object* v_preDefs_2043_ = _args[6];
lean_object* v_a_2044_ = _args[7];
lean_object* v_fixedArgs_2045_ = _args[8];
lean_object* v_as_2046_ = _args[9];
lean_object* v_i_2047_ = _args[10];
lean_object* v_j_2048_ = _args[11];
lean_object* v_bs_2049_ = _args[12];
lean_object* v___y_2050_ = _args[13];
lean_object* v___y_2051_ = _args[14];
lean_object* v___y_2052_ = _args[15];
lean_object* v___y_2053_ = _args[16];
lean_object* v___y_2054_ = _args[17];
lean_object* v___y_2055_ = _args[18];
lean_object* v___y_2056_ = _args[19];
_start:
{
lean_object* v_res_2057_; 
v_res_2057_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg(v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_hints_2042_, v_preDefs_2043_, v_a_2044_, v_fixedArgs_2045_, v_as_2046_, v_i_2047_, v_j_2048_, v_bs_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec_ref(v_as_2046_);
lean_dec_ref(v_hints_2042_);
lean_dec_ref(v_a_2039_);
lean_dec_ref(v_a_2038_);
lean_dec_ref(v_a_2037_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19(lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_hints_2063_, lean_object* v_preDefs_2064_, lean_object* v_a_2065_, lean_object* v_fixedArgs_2066_, lean_object* v_as_2067_, lean_object* v_i_2068_, lean_object* v_j_2069_, lean_object* v_inv_2070_, lean_object* v_bs_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
lean_object* v___x_2079_; 
v___x_2079_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg(v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_hints_2063_, v_preDefs_2064_, v_a_2065_, v_fixedArgs_2066_, v_as_2067_, v_i_2068_, v_j_2069_, v_bs_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
return v___x_2079_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___boxed(lean_object** _args){
lean_object* v_a_2080_ = _args[0];
lean_object* v_a_2081_ = _args[1];
lean_object* v_a_2082_ = _args[2];
lean_object* v_a_2083_ = _args[3];
lean_object* v_a_2084_ = _args[4];
lean_object* v_hints_2085_ = _args[5];
lean_object* v_preDefs_2086_ = _args[6];
lean_object* v_a_2087_ = _args[7];
lean_object* v_fixedArgs_2088_ = _args[8];
lean_object* v_as_2089_ = _args[9];
lean_object* v_i_2090_ = _args[10];
lean_object* v_j_2091_ = _args[11];
lean_object* v_inv_2092_ = _args[12];
lean_object* v_bs_2093_ = _args[13];
lean_object* v___y_2094_ = _args[14];
lean_object* v___y_2095_ = _args[15];
lean_object* v___y_2096_ = _args[16];
lean_object* v___y_2097_ = _args[17];
lean_object* v___y_2098_ = _args[18];
lean_object* v___y_2099_ = _args[19];
lean_object* v___y_2100_ = _args[20];
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19(v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_hints_2085_, v_preDefs_2086_, v_a_2087_, v_fixedArgs_2088_, v_as_2089_, v_i_2090_, v_j_2091_, v_inv_2092_, v_bs_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec_ref(v_as_2089_);
lean_dec_ref(v_hints_2085_);
lean_dec_ref(v_a_2082_);
lean_dec_ref(v_a_2081_);
lean_dec_ref(v_a_2080_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg___lam__0(lean_object* v___x_2102_, lean_object* v___x_2103_, lean_object* v___y_2104_, lean_object* v___x_2105_, lean_object* v_j_2106_, lean_object* v_a_2107_, uint8_t v_isZero_2108_, uint8_t v___x_2109_, uint8_t v___x_2110_, lean_object* v_ref_2111_, uint8_t v_kind_2112_, lean_object* v_levelParams_2113_, lean_object* v_modifiers_2114_, lean_object* v_declName_2115_, lean_object* v_binders_2116_, lean_object* v_numSectionVars_2117_, lean_object* v_type_2118_, lean_object* v_termination_2119_, lean_object* v_params_2120_, lean_object* v_x_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2129_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v___x_2102_, v_params_2120_);
v___x_2130_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v___x_2102_, v_params_2120_);
v___x_2131_ = lean_box(0);
v___x_2132_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__0(v___x_2103_, v___x_2131_);
v___x_2133_ = l_Lean_mkConst(v___y_2104_, v___x_2132_);
v___x_2134_ = l_Lean_mkAppN(v___x_2133_, v___x_2129_);
lean_dec_ref(v___x_2129_);
v___x_2135_ = l_Lean_Meta_PProdN_proj(v___x_2105_, v_j_2106_, v_a_2107_, v___x_2134_);
v___x_2136_ = l_Lean_mkAppN(v___x_2135_, v___x_2130_);
lean_dec_ref(v___x_2130_);
v___x_2137_ = l_Lean_Meta_mkLambdaFVars(v_params_2120_, v___x_2136_, v_isZero_2108_, v___x_2109_, v___x_2109_, v___x_2109_, v___x_2110_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2146_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2140_ = v___x_2137_;
v_isShared_2141_ = v_isSharedCheck_2146_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2137_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2146_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2142_; lean_object* v___x_2144_; 
v___x_2142_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_2142_, 0, v_ref_2111_);
lean_ctor_set(v___x_2142_, 1, v_levelParams_2113_);
lean_ctor_set(v___x_2142_, 2, v_modifiers_2114_);
lean_ctor_set(v___x_2142_, 3, v_declName_2115_);
lean_ctor_set(v___x_2142_, 4, v_binders_2116_);
lean_ctor_set(v___x_2142_, 5, v_numSectionVars_2117_);
lean_ctor_set(v___x_2142_, 6, v_type_2118_);
lean_ctor_set(v___x_2142_, 7, v_a_2138_);
lean_ctor_set(v___x_2142_, 8, v_termination_2119_);
lean_ctor_set_uint8(v___x_2142_, sizeof(void*)*9, v_kind_2112_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 0, v___x_2142_);
v___x_2144_ = v___x_2140_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2142_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
else
{
lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2154_; 
lean_dec_ref(v_termination_2119_);
lean_dec_ref(v_type_2118_);
lean_dec(v_numSectionVars_2117_);
lean_dec(v_binders_2116_);
lean_dec(v_declName_2115_);
lean_dec_ref(v_modifiers_2114_);
lean_dec(v_levelParams_2113_);
lean_dec(v_ref_2111_);
v_a_2147_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2149_ = v___x_2137_;
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_dec(v___x_2137_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2152_; 
if (v_isShared_2150_ == 0)
{
v___x_2152_ = v___x_2149_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_a_2147_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_2155_ = _args[0];
lean_object* v___x_2156_ = _args[1];
lean_object* v___y_2157_ = _args[2];
lean_object* v___x_2158_ = _args[3];
lean_object* v_j_2159_ = _args[4];
lean_object* v_a_2160_ = _args[5];
lean_object* v_isZero_2161_ = _args[6];
lean_object* v___x_2162_ = _args[7];
lean_object* v___x_2163_ = _args[8];
lean_object* v_ref_2164_ = _args[9];
lean_object* v_kind_2165_ = _args[10];
lean_object* v_levelParams_2166_ = _args[11];
lean_object* v_modifiers_2167_ = _args[12];
lean_object* v_declName_2168_ = _args[13];
lean_object* v_binders_2169_ = _args[14];
lean_object* v_numSectionVars_2170_ = _args[15];
lean_object* v_type_2171_ = _args[16];
lean_object* v_termination_2172_ = _args[17];
lean_object* v_params_2173_ = _args[18];
lean_object* v_x_2174_ = _args[19];
lean_object* v___y_2175_ = _args[20];
lean_object* v___y_2176_ = _args[21];
lean_object* v___y_2177_ = _args[22];
lean_object* v___y_2178_ = _args[23];
lean_object* v___y_2179_ = _args[24];
lean_object* v___y_2180_ = _args[25];
lean_object* v___y_2181_ = _args[26];
_start:
{
uint8_t v_isZero_boxed_2182_; uint8_t v___x_57057__boxed_2183_; uint8_t v___x_57058__boxed_2184_; uint8_t v_kind_boxed_2185_; lean_object* v_res_2186_; 
v_isZero_boxed_2182_ = lean_unbox(v_isZero_2161_);
v___x_57057__boxed_2183_ = lean_unbox(v___x_2162_);
v___x_57058__boxed_2184_ = lean_unbox(v___x_2163_);
v_kind_boxed_2185_ = lean_unbox(v_kind_2165_);
v_res_2186_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg___lam__0(v___x_2155_, v___x_2156_, v___y_2157_, v___x_2158_, v_j_2159_, v_a_2160_, v_isZero_boxed_2182_, v___x_57057__boxed_2183_, v___x_57058__boxed_2184_, v_ref_2164_, v_kind_boxed_2185_, v_levelParams_2166_, v_modifiers_2167_, v_declName_2168_, v_binders_2169_, v_numSectionVars_2170_, v_type_2171_, v_termination_2172_, v_params_2173_, v_x_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
lean_dec_ref(v_x_2174_);
lean_dec_ref(v_params_2173_);
lean_dec(v_j_2159_);
lean_dec(v___x_2158_);
lean_dec_ref(v___x_2155_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg(lean_object* v___x_2187_, lean_object* v___x_2188_, lean_object* v___y_2189_, lean_object* v___x_2190_, lean_object* v_a_2191_, lean_object* v_as_2192_, lean_object* v_i_2193_, lean_object* v_j_2194_, lean_object* v_bs_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v_zero_2203_; uint8_t v_isZero_2204_; 
v_zero_2203_ = lean_unsigned_to_nat(0u);
v_isZero_2204_ = lean_nat_dec_eq(v_i_2193_, v_zero_2203_);
if (v_isZero_2204_ == 1)
{
lean_object* v___x_2205_; 
lean_dec(v_j_2194_);
lean_dec(v_i_2193_);
lean_dec_ref(v_a_2191_);
lean_dec(v___x_2190_);
lean_dec(v___y_2189_);
lean_dec(v___x_2188_);
v___x_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2205_, 0, v_bs_2195_);
return v___x_2205_;
}
else
{
lean_object* v___x_2206_; lean_object* v_ref_2207_; uint8_t v_kind_2208_; lean_object* v_levelParams_2209_; lean_object* v_modifiers_2210_; lean_object* v_declName_2211_; lean_object* v_binders_2212_; lean_object* v_numSectionVars_2213_; lean_object* v_type_2214_; lean_object* v_termination_2215_; lean_object* v___x_2216_; uint8_t v___x_2217_; uint8_t v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___f_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2206_ = lean_array_fget_borrowed(v_as_2192_, v_j_2194_);
v_ref_2207_ = lean_ctor_get(v___x_2206_, 0);
v_kind_2208_ = lean_ctor_get_uint8(v___x_2206_, sizeof(void*)*9);
v_levelParams_2209_ = lean_ctor_get(v___x_2206_, 1);
v_modifiers_2210_ = lean_ctor_get(v___x_2206_, 2);
v_declName_2211_ = lean_ctor_get(v___x_2206_, 3);
v_binders_2212_ = lean_ctor_get(v___x_2206_, 4);
v_numSectionVars_2213_ = lean_ctor_get(v___x_2206_, 5);
v_type_2214_ = lean_ctor_get(v___x_2206_, 6);
v_termination_2215_ = lean_ctor_get(v___x_2206_, 8);
v___x_2216_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1);
v___x_2217_ = 1;
v___x_2218_ = 1;
v___x_2219_ = lean_array_get_borrowed(v___x_2216_, v___x_2187_, v_j_2194_);
v___x_2220_ = lean_box(v_isZero_2204_);
v___x_2221_ = lean_box(v___x_2217_);
v___x_2222_ = lean_box(v___x_2218_);
v___x_2223_ = lean_box(v_kind_2208_);
lean_inc_ref(v_termination_2215_);
lean_inc_ref_n(v_type_2214_, 2);
lean_inc(v_numSectionVars_2213_);
lean_inc(v_binders_2212_);
lean_inc(v_declName_2211_);
lean_inc_ref(v_modifiers_2210_);
lean_inc(v_levelParams_2209_);
lean_inc(v_ref_2207_);
lean_inc_ref(v_a_2191_);
lean_inc(v_j_2194_);
lean_inc(v___x_2190_);
lean_inc(v___y_2189_);
lean_inc(v___x_2188_);
lean_inc(v___x_2219_);
v___f_2224_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg___lam__0___boxed), 27, 18);
lean_closure_set(v___f_2224_, 0, v___x_2219_);
lean_closure_set(v___f_2224_, 1, v___x_2188_);
lean_closure_set(v___f_2224_, 2, v___y_2189_);
lean_closure_set(v___f_2224_, 3, v___x_2190_);
lean_closure_set(v___f_2224_, 4, v_j_2194_);
lean_closure_set(v___f_2224_, 5, v_a_2191_);
lean_closure_set(v___f_2224_, 6, v___x_2220_);
lean_closure_set(v___f_2224_, 7, v___x_2221_);
lean_closure_set(v___f_2224_, 8, v___x_2222_);
lean_closure_set(v___f_2224_, 9, v_ref_2207_);
lean_closure_set(v___f_2224_, 10, v___x_2223_);
lean_closure_set(v___f_2224_, 11, v_levelParams_2209_);
lean_closure_set(v___f_2224_, 12, v_modifiers_2210_);
lean_closure_set(v___f_2224_, 13, v_declName_2211_);
lean_closure_set(v___f_2224_, 14, v_binders_2212_);
lean_closure_set(v___f_2224_, 15, v_numSectionVars_2213_);
lean_closure_set(v___f_2224_, 16, v_type_2214_);
lean_closure_set(v___f_2224_, 17, v_termination_2215_);
v___x_2225_ = lean_array_get_size(v___x_2219_);
v___x_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2225_);
v___x_2227_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__20___redArg(v_type_2214_, v___x_2226_, v___f_2224_, v_isZero_2204_, v_isZero_2204_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v_a_2228_; lean_object* v_one_2229_; lean_object* v_n_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v_a_2228_ = lean_ctor_get(v___x_2227_, 0);
lean_inc(v_a_2228_);
lean_dec_ref(v___x_2227_);
v_one_2229_ = lean_unsigned_to_nat(1u);
v_n_2230_ = lean_nat_sub(v_i_2193_, v_one_2229_);
lean_dec(v_i_2193_);
v___x_2231_ = lean_nat_add(v_j_2194_, v_one_2229_);
lean_dec(v_j_2194_);
v___x_2232_ = lean_array_push(v_bs_2195_, v_a_2228_);
v_i_2193_ = v_n_2230_;
v_j_2194_ = v___x_2231_;
v_bs_2195_ = v___x_2232_;
goto _start;
}
else
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2241_; 
lean_dec_ref(v_bs_2195_);
lean_dec(v_j_2194_);
lean_dec(v_i_2193_);
lean_dec_ref(v_a_2191_);
lean_dec(v___x_2190_);
lean_dec(v___y_2189_);
lean_dec(v___x_2188_);
v_a_2234_ = lean_ctor_get(v___x_2227_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2236_ = v___x_2227_;
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v___x_2227_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_a_2234_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg___boxed(lean_object* v___x_2242_, lean_object* v___x_2243_, lean_object* v___y_2244_, lean_object* v___x_2245_, lean_object* v_a_2246_, lean_object* v_as_2247_, lean_object* v_i_2248_, lean_object* v_j_2249_, lean_object* v_bs_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg(v___x_2242_, v___x_2243_, v___y_2244_, v___x_2245_, v_a_2246_, v_as_2247_, v_i_2248_, v_j_2249_, v_bs_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec_ref(v_as_2247_);
lean_dec_ref(v___x_2242_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__23(size_t v_sz_2259_, size_t v_i_2260_, lean_object* v_bs_2261_){
_start:
{
uint8_t v___x_2262_; 
v___x_2262_ = lean_usize_dec_lt(v_i_2260_, v_sz_2259_);
if (v___x_2262_ == 0)
{
return v_bs_2261_;
}
else
{
lean_object* v_v_2263_; uint8_t v_fixpointType_2264_; lean_object* v___x_2265_; lean_object* v_bs_x27_2266_; size_t v___x_2267_; size_t v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
v_v_2263_ = lean_array_uget_borrowed(v_bs_2261_, v_i_2260_);
v_fixpointType_2264_ = lean_ctor_get_uint8(v_v_2263_, sizeof(void*)*2);
v___x_2265_ = lean_unsigned_to_nat(0u);
v_bs_x27_2266_ = lean_array_uset(v_bs_2261_, v_i_2260_, v___x_2265_);
v___x_2267_ = ((size_t)1ULL);
v___x_2268_ = lean_usize_add(v_i_2260_, v___x_2267_);
v___x_2269_ = lean_box(v_fixpointType_2264_);
v___x_2270_ = lean_array_uset(v_bs_x27_2266_, v_i_2260_, v___x_2269_);
v_i_2260_ = v___x_2268_;
v_bs_2261_ = v___x_2270_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__23___boxed(lean_object* v_sz_2272_, lean_object* v_i_2273_, lean_object* v_bs_2274_){
_start:
{
size_t v_sz_boxed_2275_; size_t v_i_boxed_2276_; lean_object* v_res_2277_; 
v_sz_boxed_2275_ = lean_unbox_usize(v_sz_2272_);
lean_dec(v_sz_2272_);
v_i_boxed_2276_ = lean_unbox_usize(v_i_2273_);
lean_dec(v_i_2273_);
v_res_2277_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__23(v_sz_boxed_2275_, v_i_boxed_2276_, v_bs_2274_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg___lam__0(lean_object* v___y_2278_, uint8_t v_isExporting_2279_, lean_object* v___x_2280_, lean_object* v___y_2281_, lean_object* v___x_2282_, lean_object* v_a_x3f_2283_){
_start:
{
lean_object* v___x_2285_; lean_object* v_env_2286_; lean_object* v_nextMacroScope_2287_; lean_object* v_ngen_2288_; lean_object* v_auxDeclNGen_2289_; lean_object* v_traceState_2290_; lean_object* v_messages_2291_; lean_object* v_infoState_2292_; lean_object* v_snapshotTasks_2293_; lean_object* v_newDecls_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2319_; 
v___x_2285_ = lean_st_ref_take(v___y_2278_);
v_env_2286_ = lean_ctor_get(v___x_2285_, 0);
v_nextMacroScope_2287_ = lean_ctor_get(v___x_2285_, 1);
v_ngen_2288_ = lean_ctor_get(v___x_2285_, 2);
v_auxDeclNGen_2289_ = lean_ctor_get(v___x_2285_, 3);
v_traceState_2290_ = lean_ctor_get(v___x_2285_, 4);
v_messages_2291_ = lean_ctor_get(v___x_2285_, 6);
v_infoState_2292_ = lean_ctor_get(v___x_2285_, 7);
v_snapshotTasks_2293_ = lean_ctor_get(v___x_2285_, 8);
v_newDecls_2294_ = lean_ctor_get(v___x_2285_, 9);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2319_ == 0)
{
lean_object* v_unused_2320_; 
v_unused_2320_ = lean_ctor_get(v___x_2285_, 5);
lean_dec(v_unused_2320_);
v___x_2296_ = v___x_2285_;
v_isShared_2297_ = v_isSharedCheck_2319_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_newDecls_2294_);
lean_inc(v_snapshotTasks_2293_);
lean_inc(v_infoState_2292_);
lean_inc(v_messages_2291_);
lean_inc(v_traceState_2290_);
lean_inc(v_auxDeclNGen_2289_);
lean_inc(v_ngen_2288_);
lean_inc(v_nextMacroScope_2287_);
lean_inc(v_env_2286_);
lean_dec(v___x_2285_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2319_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2298_; lean_object* v___x_2300_; 
v___x_2298_ = l_Lean_Environment_setExporting(v_env_2286_, v_isExporting_2279_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 5, v___x_2280_);
lean_ctor_set(v___x_2296_, 0, v___x_2298_);
v___x_2300_ = v___x_2296_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v___x_2298_);
lean_ctor_set(v_reuseFailAlloc_2318_, 1, v_nextMacroScope_2287_);
lean_ctor_set(v_reuseFailAlloc_2318_, 2, v_ngen_2288_);
lean_ctor_set(v_reuseFailAlloc_2318_, 3, v_auxDeclNGen_2289_);
lean_ctor_set(v_reuseFailAlloc_2318_, 4, v_traceState_2290_);
lean_ctor_set(v_reuseFailAlloc_2318_, 5, v___x_2280_);
lean_ctor_set(v_reuseFailAlloc_2318_, 6, v_messages_2291_);
lean_ctor_set(v_reuseFailAlloc_2318_, 7, v_infoState_2292_);
lean_ctor_set(v_reuseFailAlloc_2318_, 8, v_snapshotTasks_2293_);
lean_ctor_set(v_reuseFailAlloc_2318_, 9, v_newDecls_2294_);
v___x_2300_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v_mctx_2303_; lean_object* v_zetaDeltaFVarIds_2304_; lean_object* v_postponed_2305_; lean_object* v_diag_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2316_; 
v___x_2301_ = lean_st_ref_set(v___y_2278_, v___x_2300_);
v___x_2302_ = lean_st_ref_take(v___y_2281_);
v_mctx_2303_ = lean_ctor_get(v___x_2302_, 0);
v_zetaDeltaFVarIds_2304_ = lean_ctor_get(v___x_2302_, 2);
v_postponed_2305_ = lean_ctor_get(v___x_2302_, 3);
v_diag_2306_ = lean_ctor_get(v___x_2302_, 4);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2316_ == 0)
{
lean_object* v_unused_2317_; 
v_unused_2317_ = lean_ctor_get(v___x_2302_, 1);
lean_dec(v_unused_2317_);
v___x_2308_ = v___x_2302_;
v_isShared_2309_ = v_isSharedCheck_2316_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_diag_2306_);
lean_inc(v_postponed_2305_);
lean_inc(v_zetaDeltaFVarIds_2304_);
lean_inc(v_mctx_2303_);
lean_dec(v___x_2302_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2316_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2311_; 
if (v_isShared_2309_ == 0)
{
lean_ctor_set(v___x_2308_, 1, v___x_2282_);
v___x_2311_ = v___x_2308_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_mctx_2303_);
lean_ctor_set(v_reuseFailAlloc_2315_, 1, v___x_2282_);
lean_ctor_set(v_reuseFailAlloc_2315_, 2, v_zetaDeltaFVarIds_2304_);
lean_ctor_set(v_reuseFailAlloc_2315_, 3, v_postponed_2305_);
lean_ctor_set(v_reuseFailAlloc_2315_, 4, v_diag_2306_);
v___x_2311_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2312_ = lean_st_ref_set(v___y_2281_, v___x_2311_);
v___x_2313_ = lean_box(0);
v___x_2314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2313_);
return v___x_2314_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg___lam__0___boxed(lean_object* v___y_2321_, lean_object* v_isExporting_2322_, lean_object* v___x_2323_, lean_object* v___y_2324_, lean_object* v___x_2325_, lean_object* v_a_x3f_2326_, lean_object* v___y_2327_){
_start:
{
uint8_t v_isExporting_boxed_2328_; lean_object* v_res_2329_; 
v_isExporting_boxed_2328_ = lean_unbox(v_isExporting_2322_);
v_res_2329_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg___lam__0(v___y_2321_, v_isExporting_boxed_2328_, v___x_2323_, v___y_2324_, v___x_2325_, v_a_x3f_2326_);
lean_dec(v_a_x3f_2326_);
lean_dec(v___y_2324_);
lean_dec(v___y_2321_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg(lean_object* v_x_2330_, uint8_t v_isExporting_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v___x_2339_; lean_object* v_env_2340_; uint8_t v_isExporting_2341_; lean_object* v___x_2342_; lean_object* v_env_2343_; lean_object* v_nextMacroScope_2344_; lean_object* v_ngen_2345_; lean_object* v_auxDeclNGen_2346_; lean_object* v_traceState_2347_; lean_object* v_messages_2348_; lean_object* v_infoState_2349_; lean_object* v_snapshotTasks_2350_; lean_object* v_newDecls_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2405_; 
v___x_2339_ = lean_st_ref_get(v___y_2337_);
v_env_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc_ref(v_env_2340_);
lean_dec(v___x_2339_);
v_isExporting_2341_ = lean_ctor_get_uint8(v_env_2340_, sizeof(void*)*8);
lean_dec_ref(v_env_2340_);
v___x_2342_ = lean_st_ref_take(v___y_2337_);
v_env_2343_ = lean_ctor_get(v___x_2342_, 0);
v_nextMacroScope_2344_ = lean_ctor_get(v___x_2342_, 1);
v_ngen_2345_ = lean_ctor_get(v___x_2342_, 2);
v_auxDeclNGen_2346_ = lean_ctor_get(v___x_2342_, 3);
v_traceState_2347_ = lean_ctor_get(v___x_2342_, 4);
v_messages_2348_ = lean_ctor_get(v___x_2342_, 6);
v_infoState_2349_ = lean_ctor_get(v___x_2342_, 7);
v_snapshotTasks_2350_ = lean_ctor_get(v___x_2342_, 8);
v_newDecls_2351_ = lean_ctor_get(v___x_2342_, 9);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2405_ == 0)
{
lean_object* v_unused_2406_; 
v_unused_2406_ = lean_ctor_get(v___x_2342_, 5);
lean_dec(v_unused_2406_);
v___x_2353_ = v___x_2342_;
v_isShared_2354_ = v_isSharedCheck_2405_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_newDecls_2351_);
lean_inc(v_snapshotTasks_2350_);
lean_inc(v_infoState_2349_);
lean_inc(v_messages_2348_);
lean_inc(v_traceState_2347_);
lean_inc(v_auxDeclNGen_2346_);
lean_inc(v_ngen_2345_);
lean_inc(v_nextMacroScope_2344_);
lean_inc(v_env_2343_);
lean_dec(v___x_2342_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2405_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2358_; 
v___x_2355_ = l_Lean_Environment_setExporting(v_env_2343_, v_isExporting_2331_);
v___x_2356_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2);
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 5, v___x_2356_);
lean_ctor_set(v___x_2353_, 0, v___x_2355_);
v___x_2358_ = v___x_2353_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v___x_2355_);
lean_ctor_set(v_reuseFailAlloc_2404_, 1, v_nextMacroScope_2344_);
lean_ctor_set(v_reuseFailAlloc_2404_, 2, v_ngen_2345_);
lean_ctor_set(v_reuseFailAlloc_2404_, 3, v_auxDeclNGen_2346_);
lean_ctor_set(v_reuseFailAlloc_2404_, 4, v_traceState_2347_);
lean_ctor_set(v_reuseFailAlloc_2404_, 5, v___x_2356_);
lean_ctor_set(v_reuseFailAlloc_2404_, 6, v_messages_2348_);
lean_ctor_set(v_reuseFailAlloc_2404_, 7, v_infoState_2349_);
lean_ctor_set(v_reuseFailAlloc_2404_, 8, v_snapshotTasks_2350_);
lean_ctor_set(v_reuseFailAlloc_2404_, 9, v_newDecls_2351_);
v___x_2358_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v_mctx_2361_; lean_object* v_zetaDeltaFVarIds_2362_; lean_object* v_postponed_2363_; lean_object* v_diag_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2402_; 
v___x_2359_ = lean_st_ref_set(v___y_2337_, v___x_2358_);
v___x_2360_ = lean_st_ref_take(v___y_2335_);
v_mctx_2361_ = lean_ctor_get(v___x_2360_, 0);
v_zetaDeltaFVarIds_2362_ = lean_ctor_get(v___x_2360_, 2);
v_postponed_2363_ = lean_ctor_get(v___x_2360_, 3);
v_diag_2364_ = lean_ctor_get(v___x_2360_, 4);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2402_ == 0)
{
lean_object* v_unused_2403_; 
v_unused_2403_ = lean_ctor_get(v___x_2360_, 1);
lean_dec(v_unused_2403_);
v___x_2366_ = v___x_2360_;
v_isShared_2367_ = v_isSharedCheck_2402_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_diag_2364_);
lean_inc(v_postponed_2363_);
lean_inc(v_zetaDeltaFVarIds_2362_);
lean_inc(v_mctx_2361_);
lean_dec(v___x_2360_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2402_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2368_; lean_object* v___x_2370_; 
v___x_2368_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3);
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 1, v___x_2368_);
v___x_2370_ = v___x_2366_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_mctx_2361_);
lean_ctor_set(v_reuseFailAlloc_2401_, 1, v___x_2368_);
lean_ctor_set(v_reuseFailAlloc_2401_, 2, v_zetaDeltaFVarIds_2362_);
lean_ctor_set(v_reuseFailAlloc_2401_, 3, v_postponed_2363_);
lean_ctor_set(v_reuseFailAlloc_2401_, 4, v_diag_2364_);
v___x_2370_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
lean_object* v___x_2371_; lean_object* v_r_2372_; 
v___x_2371_ = lean_st_ref_set(v___y_2335_, v___x_2370_);
lean_inc(v___y_2337_);
lean_inc_ref(v___y_2336_);
lean_inc(v___y_2335_);
lean_inc_ref(v___y_2334_);
lean_inc(v___y_2333_);
lean_inc_ref(v___y_2332_);
v_r_2372_ = lean_apply_7(v_x_2330_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, lean_box(0));
if (lean_obj_tag(v_r_2372_) == 0)
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2389_; 
v_a_2373_ = lean_ctor_get(v_r_2372_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v_r_2372_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2375_ = v_r_2372_;
v_isShared_2376_ = v_isSharedCheck_2389_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v_r_2372_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2389_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
lean_inc(v_a_2373_);
if (v_isShared_2376_ == 0)
{
lean_ctor_set_tag(v___x_2375_, 1);
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2373_);
v___x_2378_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
lean_object* v___x_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2386_; 
v___x_2379_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg___lam__0(v___y_2337_, v_isExporting_2341_, v___x_2356_, v___y_2335_, v___x_2368_, v___x_2378_);
lean_dec_ref(v___x_2378_);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2386_ == 0)
{
lean_object* v_unused_2387_; 
v_unused_2387_ = lean_ctor_get(v___x_2379_, 0);
lean_dec(v_unused_2387_);
v___x_2381_ = v___x_2379_;
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
else
{
lean_dec(v___x_2379_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2384_; 
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 0, v_a_2373_);
v___x_2384_ = v___x_2381_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_a_2373_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
}
}
else
{
lean_object* v_a_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2399_; 
v_a_2390_ = lean_ctor_get(v_r_2372_, 0);
lean_inc(v_a_2390_);
lean_dec_ref(v_r_2372_);
v___x_2391_ = lean_box(0);
v___x_2392_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg___lam__0(v___y_2337_, v_isExporting_2341_, v___x_2356_, v___y_2335_, v___x_2368_, v___x_2391_);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2399_ == 0)
{
lean_object* v_unused_2400_; 
v_unused_2400_ = lean_ctor_get(v___x_2392_, 0);
lean_dec(v_unused_2400_);
v___x_2394_ = v___x_2392_;
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
else
{
lean_dec(v___x_2392_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2397_; 
if (v_isShared_2395_ == 0)
{
lean_ctor_set_tag(v___x_2394_, 1);
lean_ctor_set(v___x_2394_, 0, v_a_2390_);
v___x_2397_ = v___x_2394_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_a_2390_);
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
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg___boxed(lean_object* v_x_2407_, lean_object* v_isExporting_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
uint8_t v_isExporting_boxed_2416_; lean_object* v_res_2417_; 
v_isExporting_boxed_2416_ = lean_unbox(v_isExporting_2408_);
v_res_2417_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg(v_x_2407_, v_isExporting_boxed_2416_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
return v_res_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17___redArg(lean_object* v_x_2418_, uint8_t v_when_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
if (v_when_2419_ == 0)
{
lean_object* v___x_2427_; 
lean_inc(v___y_2425_);
lean_inc_ref(v___y_2424_);
lean_inc(v___y_2423_);
lean_inc_ref(v___y_2422_);
lean_inc(v___y_2421_);
lean_inc_ref(v___y_2420_);
v___x_2427_ = lean_apply_7(v_x_2418_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, lean_box(0));
return v___x_2427_;
}
else
{
uint8_t v___x_2428_; lean_object* v___x_2429_; 
v___x_2428_ = 0;
v___x_2429_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg(v_x_2418_, v___x_2428_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
return v___x_2429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17___redArg___boxed(lean_object* v_x_2430_, lean_object* v_when_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_){
_start:
{
uint8_t v_when_boxed_2439_; lean_object* v_res_2440_; 
v_when_boxed_2439_ = lean_unbox(v_when_2431_);
v_res_2440_ = l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17___redArg(v_x_2430_, v_when_boxed_2439_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
lean_dec(v___y_2435_);
lean_dec_ref(v___y_2434_);
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2432_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16___redArg(lean_object* v_env_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
lean_object* v___x_2445_; lean_object* v_nextMacroScope_2446_; lean_object* v_ngen_2447_; lean_object* v_auxDeclNGen_2448_; lean_object* v_traceState_2449_; lean_object* v_messages_2450_; lean_object* v_infoState_2451_; lean_object* v_snapshotTasks_2452_; lean_object* v_newDecls_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2479_; 
v___x_2445_ = lean_st_ref_take(v___y_2443_);
v_nextMacroScope_2446_ = lean_ctor_get(v___x_2445_, 1);
v_ngen_2447_ = lean_ctor_get(v___x_2445_, 2);
v_auxDeclNGen_2448_ = lean_ctor_get(v___x_2445_, 3);
v_traceState_2449_ = lean_ctor_get(v___x_2445_, 4);
v_messages_2450_ = lean_ctor_get(v___x_2445_, 6);
v_infoState_2451_ = lean_ctor_get(v___x_2445_, 7);
v_snapshotTasks_2452_ = lean_ctor_get(v___x_2445_, 8);
v_newDecls_2453_ = lean_ctor_get(v___x_2445_, 9);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2479_ == 0)
{
lean_object* v_unused_2480_; lean_object* v_unused_2481_; 
v_unused_2480_ = lean_ctor_get(v___x_2445_, 5);
lean_dec(v_unused_2480_);
v_unused_2481_ = lean_ctor_get(v___x_2445_, 0);
lean_dec(v_unused_2481_);
v___x_2455_ = v___x_2445_;
v_isShared_2456_ = v_isSharedCheck_2479_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_newDecls_2453_);
lean_inc(v_snapshotTasks_2452_);
lean_inc(v_infoState_2451_);
lean_inc(v_messages_2450_);
lean_inc(v_traceState_2449_);
lean_inc(v_auxDeclNGen_2448_);
lean_inc(v_ngen_2447_);
lean_inc(v_nextMacroScope_2446_);
lean_dec(v___x_2445_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2479_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2457_; lean_object* v___x_2459_; 
v___x_2457_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2);
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 5, v___x_2457_);
lean_ctor_set(v___x_2455_, 0, v_env_2441_);
v___x_2459_ = v___x_2455_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_env_2441_);
lean_ctor_set(v_reuseFailAlloc_2478_, 1, v_nextMacroScope_2446_);
lean_ctor_set(v_reuseFailAlloc_2478_, 2, v_ngen_2447_);
lean_ctor_set(v_reuseFailAlloc_2478_, 3, v_auxDeclNGen_2448_);
lean_ctor_set(v_reuseFailAlloc_2478_, 4, v_traceState_2449_);
lean_ctor_set(v_reuseFailAlloc_2478_, 5, v___x_2457_);
lean_ctor_set(v_reuseFailAlloc_2478_, 6, v_messages_2450_);
lean_ctor_set(v_reuseFailAlloc_2478_, 7, v_infoState_2451_);
lean_ctor_set(v_reuseFailAlloc_2478_, 8, v_snapshotTasks_2452_);
lean_ctor_set(v_reuseFailAlloc_2478_, 9, v_newDecls_2453_);
v___x_2459_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v_mctx_2462_; lean_object* v_zetaDeltaFVarIds_2463_; lean_object* v_postponed_2464_; lean_object* v_diag_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2476_; 
v___x_2460_ = lean_st_ref_set(v___y_2443_, v___x_2459_);
v___x_2461_ = lean_st_ref_take(v___y_2442_);
v_mctx_2462_ = lean_ctor_get(v___x_2461_, 0);
v_zetaDeltaFVarIds_2463_ = lean_ctor_get(v___x_2461_, 2);
v_postponed_2464_ = lean_ctor_get(v___x_2461_, 3);
v_diag_2465_ = lean_ctor_get(v___x_2461_, 4);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2476_ == 0)
{
lean_object* v_unused_2477_; 
v_unused_2477_ = lean_ctor_get(v___x_2461_, 1);
lean_dec(v_unused_2477_);
v___x_2467_ = v___x_2461_;
v_isShared_2468_ = v_isSharedCheck_2476_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_diag_2465_);
lean_inc(v_postponed_2464_);
lean_inc(v_zetaDeltaFVarIds_2463_);
lean_inc(v_mctx_2462_);
lean_dec(v___x_2461_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2476_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2469_; lean_object* v___x_2471_; 
v___x_2469_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3);
if (v_isShared_2468_ == 0)
{
lean_ctor_set(v___x_2467_, 1, v___x_2469_);
v___x_2471_ = v___x_2467_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_mctx_2462_);
lean_ctor_set(v_reuseFailAlloc_2475_, 1, v___x_2469_);
lean_ctor_set(v_reuseFailAlloc_2475_, 2, v_zetaDeltaFVarIds_2463_);
lean_ctor_set(v_reuseFailAlloc_2475_, 3, v_postponed_2464_);
lean_ctor_set(v_reuseFailAlloc_2475_, 4, v_diag_2465_);
v___x_2471_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2472_ = lean_st_ref_set(v___y_2442_, v___x_2471_);
v___x_2473_ = lean_box(0);
v___x_2474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2473_);
return v___x_2474_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16___redArg___boxed(lean_object* v_env_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_){
_start:
{
lean_object* v_res_2486_; 
v_res_2486_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16___redArg(v_env_2482_, v___y_2483_, v___y_2484_);
lean_dec(v___y_2484_);
lean_dec(v___y_2483_);
return v_res_2486_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14___redArg(lean_object* v_env_2487_, lean_object* v_x_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
lean_object* v___x_2496_; lean_object* v_env_2497_; lean_object* v_a_2499_; lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2496_ = lean_st_ref_get(v___y_2494_);
v_env_2497_ = lean_ctor_get(v___x_2496_, 0);
lean_inc_ref(v_env_2497_);
lean_dec(v___x_2496_);
v___x_2509_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16___redArg(v_env_2487_, v___y_2492_, v___y_2494_);
lean_dec_ref(v___x_2509_);
lean_inc(v___y_2494_);
lean_inc_ref(v___y_2493_);
lean_inc(v___y_2492_);
lean_inc_ref(v___y_2491_);
lean_inc(v___y_2490_);
lean_inc_ref(v___y_2489_);
v___x_2510_ = lean_apply_7(v_x_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, lean_box(0));
if (lean_obj_tag(v___x_2510_) == 0)
{
lean_object* v_a_2511_; lean_object* v___x_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2519_; 
v_a_2511_ = lean_ctor_get(v___x_2510_, 0);
lean_inc(v_a_2511_);
lean_dec_ref(v___x_2510_);
v___x_2512_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16___redArg(v_env_2497_, v___y_2492_, v___y_2494_);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2519_ == 0)
{
lean_object* v_unused_2520_; 
v_unused_2520_ = lean_ctor_get(v___x_2512_, 0);
lean_dec(v_unused_2520_);
v___x_2514_ = v___x_2512_;
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
else
{
lean_dec(v___x_2512_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2517_; 
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 0, v_a_2511_);
v___x_2517_ = v___x_2514_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_a_2511_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
else
{
lean_object* v_a_2521_; 
v_a_2521_ = lean_ctor_get(v___x_2510_, 0);
lean_inc(v_a_2521_);
lean_dec_ref(v___x_2510_);
v_a_2499_ = v_a_2521_;
goto v___jp_2498_;
}
v___jp_2498_:
{
lean_object* v___x_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
v___x_2500_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16___redArg(v_env_2497_, v___y_2492_, v___y_2494_);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2507_ == 0)
{
lean_object* v_unused_2508_; 
v_unused_2508_ = lean_ctor_get(v___x_2500_, 0);
lean_dec(v_unused_2508_);
v___x_2502_ = v___x_2500_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_dec(v___x_2500_);
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
lean_ctor_set(v___x_2502_, 0, v_a_2499_);
v___x_2505_ = v___x_2502_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_a_2499_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14___redArg___boxed(lean_object* v_env_2522_, lean_object* v_x_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_){
_start:
{
lean_object* v_res_2531_; 
v_res_2531_ = l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14___redArg(v_env_2522_, v_x_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13___redArg(lean_object* v_as_2532_, size_t v_i_2533_, size_t v_stop_2534_, lean_object* v_b_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_){
_start:
{
uint8_t v___x_2539_; 
v___x_2539_ = lean_usize_dec_eq(v_i_2533_, v_stop_2534_);
if (v___x_2539_ == 0)
{
lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2540_ = lean_array_uget_borrowed(v_as_2532_, v_i_2533_);
v___x_2541_ = l_Lean_Elab_addAsAxiom___redArg(v___x_2540_, v___y_2536_, v___y_2537_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v_a_2542_; size_t v___x_2543_; size_t v___x_2544_; 
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
lean_inc(v_a_2542_);
lean_dec_ref(v___x_2541_);
v___x_2543_ = ((size_t)1ULL);
v___x_2544_ = lean_usize_add(v_i_2533_, v___x_2543_);
v_i_2533_ = v___x_2544_;
v_b_2535_ = v_a_2542_;
goto _start;
}
else
{
return v___x_2541_;
}
}
else
{
lean_object* v___x_2546_; 
v___x_2546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2546_, 0, v_b_2535_);
return v___x_2546_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13___redArg___boxed(lean_object* v_as_2547_, lean_object* v_i_2548_, lean_object* v_stop_2549_, lean_object* v_b_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
size_t v_i_boxed_2554_; size_t v_stop_boxed_2555_; lean_object* v_res_2556_; 
v_i_boxed_2554_ = lean_unbox_usize(v_i_2548_);
lean_dec(v_i_2548_);
v_stop_boxed_2555_ = lean_unbox_usize(v_stop_2549_);
lean_dec(v_stop_2549_);
v_res_2556_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13___redArg(v_as_2547_, v_i_boxed_2554_, v_stop_boxed_2555_, v_b_2550_, v___y_2551_, v___y_2552_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec_ref(v_as_2547_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__0(lean_object* v___x_2557_, lean_object* v___x_2558_, lean_object* v___x_2559_, lean_object* v_a_2560_, lean_object* v_f_2561_, lean_object* v_a_2562_, lean_object* v_preDefs_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_){
_start:
{
lean_object* v___y_2572_; uint8_t v___x_2582_; 
v___x_2582_ = lean_nat_dec_lt(v___x_2557_, v___x_2558_);
if (v___x_2582_ == 0)
{
lean_object* v___x_2583_; 
v___x_2583_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps(v___x_2559_, v_a_2560_, v_f_2561_, v_a_2562_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
return v___x_2583_;
}
else
{
lean_object* v___x_2584_; lean_object* v___x_2585_; uint8_t v___x_2586_; 
v___x_2584_ = lean_box(0);
v___x_2585_ = lean_array_get_size(v_preDefs_2563_);
v___x_2586_ = lean_nat_dec_le(v___x_2558_, v___x_2585_);
if (v___x_2586_ == 0)
{
uint8_t v___x_2587_; 
v___x_2587_ = lean_nat_dec_lt(v___x_2557_, v___x_2585_);
if (v___x_2587_ == 0)
{
lean_object* v___x_2588_; 
v___x_2588_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps(v___x_2559_, v_a_2560_, v_f_2561_, v_a_2562_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
return v___x_2588_;
}
else
{
size_t v___x_2589_; size_t v___x_2590_; lean_object* v___x_2591_; 
v___x_2589_ = ((size_t)0ULL);
v___x_2590_ = lean_usize_of_nat(v___x_2585_);
v___x_2591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13___redArg(v_preDefs_2563_, v___x_2589_, v___x_2590_, v___x_2584_, v___y_2568_, v___y_2569_);
v___y_2572_ = v___x_2591_;
goto v___jp_2571_;
}
}
else
{
size_t v___x_2592_; size_t v___x_2593_; lean_object* v___x_2594_; 
v___x_2592_ = ((size_t)0ULL);
v___x_2593_ = lean_usize_of_nat(v___x_2558_);
v___x_2594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13___redArg(v_preDefs_2563_, v___x_2592_, v___x_2593_, v___x_2584_, v___y_2568_, v___y_2569_);
v___y_2572_ = v___x_2594_;
goto v___jp_2571_;
}
}
v___jp_2571_:
{
if (lean_obj_tag(v___y_2572_) == 0)
{
lean_object* v___x_2573_; 
lean_dec_ref(v___y_2572_);
v___x_2573_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps(v___x_2559_, v_a_2560_, v_f_2561_, v_a_2562_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
return v___x_2573_;
}
else
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2581_; 
lean_dec_ref(v_f_2561_);
lean_dec_ref(v_a_2560_);
lean_dec_ref(v___x_2559_);
v_a_2574_ = lean_ctor_get(v___y_2572_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___y_2572_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2576_ = v___y_2572_;
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___y_2572_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2579_; 
if (v_isShared_2577_ == 0)
{
v___x_2579_ = v___x_2576_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2574_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__0___boxed(lean_object* v___x_2595_, lean_object* v___x_2596_, lean_object* v___x_2597_, lean_object* v_a_2598_, lean_object* v_f_2599_, lean_object* v_a_2600_, lean_object* v_preDefs_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v_res_2609_; 
v_res_2609_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__0(v___x_2595_, v___x_2596_, v___x_2597_, v_a_2598_, v_f_2599_, v_a_2600_, v_preDefs_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
lean_dec_ref(v_preDefs_2601_);
lean_dec_ref(v_a_2600_);
lean_dec(v___x_2596_);
lean_dec(v___x_2595_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__1(lean_object* v___x_2610_, lean_object* v___x_2611_, lean_object* v___x_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_preDefs_2615_, uint8_t v_isZero_2616_, lean_object* v_f_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_){
_start:
{
lean_object* v___x_2625_; lean_object* v_env_2626_; lean_object* v___f_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2625_ = lean_st_ref_get(v___y_2623_);
v_env_2626_ = lean_ctor_get(v___x_2625_, 0);
lean_inc_ref(v_env_2626_);
lean_dec(v___x_2625_);
lean_inc_ref(v_f_2617_);
v___f_2627_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2627_, 0, v___x_2610_);
lean_closure_set(v___f_2627_, 1, v___x_2611_);
lean_closure_set(v___f_2627_, 2, v___x_2612_);
lean_closure_set(v___f_2627_, 3, v_a_2613_);
lean_closure_set(v___f_2627_, 4, v_f_2617_);
lean_closure_set(v___f_2627_, 5, v_a_2614_);
lean_closure_set(v___f_2627_, 6, v_preDefs_2615_);
v___x_2628_ = l_Lean_Environment_unlockAsync(v_env_2626_);
v___x_2629_ = l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14___redArg(v___x_2628_, v___f_2627_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_);
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_object* v_a_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; uint8_t v___x_2634_; uint8_t v___x_2635_; lean_object* v___x_2636_; 
v_a_2630_ = lean_ctor_get(v___x_2629_, 0);
lean_inc(v_a_2630_);
lean_dec_ref(v___x_2629_);
v___x_2631_ = lean_unsigned_to_nat(1u);
v___x_2632_ = lean_mk_empty_array_with_capacity(v___x_2631_);
v___x_2633_ = lean_array_push(v___x_2632_, v_f_2617_);
v___x_2634_ = 1;
v___x_2635_ = 1;
v___x_2636_ = l_Lean_Meta_mkLambdaFVars(v___x_2633_, v_a_2630_, v_isZero_2616_, v___x_2634_, v_isZero_2616_, v___x_2634_, v___x_2635_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_);
lean_dec_ref(v___x_2633_);
return v___x_2636_;
}
else
{
lean_dec_ref(v_f_2617_);
return v___x_2629_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__1___boxed(lean_object* v___x_2637_, lean_object* v___x_2638_, lean_object* v___x_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_preDefs_2642_, lean_object* v_isZero_2643_, lean_object* v_f_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
uint8_t v_isZero_boxed_2652_; lean_object* v_res_2653_; 
v_isZero_boxed_2652_ = lean_unbox(v_isZero_2643_);
v_res_2653_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__1(v___x_2637_, v___x_2638_, v___x_2639_, v_a_2640_, v_a_2641_, v_preDefs_2642_, v_isZero_boxed_2652_, v_f_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg___lam__0(lean_object* v_k_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v_b_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_){
_start:
{
lean_object* v___x_2663_; 
lean_inc(v___y_2661_);
lean_inc_ref(v___y_2660_);
lean_inc(v___y_2659_);
lean_inc_ref(v___y_2658_);
lean_inc(v___y_2656_);
lean_inc_ref(v___y_2655_);
v___x_2663_ = lean_apply_8(v_k_2654_, v_b_2657_, v___y_2655_, v___y_2656_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_, lean_box(0));
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg___lam__0___boxed(lean_object* v_k_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v_b_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
lean_object* v_res_2673_; 
v_res_2673_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg___lam__0(v_k_2664_, v___y_2665_, v___y_2666_, v_b_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
lean_dec(v___y_2671_);
lean_dec_ref(v___y_2670_);
lean_dec(v___y_2669_);
lean_dec_ref(v___y_2668_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg(lean_object* v_name_2674_, uint8_t v_bi_2675_, lean_object* v_type_2676_, lean_object* v_k_2677_, uint8_t v_kind_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
lean_object* v___f_2686_; lean_object* v___x_2687_; 
lean_inc(v___y_2680_);
lean_inc_ref(v___y_2679_);
v___f_2686_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2686_, 0, v_k_2677_);
lean_closure_set(v___f_2686_, 1, v___y_2679_);
lean_closure_set(v___f_2686_, 2, v___y_2680_);
v___x_2687_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2674_, v_bi_2675_, v_type_2676_, v___f_2686_, v_kind_2678_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
if (lean_obj_tag(v___x_2687_) == 0)
{
return v___x_2687_;
}
else
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg___boxed(lean_object* v_name_2696_, lean_object* v_bi_2697_, lean_object* v_type_2698_, lean_object* v_k_2699_, lean_object* v_kind_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
uint8_t v_bi_boxed_2708_; uint8_t v_kind_boxed_2709_; lean_object* v_res_2710_; 
v_bi_boxed_2708_ = lean_unbox(v_bi_2697_);
v_kind_boxed_2709_ = lean_unbox(v_kind_2700_);
v_res_2710_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg(v_name_2696_, v_bi_boxed_2708_, v_type_2698_, v_k_2699_, v_kind_boxed_2709_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
lean_dec(v___y_2702_);
lean_dec_ref(v___y_2701_);
return v_res_2710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15___redArg(lean_object* v_name_2711_, lean_object* v_type_2712_, lean_object* v_k_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
uint8_t v___x_2721_; uint8_t v___x_2722_; lean_object* v___x_2723_; 
v___x_2721_ = 0;
v___x_2722_ = 0;
v___x_2723_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg(v_name_2711_, v___x_2721_, v_type_2712_, v_k_2713_, v___x_2722_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15___redArg___boxed(lean_object* v_name_2724_, lean_object* v_type_2725_, lean_object* v_k_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
lean_object* v_res_2734_; 
v_res_2734_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15___redArg(v_name_2724_, v_type_2725_, v_k_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec_ref(v___y_2729_);
lean_dec(v___y_2728_);
lean_dec_ref(v___y_2727_);
return v_res_2734_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg(lean_object* v___x_2738_, lean_object* v_fixedArgs_2739_, lean_object* v___x_2740_, lean_object* v_a_2741_, lean_object* v___x_2742_, lean_object* v_preDefs_2743_, lean_object* v_a_2744_, lean_object* v_as_2745_, lean_object* v_i_2746_, lean_object* v_j_2747_, lean_object* v_bs_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_){
_start:
{
lean_object* v_zero_2756_; uint8_t v_isZero_2757_; 
v_zero_2756_ = lean_unsigned_to_nat(0u);
v_isZero_2757_ = lean_nat_dec_eq(v_i_2746_, v_zero_2756_);
if (v_isZero_2757_ == 1)
{
lean_object* v___x_2758_; 
lean_dec(v_j_2747_);
lean_dec(v_i_2746_);
lean_dec_ref(v_a_2744_);
lean_dec_ref(v_preDefs_2743_);
lean_dec(v___x_2742_);
lean_dec_ref(v_a_2741_);
lean_dec_ref(v___x_2740_);
lean_dec_ref(v_fixedArgs_2739_);
v___x_2758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2758_, 0, v_bs_2748_);
return v___x_2758_;
}
else
{
lean_object* v___x_2759_; lean_object* v_value_2760_; lean_object* v___x_2761_; lean_object* v_one_2762_; lean_object* v_n_2763_; lean_object* v___y_2765_; lean_object* v___x_2778_; lean_object* v___x_2779_; 
v___x_2759_ = lean_array_fget_borrowed(v_as_2745_, v_j_2747_);
v_value_2760_ = lean_ctor_get(v___x_2759_, 7);
v___x_2761_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1);
v_one_2762_ = lean_unsigned_to_nat(1u);
v_n_2763_ = lean_nat_sub(v_i_2746_, v_one_2762_);
lean_dec(v_i_2746_);
v___x_2778_ = lean_array_get_borrowed(v___x_2761_, v___x_2738_, v_j_2747_);
lean_inc_ref(v_fixedArgs_2739_);
lean_inc_ref(v_value_2760_);
lean_inc(v___x_2778_);
v___x_2779_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_2778_, v_value_2760_, v_fixedArgs_2739_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_object* v_a_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; 
v_a_2780_ = lean_ctor_get(v___x_2779_, 0);
lean_inc(v_a_2780_);
lean_dec_ref(v___x_2779_);
v___x_2781_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___closed__1));
v___x_2782_ = l_Lean_Core_mkFreshUserName(v___x_2781_, v___y_2753_, v___y_2754_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v_a_2783_; lean_object* v___x_2784_; lean_object* v___f_2785_; lean_object* v___x_2786_; 
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
lean_inc(v_a_2783_);
lean_dec_ref(v___x_2782_);
v___x_2784_ = lean_box(v_isZero_2757_);
lean_inc_ref(v_preDefs_2743_);
lean_inc_ref(v_a_2741_);
lean_inc_ref(v___x_2740_);
lean_inc(v___x_2742_);
v___f_2785_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__1___boxed), 15, 7);
lean_closure_set(v___f_2785_, 0, v_zero_2756_);
lean_closure_set(v___f_2785_, 1, v___x_2742_);
lean_closure_set(v___f_2785_, 2, v___x_2740_);
lean_closure_set(v___f_2785_, 3, v_a_2741_);
lean_closure_set(v___f_2785_, 4, v_a_2780_);
lean_closure_set(v___f_2785_, 5, v_preDefs_2743_);
lean_closure_set(v___f_2785_, 6, v___x_2784_);
lean_inc_ref(v_a_2744_);
v___x_2786_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15___redArg(v_a_2783_, v_a_2744_, v___f_2785_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_);
v___y_2765_ = v___x_2786_;
goto v___jp_2764_;
}
else
{
lean_object* v_a_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2794_; 
lean_dec(v_a_2780_);
lean_dec(v_n_2763_);
lean_dec_ref(v_bs_2748_);
lean_dec(v_j_2747_);
lean_dec_ref(v_a_2744_);
lean_dec_ref(v_preDefs_2743_);
lean_dec(v___x_2742_);
lean_dec_ref(v_a_2741_);
lean_dec_ref(v___x_2740_);
lean_dec_ref(v_fixedArgs_2739_);
v_a_2787_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2789_ = v___x_2782_;
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_a_2787_);
lean_dec(v___x_2782_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2792_; 
if (v_isShared_2790_ == 0)
{
v___x_2792_ = v___x_2789_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_a_2787_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
}
else
{
v___y_2765_ = v___x_2779_;
goto v___jp_2764_;
}
v___jp_2764_:
{
if (lean_obj_tag(v___y_2765_) == 0)
{
lean_object* v_a_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
v_a_2766_ = lean_ctor_get(v___y_2765_, 0);
lean_inc(v_a_2766_);
lean_dec_ref(v___y_2765_);
v___x_2767_ = lean_nat_add(v_j_2747_, v_one_2762_);
lean_dec(v_j_2747_);
v___x_2768_ = lean_array_push(v_bs_2748_, v_a_2766_);
v_i_2746_ = v_n_2763_;
v_j_2747_ = v___x_2767_;
v_bs_2748_ = v___x_2768_;
goto _start;
}
else
{
lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2777_; 
lean_dec(v_n_2763_);
lean_dec_ref(v_bs_2748_);
lean_dec(v_j_2747_);
lean_dec_ref(v_a_2744_);
lean_dec_ref(v_preDefs_2743_);
lean_dec(v___x_2742_);
lean_dec_ref(v_a_2741_);
lean_dec_ref(v___x_2740_);
lean_dec_ref(v_fixedArgs_2739_);
v_a_2770_ = lean_ctor_get(v___y_2765_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___y_2765_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2772_ = v___y_2765_;
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v___y_2765_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2775_; 
if (v_isShared_2773_ == 0)
{
v___x_2775_ = v___x_2772_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_a_2770_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___boxed(lean_object** _args){
lean_object* v___x_2795_ = _args[0];
lean_object* v_fixedArgs_2796_ = _args[1];
lean_object* v___x_2797_ = _args[2];
lean_object* v_a_2798_ = _args[3];
lean_object* v___x_2799_ = _args[4];
lean_object* v_preDefs_2800_ = _args[5];
lean_object* v_a_2801_ = _args[6];
lean_object* v_as_2802_ = _args[7];
lean_object* v_i_2803_ = _args[8];
lean_object* v_j_2804_ = _args[9];
lean_object* v_bs_2805_ = _args[10];
lean_object* v___y_2806_ = _args[11];
lean_object* v___y_2807_ = _args[12];
lean_object* v___y_2808_ = _args[13];
lean_object* v___y_2809_ = _args[14];
lean_object* v___y_2810_ = _args[15];
lean_object* v___y_2811_ = _args[16];
lean_object* v___y_2812_ = _args[17];
_start:
{
lean_object* v_res_2813_; 
v_res_2813_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg(v___x_2795_, v_fixedArgs_2796_, v___x_2797_, v_a_2798_, v___x_2799_, v_preDefs_2800_, v_a_2801_, v_as_2802_, v_i_2803_, v_j_2804_, v_bs_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
lean_dec(v___y_2809_);
lean_dec_ref(v___y_2808_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
lean_dec_ref(v_as_2802_);
lean_dec_ref(v___x_2795_);
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16(lean_object* v___x_2814_, lean_object* v_fixedArgs_2815_, lean_object* v___x_2816_, lean_object* v_a_2817_, lean_object* v___x_2818_, lean_object* v_preDefs_2819_, lean_object* v_a_2820_, lean_object* v_as_2821_, lean_object* v_i_2822_, lean_object* v_j_2823_, lean_object* v_inv_2824_, lean_object* v_bs_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
lean_object* v___x_2833_; 
v___x_2833_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg(v___x_2814_, v_fixedArgs_2815_, v___x_2816_, v_a_2817_, v___x_2818_, v_preDefs_2819_, v_a_2820_, v_as_2821_, v_i_2822_, v_j_2823_, v_bs_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___boxed(lean_object** _args){
lean_object* v___x_2834_ = _args[0];
lean_object* v_fixedArgs_2835_ = _args[1];
lean_object* v___x_2836_ = _args[2];
lean_object* v_a_2837_ = _args[3];
lean_object* v___x_2838_ = _args[4];
lean_object* v_preDefs_2839_ = _args[5];
lean_object* v_a_2840_ = _args[6];
lean_object* v_as_2841_ = _args[7];
lean_object* v_i_2842_ = _args[8];
lean_object* v_j_2843_ = _args[9];
lean_object* v_inv_2844_ = _args[10];
lean_object* v_bs_2845_ = _args[11];
lean_object* v___y_2846_ = _args[12];
lean_object* v___y_2847_ = _args[13];
lean_object* v___y_2848_ = _args[14];
lean_object* v___y_2849_ = _args[15];
lean_object* v___y_2850_ = _args[16];
lean_object* v___y_2851_ = _args[17];
lean_object* v___y_2852_ = _args[18];
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16(v___x_2834_, v_fixedArgs_2835_, v___x_2836_, v_a_2837_, v___x_2838_, v_preDefs_2839_, v_a_2840_, v_as_2841_, v_i_2842_, v_j_2843_, v_inv_2844_, v_bs_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec_ref(v_as_2841_);
lean_dec_ref(v___x_2834_);
return v_res_2853_;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; 
v___x_2854_ = l_Lean_instInhabitedExpr;
v___x_2855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2854_);
lean_ctor_set(v___x_2855_, 1, v___x_2854_);
return v___x_2855_;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; 
v___x_2861_ = ((lean_object*)(l_Lean_Elab_partialFixpoint___lam__0___closed__4));
v___x_2862_ = l_Lean_stringToMessageData(v___x_2861_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_partialFixpoint___lam__0(lean_object* v_a_2863_, lean_object* v_perms_2864_, lean_object* v___x_2865_, lean_object* v_preDefs_2866_, lean_object* v___x_2867_, lean_object* v___x_2868_, size_t v___x_2869_, lean_object* v___x_2870_, lean_object* v_a_2871_, uint8_t v___x_2872_, lean_object* v_hints_2873_, lean_object* v___x_2874_, lean_object* v_docCtx_2875_, size_t v_sz_2876_, lean_object* v_fixedArgs_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2885_ = lean_array_get_size(v_a_2863_);
v___x_2886_ = lean_mk_empty_array_with_capacity(v___x_2885_);
lean_inc(v___x_2865_);
lean_inc_ref(v_fixedArgs_2877_);
v___x_2887_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__10___redArg(v_perms_2864_, v_fixedArgs_2877_, v_a_2863_, v___x_2885_, v___x_2865_, v___x_2886_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v_a_2888_; lean_object* v___x_2889_; 
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
lean_inc(v_a_2888_);
lean_dec_ref(v___x_2887_);
lean_inc_ref(v___x_2868_);
lean_inc(v___x_2865_);
lean_inc(v___x_2867_);
lean_inc_ref(v_fixedArgs_2877_);
v___x_2889_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11___redArg(v_perms_2864_, v_fixedArgs_2877_, v_preDefs_2866_, v___x_2867_, v___x_2865_, v___x_2868_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v_a_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
v_a_2890_ = lean_ctor_get(v___x_2889_, 0);
lean_inc_n(v_a_2890_, 2);
lean_dec_ref(v___x_2889_);
v___x_2891_ = l_Lean_Level_ofNat(v___x_2865_);
v___x_2892_ = l_Lean_Meta_PProdN_pack(v___x_2891_, v_a_2890_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v_a_2893_; size_t v_sz_2894_; lean_object* v___x_2895_; 
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
lean_inc(v_a_2893_);
lean_dec_ref(v___x_2892_);
v_sz_2894_ = lean_array_size(v_a_2888_);
v___x_2895_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12(v_sz_2894_, v___x_2869_, v_a_2888_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
if (lean_obj_tag(v___x_2895_) == 0)
{
lean_object* v_a_2896_; lean_object* v___x_2897_; 
v_a_2896_ = lean_ctor_get(v___x_2895_, 0);
lean_inc_n(v_a_2896_, 2);
lean_dec_ref(v___x_2895_);
v___x_2897_ = l_Lean_Meta_mkPackedPPRodInstance(v_a_2896_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_object* v_a_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; 
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
lean_inc_n(v_a_2898_, 2);
lean_dec_ref(v___x_2897_);
v___x_2899_ = lean_box(0);
v___x_2900_ = l_Lean_Meta_toPartialOrder(v_a_2898_, v___x_2899_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
if (lean_obj_tag(v___x_2900_) == 0)
{
lean_object* v_a_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; 
v_a_2901_ = lean_ctor_get(v___x_2900_, 0);
lean_inc(v_a_2901_);
lean_dec_ref(v___x_2900_);
lean_inc(v___x_2865_);
lean_inc(v_a_2893_);
lean_inc_ref_n(v_preDefs_2866_, 2);
lean_inc_n(v___x_2867_, 2);
lean_inc_ref(v_a_2871_);
lean_inc_ref(v_fixedArgs_2877_);
lean_inc_ref(v_perms_2864_);
v___x_2902_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__16___boxed), 19, 12);
lean_closure_set(v___x_2902_, 0, v_perms_2864_);
lean_closure_set(v___x_2902_, 1, v_fixedArgs_2877_);
lean_closure_set(v___x_2902_, 2, v___x_2870_);
lean_closure_set(v___x_2902_, 3, v_a_2871_);
lean_closure_set(v___x_2902_, 4, v___x_2867_);
lean_closure_set(v___x_2902_, 5, v_preDefs_2866_);
lean_closure_set(v___x_2902_, 6, v_a_2893_);
lean_closure_set(v___x_2902_, 7, v_preDefs_2866_);
lean_closure_set(v___x_2902_, 8, v___x_2867_);
lean_closure_set(v___x_2902_, 9, v___x_2865_);
lean_closure_set(v___x_2902_, 10, lean_box(0));
lean_closure_set(v___x_2902_, 11, v___x_2868_);
v___x_2903_ = l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17___redArg(v___x_2902_, v___x_2872_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
lean_inc(v_a_2904_);
lean_dec_ref(v___x_2903_);
v___x_2905_ = lean_mk_empty_array_with_capacity(v___x_2867_);
lean_inc_ref(v___x_2905_);
lean_inc(v___x_2865_);
lean_inc(v___x_2867_);
lean_inc_ref(v_fixedArgs_2877_);
lean_inc_ref(v_a_2871_);
lean_inc_ref_n(v_preDefs_2866_, 2);
lean_inc_ref(v_hints_2873_);
lean_inc(v_a_2893_);
v___x_2906_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___boxed), 21, 14);
lean_closure_set(v___x_2906_, 0, v_a_2890_);
lean_closure_set(v___x_2906_, 1, v_a_2896_);
lean_closure_set(v___x_2906_, 2, v_a_2904_);
lean_closure_set(v___x_2906_, 3, v_a_2893_);
lean_closure_set(v___x_2906_, 4, v_a_2901_);
lean_closure_set(v___x_2906_, 5, v_hints_2873_);
lean_closure_set(v___x_2906_, 6, v_preDefs_2866_);
lean_closure_set(v___x_2906_, 7, v_a_2871_);
lean_closure_set(v___x_2906_, 8, v_fixedArgs_2877_);
lean_closure_set(v___x_2906_, 9, v_preDefs_2866_);
lean_closure_set(v___x_2906_, 10, v___x_2867_);
lean_closure_set(v___x_2906_, 11, v___x_2865_);
lean_closure_set(v___x_2906_, 12, lean_box(0));
lean_closure_set(v___x_2906_, 13, v___x_2905_);
v___x_2907_ = l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17___redArg(v___x_2906_, v___x_2872_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v_a_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v_a_2908_ = lean_ctor_get(v___x_2907_, 0);
lean_inc(v_a_2908_);
lean_dec_ref(v___x_2907_);
v___x_2909_ = lean_obj_once(&l_Lean_Elab_partialFixpoint___lam__0___closed__0, &l_Lean_Elab_partialFixpoint___lam__0___closed__0_once, _init_l_Lean_Elab_partialFixpoint___lam__0___closed__0);
v___x_2910_ = ((lean_object*)(l_Lean_Elab_partialFixpoint___lam__0___closed__1));
v___x_2911_ = l_Lean_Meta_PProdN_genMk___redArg(v___x_2909_, v___x_2910_, v_a_2908_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v_a_2912_; lean_object* v_snd_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_3034_; 
v_a_2912_ = lean_ctor_get(v___x_2911_, 0);
lean_inc(v_a_2912_);
lean_dec_ref(v___x_2911_);
v_snd_2913_ = lean_ctor_get(v_a_2912_, 1);
v_isSharedCheck_3034_ = !lean_is_exclusive(v_a_2912_);
if (v_isSharedCheck_3034_ == 0)
{
lean_object* v_unused_3035_; 
v_unused_3035_ = lean_ctor_get(v_a_2912_, 0);
lean_dec(v_unused_3035_);
v___x_2915_ = v_a_2912_;
v_isShared_2916_ = v_isSharedCheck_3034_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_snd_2913_);
lean_dec(v_a_2912_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_3034_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2917_; 
lean_inc(v_a_2893_);
v___x_2917_ = l_Lean_Meta_mkFixOfMonFun(v_a_2893_, v_a_2898_, v_snd_2913_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_object* v_a_2918_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; uint8_t v___y_2999_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v_options_3014_; uint8_t v_hasTrace_3015_; 
v_a_2918_ = lean_ctor_get(v___x_2917_, 0);
lean_inc(v_a_2918_);
lean_dec_ref(v___x_2917_);
v_options_3014_ = lean_ctor_get(v___y_2882_, 2);
v_hasTrace_3015_ = lean_ctor_get_uint8(v_options_3014_, sizeof(void*)*1);
if (v_hasTrace_3015_ == 0)
{
lean_del_object(v___x_2915_);
v___y_3005_ = v___y_2878_;
v___y_3006_ = v___y_2879_;
v___y_3007_ = v___y_2880_;
v___y_3008_ = v___y_2881_;
v___y_3009_ = v___y_2882_;
v___y_3010_ = v___y_2883_;
goto v___jp_3004_;
}
else
{
lean_object* v_inheritedTraceOptions_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; uint8_t v___x_3019_; 
v_inheritedTraceOptions_3016_ = lean_ctor_get(v___y_2882_, 13);
v___x_3017_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7));
v___x_3018_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10);
v___x_3019_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3016_, v_options_3014_, v___x_3018_);
if (v___x_3019_ == 0)
{
lean_del_object(v___x_2915_);
v___y_3005_ = v___y_2878_;
v___y_3006_ = v___y_2879_;
v___y_3007_ = v___y_2880_;
v___y_3008_ = v___y_2881_;
v___y_3009_ = v___y_2882_;
v___y_3010_ = v___y_2883_;
goto v___jp_3004_;
}
else
{
lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3023_; 
v___x_3020_ = lean_obj_once(&l_Lean_Elab_partialFixpoint___lam__0___closed__5, &l_Lean_Elab_partialFixpoint___lam__0___closed__5_once, _init_l_Lean_Elab_partialFixpoint___lam__0___closed__5);
lean_inc(v_a_2918_);
v___x_3021_ = l_Lean_MessageData_ofExpr(v_a_2918_);
if (v_isShared_2916_ == 0)
{
lean_ctor_set_tag(v___x_2915_, 7);
lean_ctor_set(v___x_2915_, 1, v___x_3021_);
lean_ctor_set(v___x_2915_, 0, v___x_3020_);
v___x_3023_ = v___x_2915_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v___x_3020_);
lean_ctor_set(v_reuseFailAlloc_3025_, 1, v___x_3021_);
v___x_3023_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
lean_object* v___x_3024_; 
v___x_3024_ = l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg(v___x_3017_, v___x_3023_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_dec_ref(v___x_3024_);
v___y_3005_ = v___y_2878_;
v___y_3006_ = v___y_2879_;
v___y_3007_ = v___y_2880_;
v___y_3008_ = v___y_2881_;
v___y_3009_ = v___y_2882_;
v___y_3010_ = v___y_2883_;
goto v___jp_3004_;
}
else
{
lean_dec(v_a_2918_);
lean_dec_ref(v___x_2905_);
lean_dec(v_a_2893_);
lean_dec_ref(v_fixedArgs_2877_);
lean_dec_ref(v_docCtx_2875_);
lean_dec_ref(v___x_2874_);
lean_dec_ref(v_hints_2873_);
lean_dec_ref(v_a_2871_);
lean_dec(v___x_2867_);
lean_dec_ref(v_preDefs_2866_);
lean_dec(v___x_2865_);
lean_dec_ref(v_perms_2864_);
return v___x_3024_;
}
}
}
}
v___jp_2919_:
{
uint8_t v___x_2927_; uint8_t v___x_2928_; lean_object* v___x_2929_; 
v___x_2927_ = 0;
v___x_2928_ = 1;
lean_inc(v_a_2893_);
v___x_2929_ = l_Lean_Meta_mkForallFVars(v_fixedArgs_2877_, v_a_2893_, v___x_2927_, v___x_2872_, v___x_2872_, v___x_2928_, v___y_2920_, v___y_2921_, v___y_2925_, v___y_2924_);
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_object* v_a_2930_; lean_object* v___x_2931_; 
v_a_2930_ = lean_ctor_get(v___x_2929_, 0);
lean_inc(v_a_2930_);
lean_dec_ref(v___x_2929_);
v___x_2931_ = l_Lean_Meta_mkLambdaFVars(v_fixedArgs_2877_, v_a_2918_, v___x_2927_, v___x_2872_, v___x_2927_, v___x_2872_, v___x_2928_, v___y_2920_, v___y_2921_, v___y_2925_, v___y_2924_);
lean_dec_ref(v_fixedArgs_2877_);
if (lean_obj_tag(v___x_2931_) == 0)
{
lean_object* v_a_2932_; lean_object* v_ref_2933_; uint8_t v_kind_2934_; lean_object* v_levelParams_2935_; lean_object* v_modifiers_2936_; lean_object* v_binders_2937_; lean_object* v_numSectionVars_2938_; lean_object* v_termination_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2972_; 
v_a_2932_ = lean_ctor_get(v___x_2931_, 0);
lean_inc(v_a_2932_);
lean_dec_ref(v___x_2931_);
v_ref_2933_ = lean_ctor_get(v___x_2874_, 0);
v_kind_2934_ = lean_ctor_get_uint8(v___x_2874_, sizeof(void*)*9);
v_levelParams_2935_ = lean_ctor_get(v___x_2874_, 1);
v_modifiers_2936_ = lean_ctor_get(v___x_2874_, 2);
v_binders_2937_ = lean_ctor_get(v___x_2874_, 4);
v_numSectionVars_2938_ = lean_ctor_get(v___x_2874_, 5);
v_termination_2939_ = lean_ctor_get(v___x_2874_, 8);
v_isSharedCheck_2972_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_2972_ == 0)
{
lean_object* v_unused_2973_; lean_object* v_unused_2974_; lean_object* v_unused_2975_; 
v_unused_2973_ = lean_ctor_get(v___x_2874_, 7);
lean_dec(v_unused_2973_);
v_unused_2974_ = lean_ctor_get(v___x_2874_, 6);
lean_dec(v_unused_2974_);
v_unused_2975_ = lean_ctor_get(v___x_2874_, 3);
lean_dec(v_unused_2975_);
v___x_2941_ = v___x_2874_;
v_isShared_2942_ = v_isSharedCheck_2972_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_termination_2939_);
lean_inc(v_numSectionVars_2938_);
lean_inc(v_binders_2937_);
lean_inc(v_modifiers_2936_);
lean_inc(v_levelParams_2935_);
lean_inc(v_ref_2933_);
lean_dec(v___x_2874_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2972_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2943_; 
lean_inc(v___x_2867_);
lean_inc(v___y_2926_);
lean_inc(v_levelParams_2935_);
v___x_2943_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg(v_perms_2864_, v_levelParams_2935_, v___y_2926_, v___x_2867_, v_a_2893_, v_preDefs_2866_, v___x_2867_, v___x_2865_, v___x_2905_, v___y_2923_, v___y_2922_, v___y_2920_, v___y_2921_, v___y_2925_, v___y_2924_);
lean_dec_ref(v_perms_2864_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v_a_2944_; lean_object* v___x_2946_; 
v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
lean_inc(v_a_2944_);
lean_dec_ref(v___x_2943_);
lean_inc(v___y_2926_);
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 7, v_a_2932_);
lean_ctor_set(v___x_2941_, 6, v_a_2930_);
lean_ctor_set(v___x_2941_, 3, v___y_2926_);
v___x_2946_ = v___x_2941_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_ref_2933_);
lean_ctor_set(v_reuseFailAlloc_2963_, 1, v_levelParams_2935_);
lean_ctor_set(v_reuseFailAlloc_2963_, 2, v_modifiers_2936_);
lean_ctor_set(v_reuseFailAlloc_2963_, 3, v___y_2926_);
lean_ctor_set(v_reuseFailAlloc_2963_, 4, v_binders_2937_);
lean_ctor_set(v_reuseFailAlloc_2963_, 5, v_numSectionVars_2938_);
lean_ctor_set(v_reuseFailAlloc_2963_, 6, v_a_2930_);
lean_ctor_set(v_reuseFailAlloc_2963_, 7, v_a_2932_);
lean_ctor_set(v_reuseFailAlloc_2963_, 8, v_termination_2939_);
lean_ctor_set_uint8(v_reuseFailAlloc_2963_, sizeof(void*)*9, v_kind_2934_);
v___x_2946_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
lean_object* v___x_2947_; 
lean_inc_ref(v_preDefs_2866_);
lean_inc_ref(v_docCtx_2875_);
v___x_2947_ = l_Lean_Elab_Mutual_addPreDefsFromUnary(v_docCtx_2875_, v_preDefs_2866_, v_a_2944_, v___x_2946_, v___x_2872_, v___y_2923_, v___y_2922_, v___y_2920_, v___y_2921_, v___y_2925_, v___y_2924_);
lean_dec(v_a_2944_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_object* v___x_2948_; 
lean_dec_ref(v___x_2947_);
lean_inc_ref(v_preDefs_2866_);
v___x_2948_ = l_Lean_Elab_addAndCompilePartialRec(v_docCtx_2875_, v_preDefs_2866_, v___y_2923_, v___y_2922_, v___y_2920_, v___y_2921_, v___y_2925_, v___y_2924_);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_object* v___x_2949_; 
lean_dec_ref(v___x_2948_);
v___x_2949_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__22___redArg(v_sz_2876_, v___x_2869_, v_preDefs_2866_, v___y_2920_, v___y_2921_, v___y_2925_, v___y_2924_);
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_object* v_a_2950_; size_t v_sz_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
v_a_2950_ = lean_ctor_get(v___x_2949_, 0);
lean_inc_n(v_a_2950_, 2);
lean_dec_ref(v___x_2949_);
v_sz_2951_ = lean_array_size(v_hints_2873_);
v___x_2952_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__23(v_sz_2951_, v___x_2869_, v_hints_2873_);
v___x_2953_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo(v_a_2950_, v___y_2926_, v_a_2871_, v___x_2952_, v___y_2920_, v___y_2921_, v___y_2925_, v___y_2924_);
if (lean_obj_tag(v___x_2953_) == 0)
{
lean_object* v___x_2954_; 
lean_dec_ref(v___x_2953_);
v___x_2954_ = l_Lean_Elab_Mutual_addPreDefAttributes(v_a_2950_, v___y_2923_, v___y_2922_, v___y_2920_, v___y_2921_, v___y_2925_, v___y_2924_);
return v___x_2954_;
}
else
{
lean_dec(v_a_2950_);
return v___x_2953_;
}
}
else
{
lean_object* v_a_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2962_; 
lean_dec(v___y_2926_);
lean_dec_ref(v_hints_2873_);
lean_dec_ref(v_a_2871_);
v_a_2955_ = lean_ctor_get(v___x_2949_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2949_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2957_ = v___x_2949_;
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_a_2955_);
lean_dec(v___x_2949_);
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
else
{
lean_dec(v___y_2926_);
lean_dec_ref(v_hints_2873_);
lean_dec_ref(v_a_2871_);
lean_dec_ref(v_preDefs_2866_);
return v___x_2948_;
}
}
else
{
lean_dec(v___y_2926_);
lean_dec_ref(v_docCtx_2875_);
lean_dec_ref(v_hints_2873_);
lean_dec_ref(v_a_2871_);
lean_dec_ref(v_preDefs_2866_);
return v___x_2947_;
}
}
}
else
{
lean_object* v_a_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2971_; 
lean_del_object(v___x_2941_);
lean_dec_ref(v_termination_2939_);
lean_dec(v_numSectionVars_2938_);
lean_dec(v_binders_2937_);
lean_dec_ref(v_modifiers_2936_);
lean_dec(v_levelParams_2935_);
lean_dec(v_ref_2933_);
lean_dec(v_a_2932_);
lean_dec(v_a_2930_);
lean_dec(v___y_2926_);
lean_dec_ref(v_docCtx_2875_);
lean_dec_ref(v_hints_2873_);
lean_dec_ref(v_a_2871_);
lean_dec_ref(v_preDefs_2866_);
v_a_2964_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2966_ = v___x_2943_;
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_a_2964_);
lean_dec(v___x_2943_);
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
}
else
{
lean_object* v_a_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2983_; 
lean_dec(v_a_2930_);
lean_dec(v___y_2926_);
lean_dec_ref(v___x_2905_);
lean_dec(v_a_2893_);
lean_dec_ref(v_docCtx_2875_);
lean_dec_ref(v___x_2874_);
lean_dec_ref(v_hints_2873_);
lean_dec_ref(v_a_2871_);
lean_dec(v___x_2867_);
lean_dec_ref(v_preDefs_2866_);
lean_dec(v___x_2865_);
lean_dec_ref(v_perms_2864_);
v_a_2976_ = lean_ctor_get(v___x_2931_, 0);
v_isSharedCheck_2983_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2978_ = v___x_2931_;
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_a_2976_);
lean_dec(v___x_2931_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2981_; 
if (v_isShared_2979_ == 0)
{
v___x_2981_ = v___x_2978_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_a_2976_);
v___x_2981_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
return v___x_2981_;
}
}
}
}
else
{
lean_object* v_a_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2991_; 
lean_dec(v___y_2926_);
lean_dec(v_a_2918_);
lean_dec_ref(v___x_2905_);
lean_dec(v_a_2893_);
lean_dec_ref(v_fixedArgs_2877_);
lean_dec_ref(v_docCtx_2875_);
lean_dec_ref(v___x_2874_);
lean_dec_ref(v_hints_2873_);
lean_dec_ref(v_a_2871_);
lean_dec(v___x_2867_);
lean_dec_ref(v_preDefs_2866_);
lean_dec(v___x_2865_);
lean_dec_ref(v_perms_2864_);
v_a_2984_ = lean_ctor_get(v___x_2929_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2929_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2986_ = v___x_2929_;
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_dec(v___x_2929_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2989_; 
if (v_isShared_2987_ == 0)
{
v___x_2989_ = v___x_2986_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_a_2984_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
}
}
v___jp_2992_:
{
if (v___y_2999_ == 0)
{
lean_object* v_declName_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v_declName_3000_ = lean_ctor_get(v___x_2874_, 3);
v___x_3001_ = ((lean_object*)(l_Lean_Elab_partialFixpoint___lam__0___closed__3));
lean_inc(v_declName_3000_);
v___x_3002_ = l_Lean_Name_append(v_declName_3000_, v___x_3001_);
v___y_2920_ = v___y_2993_;
v___y_2921_ = v___y_2994_;
v___y_2922_ = v___y_2996_;
v___y_2923_ = v___y_2995_;
v___y_2924_ = v___y_2997_;
v___y_2925_ = v___y_2998_;
v___y_2926_ = v___x_3002_;
goto v___jp_2919_;
}
else
{
lean_object* v_declName_3003_; 
v_declName_3003_ = lean_ctor_get(v___x_2874_, 3);
lean_inc(v_declName_3003_);
v___y_2920_ = v___y_2993_;
v___y_2921_ = v___y_2994_;
v___y_2922_ = v___y_2996_;
v___y_2923_ = v___y_2995_;
v___y_2924_ = v___y_2997_;
v___y_2925_ = v___y_2998_;
v___y_2926_ = v_declName_3003_;
goto v___jp_2919_;
}
}
v___jp_3004_:
{
lean_object* v___x_3011_; uint8_t v___x_3012_; 
v___x_3011_ = lean_unsigned_to_nat(1u);
v___x_3012_ = lean_nat_dec_eq(v___x_2867_, v___x_3011_);
if (v___x_3012_ == 0)
{
v___y_2993_ = v___y_3007_;
v___y_2994_ = v___y_3008_;
v___y_2995_ = v___y_3005_;
v___y_2996_ = v___y_3006_;
v___y_2997_ = v___y_3010_;
v___y_2998_ = v___y_3009_;
v___y_2999_ = v___x_3012_;
goto v___jp_2992_;
}
else
{
uint8_t v___x_3013_; 
lean_inc_ref(v_a_2871_);
v___x_3013_ = l_Lean_Elab_FixedParamPerms_fixedArePrefix(v_a_2871_);
v___y_2993_ = v___y_3007_;
v___y_2994_ = v___y_3008_;
v___y_2995_ = v___y_3005_;
v___y_2996_ = v___y_3006_;
v___y_2997_ = v___y_3010_;
v___y_2998_ = v___y_3009_;
v___y_2999_ = v___x_3013_;
goto v___jp_2992_;
}
}
}
else
{
lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3033_; 
lean_del_object(v___x_2915_);
lean_dec_ref(v___x_2905_);
lean_dec(v_a_2893_);
lean_dec_ref(v_fixedArgs_2877_);
lean_dec_ref(v_docCtx_2875_);
lean_dec_ref(v___x_2874_);
lean_dec_ref(v_hints_2873_);
lean_dec_ref(v_a_2871_);
lean_dec(v___x_2867_);
lean_dec_ref(v_preDefs_2866_);
lean_dec(v___x_2865_);
lean_dec_ref(v_perms_2864_);
v_a_3026_ = lean_ctor_get(v___x_2917_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_2917_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3028_ = v___x_2917_;
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___x_2917_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3031_; 
if (v_isShared_3029_ == 0)
{
v___x_3031_ = v___x_3028_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_a_3026_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
}
}
}
else
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3043_; 
lean_dec_ref(v___x_2905_);
lean_dec(v_a_2898_);
lean_dec(v_a_2893_);
lean_dec_ref(v_fixedArgs_2877_);
lean_dec_ref(v_docCtx_2875_);
lean_dec_ref(v___x_2874_);
lean_dec_ref(v_hints_2873_);
lean_dec_ref(v_a_2871_);
lean_dec(v___x_2867_);
lean_dec_ref(v_preDefs_2866_);
lean_dec(v___x_2865_);
lean_dec_ref(v_perms_2864_);
v_a_3036_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3038_ = v___x_2911_;
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_2911_);
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
lean_object* v_a_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3051_; 
lean_dec_ref(v___x_2905_);
lean_dec(v_a_2898_);
lean_dec(v_a_2893_);
lean_dec_ref(v_fixedArgs_2877_);
lean_dec_ref(v_docCtx_2875_);
lean_dec_ref(v___x_2874_);
lean_dec_ref(v_hints_2873_);
lean_dec_ref(v_a_2871_);
lean_dec(v___x_2867_);
lean_dec_ref(v_preDefs_2866_);
lean_dec(v___x_2865_);
lean_dec_ref(v_perms_2864_);
v_a_3044_ = lean_ctor_get(v___x_2907_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3046_ = v___x_2907_;
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_dec(v___x_2907_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3049_; 
if (v_isShared_3047_ == 0)
{
v___x_3049_ = v___x_3046_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_a_3044_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
}
else
{
lean_object* v_a_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3059_; 
lean_dec(v_a_2901_);
lean_dec(v_a_2898_);
lean_dec(v_a_2896_);
lean_dec(v_a_2893_);
lean_dec(v_a_2890_);
lean_dec_ref(v_fixedArgs_2877_);
lean_dec_ref(v_docCtx_2875_);
lean_dec_ref(v___x_2874_);
lean_dec_ref(v_hints_2873_);
lean_dec_ref(v_a_2871_);
lean_dec(v___x_2867_);
lean_dec_ref(v_preDefs_2866_);
lean_dec(v___x_2865_);
lean_dec_ref(v_perms_2864_);
v_a_3052_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3054_ = v___x_2903_;
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_a_3052_);
lean_dec(v___x_2903_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3057_; 
if (v_isShared_3055_ == 0)
{
v___x_3057_ = v___x_3054_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_a_3052_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
}
}
else
{
lean_object* v_a_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3067_; 
lean_dec(v_a_2898_);
lean_dec(v_a_2896_);
lean_dec(v_a_2893_);
lean_dec(v_a_2890_);
lean_dec_ref(v_fixedArgs_2877_);
lean_dec_ref(v_docCtx_2875_);
lean_dec_ref(v___x_2874_);
lean_dec_ref(v_hints_2873_);
lean_dec_ref(v_a_2871_);
lean_dec_ref(v___x_2870_);
lean_dec_ref(v___x_2868_);
lean_dec(v___x_2867_);
lean_dec_ref(v_preDefs_2866_);
lean_dec(v___x_2865_);
lean_dec_ref(v_perms_2864_);
v_a_3060_ = lean_ctor_get(v___x_2900_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_2900_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3062_ = v___x_2900_;
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_a_3060_);
lean_dec(v___x_2900_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3065_; 
if (v_isShared_3063_ == 0)
{
v___x_3065_ = v___x_3062_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_a_3060_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
}
}
else
{
lean_object* v_a_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3075_; 
lean_dec(v_a_2896_);
lean_dec(v_a_2893_);
lean_dec(v_a_2890_);
lean_dec_ref(v_fixedArgs_2877_);
lean_dec_ref(v_docCtx_2875_);
lean_dec_ref(v___x_2874_);
lean_dec_ref(v_hints_2873_);
lean_dec_ref(v_a_2871_);
lean_dec_ref(v___x_2870_);
lean_dec_ref(v___x_2868_);
lean_dec(v___x_2867_);
lean_dec_ref(v_preDefs_2866_);
lean_dec(v___x_2865_);
lean_dec_ref(v_perms_2864_);
v_a_3068_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3070_ = v___x_2897_;
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_a_3068_);
lean_dec(v___x_2897_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3073_; 
if (v_isShared_3071_ == 0)
{
v___x_3073_ = v___x_3070_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_a_3068_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
}
else
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3083_; 
lean_dec(v_a_2893_);
lean_dec(v_a_2890_);
lean_dec_ref(v_fixedArgs_2877_);
lean_dec_ref(v_docCtx_2875_);
lean_dec_ref(v___x_2874_);
lean_dec_ref(v_hints_2873_);
lean_dec_ref(v_a_2871_);
lean_dec_ref(v___x_2870_);
lean_dec_ref(v___x_2868_);
lean_dec(v___x_2867_);
lean_dec_ref(v_preDefs_2866_);
lean_dec(v___x_2865_);
lean_dec_ref(v_perms_2864_);
v_a_3076_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3078_ = v___x_2895_;
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_2895_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3081_; 
if (v_isShared_3079_ == 0)
{
v___x_3081_ = v___x_3078_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_a_3076_);
v___x_3081_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
return v___x_3081_;
}
}
}
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
lean_dec(v_a_2890_);
lean_dec(v_a_2888_);
lean_dec_ref(v_fixedArgs_2877_);
lean_dec_ref(v_docCtx_2875_);
lean_dec_ref(v___x_2874_);
lean_dec_ref(v_hints_2873_);
lean_dec_ref(v_a_2871_);
lean_dec_ref(v___x_2870_);
lean_dec_ref(v___x_2868_);
lean_dec(v___x_2867_);
lean_dec_ref(v_preDefs_2866_);
lean_dec(v___x_2865_);
lean_dec_ref(v_perms_2864_);
v_a_3084_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3086_ = v___x_2892_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_2892_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3089_; 
if (v_isShared_3087_ == 0)
{
v___x_3089_ = v___x_3086_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3084_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
}
else
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3099_; 
lean_dec(v_a_2888_);
lean_dec_ref(v_fixedArgs_2877_);
lean_dec_ref(v_docCtx_2875_);
lean_dec_ref(v___x_2874_);
lean_dec_ref(v_hints_2873_);
lean_dec_ref(v_a_2871_);
lean_dec_ref(v___x_2870_);
lean_dec_ref(v___x_2868_);
lean_dec(v___x_2867_);
lean_dec_ref(v_preDefs_2866_);
lean_dec(v___x_2865_);
lean_dec_ref(v_perms_2864_);
v_a_3092_ = lean_ctor_get(v___x_2889_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3094_ = v___x_2889_;
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_2889_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3097_; 
if (v_isShared_3095_ == 0)
{
v___x_3097_ = v___x_3094_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_a_3092_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
}
}
}
}
else
{
lean_object* v_a_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3107_; 
lean_dec_ref(v_fixedArgs_2877_);
lean_dec_ref(v_docCtx_2875_);
lean_dec_ref(v___x_2874_);
lean_dec_ref(v_hints_2873_);
lean_dec_ref(v_a_2871_);
lean_dec_ref(v___x_2870_);
lean_dec_ref(v___x_2868_);
lean_dec(v___x_2867_);
lean_dec_ref(v_preDefs_2866_);
lean_dec(v___x_2865_);
lean_dec_ref(v_perms_2864_);
v_a_3100_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3102_ = v___x_2887_;
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_dec(v___x_2887_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3105_; 
if (v_isShared_3103_ == 0)
{
v___x_3105_ = v___x_3102_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v_a_3100_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_partialFixpoint___lam__0___boxed(lean_object** _args){
lean_object* v_a_3108_ = _args[0];
lean_object* v_perms_3109_ = _args[1];
lean_object* v___x_3110_ = _args[2];
lean_object* v_preDefs_3111_ = _args[3];
lean_object* v___x_3112_ = _args[4];
lean_object* v___x_3113_ = _args[5];
lean_object* v___x_3114_ = _args[6];
lean_object* v___x_3115_ = _args[7];
lean_object* v_a_3116_ = _args[8];
lean_object* v___x_3117_ = _args[9];
lean_object* v_hints_3118_ = _args[10];
lean_object* v___x_3119_ = _args[11];
lean_object* v_docCtx_3120_ = _args[12];
lean_object* v_sz_3121_ = _args[13];
lean_object* v_fixedArgs_3122_ = _args[14];
lean_object* v___y_3123_ = _args[15];
lean_object* v___y_3124_ = _args[16];
lean_object* v___y_3125_ = _args[17];
lean_object* v___y_3126_ = _args[18];
lean_object* v___y_3127_ = _args[19];
lean_object* v___y_3128_ = _args[20];
lean_object* v___y_3129_ = _args[21];
_start:
{
size_t v___x_58091__boxed_3130_; uint8_t v___x_58094__boxed_3131_; size_t v_sz_boxed_3132_; lean_object* v_res_3133_; 
v___x_58091__boxed_3130_ = lean_unbox_usize(v___x_3114_);
lean_dec(v___x_3114_);
v___x_58094__boxed_3131_ = lean_unbox(v___x_3117_);
v_sz_boxed_3132_ = lean_unbox_usize(v_sz_3121_);
lean_dec(v_sz_3121_);
v_res_3133_ = l_Lean_Elab_partialFixpoint___lam__0(v_a_3108_, v_perms_3109_, v___x_3110_, v_preDefs_3111_, v___x_3112_, v___x_3113_, v___x_58091__boxed_3130_, v___x_3115_, v_a_3116_, v___x_58094__boxed_3131_, v_hints_3118_, v___x_3119_, v_docCtx_3120_, v_sz_boxed_3132_, v_fixedArgs_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
lean_dec(v___y_3126_);
lean_dec_ref(v___y_3125_);
lean_dec(v___y_3124_);
lean_dec_ref(v___y_3123_);
lean_dec_ref(v_a_3108_);
return v_res_3133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0_spec__0(lean_object* v_as_3134_, size_t v_i_3135_, size_t v_stop_3136_, lean_object* v_b_3137_){
_start:
{
lean_object* v___y_3139_; uint8_t v___x_3143_; 
v___x_3143_ = lean_usize_dec_eq(v_i_3135_, v_stop_3136_);
if (v___x_3143_ == 0)
{
lean_object* v___x_3144_; lean_object* v_termination_3145_; lean_object* v_partialFixpoint_x3f_3146_; 
v___x_3144_ = lean_array_uget_borrowed(v_as_3134_, v_i_3135_);
v_termination_3145_ = lean_ctor_get(v___x_3144_, 8);
v_partialFixpoint_x3f_3146_ = lean_ctor_get(v_termination_3145_, 3);
if (lean_obj_tag(v_partialFixpoint_x3f_3146_) == 0)
{
v___y_3139_ = v_b_3137_;
goto v___jp_3138_;
}
else
{
lean_object* v_val_3147_; lean_object* v___x_3148_; 
v_val_3147_ = lean_ctor_get(v_partialFixpoint_x3f_3146_, 0);
lean_inc(v_val_3147_);
v___x_3148_ = lean_array_push(v_b_3137_, v_val_3147_);
v___y_3139_ = v___x_3148_;
goto v___jp_3138_;
}
}
else
{
return v_b_3137_;
}
v___jp_3138_:
{
size_t v___x_3140_; size_t v___x_3141_; 
v___x_3140_ = ((size_t)1ULL);
v___x_3141_ = lean_usize_add(v_i_3135_, v___x_3140_);
v_i_3135_ = v___x_3141_;
v_b_3137_ = v___y_3139_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0_spec__0___boxed(lean_object* v_as_3149_, lean_object* v_i_3150_, lean_object* v_stop_3151_, lean_object* v_b_3152_){
_start:
{
size_t v_i_boxed_3153_; size_t v_stop_boxed_3154_; lean_object* v_res_3155_; 
v_i_boxed_3153_ = lean_unbox_usize(v_i_3150_);
lean_dec(v_i_3150_);
v_stop_boxed_3154_ = lean_unbox_usize(v_stop_3151_);
lean_dec(v_stop_3151_);
v_res_3155_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0_spec__0(v_as_3149_, v_i_boxed_3153_, v_stop_boxed_3154_, v_b_3152_);
lean_dec_ref(v_as_3149_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0(lean_object* v_as_3158_, lean_object* v_start_3159_, lean_object* v_stop_3160_){
_start:
{
lean_object* v___x_3161_; uint8_t v___x_3162_; 
v___x_3161_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0___closed__0));
v___x_3162_ = lean_nat_dec_lt(v_start_3159_, v_stop_3160_);
if (v___x_3162_ == 0)
{
return v___x_3161_;
}
else
{
lean_object* v___x_3163_; uint8_t v___x_3164_; 
v___x_3163_ = lean_array_get_size(v_as_3158_);
v___x_3164_ = lean_nat_dec_le(v_stop_3160_, v___x_3163_);
if (v___x_3164_ == 0)
{
uint8_t v___x_3165_; 
v___x_3165_ = lean_nat_dec_lt(v_start_3159_, v___x_3163_);
if (v___x_3165_ == 0)
{
return v___x_3161_;
}
else
{
size_t v___x_3166_; size_t v___x_3167_; lean_object* v___x_3168_; 
v___x_3166_ = lean_usize_of_nat(v_start_3159_);
v___x_3167_ = lean_usize_of_nat(v___x_3163_);
v___x_3168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0_spec__0(v_as_3158_, v___x_3166_, v___x_3167_, v___x_3161_);
return v___x_3168_;
}
}
else
{
size_t v___x_3169_; size_t v___x_3170_; lean_object* v___x_3171_; 
v___x_3169_ = lean_usize_of_nat(v_start_3159_);
v___x_3170_ = lean_usize_of_nat(v_stop_3160_);
v___x_3171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0_spec__0(v_as_3158_, v___x_3169_, v___x_3170_, v___x_3161_);
return v___x_3171_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0___boxed(lean_object* v_as_3172_, lean_object* v_start_3173_, lean_object* v_stop_3174_){
_start:
{
lean_object* v_res_3175_; 
v_res_3175_ = l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0(v_as_3172_, v_start_3173_, v_stop_3174_);
lean_dec(v_stop_3174_);
lean_dec(v_start_3173_);
lean_dec_ref(v_as_3172_);
return v_res_3175_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27_spec__33(uint8_t v___x_3176_, lean_object* v_as_3177_, size_t v_i_3178_, size_t v_stop_3179_){
_start:
{
uint8_t v___x_3180_; 
v___x_3180_ = lean_usize_dec_eq(v_i_3178_, v_stop_3179_);
if (v___x_3180_ == 0)
{
lean_object* v___x_3181_; uint8_t v_fixpointType_3182_; uint8_t v___x_3183_; uint8_t v___y_3185_; uint8_t v___x_3189_; 
v___x_3181_ = lean_array_uget_borrowed(v_as_3177_, v_i_3178_);
v_fixpointType_3182_ = lean_ctor_get_uint8(v___x_3181_, sizeof(void*)*2);
v___x_3183_ = 1;
v___x_3189_ = l_Lean_Elab_isLatticeTheoretic(v_fixpointType_3182_);
if (v___x_3189_ == 0)
{
v___y_3185_ = v___x_3176_;
goto v___jp_3184_;
}
else
{
v___y_3185_ = v___x_3180_;
goto v___jp_3184_;
}
v___jp_3184_:
{
if (v___y_3185_ == 0)
{
size_t v___x_3186_; size_t v___x_3187_; 
v___x_3186_ = ((size_t)1ULL);
v___x_3187_ = lean_usize_add(v_i_3178_, v___x_3186_);
v_i_3178_ = v___x_3187_;
goto _start;
}
else
{
return v___x_3183_;
}
}
}
else
{
uint8_t v___x_3190_; 
v___x_3190_ = 0;
return v___x_3190_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27_spec__33___boxed(lean_object* v___x_3191_, lean_object* v_as_3192_, lean_object* v_i_3193_, lean_object* v_stop_3194_){
_start:
{
uint8_t v___x_58617__boxed_3195_; size_t v_i_boxed_3196_; size_t v_stop_boxed_3197_; uint8_t v_res_3198_; lean_object* v_r_3199_; 
v___x_58617__boxed_3195_ = lean_unbox(v___x_3191_);
v_i_boxed_3196_ = lean_unbox_usize(v_i_3193_);
lean_dec(v_i_3193_);
v_stop_boxed_3197_ = lean_unbox_usize(v_stop_3194_);
lean_dec(v_stop_3194_);
v_res_3198_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27_spec__33(v___x_58617__boxed_3195_, v_as_3192_, v_i_boxed_3196_, v_stop_boxed_3197_);
lean_dec_ref(v_as_3192_);
v_r_3199_ = lean_box(v_res_3198_);
return v_r_3199_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27(uint8_t v___x_3200_, lean_object* v_as_3201_, size_t v_i_3202_, size_t v_stop_3203_){
_start:
{
uint8_t v___x_3204_; 
v___x_3204_ = lean_usize_dec_eq(v_i_3202_, v_stop_3203_);
if (v___x_3204_ == 0)
{
lean_object* v___x_3205_; uint8_t v_fixpointType_3206_; uint8_t v___x_3207_; uint8_t v___y_3209_; uint8_t v___x_3213_; 
v___x_3205_ = lean_array_uget_borrowed(v_as_3201_, v_i_3202_);
v_fixpointType_3206_ = lean_ctor_get_uint8(v___x_3205_, sizeof(void*)*2);
v___x_3207_ = 1;
v___x_3213_ = l_Lean_Elab_isLatticeTheoretic(v_fixpointType_3206_);
if (v___x_3213_ == 0)
{
v___y_3209_ = v___x_3200_;
goto v___jp_3208_;
}
else
{
v___y_3209_ = v___x_3204_;
goto v___jp_3208_;
}
v___jp_3208_:
{
if (v___y_3209_ == 0)
{
size_t v___x_3210_; size_t v___x_3211_; uint8_t v___x_3212_; 
v___x_3210_ = ((size_t)1ULL);
v___x_3211_ = lean_usize_add(v_i_3202_, v___x_3210_);
v___x_3212_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27_spec__33(v___x_3200_, v_as_3201_, v___x_3211_, v_stop_3203_);
return v___x_3212_;
}
else
{
return v___x_3207_;
}
}
}
else
{
uint8_t v___x_3214_; 
v___x_3214_ = 0;
return v___x_3214_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27___boxed(lean_object* v___x_3215_, lean_object* v_as_3216_, lean_object* v_i_3217_, lean_object* v_stop_3218_){
_start:
{
uint8_t v___x_58640__boxed_3219_; size_t v_i_boxed_3220_; size_t v_stop_boxed_3221_; uint8_t v_res_3222_; lean_object* v_r_3223_; 
v___x_58640__boxed_3219_ = lean_unbox(v___x_3215_);
v_i_boxed_3220_ = lean_unbox_usize(v_i_3217_);
lean_dec(v_i_3217_);
v_stop_boxed_3221_ = lean_unbox_usize(v_stop_3218_);
lean_dec(v_stop_3218_);
v_res_3222_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27(v___x_58640__boxed_3219_, v_as_3216_, v_i_boxed_3220_, v_stop_boxed_3221_);
lean_dec_ref(v_as_3216_);
v_r_3223_ = lean_box(v_res_3222_);
return v_r_3223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__7(size_t v_sz_3224_, size_t v_i_3225_, lean_object* v_bs_3226_){
_start:
{
uint8_t v___x_3227_; 
v___x_3227_ = lean_usize_dec_lt(v_i_3225_, v_sz_3224_);
if (v___x_3227_ == 0)
{
return v_bs_3226_;
}
else
{
lean_object* v_v_3228_; lean_object* v_declName_3229_; lean_object* v___x_3230_; lean_object* v_bs_x27_3231_; size_t v___x_3232_; size_t v___x_3233_; lean_object* v___x_3234_; 
v_v_3228_ = lean_array_uget_borrowed(v_bs_3226_, v_i_3225_);
v_declName_3229_ = lean_ctor_get(v_v_3228_, 3);
lean_inc(v_declName_3229_);
v___x_3230_ = lean_unsigned_to_nat(0u);
v_bs_x27_3231_ = lean_array_uset(v_bs_3226_, v_i_3225_, v___x_3230_);
v___x_3232_ = ((size_t)1ULL);
v___x_3233_ = lean_usize_add(v_i_3225_, v___x_3232_);
v___x_3234_ = lean_array_uset(v_bs_x27_3231_, v_i_3225_, v_declName_3229_);
v_i_3225_ = v___x_3233_;
v_bs_3226_ = v___x_3234_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__7___boxed(lean_object* v_sz_3236_, lean_object* v_i_3237_, lean_object* v_bs_3238_){
_start:
{
size_t v_sz_boxed_3239_; size_t v_i_boxed_3240_; lean_object* v_res_3241_; 
v_sz_boxed_3239_ = lean_unbox_usize(v_sz_3236_);
lean_dec(v_sz_3236_);
v_i_boxed_3240_ = lean_unbox_usize(v_i_3237_);
lean_dec(v_i_3237_);
v_res_3241_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__7(v_sz_boxed_3239_, v_i_boxed_3240_, v_bs_3238_);
return v_res_3241_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3243_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__0));
v___x_3244_ = l_Lean_stringToMessageData(v___x_3243_);
return v___x_3244_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; 
v___x_3246_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__2));
v___x_3247_ = l_Lean_stringToMessageData(v___x_3246_);
return v___x_3247_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__11(void){
_start:
{
lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; 
v___x_3260_ = lean_box(0);
v___x_3261_ = lean_unsigned_to_nat(2u);
v___x_3262_ = lean_mk_empty_array_with_capacity(v___x_3261_);
v___x_3263_ = lean_array_push(v___x_3262_, v___x_3260_);
return v___x_3263_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2(lean_object* v_declName_3266_, lean_object* v_type_3267_, lean_object* v_xs_3268_, lean_object* v___x_3269_, lean_object* v___x_3270_, lean_object* v_____r_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_){
_start:
{
lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
v___x_3279_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__1, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__1_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__1);
v___x_3280_ = l_Lean_MessageData_ofName(v_declName_3266_);
v___x_3281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3279_);
lean_ctor_set(v___x_3281_, 1, v___x_3280_);
v___x_3282_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__3, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__3_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__3);
v___x_3283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3281_);
lean_ctor_set(v___x_3283_, 1, v___x_3282_);
v___x_3284_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__4));
v___x_3285_ = l_Lean_Elab_mkInhabitantFor(v___x_3283_, v___x_3284_, v_type_3267_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_);
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_object* v_a_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
v_a_3286_ = lean_ctor_get(v___x_3285_, 0);
lean_inc(v_a_3286_);
lean_dec_ref(v___x_3285_);
v___x_3287_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__7));
v___x_3288_ = l_Lean_mkAppN(v_a_3286_, v_xs_3268_);
v___x_3289_ = lean_unsigned_to_nat(1u);
v___x_3290_ = lean_mk_empty_array_with_capacity(v___x_3289_);
v___x_3291_ = lean_array_push(v___x_3290_, v___x_3288_);
v___x_3292_ = l_Lean_Meta_mkAppM(v___x_3287_, v___x_3291_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_);
if (lean_obj_tag(v___x_3292_) == 0)
{
lean_object* v_a_3293_; lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3317_; 
v_a_3293_ = lean_ctor_get(v___x_3292_, 0);
v_isSharedCheck_3317_ = !lean_is_exclusive(v___x_3292_);
if (v_isSharedCheck_3317_ == 0)
{
v___x_3295_ = v___x_3292_;
v_isShared_3296_ = v_isSharedCheck_3317_;
goto v_resetjp_3294_;
}
else
{
lean_inc(v_a_3293_);
lean_dec(v___x_3292_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3317_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
lean_object* v___x_3297_; lean_object* v___x_3299_; 
v___x_3297_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__10));
if (v_isShared_3296_ == 0)
{
lean_ctor_set_tag(v___x_3295_, 1);
v___x_3299_ = v___x_3295_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_a_3293_);
v___x_3299_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3300_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__11, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__11_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__11);
v___x_3301_ = lean_array_push(v___x_3300_, v___x_3299_);
v___x_3302_ = l_Lean_Meta_mkAppOptM(v___x_3297_, v___x_3301_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_);
if (lean_obj_tag(v___x_3302_) == 0)
{
lean_object* v_a_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3315_; 
v_a_3303_ = lean_ctor_get(v___x_3302_, 0);
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3302_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3305_ = v___x_3302_;
v_isShared_3306_ = v_isSharedCheck_3315_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_a_3303_);
lean_dec(v___x_3302_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3315_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3311_; 
v___x_3307_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__12));
v___x_3308_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__13));
v___x_3309_ = l_Lean_Name_mkStr4(v___x_3269_, v___x_3270_, v___x_3307_, v___x_3308_);
if (v_isShared_3306_ == 0)
{
lean_ctor_set_tag(v___x_3305_, 1);
v___x_3311_ = v___x_3305_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v_a_3303_);
v___x_3311_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3312_ = lean_array_push(v___x_3300_, v___x_3311_);
v___x_3313_ = l_Lean_Meta_mkAppOptM(v___x_3309_, v___x_3312_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_);
return v___x_3313_;
}
}
}
else
{
lean_dec_ref(v___x_3270_);
lean_dec_ref(v___x_3269_);
return v___x_3302_;
}
}
}
}
else
{
lean_dec_ref(v___x_3270_);
lean_dec_ref(v___x_3269_);
return v___x_3292_;
}
}
else
{
lean_dec_ref(v___x_3270_);
lean_dec_ref(v___x_3269_);
return v___x_3285_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___boxed(lean_object* v_declName_3318_, lean_object* v_type_3319_, lean_object* v_xs_3320_, lean_object* v___x_3321_, lean_object* v___x_3322_, lean_object* v_____r_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_){
_start:
{
lean_object* v_res_3331_; 
v_res_3331_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2(v_declName_3318_, v_type_3319_, v_xs_3320_, v___x_3321_, v___x_3322_, v_____r_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
lean_dec(v___y_3329_);
lean_dec_ref(v___y_3328_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
lean_dec(v___y_3325_);
lean_dec_ref(v___y_3324_);
lean_dec_ref(v_xs_3320_);
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__4(lean_object* v_a_3332_, lean_object* v_a_3333_){
_start:
{
if (lean_obj_tag(v_a_3332_) == 0)
{
lean_object* v___x_3334_; 
v___x_3334_ = l_List_reverse___redArg(v_a_3333_);
return v___x_3334_;
}
else
{
lean_object* v_head_3335_; lean_object* v_tail_3336_; lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3345_; 
v_head_3335_ = lean_ctor_get(v_a_3332_, 0);
v_tail_3336_ = lean_ctor_get(v_a_3332_, 1);
v_isSharedCheck_3345_ = !lean_is_exclusive(v_a_3332_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3338_ = v_a_3332_;
v_isShared_3339_ = v_isSharedCheck_3345_;
goto v_resetjp_3337_;
}
else
{
lean_inc(v_tail_3336_);
lean_inc(v_head_3335_);
lean_dec(v_a_3332_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3345_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
lean_object* v___x_3340_; lean_object* v___x_3342_; 
v___x_3340_ = l_Lean_MessageData_ofExpr(v_head_3335_);
if (v_isShared_3339_ == 0)
{
lean_ctor_set(v___x_3338_, 1, v_a_3333_);
lean_ctor_set(v___x_3338_, 0, v___x_3340_);
v___x_3342_ = v___x_3338_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v___x_3340_);
lean_ctor_set(v_reuseFailAlloc_3344_, 1, v_a_3333_);
v___x_3342_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
v_a_3332_ = v_tail_3336_;
v_a_3333_ = v___x_3342_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_3347_; lean_object* v___x_3348_; 
v___x_3347_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__0));
v___x_3348_ = l_Lean_stringToMessageData(v___x_3347_);
return v___x_3348_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__3(void){
_start:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3350_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__2));
v___x_3351_ = l_Lean_stringToMessageData(v___x_3350_);
return v___x_3351_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__7(void){
_start:
{
lean_object* v___x_3358_; lean_object* v___x_3359_; 
v___x_3358_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__6));
v___x_3359_ = l_Lean_stringToMessageData(v___x_3358_);
return v___x_3359_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__9(void){
_start:
{
lean_object* v___x_3361_; lean_object* v___x_3362_; 
v___x_3361_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__8));
v___x_3362_ = l_Lean_stringToMessageData(v___x_3361_);
return v___x_3362_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__11(void){
_start:
{
lean_object* v___x_3364_; lean_object* v___x_3365_; 
v___x_3364_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__10));
v___x_3365_ = l_Lean_stringToMessageData(v___x_3364_);
return v___x_3365_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3(uint8_t v_isZero_3366_, lean_object* v_declName_3367_, lean_object* v_type_3368_, uint8_t v_fixpointType_3369_, lean_object* v___f_3370_, lean_object* v___f_3371_, lean_object* v_value_3372_, lean_object* v_xs_3373_, lean_object* v___body_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_){
_start:
{
lean_object* v_inst_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v_options_3408_; lean_object* v_inheritedTraceOptions_3409_; uint8_t v_hasTrace_3410_; lean_object* v_cls_3411_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; uint8_t v___y_3421_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3462_; 
v_options_3408_ = lean_ctor_get(v___y_3379_, 2);
v_inheritedTraceOptions_3409_ = lean_ctor_get(v___y_3379_, 13);
v_hasTrace_3410_ = lean_ctor_get_uint8(v_options_3408_, sizeof(void*)*1);
v_cls_3411_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7));
if (v_hasTrace_3410_ == 0)
{
lean_dec_ref(v___body_3374_);
lean_dec_ref(v_value_3372_);
v___y_3457_ = v___y_3375_;
v___y_3458_ = v___y_3376_;
v___y_3459_ = v___y_3377_;
v___y_3460_ = v___y_3378_;
v___y_3461_ = v___y_3379_;
v___y_3462_ = v___y_3380_;
goto v___jp_3456_;
}
else
{
lean_object* v___x_3482_; uint8_t v___x_3483_; 
v___x_3482_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10);
v___x_3483_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3409_, v_options_3408_, v___x_3482_);
if (v___x_3483_ == 0)
{
lean_dec_ref(v___body_3374_);
lean_dec_ref(v_value_3372_);
v___y_3457_ = v___y_3375_;
v___y_3458_ = v___y_3376_;
v___y_3459_ = v___y_3377_;
v___y_3460_ = v___y_3378_;
v___y_3461_ = v___y_3379_;
v___y_3462_ = v___y_3380_;
goto v___jp_3456_;
}
else
{
lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; 
v___x_3484_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__7, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__7_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__7);
v___x_3485_ = l_Lean_MessageData_ofExpr(v_value_3372_);
v___x_3486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3484_);
lean_ctor_set(v___x_3486_, 1, v___x_3485_);
v___x_3487_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__9, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__9_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__9);
v___x_3488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3486_);
lean_ctor_set(v___x_3488_, 1, v___x_3487_);
lean_inc_ref(v_xs_3373_);
v___x_3489_ = lean_array_to_list(v_xs_3373_);
v___x_3490_ = lean_box(0);
v___x_3491_ = l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__4(v___x_3489_, v___x_3490_);
v___x_3492_ = l_Lean_MessageData_ofList(v___x_3491_);
v___x_3493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3493_, 0, v___x_3488_);
lean_ctor_set(v___x_3493_, 1, v___x_3492_);
v___x_3494_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__11, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__11_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__11);
v___x_3495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3495_, 0, v___x_3493_);
lean_ctor_set(v___x_3495_, 1, v___x_3494_);
v___x_3496_ = l_Lean_MessageData_ofExpr(v___body_3374_);
v___x_3497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3495_);
lean_ctor_set(v___x_3497_, 1, v___x_3496_);
v___x_3498_ = l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg(v_cls_3411_, v___x_3497_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
if (lean_obj_tag(v___x_3498_) == 0)
{
lean_dec_ref(v___x_3498_);
v___y_3457_ = v___y_3375_;
v___y_3458_ = v___y_3376_;
v___y_3459_ = v___y_3377_;
v___y_3460_ = v___y_3378_;
v___y_3461_ = v___y_3379_;
v___y_3462_ = v___y_3380_;
goto v___jp_3456_;
}
else
{
lean_object* v_a_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3506_; 
lean_dec_ref(v_xs_3373_);
lean_dec_ref(v___f_3371_);
lean_dec_ref(v___f_3370_);
lean_dec_ref(v_type_3368_);
lean_dec(v_declName_3367_);
v_a_3499_ = lean_ctor_get(v___x_3498_, 0);
v_isSharedCheck_3506_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3501_ = v___x_3498_;
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_a_3499_);
lean_dec(v___x_3498_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3506_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v___x_3504_; 
if (v_isShared_3502_ == 0)
{
v___x_3504_ = v___x_3501_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_a_3499_);
v___x_3504_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
return v___x_3504_;
}
}
}
}
}
v___jp_3382_:
{
uint8_t v___x_3388_; uint8_t v___x_3389_; lean_object* v___x_3390_; 
v___x_3388_ = 1;
v___x_3389_ = 1;
v___x_3390_ = l_Lean_Meta_mkLambdaFVars(v_xs_3373_, v_inst_3383_, v_isZero_3366_, v___x_3388_, v_isZero_3366_, v___x_3388_, v___x_3389_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
lean_dec_ref(v_xs_3373_);
return v___x_3390_;
}
v___jp_3391_:
{
if (lean_obj_tag(v___y_3396_) == 0)
{
lean_object* v_a_3397_; 
v_a_3397_ = lean_ctor_get(v___y_3396_, 0);
lean_inc(v_a_3397_);
lean_dec_ref(v___y_3396_);
v_inst_3383_ = v_a_3397_;
v___y_3384_ = v___y_3395_;
v___y_3385_ = v___y_3392_;
v___y_3386_ = v___y_3394_;
v___y_3387_ = v___y_3393_;
goto v___jp_3382_;
}
else
{
lean_dec_ref(v_xs_3373_);
return v___y_3396_;
}
}
v___jp_3398_:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3406_ = lean_box(0);
lean_inc(v___y_3401_);
lean_inc_ref(v___y_3403_);
lean_inc(v___y_3400_);
lean_inc_ref(v___y_3404_);
lean_inc(v___y_3405_);
lean_inc_ref(v___y_3399_);
v___x_3407_ = lean_apply_8(v___y_3402_, v___x_3406_, v___y_3399_, v___y_3405_, v___y_3404_, v___y_3400_, v___y_3403_, v___y_3401_, lean_box(0));
v___y_3392_ = v___y_3400_;
v___y_3393_ = v___y_3401_;
v___y_3394_ = v___y_3403_;
v___y_3395_ = v___y_3404_;
v___y_3396_ = v___x_3407_;
goto v___jp_3391_;
}
v___jp_3412_:
{
if (v___y_3421_ == 0)
{
lean_object* v_options_3422_; uint8_t v_hasTrace_3423_; 
lean_dec_ref(v___y_3418_);
v_options_3422_ = lean_ctor_get(v___y_3417_, 2);
v_hasTrace_3423_ = lean_ctor_get_uint8(v_options_3422_, sizeof(void*)*1);
if (v_hasTrace_3423_ == 0)
{
lean_dec(v_declName_3367_);
v___y_3399_ = v___y_3413_;
v___y_3400_ = v___y_3414_;
v___y_3401_ = v___y_3415_;
v___y_3402_ = v___y_3416_;
v___y_3403_ = v___y_3417_;
v___y_3404_ = v___y_3419_;
v___y_3405_ = v___y_3420_;
goto v___jp_3398_;
}
else
{
lean_object* v_inheritedTraceOptions_3424_; lean_object* v___x_3425_; uint8_t v___x_3426_; 
v_inheritedTraceOptions_3424_ = lean_ctor_get(v___y_3417_, 13);
v___x_3425_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10);
v___x_3426_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3424_, v_options_3422_, v___x_3425_);
if (v___x_3426_ == 0)
{
lean_dec(v_declName_3367_);
v___y_3399_ = v___y_3413_;
v___y_3400_ = v___y_3414_;
v___y_3401_ = v___y_3415_;
v___y_3402_ = v___y_3416_;
v___y_3403_ = v___y_3417_;
v___y_3404_ = v___y_3419_;
v___y_3405_ = v___y_3420_;
goto v___jp_3398_;
}
else
{
lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; 
v___x_3427_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__1, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__1_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__1);
v___x_3428_ = l_Lean_MessageData_ofName(v_declName_3367_);
v___x_3429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3427_);
lean_ctor_set(v___x_3429_, 1, v___x_3428_);
v___x_3430_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__3, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__3_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__3);
v___x_3431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3429_);
lean_ctor_set(v___x_3431_, 1, v___x_3430_);
v___x_3432_ = l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg(v_cls_3411_, v___x_3431_, v___y_3419_, v___y_3414_, v___y_3417_, v___y_3415_);
if (lean_obj_tag(v___x_3432_) == 0)
{
lean_object* v_a_3433_; lean_object* v___x_3434_; 
v_a_3433_ = lean_ctor_get(v___x_3432_, 0);
lean_inc(v_a_3433_);
lean_dec_ref(v___x_3432_);
lean_inc(v___y_3415_);
lean_inc_ref(v___y_3417_);
lean_inc(v___y_3414_);
lean_inc_ref(v___y_3419_);
lean_inc(v___y_3420_);
lean_inc_ref(v___y_3413_);
v___x_3434_ = lean_apply_8(v___y_3416_, v_a_3433_, v___y_3413_, v___y_3420_, v___y_3419_, v___y_3414_, v___y_3417_, v___y_3415_, lean_box(0));
v___y_3392_ = v___y_3414_;
v___y_3393_ = v___y_3415_;
v___y_3394_ = v___y_3417_;
v___y_3395_ = v___y_3419_;
v___y_3396_ = v___x_3434_;
goto v___jp_3391_;
}
else
{
lean_object* v_a_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3442_; 
lean_dec_ref(v___y_3416_);
lean_dec_ref(v_xs_3373_);
v_a_3435_ = lean_ctor_get(v___x_3432_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3432_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3437_ = v___x_3432_;
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_a_3435_);
lean_dec(v___x_3432_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3440_; 
if (v_isShared_3438_ == 0)
{
v___x_3440_ = v___x_3437_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_a_3435_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_3416_);
lean_dec_ref(v_xs_3373_);
lean_dec(v_declName_3367_);
return v___y_3418_;
}
}
v___jp_3443_:
{
if (lean_obj_tag(v___y_3451_) == 0)
{
lean_object* v_a_3452_; 
lean_dec_ref(v___y_3447_);
lean_dec(v_declName_3367_);
v_a_3452_ = lean_ctor_get(v___y_3451_, 0);
lean_inc(v_a_3452_);
lean_dec_ref(v___y_3451_);
v_inst_3383_ = v_a_3452_;
v___y_3384_ = v___y_3449_;
v___y_3385_ = v___y_3445_;
v___y_3386_ = v___y_3448_;
v___y_3387_ = v___y_3446_;
goto v___jp_3382_;
}
else
{
lean_object* v_a_3453_; uint8_t v___x_3454_; 
v_a_3453_ = lean_ctor_get(v___y_3451_, 0);
v___x_3454_ = l_Lean_Exception_isInterrupt(v_a_3453_);
if (v___x_3454_ == 0)
{
uint8_t v___x_3455_; 
lean_inc(v_a_3453_);
v___x_3455_ = l_Lean_Exception_isRuntime(v_a_3453_);
v___y_3413_ = v___y_3444_;
v___y_3414_ = v___y_3445_;
v___y_3415_ = v___y_3446_;
v___y_3416_ = v___y_3447_;
v___y_3417_ = v___y_3448_;
v___y_3418_ = v___y_3451_;
v___y_3419_ = v___y_3449_;
v___y_3420_ = v___y_3450_;
v___y_3421_ = v___x_3455_;
goto v___jp_3412_;
}
else
{
v___y_3413_ = v___y_3444_;
v___y_3414_ = v___y_3445_;
v___y_3415_ = v___y_3446_;
v___y_3416_ = v___y_3447_;
v___y_3417_ = v___y_3448_;
v___y_3418_ = v___y_3451_;
v___y_3419_ = v___y_3449_;
v___y_3420_ = v___y_3450_;
v___y_3421_ = v___x_3454_;
goto v___jp_3412_;
}
}
}
v___jp_3456_:
{
lean_object* v___x_3463_; 
lean_inc_ref(v_type_3368_);
v___x_3463_ = l_Lean_Meta_instantiateForall(v_type_3368_, v_xs_3373_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_);
if (lean_obj_tag(v___x_3463_) == 0)
{
switch(v_fixpointType_3369_)
{
case 0:
{
lean_object* v_a_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___f_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; 
lean_dec_ref(v___f_3371_);
lean_dec_ref(v___f_3370_);
v_a_3464_ = lean_ctor_get(v___x_3463_, 0);
lean_inc(v_a_3464_);
lean_dec_ref(v___x_3463_);
v___x_3465_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__2));
v___x_3466_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__3));
lean_inc_ref(v_xs_3373_);
lean_inc(v_declName_3367_);
v___f_3467_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___boxed), 13, 5);
lean_closure_set(v___f_3467_, 0, v_declName_3367_);
lean_closure_set(v___f_3467_, 1, v_type_3368_);
lean_closure_set(v___f_3467_, 2, v_xs_3373_);
lean_closure_set(v___f_3467_, 3, v___x_3465_);
lean_closure_set(v___f_3467_, 4, v___x_3466_);
v___x_3468_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__5));
v___x_3469_ = lean_unsigned_to_nat(1u);
v___x_3470_ = lean_mk_empty_array_with_capacity(v___x_3469_);
v___x_3471_ = lean_array_push(v___x_3470_, v_a_3464_);
v___x_3472_ = l_Lean_Meta_mkAppM(v___x_3468_, v___x_3471_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_);
if (lean_obj_tag(v___x_3472_) == 0)
{
lean_object* v_a_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; 
v_a_3473_ = lean_ctor_get(v___x_3472_, 0);
lean_inc(v_a_3473_);
lean_dec_ref(v___x_3472_);
v___x_3474_ = lean_box(0);
v___x_3475_ = l_Lean_Meta_synthInstance(v_a_3473_, v___x_3474_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_);
v___y_3444_ = v___y_3457_;
v___y_3445_ = v___y_3460_;
v___y_3446_ = v___y_3462_;
v___y_3447_ = v___f_3467_;
v___y_3448_ = v___y_3461_;
v___y_3449_ = v___y_3459_;
v___y_3450_ = v___y_3458_;
v___y_3451_ = v___x_3475_;
goto v___jp_3443_;
}
else
{
v___y_3444_ = v___y_3457_;
v___y_3445_ = v___y_3460_;
v___y_3446_ = v___y_3462_;
v___y_3447_ = v___f_3467_;
v___y_3448_ = v___y_3461_;
v___y_3449_ = v___y_3459_;
v___y_3450_ = v___y_3458_;
v___y_3451_ = v___x_3472_;
goto v___jp_3443_;
}
}
case 1:
{
lean_object* v_a_3476_; lean_object* v___x_3477_; 
lean_dec_ref(v___f_3371_);
lean_dec_ref(v_type_3368_);
lean_dec(v_declName_3367_);
v_a_3476_ = lean_ctor_get(v___x_3463_, 0);
lean_inc(v_a_3476_);
lean_dec_ref(v___x_3463_);
v___x_3477_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg(v_a_3476_, v___f_3370_, v_isZero_3366_, v_isZero_3366_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_);
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v_a_3478_; 
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
lean_inc(v_a_3478_);
lean_dec_ref(v___x_3477_);
v_inst_3383_ = v_a_3478_;
v___y_3384_ = v___y_3459_;
v___y_3385_ = v___y_3460_;
v___y_3386_ = v___y_3461_;
v___y_3387_ = v___y_3462_;
goto v___jp_3382_;
}
else
{
lean_dec_ref(v_xs_3373_);
return v___x_3477_;
}
}
default: 
{
lean_object* v_a_3479_; lean_object* v___x_3480_; 
lean_dec_ref(v___f_3370_);
lean_dec_ref(v_type_3368_);
lean_dec(v_declName_3367_);
v_a_3479_ = lean_ctor_get(v___x_3463_, 0);
lean_inc(v_a_3479_);
lean_dec_ref(v___x_3463_);
v___x_3480_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg(v_a_3479_, v___f_3371_, v_isZero_3366_, v_isZero_3366_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_);
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_object* v_a_3481_; 
v_a_3481_ = lean_ctor_get(v___x_3480_, 0);
lean_inc(v_a_3481_);
lean_dec_ref(v___x_3480_);
v_inst_3383_ = v_a_3481_;
v___y_3384_ = v___y_3459_;
v___y_3385_ = v___y_3460_;
v___y_3386_ = v___y_3461_;
v___y_3387_ = v___y_3462_;
goto v___jp_3382_;
}
else
{
lean_dec_ref(v_xs_3373_);
return v___x_3480_;
}
}
}
}
else
{
lean_dec_ref(v_xs_3373_);
lean_dec_ref(v___f_3371_);
lean_dec_ref(v___f_3370_);
lean_dec_ref(v_type_3368_);
lean_dec(v_declName_3367_);
return v___x_3463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___boxed(lean_object* v_isZero_3507_, lean_object* v_declName_3508_, lean_object* v_type_3509_, lean_object* v_fixpointType_3510_, lean_object* v___f_3511_, lean_object* v___f_3512_, lean_object* v_value_3513_, lean_object* v_xs_3514_, lean_object* v___body_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_){
_start:
{
uint8_t v_isZero_boxed_3523_; uint8_t v_fixpointType_boxed_3524_; lean_object* v_res_3525_; 
v_isZero_boxed_3523_ = lean_unbox(v_isZero_3507_);
v_fixpointType_boxed_3524_ = lean_unbox(v_fixpointType_3510_);
v_res_3525_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3(v_isZero_boxed_3523_, v_declName_3508_, v_type_3509_, v_fixpointType_boxed_3524_, v___f_3511_, v___f_3512_, v_value_3513_, v_xs_3514_, v___body_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3520_);
lean_dec(v___y_3519_);
lean_dec_ref(v___y_3518_);
lean_dec(v___y_3517_);
lean_dec_ref(v___y_3516_);
return v_res_3525_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__0(void){
_start:
{
lean_object* v___x_3526_; lean_object* v___x_3527_; 
v___x_3526_ = lean_box(1);
v___x_3527_ = l_Lean_MessageData_ofFormat(v___x_3526_);
return v___x_3527_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__3(void){
_start:
{
lean_object* v___x_3531_; lean_object* v___x_3532_; 
v___x_3531_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__2));
v___x_3532_ = l_Lean_MessageData_ofFormat(v___x_3531_);
return v___x_3532_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11(lean_object* v_x_3533_, lean_object* v_x_3534_){
_start:
{
if (lean_obj_tag(v_x_3534_) == 0)
{
return v_x_3533_;
}
else
{
lean_object* v_head_3535_; lean_object* v_tail_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3558_; 
v_head_3535_ = lean_ctor_get(v_x_3534_, 0);
v_tail_3536_ = lean_ctor_get(v_x_3534_, 1);
v_isSharedCheck_3558_ = !lean_is_exclusive(v_x_3534_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3538_ = v_x_3534_;
v_isShared_3539_ = v_isSharedCheck_3558_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_tail_3536_);
lean_inc(v_head_3535_);
lean_dec(v_x_3534_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3558_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v_before_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3556_; 
v_before_3540_ = lean_ctor_get(v_head_3535_, 0);
v_isSharedCheck_3556_ = !lean_is_exclusive(v_head_3535_);
if (v_isSharedCheck_3556_ == 0)
{
lean_object* v_unused_3557_; 
v_unused_3557_ = lean_ctor_get(v_head_3535_, 1);
lean_dec(v_unused_3557_);
v___x_3542_ = v_head_3535_;
v_isShared_3543_ = v_isSharedCheck_3556_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_before_3540_);
lean_dec(v_head_3535_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3556_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3544_; lean_object* v___x_3546_; 
v___x_3544_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__0);
if (v_isShared_3543_ == 0)
{
lean_ctor_set_tag(v___x_3542_, 7);
lean_ctor_set(v___x_3542_, 1, v___x_3544_);
lean_ctor_set(v___x_3542_, 0, v_x_3533_);
v___x_3546_ = v___x_3542_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_x_3533_);
lean_ctor_set(v_reuseFailAlloc_3555_, 1, v___x_3544_);
v___x_3546_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
lean_object* v___x_3547_; lean_object* v___x_3549_; 
v___x_3547_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__3);
if (v_isShared_3539_ == 0)
{
lean_ctor_set_tag(v___x_3538_, 7);
lean_ctor_set(v___x_3538_, 1, v___x_3547_);
lean_ctor_set(v___x_3538_, 0, v___x_3546_);
v___x_3549_ = v___x_3538_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v___x_3546_);
lean_ctor_set(v_reuseFailAlloc_3554_, 1, v___x_3547_);
v___x_3549_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___x_3550_ = l_Lean_MessageData_ofSyntax(v_before_3540_);
v___x_3551_ = l_Lean_indentD(v___x_3550_);
v___x_3552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3552_, 0, v___x_3549_);
lean_ctor_set(v___x_3552_, 1, v___x_3551_);
v_x_3533_ = v___x_3552_;
v_x_3534_ = v_tail_3536_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__10(lean_object* v_opts_3559_, lean_object* v_opt_3560_){
_start:
{
lean_object* v_name_3561_; lean_object* v_defValue_3562_; lean_object* v_map_3563_; lean_object* v___x_3564_; 
v_name_3561_ = lean_ctor_get(v_opt_3560_, 0);
v_defValue_3562_ = lean_ctor_get(v_opt_3560_, 1);
v_map_3563_ = lean_ctor_get(v_opts_3559_, 0);
v___x_3564_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3563_, v_name_3561_);
if (lean_obj_tag(v___x_3564_) == 0)
{
uint8_t v___x_3565_; 
v___x_3565_ = lean_unbox(v_defValue_3562_);
return v___x_3565_;
}
else
{
lean_object* v_val_3566_; 
v_val_3566_ = lean_ctor_get(v___x_3564_, 0);
lean_inc(v_val_3566_);
lean_dec_ref(v___x_3564_);
if (lean_obj_tag(v_val_3566_) == 1)
{
uint8_t v_v_3567_; 
v_v_3567_ = lean_ctor_get_uint8(v_val_3566_, 0);
lean_dec_ref(v_val_3566_);
return v_v_3567_;
}
else
{
uint8_t v___x_3568_; 
lean_dec(v_val_3566_);
v___x_3568_ = lean_unbox(v_defValue_3562_);
return v___x_3568_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__10___boxed(lean_object* v_opts_3569_, lean_object* v_opt_3570_){
_start:
{
uint8_t v_res_3571_; lean_object* v_r_3572_; 
v_res_3571_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__10(v_opts_3569_, v_opt_3570_);
lean_dec_ref(v_opt_3570_);
lean_dec_ref(v_opts_3569_);
v_r_3572_ = lean_box(v_res_3571_);
return v_r_3572_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_3576_; lean_object* v___x_3577_; 
v___x_3576_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__1));
v___x_3577_ = l_Lean_MessageData_ofFormat(v___x_3576_);
return v___x_3577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg(lean_object* v_msgData_3578_, lean_object* v_macroStack_3579_, lean_object* v___y_3580_){
_start:
{
lean_object* v_options_3582_; lean_object* v___x_3583_; uint8_t v___x_3584_; 
v_options_3582_ = lean_ctor_get(v___y_3580_, 2);
v___x_3583_ = l_Lean_Elab_pp_macroStack;
v___x_3584_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__10(v_options_3582_, v___x_3583_);
if (v___x_3584_ == 0)
{
lean_object* v___x_3585_; 
lean_dec(v_macroStack_3579_);
v___x_3585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3585_, 0, v_msgData_3578_);
return v___x_3585_;
}
else
{
if (lean_obj_tag(v_macroStack_3579_) == 0)
{
lean_object* v___x_3586_; 
v___x_3586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3586_, 0, v_msgData_3578_);
return v___x_3586_;
}
else
{
lean_object* v_head_3587_; lean_object* v_after_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3603_; 
v_head_3587_ = lean_ctor_get(v_macroStack_3579_, 0);
lean_inc(v_head_3587_);
v_after_3588_ = lean_ctor_get(v_head_3587_, 1);
v_isSharedCheck_3603_ = !lean_is_exclusive(v_head_3587_);
if (v_isSharedCheck_3603_ == 0)
{
lean_object* v_unused_3604_; 
v_unused_3604_ = lean_ctor_get(v_head_3587_, 0);
lean_dec(v_unused_3604_);
v___x_3590_ = v_head_3587_;
v_isShared_3591_ = v_isSharedCheck_3603_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_after_3588_);
lean_dec(v_head_3587_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3603_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v___x_3592_; lean_object* v___x_3594_; 
v___x_3592_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__0);
if (v_isShared_3591_ == 0)
{
lean_ctor_set_tag(v___x_3590_, 7);
lean_ctor_set(v___x_3590_, 1, v___x_3592_);
lean_ctor_set(v___x_3590_, 0, v_msgData_3578_);
v___x_3594_ = v___x_3590_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_msgData_3578_);
lean_ctor_set(v_reuseFailAlloc_3602_, 1, v___x_3592_);
v___x_3594_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v_msgData_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; 
v___x_3595_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__2);
v___x_3596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3596_, 0, v___x_3594_);
lean_ctor_set(v___x_3596_, 1, v___x_3595_);
v___x_3597_ = l_Lean_MessageData_ofSyntax(v_after_3588_);
v___x_3598_ = l_Lean_indentD(v___x_3597_);
v_msgData_3599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_3599_, 0, v___x_3596_);
lean_ctor_set(v_msgData_3599_, 1, v___x_3598_);
v___x_3600_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11(v_msgData_3599_, v_macroStack_3579_);
v___x_3601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3601_, 0, v___x_3600_);
return v___x_3601_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_3605_, lean_object* v_macroStack_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_){
_start:
{
lean_object* v_res_3609_; 
v_res_3609_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg(v_msgData_3605_, v_macroStack_3606_, v___y_3607_);
lean_dec_ref(v___y_3607_);
return v_res_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___redArg(lean_object* v_msg_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_){
_start:
{
lean_object* v_ref_3618_; lean_object* v___x_3619_; lean_object* v_a_3620_; lean_object* v_macroStack_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3632_; 
v_ref_3618_ = lean_ctor_get(v___y_3615_, 5);
v___x_3619_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6_spec__7(v_msg_3610_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_);
v_a_3620_ = lean_ctor_get(v___x_3619_, 0);
lean_inc(v_a_3620_);
lean_dec_ref(v___x_3619_);
v_macroStack_3621_ = lean_ctor_get(v___y_3611_, 1);
v___x_3622_ = l_Lean_Elab_getBetterRef(v_ref_3618_, v_macroStack_3621_);
lean_inc(v_macroStack_3621_);
v___x_3623_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg(v_a_3620_, v_macroStack_3621_, v___y_3615_);
v_a_3624_ = lean_ctor_get(v___x_3623_, 0);
v_isSharedCheck_3632_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3626_ = v___x_3623_;
v_isShared_3627_ = v_isSharedCheck_3632_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v___x_3623_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3632_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3628_; lean_object* v___x_3630_; 
v___x_3628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3628_, 0, v___x_3622_);
lean_ctor_set(v___x_3628_, 1, v_a_3624_);
if (v_isShared_3627_ == 0)
{
lean_ctor_set_tag(v___x_3626_, 1);
lean_ctor_set(v___x_3626_, 0, v___x_3628_);
v___x_3630_ = v___x_3626_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___redArg___boxed(lean_object* v_msg_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_){
_start:
{
lean_object* v_res_3641_; 
v_res_3641_ = l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___redArg(v_msg_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_);
lean_dec(v___y_3639_);
lean_dec_ref(v___y_3638_);
lean_dec(v___y_3637_);
lean_dec_ref(v___y_3636_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
return v_res_3641_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; 
v___x_3649_ = lean_box(0);
v___x_3650_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__2));
v___x_3651_ = l_Lean_mkConst(v___x_3650_, v___x_3649_);
return v___x_3651_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__5(void){
_start:
{
lean_object* v___x_3653_; lean_object* v___x_3654_; 
v___x_3653_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__4));
v___x_3654_ = l_Lean_stringToMessageData(v___x_3653_);
return v___x_3654_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1(lean_object* v_xs_3655_, lean_object* v_e_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_){
_start:
{
uint8_t v___x_3667_; 
v___x_3667_ = l_Lean_Expr_isProp(v_e_3656_);
if (v___x_3667_ == 0)
{
lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v_a_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3677_; 
lean_dec_ref(v_xs_3655_);
v___x_3668_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__5, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__5_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__5);
v___x_3669_ = l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___redArg(v___x_3668_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_);
v_a_3670_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3672_ = v___x_3669_;
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_a_3670_);
lean_dec(v___x_3669_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3675_; 
if (v_isShared_3673_ == 0)
{
v___x_3675_ = v___x_3672_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_a_3670_);
v___x_3675_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
return v___x_3675_;
}
}
}
else
{
goto v___jp_3664_;
}
v___jp_3664_:
{
lean_object* v___x_3665_; lean_object* v___x_3666_; 
v___x_3665_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__3, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__3_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__3);
v___x_3666_ = l_Lean_Meta_mkInstPiOfInstsForall(v_xs_3655_, v___x_3665_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_);
return v___x_3666_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___boxed(lean_object* v_xs_3678_, lean_object* v_e_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_){
_start:
{
lean_object* v_res_3687_; 
v_res_3687_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1(v_xs_3678_, v_e_3679_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_);
lean_dec(v___y_3685_);
lean_dec_ref(v___y_3684_);
lean_dec(v___y_3683_);
lean_dec_ref(v___y_3682_);
lean_dec(v___y_3681_);
lean_dec_ref(v___y_3680_);
lean_dec_ref(v_e_3679_);
return v_res_3687_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; 
v___x_3694_ = lean_box(0);
v___x_3695_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__1));
v___x_3696_ = l_Lean_mkConst(v___x_3695_, v___x_3694_);
return v___x_3696_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; 
v___x_3698_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__3));
v___x_3699_ = l_Lean_stringToMessageData(v___x_3698_);
return v___x_3699_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0(lean_object* v_xs_3700_, lean_object* v_e_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_){
_start:
{
uint8_t v___x_3712_; 
v___x_3712_ = l_Lean_Expr_isProp(v_e_3701_);
if (v___x_3712_ == 0)
{
lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v_a_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3722_; 
lean_dec_ref(v_xs_3700_);
v___x_3713_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__4, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__4_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__4);
v___x_3714_ = l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___redArg(v___x_3713_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_);
v_a_3715_ = lean_ctor_get(v___x_3714_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3714_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3717_ = v___x_3714_;
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_a_3715_);
lean_dec(v___x_3714_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3722_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v___x_3720_; 
if (v_isShared_3718_ == 0)
{
v___x_3720_ = v___x_3717_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_a_3715_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
return v___x_3720_;
}
}
}
else
{
goto v___jp_3709_;
}
v___jp_3709_:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; 
v___x_3710_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__2, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__2_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__2);
v___x_3711_ = l_Lean_Meta_mkInstPiOfInstsForall(v_xs_3700_, v___x_3710_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_);
return v___x_3711_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___boxed(lean_object* v_xs_3723_, lean_object* v_e_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_){
_start:
{
lean_object* v_res_3732_; 
v_res_3732_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0(v_xs_3723_, v_e_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
lean_dec(v___y_3730_);
lean_dec_ref(v___y_3729_);
lean_dec(v___y_3728_);
lean_dec_ref(v___y_3727_);
lean_dec(v___y_3726_);
lean_dec_ref(v___y_3725_);
lean_dec_ref(v_e_3724_);
return v_res_3732_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg(lean_object* v_hints_3735_, lean_object* v_as_3736_, lean_object* v_i_3737_, lean_object* v_j_3738_, lean_object* v_bs_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_){
_start:
{
lean_object* v_zero_3747_; uint8_t v_isZero_3748_; 
v_zero_3747_ = lean_unsigned_to_nat(0u);
v_isZero_3748_ = lean_nat_dec_eq(v_i_3737_, v_zero_3747_);
if (v_isZero_3748_ == 1)
{
lean_object* v___x_3749_; 
lean_dec(v_j_3738_);
lean_dec(v_i_3737_);
v___x_3749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3749_, 0, v_bs_3739_);
return v___x_3749_;
}
else
{
lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v_ref_3752_; uint8_t v_fixpointType_3753_; lean_object* v___x_3754_; lean_object* v_declName_3755_; lean_object* v_type_3756_; lean_object* v_value_3757_; lean_object* v_fileName_3758_; lean_object* v_fileMap_3759_; lean_object* v_options_3760_; lean_object* v_currRecDepth_3761_; lean_object* v_maxRecDepth_3762_; lean_object* v_ref_3763_; lean_object* v_currNamespace_3764_; lean_object* v_openDecls_3765_; lean_object* v_initHeartbeats_3766_; lean_object* v_maxHeartbeats_3767_; lean_object* v_quotContext_3768_; lean_object* v_currMacroScope_3769_; uint8_t v_diag_3770_; lean_object* v_cancelTk_x3f_3771_; uint8_t v_suppressElabErrors_3772_; lean_object* v_inheritedTraceOptions_3773_; lean_object* v___f_3774_; lean_object* v___f_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___f_3778_; lean_object* v_ref_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; 
v___x_3750_ = l_Lean_Elab_instInhabitedPartialFixpoint_default;
v___x_3751_ = lean_array_get_borrowed(v___x_3750_, v_hints_3735_, v_j_3738_);
v_ref_3752_ = lean_ctor_get(v___x_3751_, 0);
v_fixpointType_3753_ = lean_ctor_get_uint8(v___x_3751_, sizeof(void*)*2);
v___x_3754_ = lean_array_fget_borrowed(v_as_3736_, v_j_3738_);
v_declName_3755_ = lean_ctor_get(v___x_3754_, 3);
v_type_3756_ = lean_ctor_get(v___x_3754_, 6);
v_value_3757_ = lean_ctor_get(v___x_3754_, 7);
v_fileName_3758_ = lean_ctor_get(v___y_3744_, 0);
v_fileMap_3759_ = lean_ctor_get(v___y_3744_, 1);
v_options_3760_ = lean_ctor_get(v___y_3744_, 2);
v_currRecDepth_3761_ = lean_ctor_get(v___y_3744_, 3);
v_maxRecDepth_3762_ = lean_ctor_get(v___y_3744_, 4);
v_ref_3763_ = lean_ctor_get(v___y_3744_, 5);
v_currNamespace_3764_ = lean_ctor_get(v___y_3744_, 6);
v_openDecls_3765_ = lean_ctor_get(v___y_3744_, 7);
v_initHeartbeats_3766_ = lean_ctor_get(v___y_3744_, 8);
v_maxHeartbeats_3767_ = lean_ctor_get(v___y_3744_, 9);
v_quotContext_3768_ = lean_ctor_get(v___y_3744_, 10);
v_currMacroScope_3769_ = lean_ctor_get(v___y_3744_, 11);
v_diag_3770_ = lean_ctor_get_uint8(v___y_3744_, sizeof(void*)*14);
v_cancelTk_x3f_3771_ = lean_ctor_get(v___y_3744_, 12);
v_suppressElabErrors_3772_ = lean_ctor_get_uint8(v___y_3744_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3773_ = lean_ctor_get(v___y_3744_, 13);
v___f_3774_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___closed__0));
v___f_3775_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___closed__1));
v___x_3776_ = lean_box(v_isZero_3748_);
v___x_3777_ = lean_box(v_fixpointType_3753_);
lean_inc_ref_n(v_value_3757_, 2);
lean_inc_ref(v_type_3756_);
lean_inc(v_declName_3755_);
v___f_3778_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___boxed), 16, 7);
lean_closure_set(v___f_3778_, 0, v___x_3776_);
lean_closure_set(v___f_3778_, 1, v_declName_3755_);
lean_closure_set(v___f_3778_, 2, v_type_3756_);
lean_closure_set(v___f_3778_, 3, v___x_3777_);
lean_closure_set(v___f_3778_, 4, v___f_3774_);
lean_closure_set(v___f_3778_, 5, v___f_3775_);
lean_closure_set(v___f_3778_, 6, v_value_3757_);
v_ref_3779_ = l_Lean_replaceRef(v_ref_3752_, v_ref_3763_);
lean_inc_ref(v_inheritedTraceOptions_3773_);
lean_inc(v_cancelTk_x3f_3771_);
lean_inc(v_currMacroScope_3769_);
lean_inc(v_quotContext_3768_);
lean_inc(v_maxHeartbeats_3767_);
lean_inc(v_initHeartbeats_3766_);
lean_inc(v_openDecls_3765_);
lean_inc(v_currNamespace_3764_);
lean_inc(v_maxRecDepth_3762_);
lean_inc(v_currRecDepth_3761_);
lean_inc_ref(v_options_3760_);
lean_inc_ref(v_fileMap_3759_);
lean_inc_ref(v_fileName_3758_);
v___x_3780_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3780_, 0, v_fileName_3758_);
lean_ctor_set(v___x_3780_, 1, v_fileMap_3759_);
lean_ctor_set(v___x_3780_, 2, v_options_3760_);
lean_ctor_set(v___x_3780_, 3, v_currRecDepth_3761_);
lean_ctor_set(v___x_3780_, 4, v_maxRecDepth_3762_);
lean_ctor_set(v___x_3780_, 5, v_ref_3779_);
lean_ctor_set(v___x_3780_, 6, v_currNamespace_3764_);
lean_ctor_set(v___x_3780_, 7, v_openDecls_3765_);
lean_ctor_set(v___x_3780_, 8, v_initHeartbeats_3766_);
lean_ctor_set(v___x_3780_, 9, v_maxHeartbeats_3767_);
lean_ctor_set(v___x_3780_, 10, v_quotContext_3768_);
lean_ctor_set(v___x_3780_, 11, v_currMacroScope_3769_);
lean_ctor_set(v___x_3780_, 12, v_cancelTk_x3f_3771_);
lean_ctor_set(v___x_3780_, 13, v_inheritedTraceOptions_3773_);
lean_ctor_set_uint8(v___x_3780_, sizeof(void*)*14, v_diag_3770_);
lean_ctor_set_uint8(v___x_3780_, sizeof(void*)*14 + 1, v_suppressElabErrors_3772_);
v___x_3781_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5___redArg(v_value_3757_, v___f_3778_, v_isZero_3748_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_, v___x_3780_, v___y_3745_);
lean_dec_ref(v___x_3780_);
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_object* v_a_3782_; lean_object* v_one_3783_; lean_object* v_n_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; 
v_a_3782_ = lean_ctor_get(v___x_3781_, 0);
lean_inc(v_a_3782_);
lean_dec_ref(v___x_3781_);
v_one_3783_ = lean_unsigned_to_nat(1u);
v_n_3784_ = lean_nat_sub(v_i_3737_, v_one_3783_);
lean_dec(v_i_3737_);
v___x_3785_ = lean_nat_add(v_j_3738_, v_one_3783_);
lean_dec(v_j_3738_);
v___x_3786_ = lean_array_push(v_bs_3739_, v_a_3782_);
v_i_3737_ = v_n_3784_;
v_j_3738_ = v___x_3785_;
v_bs_3739_ = v___x_3786_;
goto _start;
}
else
{
lean_object* v_a_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3795_; 
lean_dec_ref(v_bs_3739_);
lean_dec(v_j_3738_);
lean_dec(v_i_3737_);
v_a_3788_ = lean_ctor_get(v___x_3781_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3781_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3790_ = v___x_3781_;
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_a_3788_);
lean_dec(v___x_3781_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v___x_3793_; 
if (v_isShared_3791_ == 0)
{
v___x_3793_ = v___x_3790_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3788_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___boxed(lean_object* v_hints_3796_, lean_object* v_as_3797_, lean_object* v_i_3798_, lean_object* v_j_3799_, lean_object* v_bs_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_){
_start:
{
lean_object* v_res_3808_; 
v_res_3808_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg(v_hints_3796_, v_as_3797_, v_i_3798_, v_j_3799_, v_bs_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_);
lean_dec(v___y_3806_);
lean_dec_ref(v___y_3805_);
lean_dec(v___y_3804_);
lean_dec_ref(v___y_3803_);
lean_dec(v___y_3802_);
lean_dec_ref(v___y_3801_);
lean_dec_ref(v_as_3797_);
lean_dec_ref(v_hints_3796_);
return v_res_3808_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__26_spec__31(lean_object* v_as_3809_, size_t v_i_3810_, size_t v_stop_3811_){
_start:
{
uint8_t v___x_3812_; 
v___x_3812_ = lean_usize_dec_eq(v_i_3810_, v_stop_3811_);
if (v___x_3812_ == 0)
{
lean_object* v___x_3813_; uint8_t v_fixpointType_3814_; uint8_t v___x_3815_; 
v___x_3813_ = lean_array_uget_borrowed(v_as_3809_, v_i_3810_);
v_fixpointType_3814_ = lean_ctor_get_uint8(v___x_3813_, sizeof(void*)*2);
v___x_3815_ = l_Lean_Elab_isLatticeTheoretic(v_fixpointType_3814_);
if (v___x_3815_ == 0)
{
size_t v___x_3816_; size_t v___x_3817_; 
v___x_3816_ = ((size_t)1ULL);
v___x_3817_ = lean_usize_add(v_i_3810_, v___x_3816_);
v_i_3810_ = v___x_3817_;
goto _start;
}
else
{
return v___x_3815_;
}
}
else
{
uint8_t v___x_3819_; 
v___x_3819_ = 0;
return v___x_3819_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__26_spec__31___boxed(lean_object* v_as_3820_, lean_object* v_i_3821_, lean_object* v_stop_3822_){
_start:
{
size_t v_i_boxed_3823_; size_t v_stop_boxed_3824_; uint8_t v_res_3825_; lean_object* v_r_3826_; 
v_i_boxed_3823_ = lean_unbox_usize(v_i_3821_);
lean_dec(v_i_3821_);
v_stop_boxed_3824_ = lean_unbox_usize(v_stop_3822_);
lean_dec(v_stop_3822_);
v_res_3825_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__26_spec__31(v_as_3820_, v_i_boxed_3823_, v_stop_boxed_3824_);
lean_dec_ref(v_as_3820_);
v_r_3826_ = lean_box(v_res_3825_);
return v_r_3826_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__26(lean_object* v_as_3827_, size_t v_i_3828_, size_t v_stop_3829_){
_start:
{
uint8_t v___x_3830_; 
v___x_3830_ = lean_usize_dec_eq(v_i_3828_, v_stop_3829_);
if (v___x_3830_ == 0)
{
lean_object* v___x_3831_; uint8_t v_fixpointType_3832_; uint8_t v___x_3833_; 
v___x_3831_ = lean_array_uget_borrowed(v_as_3827_, v_i_3828_);
v_fixpointType_3832_ = lean_ctor_get_uint8(v___x_3831_, sizeof(void*)*2);
v___x_3833_ = l_Lean_Elab_isLatticeTheoretic(v_fixpointType_3832_);
if (v___x_3833_ == 0)
{
size_t v___x_3834_; size_t v___x_3835_; uint8_t v___x_3836_; 
v___x_3834_ = ((size_t)1ULL);
v___x_3835_ = lean_usize_add(v_i_3828_, v___x_3834_);
v___x_3836_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__26_spec__31(v_as_3827_, v___x_3835_, v_stop_3829_);
return v___x_3836_;
}
else
{
return v___x_3833_;
}
}
else
{
uint8_t v___x_3837_; 
v___x_3837_ = 0;
return v___x_3837_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__26___boxed(lean_object* v_as_3838_, lean_object* v_i_3839_, lean_object* v_stop_3840_){
_start:
{
size_t v_i_boxed_3841_; size_t v_stop_boxed_3842_; uint8_t v_res_3843_; lean_object* v_r_3844_; 
v_i_boxed_3841_ = lean_unbox_usize(v_i_3839_);
lean_dec(v_i_3839_);
v_stop_boxed_3842_ = lean_unbox_usize(v_stop_3840_);
lean_dec(v_stop_3840_);
v_res_3843_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__26(v_as_3838_, v_i_boxed_3841_, v_stop_boxed_3842_);
lean_dec_ref(v_as_3838_);
v_r_3844_ = lean_box(v_res_3843_);
return v_r_3844_;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___closed__1(void){
_start:
{
lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; 
v___x_3846_ = ((lean_object*)(l_Lean_Elab_partialFixpoint___closed__0));
v___x_3847_ = lean_unsigned_to_nat(2u);
v___x_3848_ = lean_unsigned_to_nat(82u);
v___x_3849_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__7));
v___x_3850_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__0));
v___x_3851_ = l_mkPanicMessageWithDecl(v___x_3850_, v___x_3849_, v___x_3848_, v___x_3847_, v___x_3846_);
return v___x_3851_;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___closed__3(void){
_start:
{
lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; 
v___x_3853_ = ((lean_object*)(l_Lean_Elab_partialFixpoint___closed__2));
v___x_3854_ = lean_unsigned_to_nat(4u);
v___x_3855_ = lean_unsigned_to_nat(86u);
v___x_3856_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__7));
v___x_3857_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__0));
v___x_3858_ = l_mkPanicMessageWithDecl(v___x_3857_, v___x_3856_, v___x_3855_, v___x_3854_, v___x_3853_);
return v___x_3858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_partialFixpoint(lean_object* v_docCtx_3861_, lean_object* v_preDefs_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_){
_start:
{
lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v_hints_3872_; lean_object* v___x_3873_; uint8_t v___x_3874_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; 
v___x_3870_ = lean_unsigned_to_nat(0u);
v___x_3871_ = lean_array_get_size(v_preDefs_3862_);
v_hints_3872_ = l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0(v_preDefs_3862_, v___x_3870_, v___x_3871_);
v___x_3873_ = lean_array_get_size(v_hints_3872_);
v___x_3874_ = lean_nat_dec_eq(v___x_3871_, v___x_3873_);
if (v___x_3874_ == 0)
{
lean_object* v___x_3917_; lean_object* v___x_3918_; 
lean_dec_ref(v_hints_3872_);
lean_dec_ref(v_preDefs_3862_);
lean_dec_ref(v_docCtx_3861_);
v___x_3917_ = lean_obj_once(&l_Lean_Elab_partialFixpoint___closed__1, &l_Lean_Elab_partialFixpoint___closed__1_once, _init_l_Lean_Elab_partialFixpoint___closed__1);
v___x_3918_ = l_panic___at___00Lean_Elab_partialFixpoint_spec__25(v___x_3917_, v_a_3863_, v_a_3864_, v_a_3865_, v_a_3866_, v_a_3867_, v_a_3868_);
return v___x_3918_;
}
else
{
uint8_t v___x_3919_; 
v___x_3919_ = lean_nat_dec_lt(v___x_3870_, v___x_3873_);
if (v___x_3919_ == 0)
{
v___y_3876_ = v_a_3863_;
v___y_3877_ = v_a_3864_;
v___y_3878_ = v_a_3865_;
v___y_3879_ = v_a_3866_;
v___y_3880_ = v_a_3867_;
v___y_3881_ = v_a_3868_;
goto v___jp_3875_;
}
else
{
if (v___x_3919_ == 0)
{
v___y_3876_ = v_a_3863_;
v___y_3877_ = v_a_3864_;
v___y_3878_ = v_a_3865_;
v___y_3879_ = v_a_3866_;
v___y_3880_ = v_a_3867_;
v___y_3881_ = v_a_3868_;
goto v___jp_3875_;
}
else
{
size_t v___x_3920_; size_t v___x_3921_; uint8_t v___x_3922_; 
v___x_3920_ = ((size_t)0ULL);
v___x_3921_ = lean_usize_of_nat(v___x_3873_);
v___x_3922_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__26(v_hints_3872_, v___x_3920_, v___x_3921_);
if (v___x_3922_ == 0)
{
v___y_3876_ = v_a_3863_;
v___y_3877_ = v_a_3864_;
v___y_3878_ = v_a_3865_;
v___y_3879_ = v_a_3866_;
v___y_3880_ = v_a_3867_;
v___y_3881_ = v_a_3868_;
goto v___jp_3875_;
}
else
{
if (v___x_3919_ == 0)
{
v___y_3876_ = v_a_3863_;
v___y_3877_ = v_a_3864_;
v___y_3878_ = v_a_3865_;
v___y_3879_ = v_a_3866_;
v___y_3880_ = v_a_3867_;
v___y_3881_ = v_a_3868_;
goto v___jp_3875_;
}
else
{
if (v___x_3919_ == 0)
{
v___y_3876_ = v_a_3863_;
v___y_3877_ = v_a_3864_;
v___y_3878_ = v_a_3865_;
v___y_3879_ = v_a_3866_;
v___y_3880_ = v_a_3867_;
v___y_3881_ = v_a_3868_;
goto v___jp_3875_;
}
else
{
uint8_t v___x_3923_; 
v___x_3923_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27(v___x_3922_, v_hints_3872_, v___x_3920_, v___x_3921_);
if (v___x_3923_ == 0)
{
v___y_3876_ = v_a_3863_;
v___y_3877_ = v_a_3864_;
v___y_3878_ = v_a_3865_;
v___y_3879_ = v_a_3866_;
v___y_3880_ = v_a_3867_;
v___y_3881_ = v_a_3868_;
goto v___jp_3875_;
}
else
{
lean_object* v___x_3924_; lean_object* v___x_3925_; 
lean_dec_ref(v_hints_3872_);
lean_dec_ref(v_preDefs_3862_);
lean_dec_ref(v_docCtx_3861_);
v___x_3924_ = lean_obj_once(&l_Lean_Elab_partialFixpoint___closed__3, &l_Lean_Elab_partialFixpoint___closed__3_once, _init_l_Lean_Elab_partialFixpoint___closed__3);
v___x_3925_ = l_panic___at___00Lean_Elab_partialFixpoint_spec__25(v___x_3924_, v_a_3863_, v_a_3864_, v_a_3865_, v_a_3866_, v_a_3867_, v_a_3868_);
return v___x_3925_;
}
}
}
}
}
}
}
v___jp_3875_:
{
lean_object* v___x_3882_; lean_object* v___x_3883_; 
v___x_3882_ = lean_mk_empty_array_with_capacity(v___x_3871_);
lean_inc_ref(v___x_3882_);
v___x_3883_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg(v_hints_3872_, v_preDefs_3862_, v___x_3871_, v___x_3870_, v___x_3882_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_);
if (lean_obj_tag(v___x_3883_) == 0)
{
lean_object* v_a_3884_; size_t v_sz_3885_; size_t v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; 
v_a_3884_ = lean_ctor_get(v___x_3883_, 0);
lean_inc(v_a_3884_);
lean_dec_ref(v___x_3883_);
v_sz_3885_ = lean_array_size(v_preDefs_3862_);
v___x_3886_ = ((size_t)0ULL);
lean_inc_ref_n(v_preDefs_3862_, 2);
v___x_3887_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__7(v_sz_3885_, v___x_3886_, v_preDefs_3862_);
v___x_3888_ = l_Lean_Elab_getFixedParamPerms(v_preDefs_3862_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_);
if (lean_obj_tag(v___x_3888_) == 0)
{
lean_object* v_a_3889_; lean_object* v_perms_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v_type_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___f_3899_; lean_object* v___x_3900_; 
v_a_3889_ = lean_ctor_get(v___x_3888_, 0);
lean_inc(v_a_3889_);
lean_dec_ref(v___x_3888_);
v_perms_3890_ = lean_ctor_get(v_a_3889_, 1);
lean_inc_ref(v_perms_3890_);
v___x_3891_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_3892_ = lean_array_get(v___x_3891_, v_preDefs_3862_, v___x_3870_);
v_type_3893_ = lean_ctor_get(v___x_3892_, 6);
lean_inc_ref(v_type_3893_);
v___x_3894_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1);
v___x_3895_ = lean_array_get(v___x_3894_, v_perms_3890_, v___x_3870_);
v___x_3896_ = ((lean_object*)(l_Lean_Elab_partialFixpoint___boxed__const__1));
v___x_3897_ = lean_box(v___x_3874_);
v___x_3898_ = lean_box_usize(v_sz_3885_);
v___f_3899_ = lean_alloc_closure((void*)(l_Lean_Elab_partialFixpoint___lam__0___boxed), 22, 14);
lean_closure_set(v___f_3899_, 0, v_a_3884_);
lean_closure_set(v___f_3899_, 1, v_perms_3890_);
lean_closure_set(v___f_3899_, 2, v___x_3870_);
lean_closure_set(v___f_3899_, 3, v_preDefs_3862_);
lean_closure_set(v___f_3899_, 4, v___x_3871_);
lean_closure_set(v___f_3899_, 5, v___x_3882_);
lean_closure_set(v___f_3899_, 6, v___x_3896_);
lean_closure_set(v___f_3899_, 7, v___x_3887_);
lean_closure_set(v___f_3899_, 8, v_a_3889_);
lean_closure_set(v___f_3899_, 9, v___x_3897_);
lean_closure_set(v___f_3899_, 10, v_hints_3872_);
lean_closure_set(v___f_3899_, 11, v___x_3892_);
lean_closure_set(v___f_3899_, 12, v_docCtx_3861_);
lean_closure_set(v___f_3899_, 13, v___x_3898_);
v___x_3900_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg(v___x_3895_, v_type_3893_, v___f_3899_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_);
return v___x_3900_;
}
else
{
lean_object* v_a_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3908_; 
lean_dec_ref(v___x_3887_);
lean_dec(v_a_3884_);
lean_dec_ref(v___x_3882_);
lean_dec_ref(v_hints_3872_);
lean_dec_ref(v_preDefs_3862_);
lean_dec_ref(v_docCtx_3861_);
v_a_3901_ = lean_ctor_get(v___x_3888_, 0);
v_isSharedCheck_3908_ = !lean_is_exclusive(v___x_3888_);
if (v_isSharedCheck_3908_ == 0)
{
v___x_3903_ = v___x_3888_;
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_a_3901_);
lean_dec(v___x_3888_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3906_; 
if (v_isShared_3904_ == 0)
{
v___x_3906_ = v___x_3903_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_a_3901_);
v___x_3906_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
return v___x_3906_;
}
}
}
}
else
{
lean_object* v_a_3909_; lean_object* v___x_3911_; uint8_t v_isShared_3912_; uint8_t v_isSharedCheck_3916_; 
lean_dec_ref(v___x_3882_);
lean_dec_ref(v_hints_3872_);
lean_dec_ref(v_preDefs_3862_);
lean_dec_ref(v_docCtx_3861_);
v_a_3909_ = lean_ctor_get(v___x_3883_, 0);
v_isSharedCheck_3916_ = !lean_is_exclusive(v___x_3883_);
if (v_isSharedCheck_3916_ == 0)
{
v___x_3911_ = v___x_3883_;
v_isShared_3912_ = v_isSharedCheck_3916_;
goto v_resetjp_3910_;
}
else
{
lean_inc(v_a_3909_);
lean_dec(v___x_3883_);
v___x_3911_ = lean_box(0);
v_isShared_3912_ = v_isSharedCheck_3916_;
goto v_resetjp_3910_;
}
v_resetjp_3910_:
{
lean_object* v___x_3914_; 
if (v_isShared_3912_ == 0)
{
v___x_3914_ = v___x_3911_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v_a_3909_);
v___x_3914_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
return v___x_3914_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_partialFixpoint___boxed(lean_object* v_docCtx_3926_, lean_object* v_preDefs_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_){
_start:
{
lean_object* v_res_3935_; 
v_res_3935_ = l_Lean_Elab_partialFixpoint(v_docCtx_3926_, v_preDefs_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_, v_a_3933_);
lean_dec(v_a_3933_);
lean_dec_ref(v_a_3932_);
lean_dec(v_a_3931_);
lean_dec_ref(v_a_3930_);
lean_dec(v_a_3929_);
lean_dec_ref(v_a_3928_);
return v_res_3935_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1(lean_object* v_00_u03b1_3936_, lean_object* v_msg_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_){
_start:
{
lean_object* v___x_3945_; 
v___x_3945_ = l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___redArg(v_msg_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_);
return v___x_3945_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___boxed(lean_object* v_00_u03b1_3946_, lean_object* v_msg_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_){
_start:
{
lean_object* v_res_3955_; 
v_res_3955_ = l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1(v_00_u03b1_3946_, v_msg_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_);
lean_dec(v___y_3953_);
lean_dec_ref(v___y_3952_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
return v_res_3955_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2(lean_object* v_cls_3956_, lean_object* v_msg_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_){
_start:
{
lean_object* v___x_3965_; 
v___x_3965_ = l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg(v_cls_3956_, v_msg_3957_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_);
return v___x_3965_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___boxed(lean_object* v_cls_3966_, lean_object* v_msg_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_){
_start:
{
lean_object* v_res_3975_; 
v_res_3975_ = l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2(v_cls_3966_, v_msg_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_);
lean_dec(v___y_3973_);
lean_dec_ref(v___y_3972_);
lean_dec(v___y_3971_);
lean_dec_ref(v___y_3970_);
lean_dec(v___y_3969_);
lean_dec_ref(v___y_3968_);
return v_res_3975_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6(lean_object* v_hints_3976_, lean_object* v_as_3977_, lean_object* v_i_3978_, lean_object* v_j_3979_, lean_object* v_inv_3980_, lean_object* v_bs_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_){
_start:
{
lean_object* v___x_3989_; 
v___x_3989_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg(v_hints_3976_, v_as_3977_, v_i_3978_, v_j_3979_, v_bs_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
return v___x_3989_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6___boxed(lean_object* v_hints_3990_, lean_object* v_as_3991_, lean_object* v_i_3992_, lean_object* v_j_3993_, lean_object* v_inv_3994_, lean_object* v_bs_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_){
_start:
{
lean_object* v_res_4003_; 
v_res_4003_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__6(v_hints_3990_, v_as_3991_, v_i_3992_, v_j_3993_, v_inv_3994_, v_bs_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_);
lean_dec(v___y_4001_);
lean_dec_ref(v___y_4000_);
lean_dec(v___y_3999_);
lean_dec_ref(v___y_3998_);
lean_dec(v___y_3997_);
lean_dec_ref(v___y_3996_);
lean_dec_ref(v_as_3991_);
lean_dec_ref(v_hints_3990_);
return v_res_4003_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__10(lean_object* v___x_4004_, lean_object* v_fixedArgs_4005_, lean_object* v_as_4006_, lean_object* v_i_4007_, lean_object* v_j_4008_, lean_object* v_inv_4009_, lean_object* v_bs_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_){
_start:
{
lean_object* v___x_4018_; 
v___x_4018_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__10___redArg(v___x_4004_, v_fixedArgs_4005_, v_as_4006_, v_i_4007_, v_j_4008_, v_bs_4010_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_);
return v___x_4018_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__10___boxed(lean_object* v___x_4019_, lean_object* v_fixedArgs_4020_, lean_object* v_as_4021_, lean_object* v_i_4022_, lean_object* v_j_4023_, lean_object* v_inv_4024_, lean_object* v_bs_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_){
_start:
{
lean_object* v_res_4033_; 
v_res_4033_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__10(v___x_4019_, v_fixedArgs_4020_, v_as_4021_, v_i_4022_, v_j_4023_, v_inv_4024_, v_bs_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_);
lean_dec(v___y_4031_);
lean_dec_ref(v___y_4030_);
lean_dec(v___y_4029_);
lean_dec_ref(v___y_4028_);
lean_dec(v___y_4027_);
lean_dec_ref(v___y_4026_);
lean_dec_ref(v_as_4021_);
lean_dec_ref(v___x_4019_);
return v_res_4033_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11(lean_object* v___x_4034_, lean_object* v_fixedArgs_4035_, lean_object* v_as_4036_, lean_object* v_i_4037_, lean_object* v_j_4038_, lean_object* v_inv_4039_, lean_object* v_bs_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_){
_start:
{
lean_object* v___x_4048_; 
v___x_4048_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11___redArg(v___x_4034_, v_fixedArgs_4035_, v_as_4036_, v_i_4037_, v_j_4038_, v_bs_4040_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_);
return v___x_4048_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11___boxed(lean_object* v___x_4049_, lean_object* v_fixedArgs_4050_, lean_object* v_as_4051_, lean_object* v_i_4052_, lean_object* v_j_4053_, lean_object* v_inv_4054_, lean_object* v_bs_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_){
_start:
{
lean_object* v_res_4063_; 
v_res_4063_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11(v___x_4049_, v_fixedArgs_4050_, v_as_4051_, v_i_4052_, v_j_4053_, v_inv_4054_, v_bs_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_);
lean_dec(v___y_4061_);
lean_dec_ref(v___y_4060_);
lean_dec(v___y_4059_);
lean_dec_ref(v___y_4058_);
lean_dec(v___y_4057_);
lean_dec_ref(v___y_4056_);
lean_dec_ref(v_as_4051_);
lean_dec_ref(v___x_4049_);
return v_res_4063_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13(lean_object* v_as_4064_, size_t v_i_4065_, size_t v_stop_4066_, lean_object* v_b_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_){
_start:
{
lean_object* v___x_4075_; 
v___x_4075_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13___redArg(v_as_4064_, v_i_4065_, v_stop_4066_, v_b_4067_, v___y_4072_, v___y_4073_);
return v___x_4075_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13___boxed(lean_object* v_as_4076_, lean_object* v_i_4077_, lean_object* v_stop_4078_, lean_object* v_b_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_){
_start:
{
size_t v_i_boxed_4087_; size_t v_stop_boxed_4088_; lean_object* v_res_4089_; 
v_i_boxed_4087_ = lean_unbox_usize(v_i_4077_);
lean_dec(v_i_4077_);
v_stop_boxed_4088_ = lean_unbox_usize(v_stop_4078_);
lean_dec(v_stop_4078_);
v_res_4089_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13(v_as_4076_, v_i_boxed_4087_, v_stop_boxed_4088_, v_b_4079_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_);
lean_dec(v___y_4085_);
lean_dec_ref(v___y_4084_);
lean_dec(v___y_4083_);
lean_dec_ref(v___y_4082_);
lean_dec(v___y_4081_);
lean_dec_ref(v___y_4080_);
lean_dec_ref(v_as_4076_);
return v_res_4089_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16(lean_object* v_env_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_){
_start:
{
lean_object* v___x_4098_; 
v___x_4098_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16___redArg(v_env_4090_, v___y_4094_, v___y_4096_);
return v___x_4098_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16___boxed(lean_object* v_env_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_){
_start:
{
lean_object* v_res_4107_; 
v_res_4107_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16(v_env_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_);
lean_dec(v___y_4105_);
lean_dec_ref(v___y_4104_);
lean_dec(v___y_4103_);
lean_dec_ref(v___y_4102_);
lean_dec(v___y_4101_);
lean_dec_ref(v___y_4100_);
return v_res_4107_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14(lean_object* v_00_u03b1_4108_, lean_object* v_env_4109_, lean_object* v_x_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_){
_start:
{
lean_object* v___x_4118_; 
v___x_4118_ = l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14___redArg(v_env_4109_, v_x_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_);
return v___x_4118_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14___boxed(lean_object* v_00_u03b1_4119_, lean_object* v_env_4120_, lean_object* v_x_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_){
_start:
{
lean_object* v_res_4129_; 
v_res_4129_ = l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14(v_00_u03b1_4119_, v_env_4120_, v_x_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_);
lean_dec(v___y_4127_);
lean_dec_ref(v___y_4126_);
lean_dec(v___y_4125_);
lean_dec_ref(v___y_4124_);
lean_dec(v___y_4123_);
lean_dec_ref(v___y_4122_);
return v_res_4129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18(lean_object* v_00_u03b1_4130_, lean_object* v_name_4131_, uint8_t v_bi_4132_, lean_object* v_type_4133_, lean_object* v_k_4134_, uint8_t v_kind_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_){
_start:
{
lean_object* v___x_4143_; 
v___x_4143_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg(v_name_4131_, v_bi_4132_, v_type_4133_, v_k_4134_, v_kind_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_);
return v___x_4143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___boxed(lean_object* v_00_u03b1_4144_, lean_object* v_name_4145_, lean_object* v_bi_4146_, lean_object* v_type_4147_, lean_object* v_k_4148_, lean_object* v_kind_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_){
_start:
{
uint8_t v_bi_boxed_4157_; uint8_t v_kind_boxed_4158_; lean_object* v_res_4159_; 
v_bi_boxed_4157_ = lean_unbox(v_bi_4146_);
v_kind_boxed_4158_ = lean_unbox(v_kind_4149_);
v_res_4159_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18(v_00_u03b1_4144_, v_name_4145_, v_bi_boxed_4157_, v_type_4147_, v_k_4148_, v_kind_boxed_4158_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_);
lean_dec(v___y_4155_);
lean_dec_ref(v___y_4154_);
lean_dec(v___y_4153_);
lean_dec_ref(v___y_4152_);
lean_dec(v___y_4151_);
lean_dec_ref(v___y_4150_);
return v_res_4159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15(lean_object* v_00_u03b1_4160_, lean_object* v_name_4161_, lean_object* v_type_4162_, lean_object* v_k_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_){
_start:
{
lean_object* v___x_4171_; 
v___x_4171_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15___redArg(v_name_4161_, v_type_4162_, v_k_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_);
return v___x_4171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15___boxed(lean_object* v_00_u03b1_4172_, lean_object* v_name_4173_, lean_object* v_type_4174_, lean_object* v_k_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_){
_start:
{
lean_object* v_res_4183_; 
v_res_4183_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15(v_00_u03b1_4172_, v_name_4173_, v_type_4174_, v_k_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_);
lean_dec(v___y_4181_);
lean_dec_ref(v___y_4180_);
lean_dec(v___y_4179_);
lean_dec_ref(v___y_4178_);
lean_dec(v___y_4177_);
lean_dec_ref(v___y_4176_);
return v_res_4183_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21(lean_object* v_00_u03b1_4184_, lean_object* v_x_4185_, uint8_t v_isExporting_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_){
_start:
{
lean_object* v___x_4194_; 
v___x_4194_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg(v_x_4185_, v_isExporting_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
return v___x_4194_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___boxed(lean_object* v_00_u03b1_4195_, lean_object* v_x_4196_, lean_object* v_isExporting_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_){
_start:
{
uint8_t v_isExporting_boxed_4205_; lean_object* v_res_4206_; 
v_isExporting_boxed_4205_ = lean_unbox(v_isExporting_4197_);
v_res_4206_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21(v_00_u03b1_4195_, v_x_4196_, v_isExporting_boxed_4205_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_);
lean_dec(v___y_4203_);
lean_dec_ref(v___y_4202_);
lean_dec(v___y_4201_);
lean_dec_ref(v___y_4200_);
lean_dec(v___y_4199_);
lean_dec_ref(v___y_4198_);
return v_res_4206_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17(lean_object* v_00_u03b1_4207_, lean_object* v_x_4208_, uint8_t v_when_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_){
_start:
{
lean_object* v___x_4217_; 
v___x_4217_ = l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17___redArg(v_x_4208_, v_when_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_);
return v___x_4217_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17___boxed(lean_object* v_00_u03b1_4218_, lean_object* v_x_4219_, lean_object* v_when_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_){
_start:
{
uint8_t v_when_boxed_4228_; lean_object* v_res_4229_; 
v_when_boxed_4228_ = lean_unbox(v_when_4220_);
v_res_4229_ = l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17(v_00_u03b1_4218_, v_x_4219_, v_when_boxed_4228_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_);
lean_dec(v___y_4226_);
lean_dec_ref(v___y_4225_);
lean_dec(v___y_4224_);
lean_dec_ref(v___y_4223_);
lean_dec(v___y_4222_);
lean_dec_ref(v___y_4221_);
return v_res_4229_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21(lean_object* v___x_4230_, lean_object* v___x_4231_, lean_object* v___y_4232_, lean_object* v___x_4233_, lean_object* v_a_4234_, lean_object* v_as_4235_, lean_object* v_i_4236_, lean_object* v_j_4237_, lean_object* v_inv_4238_, lean_object* v_bs_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_){
_start:
{
lean_object* v___x_4247_; 
v___x_4247_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg(v___x_4230_, v___x_4231_, v___y_4232_, v___x_4233_, v_a_4234_, v_as_4235_, v_i_4236_, v_j_4237_, v_bs_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_);
return v___x_4247_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21___boxed(lean_object** _args){
lean_object* v___x_4248_ = _args[0];
lean_object* v___x_4249_ = _args[1];
lean_object* v___y_4250_ = _args[2];
lean_object* v___x_4251_ = _args[3];
lean_object* v_a_4252_ = _args[4];
lean_object* v_as_4253_ = _args[5];
lean_object* v_i_4254_ = _args[6];
lean_object* v_j_4255_ = _args[7];
lean_object* v_inv_4256_ = _args[8];
lean_object* v_bs_4257_ = _args[9];
lean_object* v___y_4258_ = _args[10];
lean_object* v___y_4259_ = _args[11];
lean_object* v___y_4260_ = _args[12];
lean_object* v___y_4261_ = _args[13];
lean_object* v___y_4262_ = _args[14];
lean_object* v___y_4263_ = _args[15];
lean_object* v___y_4264_ = _args[16];
_start:
{
lean_object* v_res_4265_; 
v_res_4265_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__21(v___x_4248_, v___x_4249_, v___y_4250_, v___x_4251_, v_a_4252_, v_as_4253_, v_i_4254_, v_j_4255_, v_inv_4256_, v_bs_4257_, v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_);
lean_dec(v___y_4263_);
lean_dec_ref(v___y_4262_);
lean_dec(v___y_4261_);
lean_dec_ref(v___y_4260_);
lean_dec(v___y_4259_);
lean_dec_ref(v___y_4258_);
lean_dec_ref(v_as_4253_);
lean_dec_ref(v___x_4248_);
return v_res_4265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__22(size_t v_sz_4266_, size_t v_i_4267_, lean_object* v_bs_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_){
_start:
{
lean_object* v___x_4276_; 
v___x_4276_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__22___redArg(v_sz_4266_, v_i_4267_, v_bs_4268_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_);
return v___x_4276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__22___boxed(lean_object* v_sz_4277_, lean_object* v_i_4278_, lean_object* v_bs_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_){
_start:
{
size_t v_sz_boxed_4287_; size_t v_i_boxed_4288_; lean_object* v_res_4289_; 
v_sz_boxed_4287_ = lean_unbox_usize(v_sz_4277_);
lean_dec(v_sz_4277_);
v_i_boxed_4288_ = lean_unbox_usize(v_i_4278_);
lean_dec(v_i_4278_);
v_res_4289_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__22(v_sz_boxed_4287_, v_i_boxed_4288_, v_bs_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_);
lean_dec(v___y_4285_);
lean_dec_ref(v___y_4284_);
lean_dec(v___y_4283_);
lean_dec_ref(v___y_4282_);
lean_dec(v___y_4281_);
lean_dec_ref(v___y_4280_);
return v_res_4289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2(lean_object* v_msgData_4290_, lean_object* v_macroStack_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_){
_start:
{
lean_object* v___x_4299_; 
v___x_4299_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg(v_msgData_4290_, v_macroStack_4291_, v___y_4296_);
return v___x_4299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___boxed(lean_object* v_msgData_4300_, lean_object* v_macroStack_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_){
_start:
{
lean_object* v_res_4309_; 
v_res_4309_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2(v_msgData_4300_, v_macroStack_4301_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_);
lean_dec(v___y_4307_);
lean_dec_ref(v___y_4306_);
lean_dec(v___y_4305_);
lean_dec_ref(v___y_4304_);
lean_dec(v___y_4303_);
lean_dec_ref(v___y_4302_);
return v_res_4309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4373_; uint8_t v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; 
v___x_4373_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7));
v___x_4374_ = 0;
v___x_4375_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__25_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_));
v___x_4376_ = l_Lean_registerTraceClass(v___x_4373_, v___x_4374_, v___x_4375_);
return v___x_4376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2____boxed(lean_object* v_a_4377_){
_start:
{
lean_object* v_res_4378_; 
v_res_4378_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_();
return v_res_4378_;
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
