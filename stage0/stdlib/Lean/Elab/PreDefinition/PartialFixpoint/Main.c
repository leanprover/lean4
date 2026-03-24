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
lean_object* l_Lean_hasRecAppSyntax___boxed(lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_Lean_getRecAppSyntax_x3f(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_andList(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkInstPiOfInstsForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_isLatticeTheoretic(uint8_t);
lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Elab_Mutual_cleanPreDef(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedPartialFixpoint_default;
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkInhabitantFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Meta_toPartialOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_logUnassignedUsingErrorInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSorry(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_Monotonicity_solveMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapErrorImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM(lean_object*);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_partialFixpoint_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_partialFixpoint_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_partialFixpoint_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_partialFixpoint_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__4___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__4(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__6___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__19___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__21___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__25___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__25___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__25___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__25___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Elab_partialFixpoint_spec__26___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__26___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__13___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__13___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__13___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__13___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__13___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__13(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__16_spec__19___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__16_spec__19___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__16_spec__19___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__16_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__15_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__15_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__14___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__17___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__17___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__17___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__17___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__17___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "f"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__17___redArg___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__17___redArg___closed__0_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__17___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__17___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 68, 183, 24, 128, 148, 178, 23)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__17___redArg___closed__1 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__17___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__17___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__17___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__3___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__3___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__3___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__2(lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__10___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__10___closed__0_value;
static lean_once_cell_t l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__10___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__10___closed__1;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__10(lean_object*, lean_object*);
static const lean_closure_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_hasRecAppSyntax___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__0_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Cannot eliminate recursive call `"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__1 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__1_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__2;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "` enclosed in"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__3 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__3_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__4;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__5 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__5_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__6;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Elab.partialFixpoint"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__7 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__7_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "getRecAppSyntax\? failed"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__8 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__8_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__9;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Cannot eliminate recursive call in"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__10 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__10_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__11;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Tried to apply "};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__12 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__12_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__13;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = ", but failed.\nPossible cause: A missing `"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__14 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__14_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__15;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "MonoBind"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__16 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__16_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__3_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__17_value_aux_1),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__16_value),LEAN_SCALAR_PTR_LITERAL(150, 25, 7, 134, 163, 66, 53, 232)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__17 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__17_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "` instance.\nUse `set_option trace.Elab.Tactic.monotonicity true` to debug."};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__18 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__18_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__19;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__20;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Could not prove '"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__0_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__1;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "' to be monotone in its recursive calls:"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__2 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__2_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__3;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__4 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__4_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__5 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__5_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "partialFixpoint"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__6 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__6_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__7_value_aux_0),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__7_value_aux_1),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(21, 214, 78, 192, 157, 92, 193, 45)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__7 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__7_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "monotonicity proof for "};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__8 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__8_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__9;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__10 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__10_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__11;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__24(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__24___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__23___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__22___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__22___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__22___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__18_spec__22___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__18_spec__22___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__18_spec__22___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__18_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__18___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__5(lean_object*, lean_object*);
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "failed to compile definition '"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__0_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__1;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "' using `partial_fixpoint`"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__2 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__2_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__3;
static const lean_array_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__4 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__4_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Nonempty"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__5 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__5_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__6 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__6_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(142, 191, 110, 220, 210, 100, 152, 183)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__7_value_aux_0),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__6_value),LEAN_SCALAR_PTR_LITERAL(113, 209, 180, 93, 84, 117, 67, 110)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__7 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__7_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Classical"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__8 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__8_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ofNonempty"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__9 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__9_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__8_value),LEAN_SCALAR_PTR_LITERAL(40, 236, 220, 79, 38, 141, 161, 150)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__10_value_aux_0),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__9_value),LEAN_SCALAR_PTR_LITERAL(197, 41, 144, 91, 215, 43, 73, 12)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__10 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__10_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__11;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "FlatOrder"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__12 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__12_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instCCPO"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__13 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__13_value;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "No CCPO instance found for "};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__0_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__1;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = ", trying inhabitation"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__2 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__2_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__3;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "CCPO"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__4 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__4_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__3_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__5_value_aux_1),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(19, 35, 8, 63, 189, 207, 68, 204)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__5 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__5_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "preDef.value: "};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__6 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__6_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__7;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = ", xs: "};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__8 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__8_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__9;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = ", _body: "};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__10 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__10_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__11;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__12___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__12___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__12___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__12___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__12___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__12___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__12___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__12___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__12___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__12___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__12(lean_object*, lean_object*);
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
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "ReverseImplicationOrder"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___closed__0_value;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "instCompleteLattice"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___closed__1 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___closed__1_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__3_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___closed__2_value_aux_1),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 161, 0, 6, 7, 21, 122, 42)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___closed__2_value_aux_2),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(58, 218, 120, 132, 216, 84, 59, 130)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___closed__2 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___closed__2_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___closed__3;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "`coinductive_fixpoint` can be only used to define predicates"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___closed__4 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___closed__4_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ImplicationOrder"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__1___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__3_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__1___closed__1_value_aux_1),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(106, 240, 34, 128, 168, 240, 126, 19)}};
static const lean_ctor_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__1___closed__1_value_aux_2),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(89, 9, 5, 228, 125, 57, 241, 212)}};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__1___closed__1 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__1___closed__1_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__1___closed__2;
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "`inductive_fixpoint` can be only used to define predicates"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__1___closed__3 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__1___closed__3_value;
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__1___closed__4;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___closed__0_value;
static const lean_closure_object l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___closed__1 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27_spec__32(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27_spec__32___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__28_spec__34(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__28_spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__28(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__14(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__15_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__15_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__16_spec__19(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__16_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__18_spec__22(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__18_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__18(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__22___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__23(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__0_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__1_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
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
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__16_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__15_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value),((lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(165, 120, 90, 26, 169, 90, 9, 167)}};
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
v___x_710__overap_9_ = lean_panic_fn(v___f_8_, v_msg_2_);
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
lean_inc(v_a_946_);
lean_dec_ref(v___x_945_);
lean_inc(v_a_870_);
lean_inc_ref(v_a_869_);
lean_inc(v_a_868_);
lean_inc_ref(v_a_867_);
lean_inc(v_a_946_);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_partialFixpoint_spec__2___redArg(lean_object* v_cls_988_, lean_object* v___y_989_){
_start:
{
lean_object* v_options_991_; uint8_t v_hasTrace_992_; 
v_options_991_ = lean_ctor_get(v___y_989_, 2);
v_hasTrace_992_ = lean_ctor_get_uint8(v_options_991_, sizeof(void*)*1);
if (v_hasTrace_992_ == 0)
{
lean_object* v___x_993_; lean_object* v___x_994_; 
lean_dec(v_cls_988_);
v___x_993_ = lean_box(v_hasTrace_992_);
v___x_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
return v___x_994_;
}
else
{
lean_object* v_inheritedTraceOptions_995_; lean_object* v___x_996_; lean_object* v___x_997_; uint8_t v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v_inheritedTraceOptions_995_ = lean_ctor_get(v___y_989_, 13);
v___x_996_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__1));
v___x_997_ = l_Lean_Name_append(v___x_996_, v_cls_988_);
v___x_998_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_995_, v_options_991_, v___x_997_);
lean_dec(v___x_997_);
v___x_999_ = lean_box(v___x_998_);
v___x_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
return v___x_1000_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_partialFixpoint_spec__2___redArg___boxed(lean_object* v_cls_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_partialFixpoint_spec__2___redArg(v_cls_1001_, v___y_1002_);
lean_dec_ref(v___y_1002_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_partialFixpoint_spec__2(lean_object* v_cls_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_partialFixpoint_spec__2___redArg(v_cls_1005_, v___y_1010_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_partialFixpoint_spec__2___boxed(lean_object* v_cls_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_partialFixpoint_spec__2(v_cls_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__4___redArg___lam__0(lean_object* v_k_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v_b_1026_, lean_object* v_c_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v___x_1033_; 
lean_inc(v___y_1031_);
lean_inc_ref(v___y_1030_);
lean_inc(v___y_1029_);
lean_inc_ref(v___y_1028_);
lean_inc(v___y_1025_);
lean_inc_ref(v___y_1024_);
v___x_1033_ = lean_apply_9(v_k_1023_, v_b_1026_, v_c_1027_, v___y_1024_, v___y_1025_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, lean_box(0));
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__4___redArg___lam__0___boxed(lean_object* v_k_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v_b_1037_, lean_object* v_c_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__4___redArg___lam__0(v_k_1034_, v___y_1035_, v___y_1036_, v_b_1037_, v_c_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__4___redArg(lean_object* v_type_1045_, lean_object* v_k_1046_, uint8_t v_cleanupAnnotations_1047_, uint8_t v_whnfType_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v___f_1056_; lean_object* v___x_1057_; 
lean_inc(v___y_1050_);
lean_inc_ref(v___y_1049_);
v___f_1056_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__4___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1056_, 0, v_k_1046_);
lean_closure_set(v___f_1056_, 1, v___y_1049_);
lean_closure_set(v___f_1056_, 2, v___y_1050_);
v___x_1057_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1045_, v___f_1056_, v_cleanupAnnotations_1047_, v_whnfType_1048_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
if (lean_obj_tag(v___x_1057_) == 0)
{
return v___x_1057_;
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_1057_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1057_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1058_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__4___redArg___boxed(lean_object* v_type_1066_, lean_object* v_k_1067_, lean_object* v_cleanupAnnotations_1068_, lean_object* v_whnfType_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1077_; uint8_t v_whnfType_boxed_1078_; lean_object* v_res_1079_; 
v_cleanupAnnotations_boxed_1077_ = lean_unbox(v_cleanupAnnotations_1068_);
v_whnfType_boxed_1078_ = lean_unbox(v_whnfType_1069_);
v_res_1079_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__4___redArg(v_type_1066_, v_k_1067_, v_cleanupAnnotations_boxed_1077_, v_whnfType_boxed_1078_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__4(lean_object* v_00_u03b1_1080_, lean_object* v_type_1081_, lean_object* v_k_1082_, uint8_t v_cleanupAnnotations_1083_, uint8_t v_whnfType_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v___x_1092_; 
v___x_1092_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__4___redArg(v_type_1081_, v_k_1082_, v_cleanupAnnotations_1083_, v_whnfType_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__4___boxed(lean_object* v_00_u03b1_1093_, lean_object* v_type_1094_, lean_object* v_k_1095_, lean_object* v_cleanupAnnotations_1096_, lean_object* v_whnfType_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1105_; uint8_t v_whnfType_boxed_1106_; lean_object* v_res_1107_; 
v_cleanupAnnotations_boxed_1105_ = lean_unbox(v_cleanupAnnotations_1096_);
v_whnfType_boxed_1106_ = lean_unbox(v_whnfType_1097_);
v_res_1107_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__4(v_00_u03b1_1093_, v_type_1094_, v_k_1095_, v_cleanupAnnotations_boxed_1105_, v_whnfType_boxed_1106_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__6___redArg(lean_object* v_e_1108_, lean_object* v_k_1109_, uint8_t v_cleanupAnnotations_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v___f_1118_; uint8_t v___x_1119_; uint8_t v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
lean_inc(v___y_1112_);
lean_inc_ref(v___y_1111_);
v___f_1118_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__4___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1118_, 0, v_k_1109_);
lean_closure_set(v___f_1118_, 1, v___y_1111_);
lean_closure_set(v___f_1118_, 2, v___y_1112_);
v___x_1119_ = 1;
v___x_1120_ = 0;
v___x_1121_ = lean_box(0);
v___x_1122_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1108_, v___x_1119_, v___x_1120_, v___x_1119_, v___x_1120_, v___x_1121_, v___f_1118_, v_cleanupAnnotations_1110_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
if (lean_obj_tag(v___x_1122_) == 0)
{
return v___x_1122_;
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v___x_1122_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1122_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_a_1123_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__6___redArg___boxed(lean_object* v_e_1131_, lean_object* v_k_1132_, lean_object* v_cleanupAnnotations_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1141_; lean_object* v_res_1142_; 
v_cleanupAnnotations_boxed_1141_ = lean_unbox(v_cleanupAnnotations_1133_);
v_res_1142_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__6___redArg(v_e_1131_, v_k_1132_, v_cleanupAnnotations_boxed_1141_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__6(lean_object* v_00_u03b1_1143_, lean_object* v_e_1144_, lean_object* v_k_1145_, uint8_t v_cleanupAnnotations_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__6___redArg(v_e_1144_, v_k_1145_, v_cleanupAnnotations_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__6___boxed(lean_object* v_00_u03b1_1155_, lean_object* v_e_1156_, lean_object* v_k_1157_, lean_object* v_cleanupAnnotations_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1166_; lean_object* v_res_1167_; 
v_cleanupAnnotations_boxed_1166_ = lean_unbox(v_cleanupAnnotations_1158_);
v_res_1167_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__6(v_00_u03b1_1155_, v_e_1156_, v_k_1157_, v_cleanupAnnotations_boxed_1166_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__9___redArg(lean_object* v_msg_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v___f_1174_; lean_object* v___x_38662__overap_1175_; lean_object* v___x_1176_; 
v___f_1174_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__0___closed__0));
v___x_38662__overap_1175_ = lean_panic_fn(v___f_1174_, v_msg_1168_);
lean_inc(v___y_1172_);
lean_inc_ref(v___y_1171_);
lean_inc(v___y_1170_);
lean_inc_ref(v___y_1169_);
v___x_1176_ = lean_apply_5(v___x_38662__overap_1175_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, lean_box(0));
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__9___redArg___boxed(lean_object* v_msg_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_panic___at___00Lean_Elab_partialFixpoint_spec__9___redArg(v_msg_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__9(lean_object* v_00_u03b1_1184_, lean_object* v_msg_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l_panic___at___00Lean_Elab_partialFixpoint_spec__9___redArg(v_msg_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__9___boxed(lean_object* v_00_u03b1_1192_, lean_object* v_msg_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_panic___at___00Lean_Elab_partialFixpoint_spec__9(v_00_u03b1_1192_, v_msg_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__19___redArg(lean_object* v_e_1200_, lean_object* v___y_1201_){
_start:
{
uint8_t v___x_1203_; 
v___x_1203_ = l_Lean_Expr_hasMVar(v_e_1200_);
if (v___x_1203_ == 0)
{
lean_object* v___x_1204_; 
v___x_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1204_, 0, v_e_1200_);
return v___x_1204_;
}
else
{
lean_object* v___x_1205_; lean_object* v_mctx_1206_; lean_object* v___x_1207_; lean_object* v_fst_1208_; lean_object* v_snd_1209_; lean_object* v___x_1210_; lean_object* v_cache_1211_; lean_object* v_zetaDeltaFVarIds_1212_; lean_object* v_postponed_1213_; lean_object* v_diag_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1223_; 
v___x_1205_ = lean_st_ref_get(v___y_1201_);
v_mctx_1206_ = lean_ctor_get(v___x_1205_, 0);
lean_inc_ref(v_mctx_1206_);
lean_dec(v___x_1205_);
v___x_1207_ = l_Lean_instantiateMVarsCore(v_mctx_1206_, v_e_1200_);
v_fst_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_fst_1208_);
v_snd_1209_ = lean_ctor_get(v___x_1207_, 1);
lean_inc(v_snd_1209_);
lean_dec_ref(v___x_1207_);
v___x_1210_ = lean_st_ref_take(v___y_1201_);
v_cache_1211_ = lean_ctor_get(v___x_1210_, 1);
v_zetaDeltaFVarIds_1212_ = lean_ctor_get(v___x_1210_, 2);
v_postponed_1213_ = lean_ctor_get(v___x_1210_, 3);
v_diag_1214_ = lean_ctor_get(v___x_1210_, 4);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1223_ == 0)
{
lean_object* v_unused_1224_; 
v_unused_1224_ = lean_ctor_get(v___x_1210_, 0);
lean_dec(v_unused_1224_);
v___x_1216_ = v___x_1210_;
v_isShared_1217_ = v_isSharedCheck_1223_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_diag_1214_);
lean_inc(v_postponed_1213_);
lean_inc(v_zetaDeltaFVarIds_1212_);
lean_inc(v_cache_1211_);
lean_dec(v___x_1210_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1223_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 0, v_snd_1209_);
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_snd_1209_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v_cache_1211_);
lean_ctor_set(v_reuseFailAlloc_1222_, 2, v_zetaDeltaFVarIds_1212_);
lean_ctor_set(v_reuseFailAlloc_1222_, 3, v_postponed_1213_);
lean_ctor_set(v_reuseFailAlloc_1222_, 4, v_diag_1214_);
v___x_1219_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = lean_st_ref_set(v___y_1201_, v___x_1219_);
v___x_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1221_, 0, v_fst_1208_);
return v___x_1221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__19___redArg___boxed(lean_object* v_e_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__19___redArg(v_e_1225_, v___y_1226_);
lean_dec(v___y_1226_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__19(lean_object* v_e_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__19___redArg(v_e_1229_, v___y_1233_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__19___boxed(lean_object* v_e_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__19(v_e_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__21___redArg(lean_object* v_type_1247_, lean_object* v_maxFVars_x3f_1248_, lean_object* v_k_1249_, uint8_t v_cleanupAnnotations_1250_, uint8_t v_whnfType_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v___f_1259_; lean_object* v___x_1260_; 
lean_inc(v___y_1253_);
lean_inc_ref(v___y_1252_);
v___f_1259_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__4___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1259_, 0, v_k_1249_);
lean_closure_set(v___f_1259_, 1, v___y_1252_);
lean_closure_set(v___f_1259_, 2, v___y_1253_);
v___x_1260_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1247_, v_maxFVars_x3f_1248_, v___f_1259_, v_cleanupAnnotations_1250_, v_whnfType_1251_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
if (lean_obj_tag(v___x_1260_) == 0)
{
return v___x_1260_;
}
else
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1268_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1263_ = v___x_1260_;
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1260_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_a_1261_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__21___redArg___boxed(lean_object* v_type_1269_, lean_object* v_maxFVars_x3f_1270_, lean_object* v_k_1271_, lean_object* v_cleanupAnnotations_1272_, lean_object* v_whnfType_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1281_; uint8_t v_whnfType_boxed_1282_; lean_object* v_res_1283_; 
v_cleanupAnnotations_boxed_1281_ = lean_unbox(v_cleanupAnnotations_1272_);
v_whnfType_boxed_1282_ = lean_unbox(v_whnfType_1273_);
v_res_1283_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__21___redArg(v_type_1269_, v_maxFVars_x3f_1270_, v_k_1271_, v_cleanupAnnotations_boxed_1281_, v_whnfType_boxed_1282_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__21(lean_object* v_00_u03b1_1284_, lean_object* v_type_1285_, lean_object* v_maxFVars_x3f_1286_, lean_object* v_k_1287_, uint8_t v_cleanupAnnotations_1288_, uint8_t v_whnfType_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__21___redArg(v_type_1285_, v_maxFVars_x3f_1286_, v_k_1287_, v_cleanupAnnotations_1288_, v_whnfType_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__21___boxed(lean_object* v_00_u03b1_1298_, lean_object* v_type_1299_, lean_object* v_maxFVars_x3f_1300_, lean_object* v_k_1301_, lean_object* v_cleanupAnnotations_1302_, lean_object* v_whnfType_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1311_; uint8_t v_whnfType_boxed_1312_; lean_object* v_res_1313_; 
v_cleanupAnnotations_boxed_1311_ = lean_unbox(v_cleanupAnnotations_1302_);
v_whnfType_boxed_1312_ = lean_unbox(v_whnfType_1303_);
v_res_1313_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__21(v_00_u03b1_1298_, v_type_1299_, v_maxFVars_x3f_1300_, v_k_1301_, v_cleanupAnnotations_boxed_1311_, v_whnfType_boxed_1312_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__25___redArg___lam__0(lean_object* v_k_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v_b_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v___x_1323_; 
lean_inc(v___y_1321_);
lean_inc_ref(v___y_1320_);
lean_inc(v___y_1319_);
lean_inc_ref(v___y_1318_);
lean_inc(v___y_1316_);
lean_inc_ref(v___y_1315_);
v___x_1323_ = lean_apply_8(v_k_1314_, v_b_1317_, v___y_1315_, v___y_1316_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, lean_box(0));
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__25___redArg___lam__0___boxed(lean_object* v_k_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v_b_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__25___redArg___lam__0(v_k_1324_, v___y_1325_, v___y_1326_, v_b_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__25___redArg(lean_object* v_perm_1334_, lean_object* v_type_1335_, lean_object* v_k_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v___f_1344_; lean_object* v___x_1345_; 
lean_inc(v___y_1338_);
lean_inc_ref(v___y_1337_);
v___f_1344_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__25___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1344_, 0, v_k_1336_);
lean_closure_set(v___f_1344_, 1, v___y_1337_);
lean_closure_set(v___f_1344_, 2, v___y_1338_);
v___x_1345_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_box(0), v_perm_1334_, v_type_1335_, v___f_1344_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
if (lean_obj_tag(v___x_1345_) == 0)
{
return v___x_1345_;
}
else
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1353_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1348_ = v___x_1345_;
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1345_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1351_; 
if (v_isShared_1349_ == 0)
{
v___x_1351_ = v___x_1348_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1346_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__25___redArg___boxed(lean_object* v_perm_1354_, lean_object* v_type_1355_, lean_object* v_k_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__25___redArg(v_perm_1354_, v_type_1355_, v_k_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__25(lean_object* v_00_u03b1_1365_, lean_object* v_perm_1366_, lean_object* v_type_1367_, lean_object* v_k_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v___x_1376_; 
v___x_1376_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__25___redArg(v_perm_1366_, v_type_1367_, v_k_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__25___boxed(lean_object* v_00_u03b1_1377_, lean_object* v_perm_1378_, lean_object* v_type_1379_, lean_object* v_k_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__25(v_00_u03b1_1377_, v_perm_1378_, v_type_1379_, v_k_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
return v_res_1388_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_partialFixpoint_spec__26___closed__0(void){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__26(lean_object* v_msg_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_44603__overap_1399_; lean_object* v___x_1400_; 
v___x_1398_ = lean_obj_once(&l_panic___at___00Lean_Elab_partialFixpoint_spec__26___closed__0, &l_panic___at___00Lean_Elab_partialFixpoint_spec__26___closed__0_once, _init_l_panic___at___00Lean_Elab_partialFixpoint_spec__26___closed__0);
v___x_44603__overap_1399_ = lean_panic_fn(v___x_1398_, v_msg_1390_);
lean_inc(v___y_1396_);
lean_inc_ref(v___y_1395_);
lean_inc(v___y_1394_);
lean_inc_ref(v___y_1393_);
lean_inc(v___y_1392_);
lean_inc_ref(v___y_1391_);
v___x_1400_ = lean_apply_7(v___x_44603__overap_1399_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, lean_box(0));
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__26___boxed(lean_object* v_msg_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_panic___at___00Lean_Elab_partialFixpoint_spec__26(v_msg_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__13___lam__0(lean_object* v_xs_1410_, lean_object* v_inst_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = l_Lean_Meta_mkInstPiOfInstsForall(v_xs_1410_, v_inst_1411_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__13___lam__0___boxed(lean_object* v_xs_1420_, lean_object* v_inst_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__13___lam__0(v_xs_1420_, v_inst_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__13(size_t v_sz_1431_, size_t v_i_1432_, lean_object* v_bs_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
uint8_t v___x_1441_; 
v___x_1441_ = lean_usize_dec_lt(v_i_1432_, v_sz_1431_);
if (v___x_1441_ == 0)
{
lean_object* v___x_1442_; 
v___x_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1442_, 0, v_bs_1433_);
return v___x_1442_;
}
else
{
lean_object* v___f_1443_; lean_object* v_v_1444_; uint8_t v___x_1445_; lean_object* v___x_1446_; 
v___f_1443_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__13___closed__0));
v_v_1444_ = lean_array_uget_borrowed(v_bs_1433_, v_i_1432_);
v___x_1445_ = 0;
lean_inc(v_v_1444_);
v___x_1446_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__6___redArg(v_v_1444_, v___f_1443_, v___x_1445_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_object* v_a_1447_; lean_object* v___x_1448_; lean_object* v_bs_x27_1449_; size_t v___x_1450_; size_t v___x_1451_; lean_object* v___x_1452_; 
v_a_1447_ = lean_ctor_get(v___x_1446_, 0);
lean_inc(v_a_1447_);
lean_dec_ref(v___x_1446_);
v___x_1448_ = lean_unsigned_to_nat(0u);
v_bs_x27_1449_ = lean_array_uset(v_bs_1433_, v_i_1432_, v___x_1448_);
v___x_1450_ = ((size_t)1ULL);
v___x_1451_ = lean_usize_add(v_i_1432_, v___x_1450_);
v___x_1452_ = lean_array_uset(v_bs_x27_1449_, v_i_1432_, v_a_1447_);
v_i_1432_ = v___x_1451_;
v_bs_1433_ = v___x_1452_;
goto _start;
}
else
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
lean_dec_ref(v_bs_1433_);
v_a_1454_ = lean_ctor_get(v___x_1446_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___x_1446_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1446_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_a_1454_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__13___boxed(lean_object* v_sz_1462_, lean_object* v_i_1463_, lean_object* v_bs_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
size_t v_sz_boxed_1472_; size_t v_i_boxed_1473_; lean_object* v_res_1474_; 
v_sz_boxed_1472_ = lean_unbox_usize(v_sz_1462_);
lean_dec(v_sz_1462_);
v_i_boxed_1473_ = lean_unbox_usize(v_i_1463_);
lean_dec(v_i_1463_);
v_res_1474_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__13(v_sz_boxed_1472_, v_i_boxed_1473_, v_bs_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__16_spec__19___redArg___lam__0(lean_object* v_k_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v_b_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v___x_1484_; 
lean_inc(v___y_1482_);
lean_inc_ref(v___y_1481_);
lean_inc(v___y_1480_);
lean_inc_ref(v___y_1479_);
lean_inc(v___y_1477_);
lean_inc_ref(v___y_1476_);
v___x_1484_ = lean_apply_8(v_k_1475_, v_b_1478_, v___y_1476_, v___y_1477_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, lean_box(0));
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__16_spec__19___redArg___lam__0___boxed(lean_object* v_k_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v_b_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__16_spec__19___redArg___lam__0(v_k_1485_, v___y_1486_, v___y_1487_, v_b_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__16_spec__19___redArg(lean_object* v_name_1495_, uint8_t v_bi_1496_, lean_object* v_type_1497_, lean_object* v_k_1498_, uint8_t v_kind_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v___f_1507_; lean_object* v___x_1508_; 
lean_inc(v___y_1501_);
lean_inc_ref(v___y_1500_);
v___f_1507_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__16_spec__19___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1507_, 0, v_k_1498_);
lean_closure_set(v___f_1507_, 1, v___y_1500_);
lean_closure_set(v___f_1507_, 2, v___y_1501_);
v___x_1508_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1495_, v_bi_1496_, v_type_1497_, v___f_1507_, v_kind_1499_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
if (lean_obj_tag(v___x_1508_) == 0)
{
return v___x_1508_;
}
else
{
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1516_; 
v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1511_ = v___x_1508_;
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1508_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1514_; 
if (v_isShared_1512_ == 0)
{
v___x_1514_ = v___x_1511_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_a_1509_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__16_spec__19___redArg___boxed(lean_object* v_name_1517_, lean_object* v_bi_1518_, lean_object* v_type_1519_, lean_object* v_k_1520_, lean_object* v_kind_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
uint8_t v_bi_boxed_1529_; uint8_t v_kind_boxed_1530_; lean_object* v_res_1531_; 
v_bi_boxed_1529_ = lean_unbox(v_bi_1518_);
v_kind_boxed_1530_ = lean_unbox(v_kind_1521_);
v_res_1531_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__16_spec__19___redArg(v_name_1517_, v_bi_boxed_1529_, v_type_1519_, v_k_1520_, v_kind_boxed_1530_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__16___redArg(lean_object* v_name_1532_, lean_object* v_type_1533_, lean_object* v_k_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
uint8_t v___x_1542_; uint8_t v___x_1543_; lean_object* v___x_1544_; 
v___x_1542_ = 0;
v___x_1543_ = 0;
v___x_1544_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__16_spec__19___redArg(v_name_1532_, v___x_1542_, v_type_1533_, v_k_1534_, v___x_1543_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__16___redArg___boxed(lean_object* v_name_1545_, lean_object* v_type_1546_, lean_object* v_k_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__16___redArg(v_name_1545_, v_type_1546_, v_k_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__15_spec__17___redArg(lean_object* v_env_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_){
_start:
{
lean_object* v___x_1560_; lean_object* v_nextMacroScope_1561_; lean_object* v_ngen_1562_; lean_object* v_auxDeclNGen_1563_; lean_object* v_traceState_1564_; lean_object* v_messages_1565_; lean_object* v_infoState_1566_; lean_object* v_snapshotTasks_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1593_; 
v___x_1560_ = lean_st_ref_take(v___y_1558_);
v_nextMacroScope_1561_ = lean_ctor_get(v___x_1560_, 1);
v_ngen_1562_ = lean_ctor_get(v___x_1560_, 2);
v_auxDeclNGen_1563_ = lean_ctor_get(v___x_1560_, 3);
v_traceState_1564_ = lean_ctor_get(v___x_1560_, 4);
v_messages_1565_ = lean_ctor_get(v___x_1560_, 6);
v_infoState_1566_ = lean_ctor_get(v___x_1560_, 7);
v_snapshotTasks_1567_ = lean_ctor_get(v___x_1560_, 8);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1593_ == 0)
{
lean_object* v_unused_1594_; lean_object* v_unused_1595_; 
v_unused_1594_ = lean_ctor_get(v___x_1560_, 5);
lean_dec(v_unused_1594_);
v_unused_1595_ = lean_ctor_get(v___x_1560_, 0);
lean_dec(v_unused_1595_);
v___x_1569_ = v___x_1560_;
v_isShared_1570_ = v_isSharedCheck_1593_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_snapshotTasks_1567_);
lean_inc(v_infoState_1566_);
lean_inc(v_messages_1565_);
lean_inc(v_traceState_1564_);
lean_inc(v_auxDeclNGen_1563_);
lean_inc(v_ngen_1562_);
lean_inc(v_nextMacroScope_1561_);
lean_dec(v___x_1560_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1593_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1571_; lean_object* v___x_1573_; 
v___x_1571_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2);
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 5, v___x_1571_);
lean_ctor_set(v___x_1569_, 0, v_env_1556_);
v___x_1573_ = v___x_1569_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_env_1556_);
lean_ctor_set(v_reuseFailAlloc_1592_, 1, v_nextMacroScope_1561_);
lean_ctor_set(v_reuseFailAlloc_1592_, 2, v_ngen_1562_);
lean_ctor_set(v_reuseFailAlloc_1592_, 3, v_auxDeclNGen_1563_);
lean_ctor_set(v_reuseFailAlloc_1592_, 4, v_traceState_1564_);
lean_ctor_set(v_reuseFailAlloc_1592_, 5, v___x_1571_);
lean_ctor_set(v_reuseFailAlloc_1592_, 6, v_messages_1565_);
lean_ctor_set(v_reuseFailAlloc_1592_, 7, v_infoState_1566_);
lean_ctor_set(v_reuseFailAlloc_1592_, 8, v_snapshotTasks_1567_);
v___x_1573_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v_mctx_1576_; lean_object* v_zetaDeltaFVarIds_1577_; lean_object* v_postponed_1578_; lean_object* v_diag_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1590_; 
v___x_1574_ = lean_st_ref_set(v___y_1558_, v___x_1573_);
v___x_1575_ = lean_st_ref_take(v___y_1557_);
v_mctx_1576_ = lean_ctor_get(v___x_1575_, 0);
v_zetaDeltaFVarIds_1577_ = lean_ctor_get(v___x_1575_, 2);
v_postponed_1578_ = lean_ctor_get(v___x_1575_, 3);
v_diag_1579_ = lean_ctor_get(v___x_1575_, 4);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1590_ == 0)
{
lean_object* v_unused_1591_; 
v_unused_1591_ = lean_ctor_get(v___x_1575_, 1);
lean_dec(v_unused_1591_);
v___x_1581_ = v___x_1575_;
v_isShared_1582_ = v_isSharedCheck_1590_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_diag_1579_);
lean_inc(v_postponed_1578_);
lean_inc(v_zetaDeltaFVarIds_1577_);
lean_inc(v_mctx_1576_);
lean_dec(v___x_1575_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1590_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1583_; lean_object* v___x_1585_; 
v___x_1583_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 1, v___x_1583_);
v___x_1585_ = v___x_1581_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_mctx_1576_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v___x_1583_);
lean_ctor_set(v_reuseFailAlloc_1589_, 2, v_zetaDeltaFVarIds_1577_);
lean_ctor_set(v_reuseFailAlloc_1589_, 3, v_postponed_1578_);
lean_ctor_set(v_reuseFailAlloc_1589_, 4, v_diag_1579_);
v___x_1585_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1586_ = lean_st_ref_set(v___y_1557_, v___x_1585_);
v___x_1587_ = lean_box(0);
v___x_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1587_);
return v___x_1588_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__15_spec__17___redArg___boxed(lean_object* v_env_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__15_spec__17___redArg(v_env_1596_, v___y_1597_, v___y_1598_);
lean_dec(v___y_1598_);
lean_dec(v___y_1597_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__15___redArg(lean_object* v_env_1601_, lean_object* v_x_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v___x_1610_; lean_object* v_env_1611_; lean_object* v_a_1613_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1610_ = lean_st_ref_get(v___y_1608_);
v_env_1611_ = lean_ctor_get(v___x_1610_, 0);
lean_inc_ref(v_env_1611_);
lean_dec(v___x_1610_);
v___x_1623_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__15_spec__17___redArg(v_env_1601_, v___y_1606_, v___y_1608_);
lean_dec_ref(v___x_1623_);
lean_inc(v___y_1608_);
lean_inc_ref(v___y_1607_);
lean_inc(v___y_1606_);
lean_inc_ref(v___y_1605_);
lean_inc(v___y_1604_);
lean_inc_ref(v___y_1603_);
v___x_1624_ = lean_apply_7(v_x_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, lean_box(0));
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; lean_object* v___x_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1633_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_a_1625_);
lean_dec_ref(v___x_1624_);
v___x_1626_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__15_spec__17___redArg(v_env_1611_, v___y_1606_, v___y_1608_);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1633_ == 0)
{
lean_object* v_unused_1634_; 
v_unused_1634_ = lean_ctor_get(v___x_1626_, 0);
lean_dec(v_unused_1634_);
v___x_1628_ = v___x_1626_;
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
else
{
lean_dec(v___x_1626_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1631_; 
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 0, v_a_1625_);
v___x_1631_ = v___x_1628_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_a_1625_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
else
{
lean_object* v_a_1635_; 
v_a_1635_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_a_1635_);
lean_dec_ref(v___x_1624_);
v_a_1613_ = v_a_1635_;
goto v___jp_1612_;
}
v___jp_1612_:
{
lean_object* v___x_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1621_; 
v___x_1614_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__15_spec__17___redArg(v_env_1611_, v___y_1606_, v___y_1608_);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1621_ == 0)
{
lean_object* v_unused_1622_; 
v_unused_1622_ = lean_ctor_get(v___x_1614_, 0);
lean_dec(v_unused_1622_);
v___x_1616_ = v___x_1614_;
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
else
{
lean_dec(v___x_1614_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1619_; 
if (v_isShared_1617_ == 0)
{
lean_ctor_set_tag(v___x_1616_, 1);
lean_ctor_set(v___x_1616_, 0, v_a_1613_);
v___x_1619_ = v___x_1616_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_a_1613_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__15___redArg___boxed(lean_object* v_env_1636_, lean_object* v_x_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__15___redArg(v_env_1636_, v_x_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__14___redArg(lean_object* v_as_1646_, size_t v_i_1647_, size_t v_stop_1648_, lean_object* v_b_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
uint8_t v___x_1653_; 
v___x_1653_ = lean_usize_dec_eq(v_i_1647_, v_stop_1648_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1654_ = lean_array_uget_borrowed(v_as_1646_, v_i_1647_);
v___x_1655_ = l_Lean_Elab_addAsAxiom___redArg(v___x_1654_, v___y_1650_, v___y_1651_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; size_t v___x_1657_; size_t v___x_1658_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
lean_inc(v_a_1656_);
lean_dec_ref(v___x_1655_);
v___x_1657_ = ((size_t)1ULL);
v___x_1658_ = lean_usize_add(v_i_1647_, v___x_1657_);
v_i_1647_ = v___x_1658_;
v_b_1649_ = v_a_1656_;
goto _start;
}
else
{
return v___x_1655_;
}
}
else
{
lean_object* v___x_1660_; 
v___x_1660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1660_, 0, v_b_1649_);
return v___x_1660_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__14___redArg___boxed(lean_object* v_as_1661_, lean_object* v_i_1662_, lean_object* v_stop_1663_, lean_object* v_b_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
size_t v_i_boxed_1668_; size_t v_stop_boxed_1669_; lean_object* v_res_1670_; 
v_i_boxed_1668_ = lean_unbox_usize(v_i_1662_);
lean_dec(v_i_1662_);
v_stop_boxed_1669_ = lean_unbox_usize(v_stop_1663_);
lean_dec(v_stop_1663_);
v_res_1670_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__14___redArg(v_as_1661_, v_i_boxed_1668_, v_stop_boxed_1669_, v_b_1664_, v___y_1665_, v___y_1666_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec_ref(v_as_1661_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__17___redArg___lam__0(lean_object* v___x_1671_, lean_object* v___x_1672_, lean_object* v___x_1673_, lean_object* v_a_1674_, lean_object* v_f_1675_, lean_object* v_a_1676_, lean_object* v_preDefs_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v___y_1686_; uint8_t v___x_1696_; 
v___x_1696_ = lean_nat_dec_lt(v___x_1671_, v___x_1672_);
if (v___x_1696_ == 0)
{
lean_object* v___x_1697_; 
v___x_1697_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps(v___x_1673_, v_a_1674_, v_f_1675_, v_a_1676_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
return v___x_1697_;
}
else
{
lean_object* v___x_1698_; lean_object* v___x_1699_; uint8_t v___x_1700_; 
v___x_1698_ = lean_box(0);
v___x_1699_ = lean_array_get_size(v_preDefs_1677_);
v___x_1700_ = lean_nat_dec_le(v___x_1672_, v___x_1699_);
if (v___x_1700_ == 0)
{
uint8_t v___x_1701_; 
v___x_1701_ = lean_nat_dec_lt(v___x_1671_, v___x_1699_);
if (v___x_1701_ == 0)
{
lean_object* v___x_1702_; 
v___x_1702_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps(v___x_1673_, v_a_1674_, v_f_1675_, v_a_1676_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
return v___x_1702_;
}
else
{
size_t v___x_1703_; size_t v___x_1704_; lean_object* v___x_1705_; 
v___x_1703_ = ((size_t)0ULL);
v___x_1704_ = lean_usize_of_nat(v___x_1699_);
v___x_1705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__14___redArg(v_preDefs_1677_, v___x_1703_, v___x_1704_, v___x_1698_, v___y_1682_, v___y_1683_);
v___y_1686_ = v___x_1705_;
goto v___jp_1685_;
}
}
else
{
size_t v___x_1706_; size_t v___x_1707_; lean_object* v___x_1708_; 
v___x_1706_ = ((size_t)0ULL);
v___x_1707_ = lean_usize_of_nat(v___x_1672_);
v___x_1708_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__14___redArg(v_preDefs_1677_, v___x_1706_, v___x_1707_, v___x_1698_, v___y_1682_, v___y_1683_);
v___y_1686_ = v___x_1708_;
goto v___jp_1685_;
}
}
v___jp_1685_:
{
if (lean_obj_tag(v___y_1686_) == 0)
{
lean_object* v___x_1687_; 
lean_dec_ref(v___y_1686_);
v___x_1687_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps(v___x_1673_, v_a_1674_, v_f_1675_, v_a_1676_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
return v___x_1687_;
}
else
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
lean_dec_ref(v_f_1675_);
lean_dec_ref(v_a_1674_);
lean_dec_ref(v___x_1673_);
v_a_1688_ = lean_ctor_get(v___y_1686_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___y_1686_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1690_ = v___y_1686_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___y_1686_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1688_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__17___redArg___lam__0___boxed(lean_object* v___x_1709_, lean_object* v___x_1710_, lean_object* v___x_1711_, lean_object* v_a_1712_, lean_object* v_f_1713_, lean_object* v_a_1714_, lean_object* v_preDefs_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__17___redArg___lam__0(v___x_1709_, v___x_1710_, v___x_1711_, v_a_1712_, v_f_1713_, v_a_1714_, v_preDefs_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
lean_dec_ref(v_preDefs_1715_);
lean_dec_ref(v_a_1714_);
lean_dec(v___x_1710_);
lean_dec(v___x_1709_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__17___redArg___lam__1(lean_object* v___x_1724_, lean_object* v___x_1725_, lean_object* v___x_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_preDefs_1729_, uint8_t v_isZero_1730_, lean_object* v_f_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v___x_1739_; lean_object* v_env_1740_; lean_object* v___f_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1739_ = lean_st_ref_get(v___y_1737_);
v_env_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc_ref(v_env_1740_);
lean_dec(v___x_1739_);
lean_inc_ref(v_f_1731_);
v___f_1741_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__17___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1741_, 0, v___x_1724_);
lean_closure_set(v___f_1741_, 1, v___x_1725_);
lean_closure_set(v___f_1741_, 2, v___x_1726_);
lean_closure_set(v___f_1741_, 3, v_a_1727_);
lean_closure_set(v___f_1741_, 4, v_f_1731_);
lean_closure_set(v___f_1741_, 5, v_a_1728_);
lean_closure_set(v___f_1741_, 6, v_preDefs_1729_);
v___x_1742_ = l_Lean_Environment_unlockAsync(v_env_1740_);
v___x_1743_ = l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__15___redArg(v___x_1742_, v___f_1741_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v_a_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; uint8_t v___x_1748_; uint8_t v___x_1749_; lean_object* v___x_1750_; 
v_a_1744_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_a_1744_);
lean_dec_ref(v___x_1743_);
v___x_1745_ = lean_unsigned_to_nat(1u);
v___x_1746_ = lean_mk_empty_array_with_capacity(v___x_1745_);
v___x_1747_ = lean_array_push(v___x_1746_, v_f_1731_);
v___x_1748_ = 1;
v___x_1749_ = 1;
v___x_1750_ = l_Lean_Meta_mkLambdaFVars(v___x_1747_, v_a_1744_, v_isZero_1730_, v___x_1748_, v_isZero_1730_, v___x_1748_, v___x_1749_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
lean_dec_ref(v___x_1747_);
return v___x_1750_;
}
else
{
lean_dec_ref(v_f_1731_);
return v___x_1743_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__17___redArg___lam__1___boxed(lean_object* v___x_1751_, lean_object* v___x_1752_, lean_object* v___x_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_preDefs_1756_, lean_object* v_isZero_1757_, lean_object* v_f_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
uint8_t v_isZero_boxed_1766_; lean_object* v_res_1767_; 
v_isZero_boxed_1766_ = lean_unbox(v_isZero_1757_);
v_res_1767_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__17___redArg___lam__1(v___x_1751_, v___x_1752_, v___x_1753_, v_a_1754_, v_a_1755_, v_preDefs_1756_, v_isZero_boxed_1766_, v_f_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__17___redArg(lean_object* v___x_1771_, lean_object* v_fixedArgs_1772_, lean_object* v___x_1773_, lean_object* v_a_1774_, lean_object* v___x_1775_, lean_object* v_preDefs_1776_, lean_object* v_a_1777_, lean_object* v_as_1778_, lean_object* v_i_1779_, lean_object* v_j_1780_, lean_object* v_bs_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v_zero_1789_; uint8_t v_isZero_1790_; 
v_zero_1789_ = lean_unsigned_to_nat(0u);
v_isZero_1790_ = lean_nat_dec_eq(v_i_1779_, v_zero_1789_);
if (v_isZero_1790_ == 1)
{
lean_object* v___x_1791_; 
lean_dec(v_j_1780_);
lean_dec(v_i_1779_);
lean_dec_ref(v_a_1777_);
lean_dec_ref(v_preDefs_1776_);
lean_dec(v___x_1775_);
lean_dec_ref(v_a_1774_);
lean_dec_ref(v___x_1773_);
lean_dec_ref(v_fixedArgs_1772_);
v___x_1791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1791_, 0, v_bs_1781_);
return v___x_1791_;
}
else
{
lean_object* v___x_1792_; lean_object* v_value_1793_; lean_object* v___x_1794_; lean_object* v_one_1795_; lean_object* v_n_1796_; lean_object* v___y_1798_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1792_ = lean_array_fget_borrowed(v_as_1778_, v_j_1780_);
v_value_1793_ = lean_ctor_get(v___x_1792_, 7);
v___x_1794_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1);
v_one_1795_ = lean_unsigned_to_nat(1u);
v_n_1796_ = lean_nat_sub(v_i_1779_, v_one_1795_);
lean_dec(v_i_1779_);
v___x_1811_ = lean_array_get_borrowed(v___x_1794_, v___x_1771_, v_j_1780_);
lean_inc_ref(v_fixedArgs_1772_);
lean_inc_ref(v_value_1793_);
lean_inc(v___x_1811_);
v___x_1812_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_1811_, v_value_1793_, v_fixedArgs_1772_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_a_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_a_1813_);
lean_dec_ref(v___x_1812_);
v___x_1814_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__17___redArg___closed__1));
v___x_1815_ = l_Lean_Core_mkFreshUserName(v___x_1814_, v___y_1786_, v___y_1787_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_a_1816_; lean_object* v___x_1817_; lean_object* v___f_1818_; lean_object* v___x_1819_; 
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
lean_inc(v_a_1816_);
lean_dec_ref(v___x_1815_);
v___x_1817_ = lean_box(v_isZero_1790_);
lean_inc_ref(v_preDefs_1776_);
lean_inc_ref(v_a_1774_);
lean_inc_ref(v___x_1773_);
lean_inc(v___x_1775_);
v___f_1818_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__17___redArg___lam__1___boxed), 15, 7);
lean_closure_set(v___f_1818_, 0, v_zero_1789_);
lean_closure_set(v___f_1818_, 1, v___x_1775_);
lean_closure_set(v___f_1818_, 2, v___x_1773_);
lean_closure_set(v___f_1818_, 3, v_a_1774_);
lean_closure_set(v___f_1818_, 4, v_a_1813_);
lean_closure_set(v___f_1818_, 5, v_preDefs_1776_);
lean_closure_set(v___f_1818_, 6, v___x_1817_);
lean_inc_ref(v_a_1777_);
v___x_1819_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__16___redArg(v_a_1816_, v_a_1777_, v___f_1818_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
v___y_1798_ = v___x_1819_;
goto v___jp_1797_;
}
else
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1827_; 
lean_dec(v_a_1813_);
lean_dec(v_n_1796_);
lean_dec_ref(v_bs_1781_);
lean_dec(v_j_1780_);
lean_dec_ref(v_a_1777_);
lean_dec_ref(v_preDefs_1776_);
lean_dec(v___x_1775_);
lean_dec_ref(v_a_1774_);
lean_dec_ref(v___x_1773_);
lean_dec_ref(v_fixedArgs_1772_);
v_a_1820_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1822_ = v___x_1815_;
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1815_);
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
else
{
v___y_1798_ = v___x_1812_;
goto v___jp_1797_;
}
v___jp_1797_:
{
if (lean_obj_tag(v___y_1798_) == 0)
{
lean_object* v_a_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v_a_1799_ = lean_ctor_get(v___y_1798_, 0);
lean_inc(v_a_1799_);
lean_dec_ref(v___y_1798_);
v___x_1800_ = lean_nat_add(v_j_1780_, v_one_1795_);
lean_dec(v_j_1780_);
v___x_1801_ = lean_array_push(v_bs_1781_, v_a_1799_);
v_i_1779_ = v_n_1796_;
v_j_1780_ = v___x_1800_;
v_bs_1781_ = v___x_1801_;
goto _start;
}
else
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1810_; 
lean_dec(v_n_1796_);
lean_dec_ref(v_bs_1781_);
lean_dec(v_j_1780_);
lean_dec_ref(v_a_1777_);
lean_dec_ref(v_preDefs_1776_);
lean_dec(v___x_1775_);
lean_dec_ref(v_a_1774_);
lean_dec_ref(v___x_1773_);
lean_dec_ref(v_fixedArgs_1772_);
v_a_1803_ = lean_ctor_get(v___y_1798_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___y_1798_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1805_ = v___y_1798_;
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___y_1798_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1808_; 
if (v_isShared_1806_ == 0)
{
v___x_1808_ = v___x_1805_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_a_1803_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__17___redArg___boxed(lean_object** _args){
lean_object* v___x_1828_ = _args[0];
lean_object* v_fixedArgs_1829_ = _args[1];
lean_object* v___x_1830_ = _args[2];
lean_object* v_a_1831_ = _args[3];
lean_object* v___x_1832_ = _args[4];
lean_object* v_preDefs_1833_ = _args[5];
lean_object* v_a_1834_ = _args[6];
lean_object* v_as_1835_ = _args[7];
lean_object* v_i_1836_ = _args[8];
lean_object* v_j_1837_ = _args[9];
lean_object* v_bs_1838_ = _args[10];
lean_object* v___y_1839_ = _args[11];
lean_object* v___y_1840_ = _args[12];
lean_object* v___y_1841_ = _args[13];
lean_object* v___y_1842_ = _args[14];
lean_object* v___y_1843_ = _args[15];
lean_object* v___y_1844_ = _args[16];
lean_object* v___y_1845_ = _args[17];
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__17___redArg(v___x_1828_, v_fixedArgs_1829_, v___x_1830_, v_a_1831_, v___x_1832_, v_preDefs_1833_, v_a_1834_, v_as_1835_, v_i_1836_, v_j_1837_, v_bs_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec_ref(v_as_1835_);
lean_dec_ref(v___x_1828_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__17(lean_object* v___x_1847_, lean_object* v_fixedArgs_1848_, lean_object* v___x_1849_, lean_object* v_a_1850_, lean_object* v___x_1851_, lean_object* v_preDefs_1852_, lean_object* v_a_1853_, lean_object* v_as_1854_, lean_object* v_i_1855_, lean_object* v_j_1856_, lean_object* v_inv_1857_, lean_object* v_bs_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__17___redArg(v___x_1847_, v_fixedArgs_1848_, v___x_1849_, v_a_1850_, v___x_1851_, v_preDefs_1852_, v_a_1853_, v_as_1854_, v_i_1855_, v_j_1856_, v_bs_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__17___boxed(lean_object** _args){
lean_object* v___x_1867_ = _args[0];
lean_object* v_fixedArgs_1868_ = _args[1];
lean_object* v___x_1869_ = _args[2];
lean_object* v_a_1870_ = _args[3];
lean_object* v___x_1871_ = _args[4];
lean_object* v_preDefs_1872_ = _args[5];
lean_object* v_a_1873_ = _args[6];
lean_object* v_as_1874_ = _args[7];
lean_object* v_i_1875_ = _args[8];
lean_object* v_j_1876_ = _args[9];
lean_object* v_inv_1877_ = _args[10];
lean_object* v_bs_1878_ = _args[11];
lean_object* v___y_1879_ = _args[12];
lean_object* v___y_1880_ = _args[13];
lean_object* v___y_1881_ = _args[14];
lean_object* v___y_1882_ = _args[15];
lean_object* v___y_1883_ = _args[16];
lean_object* v___y_1884_ = _args[17];
lean_object* v___y_1885_ = _args[18];
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__17(v___x_1867_, v_fixedArgs_1868_, v___x_1869_, v_a_1870_, v___x_1871_, v_preDefs_1872_, v_a_1873_, v_as_1874_, v_i_1875_, v_j_1876_, v_inv_1877_, v_bs_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec_ref(v_as_1874_);
lean_dec_ref(v___x_1867_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__3(lean_object* v___f_1887_, lean_object* v___x_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l_Lean_Meta_Monotonicity_solveMono(v___f_1887_, v___x_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__3___boxed(lean_object* v___f_1895_, lean_object* v___x_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__3(v___f_1895_, v___x_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
return v_res_1902_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1903_; double v___x_1904_; 
v___x_1903_ = lean_unsigned_to_nat(0u);
v___x_1904_ = lean_float_of_nat(v___x_1903_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__3___redArg(lean_object* v_cls_1908_, lean_object* v_msg_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v_ref_1915_; lean_object* v___x_1916_; lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1961_; 
v_ref_1915_ = lean_ctor_get(v___y_1912_, 5);
v___x_1916_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6_spec__7(v_msg_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1919_ = v___x_1916_;
v_isShared_1920_ = v_isSharedCheck_1961_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1916_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1961_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1921_; lean_object* v_traceState_1922_; lean_object* v_env_1923_; lean_object* v_nextMacroScope_1924_; lean_object* v_ngen_1925_; lean_object* v_auxDeclNGen_1926_; lean_object* v_cache_1927_; lean_object* v_messages_1928_; lean_object* v_infoState_1929_; lean_object* v_snapshotTasks_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1960_; 
v___x_1921_ = lean_st_ref_take(v___y_1913_);
v_traceState_1922_ = lean_ctor_get(v___x_1921_, 4);
v_env_1923_ = lean_ctor_get(v___x_1921_, 0);
v_nextMacroScope_1924_ = lean_ctor_get(v___x_1921_, 1);
v_ngen_1925_ = lean_ctor_get(v___x_1921_, 2);
v_auxDeclNGen_1926_ = lean_ctor_get(v___x_1921_, 3);
v_cache_1927_ = lean_ctor_get(v___x_1921_, 5);
v_messages_1928_ = lean_ctor_get(v___x_1921_, 6);
v_infoState_1929_ = lean_ctor_get(v___x_1921_, 7);
v_snapshotTasks_1930_ = lean_ctor_get(v___x_1921_, 8);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1932_ = v___x_1921_;
v_isShared_1933_ = v_isSharedCheck_1960_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_snapshotTasks_1930_);
lean_inc(v_infoState_1929_);
lean_inc(v_messages_1928_);
lean_inc(v_cache_1927_);
lean_inc(v_traceState_1922_);
lean_inc(v_auxDeclNGen_1926_);
lean_inc(v_ngen_1925_);
lean_inc(v_nextMacroScope_1924_);
lean_inc(v_env_1923_);
lean_dec(v___x_1921_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1960_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
uint64_t v_tid_1934_; lean_object* v_traces_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1959_; 
v_tid_1934_ = lean_ctor_get_uint64(v_traceState_1922_, sizeof(void*)*1);
v_traces_1935_ = lean_ctor_get(v_traceState_1922_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v_traceState_1922_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1937_ = v_traceState_1922_;
v_isShared_1938_ = v_isSharedCheck_1959_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_traces_1935_);
lean_dec(v_traceState_1922_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1959_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1939_; double v___x_1940_; uint8_t v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1949_; 
v___x_1939_ = lean_box(0);
v___x_1940_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__3___redArg___closed__0);
v___x_1941_ = 0;
v___x_1942_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__3___redArg___closed__1));
v___x_1943_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1943_, 0, v_cls_1908_);
lean_ctor_set(v___x_1943_, 1, v___x_1939_);
lean_ctor_set(v___x_1943_, 2, v___x_1942_);
lean_ctor_set_float(v___x_1943_, sizeof(void*)*3, v___x_1940_);
lean_ctor_set_float(v___x_1943_, sizeof(void*)*3 + 8, v___x_1940_);
lean_ctor_set_uint8(v___x_1943_, sizeof(void*)*3 + 16, v___x_1941_);
v___x_1944_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__3___redArg___closed__2));
v___x_1945_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1943_);
lean_ctor_set(v___x_1945_, 1, v_a_1917_);
lean_ctor_set(v___x_1945_, 2, v___x_1944_);
lean_inc(v_ref_1915_);
v___x_1946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1946_, 0, v_ref_1915_);
lean_ctor_set(v___x_1946_, 1, v___x_1945_);
v___x_1947_ = l_Lean_PersistentArray_push___redArg(v_traces_1935_, v___x_1946_);
if (v_isShared_1938_ == 0)
{
lean_ctor_set(v___x_1937_, 0, v___x_1947_);
v___x_1949_ = v___x_1937_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1947_);
lean_ctor_set_uint64(v_reuseFailAlloc_1958_, sizeof(void*)*1, v_tid_1934_);
v___x_1949_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
lean_object* v___x_1951_; 
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 4, v___x_1949_);
v___x_1951_ = v___x_1932_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_env_1923_);
lean_ctor_set(v_reuseFailAlloc_1957_, 1, v_nextMacroScope_1924_);
lean_ctor_set(v_reuseFailAlloc_1957_, 2, v_ngen_1925_);
lean_ctor_set(v_reuseFailAlloc_1957_, 3, v_auxDeclNGen_1926_);
lean_ctor_set(v_reuseFailAlloc_1957_, 4, v___x_1949_);
lean_ctor_set(v_reuseFailAlloc_1957_, 5, v_cache_1927_);
lean_ctor_set(v_reuseFailAlloc_1957_, 6, v_messages_1928_);
lean_ctor_set(v_reuseFailAlloc_1957_, 7, v_infoState_1929_);
lean_ctor_set(v_reuseFailAlloc_1957_, 8, v_snapshotTasks_1930_);
v___x_1951_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1955_; 
v___x_1952_ = lean_st_ref_set(v___y_1913_, v___x_1951_);
v___x_1953_ = lean_box(0);
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 0, v___x_1953_);
v___x_1955_ = v___x_1919_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v___x_1953_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__3___redArg___boxed(lean_object* v_cls_1962_, lean_object* v_msg_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__3___redArg(v_cls_1962_, v_msg_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__2(lean_object* v___x_1970_, lean_object* v_e_1971_){
_start:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1972_ = l_Lean_indentD(v_e_1971_);
v___x_1973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1970_);
lean_ctor_set(v___x_1973_, 1, v___x_1972_);
return v___x_1973_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__10___closed__1(void){
_start:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1975_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__10___closed__0));
v___x_1976_ = l_Lean_stringToMessageData(v___x_1975_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__10(lean_object* v_a_1977_, lean_object* v_a_1978_){
_start:
{
if (lean_obj_tag(v_a_1977_) == 0)
{
lean_object* v___x_1979_; 
v___x_1979_ = l_List_reverse___redArg(v_a_1978_);
return v___x_1979_;
}
else
{
lean_object* v_head_1980_; lean_object* v_tail_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1994_; 
v_head_1980_ = lean_ctor_get(v_a_1977_, 0);
v_tail_1981_ = lean_ctor_get(v_a_1977_, 1);
v_isSharedCheck_1994_ = !lean_is_exclusive(v_a_1977_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1983_ = v_a_1977_;
v_isShared_1984_ = v_isSharedCheck_1994_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_tail_1981_);
lean_inc(v_head_1980_);
lean_dec(v_a_1977_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1994_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1985_; uint8_t v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1991_; 
v___x_1985_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__10___closed__1, &l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__10___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__10___closed__1);
v___x_1986_ = 0;
v___x_1987_ = l_Lean_MessageData_ofConstName(v_head_1980_, v___x_1986_);
v___x_1988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1985_);
lean_ctor_set(v___x_1988_, 1, v___x_1987_);
v___x_1989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1988_);
lean_ctor_set(v___x_1989_, 1, v___x_1985_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 1, v_a_1978_);
lean_ctor_set(v___x_1983_, 0, v___x_1989_);
v___x_1991_ = v___x_1983_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1989_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v_a_1978_);
v___x_1991_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
v_a_1977_ = v_tail_1981_;
v_a_1978_ = v___x_1991_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__1));
v___x_1998_ = l_Lean_stringToMessageData(v___x_1997_);
return v___x_1998_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_2000_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__3));
v___x_2001_ = l_Lean_stringToMessageData(v___x_2000_);
return v___x_2001_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__6(void){
_start:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2003_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__5));
v___x_2004_ = l_Lean_stringToMessageData(v___x_2003_);
return v___x_2004_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__9(void){
_start:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2007_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__8));
v___x_2008_ = lean_unsigned_to_nat(52u);
v___x_2009_ = lean_unsigned_to_nat(148u);
v___x_2010_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__7));
v___x_2011_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__0));
v___x_2012_ = l_mkPanicMessageWithDecl(v___x_2011_, v___x_2010_, v___x_2009_, v___x_2008_, v___x_2007_);
return v___x_2012_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__11(void){
_start:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2014_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__10));
v___x_2015_ = l_Lean_stringToMessageData(v___x_2014_);
return v___x_2015_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__13(void){
_start:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2017_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__12));
v___x_2018_ = l_Lean_stringToMessageData(v___x_2017_);
return v___x_2018_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__15(void){
_start:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__14));
v___x_2021_ = l_Lean_stringToMessageData(v___x_2020_);
return v___x_2021_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__19(void){
_start:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2028_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__18));
v___x_2029_ = l_Lean_stringToMessageData(v___x_2028_);
return v___x_2029_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__20(void){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__3___redArg___closed__1));
v___x_2031_ = l_Lean_stringToMessageData(v___x_2030_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0(lean_object* v_monoThms_2032_, lean_object* v_t_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_){
_start:
{
lean_object* v___y_2040_; lean_object* v___x_2084_; lean_object* v___x_2085_; uint8_t v___x_2086_; 
v___x_2084_ = lean_array_get_size(v_monoThms_2032_);
v___x_2085_ = lean_unsigned_to_nat(0u);
v___x_2086_ = lean_nat_dec_eq(v___x_2084_, v___x_2085_);
if (v___x_2086_ == 0)
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2087_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__13, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__13_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__13);
v___x_2088_ = lean_array_to_list(v_monoThms_2032_);
v___x_2089_ = lean_box(0);
v___x_2090_ = l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__10(v___x_2088_, v___x_2089_);
v___x_2091_ = l_Lean_MessageData_andList(v___x_2090_);
v___x_2092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2087_);
lean_ctor_set(v___x_2092_, 1, v___x_2091_);
v___x_2093_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__15, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__15_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__15);
v___x_2094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2092_);
lean_ctor_set(v___x_2094_, 1, v___x_2093_);
v___x_2095_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__17));
v___x_2096_ = l_Lean_MessageData_ofConstName(v___x_2095_, v___x_2086_);
v___x_2097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2094_);
lean_ctor_set(v___x_2097_, 1, v___x_2096_);
v___x_2098_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__19, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__19_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__19);
v___x_2099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2097_);
lean_ctor_set(v___x_2099_, 1, v___x_2098_);
v___y_2040_ = v___x_2099_;
goto v___jp_2039_;
}
else
{
lean_object* v___x_2100_; 
lean_dec_ref(v_monoThms_2032_);
v___x_2100_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__20, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__20_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__20);
v___y_2040_ = v___x_2100_;
goto v___jp_2039_;
}
v___jp_2039_:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2041_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__0));
v___x_2042_ = lean_find_expr(v___x_2041_, v_t_2033_);
if (lean_obj_tag(v___x_2042_) == 1)
{
lean_object* v_val_2043_; lean_object* v___x_2044_; 
v_val_2043_ = lean_ctor_get(v___x_2042_, 0);
lean_inc(v_val_2043_);
lean_dec_ref(v___x_2042_);
v___x_2044_ = l_Lean_getRecAppSyntax_x3f(v_val_2043_);
lean_dec(v_val_2043_);
if (lean_obj_tag(v___x_2044_) == 1)
{
lean_object* v_val_2045_; lean_object* v_fileName_2046_; lean_object* v_fileMap_2047_; lean_object* v_options_2048_; lean_object* v_currRecDepth_2049_; lean_object* v_maxRecDepth_2050_; lean_object* v_ref_2051_; lean_object* v_currNamespace_2052_; lean_object* v_openDecls_2053_; lean_object* v_initHeartbeats_2054_; lean_object* v_maxHeartbeats_2055_; lean_object* v_quotContext_2056_; lean_object* v_currMacroScope_2057_; uint8_t v_diag_2058_; lean_object* v_cancelTk_x3f_2059_; uint8_t v_suppressElabErrors_2060_; lean_object* v_inheritedTraceOptions_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v_ref_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v_val_2045_ = lean_ctor_get(v___x_2044_, 0);
lean_inc(v_val_2045_);
lean_dec_ref(v___x_2044_);
v_fileName_2046_ = lean_ctor_get(v___y_2036_, 0);
v_fileMap_2047_ = lean_ctor_get(v___y_2036_, 1);
v_options_2048_ = lean_ctor_get(v___y_2036_, 2);
v_currRecDepth_2049_ = lean_ctor_get(v___y_2036_, 3);
v_maxRecDepth_2050_ = lean_ctor_get(v___y_2036_, 4);
v_ref_2051_ = lean_ctor_get(v___y_2036_, 5);
v_currNamespace_2052_ = lean_ctor_get(v___y_2036_, 6);
v_openDecls_2053_ = lean_ctor_get(v___y_2036_, 7);
v_initHeartbeats_2054_ = lean_ctor_get(v___y_2036_, 8);
v_maxHeartbeats_2055_ = lean_ctor_get(v___y_2036_, 9);
v_quotContext_2056_ = lean_ctor_get(v___y_2036_, 10);
v_currMacroScope_2057_ = lean_ctor_get(v___y_2036_, 11);
v_diag_2058_ = lean_ctor_get_uint8(v___y_2036_, sizeof(void*)*14);
v_cancelTk_x3f_2059_ = lean_ctor_get(v___y_2036_, 12);
v_suppressElabErrors_2060_ = lean_ctor_get_uint8(v___y_2036_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2061_ = lean_ctor_get(v___y_2036_, 13);
v___x_2062_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__2, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__2_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__2);
lean_inc(v_val_2045_);
v___x_2063_ = l_Lean_MessageData_ofSyntax(v_val_2045_);
v___x_2064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2062_);
lean_ctor_set(v___x_2064_, 1, v___x_2063_);
v___x_2065_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__4, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__4_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__4);
v___x_2066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2064_);
lean_ctor_set(v___x_2066_, 1, v___x_2065_);
v___x_2067_ = l_Lean_indentExpr(v_t_2033_);
v___x_2068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2066_);
lean_ctor_set(v___x_2068_, 1, v___x_2067_);
v___x_2069_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__6, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__6_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__6);
v___x_2070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2068_);
lean_ctor_set(v___x_2070_, 1, v___x_2069_);
v___x_2071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
lean_ctor_set(v___x_2071_, 1, v___y_2040_);
v_ref_2072_ = l_Lean_replaceRef(v_val_2045_, v_ref_2051_);
lean_dec(v_val_2045_);
lean_inc_ref(v_inheritedTraceOptions_2061_);
lean_inc(v_cancelTk_x3f_2059_);
lean_inc(v_currMacroScope_2057_);
lean_inc(v_quotContext_2056_);
lean_inc(v_maxHeartbeats_2055_);
lean_inc(v_initHeartbeats_2054_);
lean_inc(v_openDecls_2053_);
lean_inc(v_currNamespace_2052_);
lean_inc(v_maxRecDepth_2050_);
lean_inc(v_currRecDepth_2049_);
lean_inc_ref(v_options_2048_);
lean_inc_ref(v_fileMap_2047_);
lean_inc_ref(v_fileName_2046_);
v___x_2073_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2073_, 0, v_fileName_2046_);
lean_ctor_set(v___x_2073_, 1, v_fileMap_2047_);
lean_ctor_set(v___x_2073_, 2, v_options_2048_);
lean_ctor_set(v___x_2073_, 3, v_currRecDepth_2049_);
lean_ctor_set(v___x_2073_, 4, v_maxRecDepth_2050_);
lean_ctor_set(v___x_2073_, 5, v_ref_2072_);
lean_ctor_set(v___x_2073_, 6, v_currNamespace_2052_);
lean_ctor_set(v___x_2073_, 7, v_openDecls_2053_);
lean_ctor_set(v___x_2073_, 8, v_initHeartbeats_2054_);
lean_ctor_set(v___x_2073_, 9, v_maxHeartbeats_2055_);
lean_ctor_set(v___x_2073_, 10, v_quotContext_2056_);
lean_ctor_set(v___x_2073_, 11, v_currMacroScope_2057_);
lean_ctor_set(v___x_2073_, 12, v_cancelTk_x3f_2059_);
lean_ctor_set(v___x_2073_, 13, v_inheritedTraceOptions_2061_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*14, v_diag_2058_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*14 + 1, v_suppressElabErrors_2060_);
v___x_2074_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg(v___x_2071_, v___y_2034_, v___y_2035_, v___x_2073_, v___y_2037_);
lean_dec_ref(v___x_2073_);
return v___x_2074_;
}
else
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
lean_dec(v___x_2044_);
lean_dec_ref(v___y_2040_);
lean_dec_ref(v_t_2033_);
v___x_2075_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__9, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__9_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__9);
v___x_2076_ = l_panic___at___00Lean_Elab_partialFixpoint_spec__9___redArg(v___x_2075_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
return v___x_2076_;
}
}
else
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
lean_dec(v___x_2042_);
v___x_2077_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__11, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__11_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__11);
v___x_2078_ = l_Lean_indentExpr(v_t_2033_);
v___x_2079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2077_);
lean_ctor_set(v___x_2079_, 1, v___x_2078_);
v___x_2080_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__6, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__6_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__6);
v___x_2081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2079_);
lean_ctor_set(v___x_2081_, 1, v___x_2080_);
v___x_2082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
lean_ctor_set(v___x_2082_, 1, v___y_2040_);
v___x_2083_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg(v___x_2082_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
return v___x_2083_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___boxed(lean_object* v_monoThms_2101_, lean_object* v_t_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
lean_object* v_res_2108_; 
v_res_2108_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0(v_monoThms_2101_, v_t_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__1(lean_object* v_preDefs_2109_, lean_object* v_a_2110_, lean_object* v_fixedArgs_2111_, lean_object* v_00_u03b1_2112_, lean_object* v_f_2113_, lean_object* v_monoThms_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
lean_object* v___f_2120_; lean_object* v___x_2121_; 
v___f_2120_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2120_, 0, v_monoThms_2114_);
v___x_2121_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg(v_preDefs_2109_, v_a_2110_, v_fixedArgs_2111_, v_f_2113_, v___f_2120_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__1___boxed(lean_object* v_preDefs_2122_, lean_object* v_a_2123_, lean_object* v_fixedArgs_2124_, lean_object* v_00_u03b1_2125_, lean_object* v_f_2126_, lean_object* v_monoThms_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__1(v_preDefs_2122_, v_a_2123_, v_fixedArgs_2124_, v_00_u03b1_2125_, v_f_2126_, v_monoThms_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
return v_res_2133_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__1(void){
_start:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2135_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__0));
v___x_2136_ = l_Lean_stringToMessageData(v___x_2135_);
return v___x_2136_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__3(void){
_start:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2138_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__2));
v___x_2139_ = l_Lean_stringToMessageData(v___x_2138_);
return v___x_2139_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__9(void){
_start:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2148_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__8));
v___x_2149_ = l_Lean_stringToMessageData(v___x_2148_);
return v___x_2149_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__11(void){
_start:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2151_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__10));
v___x_2152_ = l_Lean_stringToMessageData(v___x_2151_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg(lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_hints_2158_, lean_object* v_preDefs_2159_, lean_object* v_a_2160_, lean_object* v_fixedArgs_2161_, lean_object* v_as_2162_, lean_object* v_i_2163_, lean_object* v_j_2164_, lean_object* v_bs_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
lean_object* v_zero_2173_; uint8_t v_isZero_2174_; 
v_zero_2173_ = lean_unsigned_to_nat(0u);
v_isZero_2174_ = lean_nat_dec_eq(v_i_2163_, v_zero_2173_);
if (v_isZero_2174_ == 1)
{
lean_object* v___x_2175_; 
lean_dec(v_j_2164_);
lean_dec(v_i_2163_);
lean_dec_ref(v_fixedArgs_2161_);
lean_dec_ref(v_a_2160_);
lean_dec_ref(v_preDefs_2159_);
lean_dec_ref(v_a_2157_);
lean_dec_ref(v_a_2156_);
v___x_2175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2175_, 0, v_bs_2165_);
return v___x_2175_;
}
else
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2176_ = l_Lean_instInhabitedExpr;
v___x_2177_ = lean_array_get_borrowed(v___x_2176_, v_a_2153_, v_j_2164_);
v___x_2178_ = lean_array_get_borrowed(v___x_2176_, v_a_2154_, v_j_2164_);
v___x_2179_ = lean_array_get_borrowed(v___x_2176_, v_a_2155_, v_j_2164_);
lean_inc(v___x_2177_);
v___x_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2177_);
lean_inc_ref(v___x_2180_);
lean_inc(v___x_2179_);
v___x_2181_ = l_Lean_Meta_toPartialOrder(v___x_2179_, v___x_2180_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_a_2182_);
lean_dec_ref(v___x_2181_);
v___x_2183_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__5));
lean_inc_ref(v_a_2156_);
v___x_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2184_, 0, v_a_2156_);
lean_inc_ref(v_a_2157_);
v___x_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2185_, 0, v_a_2157_);
v___x_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2186_, 0, v_a_2182_);
lean_inc(v___x_2178_);
v___x_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2178_);
v___x_2188_ = lean_unsigned_to_nat(5u);
v___x_2189_ = lean_mk_empty_array_with_capacity(v___x_2188_);
v___x_2190_ = lean_array_push(v___x_2189_, v___x_2184_);
v___x_2191_ = lean_array_push(v___x_2190_, v___x_2185_);
v___x_2192_ = lean_array_push(v___x_2191_, v___x_2180_);
v___x_2193_ = lean_array_push(v___x_2192_, v___x_2186_);
v___x_2194_ = lean_array_push(v___x_2193_, v___x_2187_);
v___x_2195_ = l_Lean_Meta_mkAppOptM(v___x_2183_, v___x_2194_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v_term_x3f_2199_; lean_object* v_one_2200_; lean_object* v_n_2201_; lean_object* v_a_2203_; 
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_a_2196_);
lean_dec_ref(v___x_2195_);
v___x_2197_ = l_Lean_Elab_instInhabitedPartialFixpoint_default;
v___x_2198_ = lean_array_get_borrowed(v___x_2197_, v_hints_2158_, v_j_2164_);
v_term_x3f_2199_ = lean_ctor_get(v___x_2198_, 1);
lean_inc(v_term_x3f_2199_);
v_one_2200_ = lean_unsigned_to_nat(1u);
v_n_2201_ = lean_nat_sub(v_i_2163_, v_one_2200_);
lean_dec(v_i_2163_);
if (lean_obj_tag(v_term_x3f_2199_) == 1)
{
lean_object* v_val_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2265_; 
v_val_2207_ = lean_ctor_get(v_term_x3f_2199_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v_term_x3f_2199_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2209_ = v_term_x3f_2199_;
v_isShared_2210_ = v_isSharedCheck_2265_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_val_2207_);
lean_dec(v_term_x3f_2199_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2265_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
uint8_t v___x_2211_; lean_object* v___x_2213_; 
v___x_2211_ = 1;
lean_inc(v_a_2196_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 0, v_a_2196_);
v___x_2213_ = v___x_2209_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_a_2196_);
v___x_2213_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; uint8_t v___x_2218_; lean_object* v___x_2219_; 
v___x_2214_ = lean_box(0);
v___x_2215_ = lean_box(v___x_2211_);
v___x_2216_ = lean_box(v___x_2211_);
v___x_2217_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_2217_, 0, v_val_2207_);
lean_closure_set(v___x_2217_, 1, v___x_2213_);
lean_closure_set(v___x_2217_, 2, v___x_2215_);
lean_closure_set(v___x_2217_, 3, v___x_2216_);
lean_closure_set(v___x_2217_, 4, v___x_2214_);
v___x_2218_ = 1;
v___x_2219_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_2217_, v___x_2218_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_object* v_a_2220_; lean_object* v___x_2221_; lean_object* v_a_2222_; lean_object* v___x_2223_; 
v_a_2220_ = lean_ctor_get(v___x_2219_, 0);
lean_inc(v_a_2220_);
lean_dec_ref(v___x_2219_);
v___x_2221_ = l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__19___redArg(v_a_2220_, v___y_2169_);
v_a_2222_ = lean_ctor_get(v___x_2221_, 0);
lean_inc(v_a_2222_);
lean_dec_ref(v___x_2221_);
lean_inc(v_a_2222_);
v___x_2223_ = l_Lean_Meta_getMVars(v_a_2222_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_object* v_a_2224_; lean_object* v___x_2225_; uint8_t v___x_2226_; 
v_a_2224_ = lean_ctor_get(v___x_2223_, 0);
lean_inc(v_a_2224_);
lean_dec_ref(v___x_2223_);
v___x_2225_ = lean_array_get_size(v_a_2224_);
v___x_2226_ = lean_nat_dec_eq(v___x_2225_, v_zero_2173_);
if (v___x_2226_ == 0)
{
lean_object* v___x_2227_; 
lean_dec(v_a_2222_);
v___x_2227_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_2224_, v___x_2214_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
lean_dec(v_a_2224_);
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v___x_2228_; 
lean_dec_ref(v___x_2227_);
lean_inc(v_a_2196_);
v___x_2228_ = l_Lean_Meta_mkSorry(v_a_2196_, v___x_2211_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v_a_2229_; lean_object* v___x_2230_; 
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
lean_inc(v_a_2229_);
lean_dec_ref(v___x_2228_);
v___x_2230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2230_, 0, v_a_2196_);
lean_ctor_set(v___x_2230_, 1, v_a_2229_);
v_a_2203_ = v___x_2230_;
goto v___jp_2202_;
}
else
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2238_; 
lean_dec(v_n_2201_);
lean_dec(v_a_2196_);
lean_dec_ref(v_bs_2165_);
lean_dec(v_j_2164_);
lean_dec_ref(v_fixedArgs_2161_);
lean_dec_ref(v_a_2160_);
lean_dec_ref(v_preDefs_2159_);
lean_dec_ref(v_a_2157_);
lean_dec_ref(v_a_2156_);
v_a_2231_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2233_ = v___x_2228_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2228_);
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
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
lean_dec(v_n_2201_);
lean_dec(v_a_2196_);
lean_dec_ref(v_bs_2165_);
lean_dec(v_j_2164_);
lean_dec_ref(v_fixedArgs_2161_);
lean_dec_ref(v_a_2160_);
lean_dec_ref(v_preDefs_2159_);
lean_dec_ref(v_a_2157_);
lean_dec_ref(v_a_2156_);
v_a_2239_ = lean_ctor_get(v___x_2227_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2227_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2227_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2239_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
}
else
{
lean_object* v___x_2247_; 
lean_dec(v_a_2224_);
v___x_2247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2247_, 0, v_a_2196_);
lean_ctor_set(v___x_2247_, 1, v_a_2222_);
v_a_2203_ = v___x_2247_;
goto v___jp_2202_;
}
}
else
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2255_; 
lean_dec(v_a_2222_);
lean_dec(v_n_2201_);
lean_dec(v_a_2196_);
lean_dec_ref(v_bs_2165_);
lean_dec(v_j_2164_);
lean_dec_ref(v_fixedArgs_2161_);
lean_dec_ref(v_a_2160_);
lean_dec_ref(v_preDefs_2159_);
lean_dec_ref(v_a_2157_);
lean_dec_ref(v_a_2156_);
v_a_2248_ = lean_ctor_get(v___x_2223_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2250_ = v___x_2223_;
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2223_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2253_; 
if (v_isShared_2251_ == 0)
{
v___x_2253_ = v___x_2250_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_a_2248_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
}
else
{
lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2263_; 
lean_dec(v_n_2201_);
lean_dec(v_a_2196_);
lean_dec_ref(v_bs_2165_);
lean_dec(v_j_2164_);
lean_dec_ref(v_fixedArgs_2161_);
lean_dec_ref(v_a_2160_);
lean_dec_ref(v_preDefs_2159_);
lean_dec_ref(v_a_2157_);
lean_dec_ref(v_a_2156_);
v_a_2256_ = lean_ctor_get(v___x_2219_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2258_ = v___x_2219_;
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v___x_2219_);
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
}
}
else
{
lean_object* v___x_2266_; lean_object* v___x_2267_; 
lean_dec(v_term_x3f_2199_);
v___x_2266_ = lean_box(0);
lean_inc(v_a_2196_);
v___x_2267_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2196_, v___x_2266_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
if (lean_obj_tag(v___x_2267_) == 0)
{
lean_object* v_a_2268_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___x_2279_; lean_object* v_declName_2280_; lean_object* v___f_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___f_2287_; lean_object* v___x_2288_; lean_object* v___f_2289_; lean_object* v___x_2290_; 
v_a_2268_ = lean_ctor_get(v___x_2267_, 0);
lean_inc(v_a_2268_);
lean_dec_ref(v___x_2267_);
v___x_2279_ = lean_array_fget_borrowed(v_as_2162_, v_j_2164_);
v_declName_2280_ = lean_ctor_get(v___x_2279_, 3);
lean_inc_ref(v_fixedArgs_2161_);
lean_inc_ref(v_a_2160_);
lean_inc_ref(v_preDefs_2159_);
v___f_2281_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__1___boxed), 11, 3);
lean_closure_set(v___f_2281_, 0, v_preDefs_2159_);
lean_closure_set(v___f_2281_, 1, v_a_2160_);
lean_closure_set(v___f_2281_, 2, v_fixedArgs_2161_);
v___x_2282_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__1, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__1_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__1);
lean_inc(v_declName_2280_);
v___x_2283_ = l_Lean_MessageData_ofName(v_declName_2280_);
lean_inc_ref(v___x_2283_);
v___x_2284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2282_);
lean_ctor_set(v___x_2284_, 1, v___x_2283_);
v___x_2285_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__3, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__3_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__3);
v___x_2286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2284_);
lean_ctor_set(v___x_2286_, 1, v___x_2285_);
v___f_2287_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2287_, 0, v___x_2286_);
v___x_2288_ = l_Lean_Expr_mvarId_x21(v_a_2268_);
v___f_2289_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__3___boxed), 7, 2);
lean_closure_set(v___f_2289_, 0, v___f_2281_);
lean_closure_set(v___f_2289_, 1, v___x_2288_);
v___x_2290_ = l_Lean_Meta_mapErrorImp___redArg(v___f_2289_, v___f_2287_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
if (lean_obj_tag(v___x_2290_) == 0)
{
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v_a_2293_; uint8_t v___x_2294_; 
lean_dec_ref(v___x_2290_);
v___x_2291_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__7));
v___x_2292_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_partialFixpoint_spec__2___redArg(v___x_2291_, v___y_2170_);
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_a_2293_);
lean_dec_ref(v___x_2292_);
v___x_2294_ = lean_unbox(v_a_2293_);
lean_dec(v_a_2293_);
if (v___x_2294_ == 0)
{
lean_dec_ref(v___x_2283_);
v___y_2270_ = v___y_2166_;
v___y_2271_ = v___y_2167_;
v___y_2272_ = v___y_2168_;
v___y_2273_ = v___y_2169_;
v___y_2274_ = v___y_2170_;
v___y_2275_ = v___y_2171_;
goto v___jp_2269_;
}
else
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2295_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__9, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__9_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__9);
v___x_2296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2295_);
lean_ctor_set(v___x_2296_, 1, v___x_2283_);
v___x_2297_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__11, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__11_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__11);
v___x_2298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2296_);
lean_ctor_set(v___x_2298_, 1, v___x_2297_);
lean_inc(v_a_2268_);
v___x_2299_ = l_Lean_MessageData_ofExpr(v_a_2268_);
v___x_2300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2298_);
lean_ctor_set(v___x_2300_, 1, v___x_2299_);
v___x_2301_ = l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__3___redArg(v___x_2291_, v___x_2300_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_dec_ref(v___x_2301_);
v___y_2270_ = v___y_2166_;
v___y_2271_ = v___y_2167_;
v___y_2272_ = v___y_2168_;
v___y_2273_ = v___y_2169_;
v___y_2274_ = v___y_2170_;
v___y_2275_ = v___y_2171_;
goto v___jp_2269_;
}
else
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2309_; 
lean_dec(v_a_2268_);
lean_dec(v_n_2201_);
lean_dec(v_a_2196_);
lean_dec_ref(v_bs_2165_);
lean_dec(v_j_2164_);
lean_dec_ref(v_fixedArgs_2161_);
lean_dec_ref(v_a_2160_);
lean_dec_ref(v_preDefs_2159_);
lean_dec_ref(v_a_2157_);
lean_dec_ref(v_a_2156_);
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2304_ = v___x_2301_;
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2301_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2307_; 
if (v_isShared_2305_ == 0)
{
v___x_2307_ = v___x_2304_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2302_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
}
}
else
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
lean_dec_ref(v___x_2283_);
lean_dec(v_a_2268_);
lean_dec(v_n_2201_);
lean_dec(v_a_2196_);
lean_dec_ref(v_bs_2165_);
lean_dec(v_j_2164_);
lean_dec_ref(v_fixedArgs_2161_);
lean_dec_ref(v_a_2160_);
lean_dec_ref(v_preDefs_2159_);
lean_dec_ref(v_a_2157_);
lean_dec_ref(v_a_2156_);
v_a_2310_ = lean_ctor_get(v___x_2290_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2290_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2290_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
lean_ctor_set_tag(v___x_2312_, 1);
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
lean_dec_ref(v___x_2283_);
lean_dec(v_a_2268_);
lean_dec(v_n_2201_);
lean_dec(v_a_2196_);
lean_dec_ref(v_bs_2165_);
lean_dec(v_j_2164_);
lean_dec_ref(v_fixedArgs_2161_);
lean_dec_ref(v_a_2160_);
lean_dec_ref(v_preDefs_2159_);
lean_dec_ref(v_a_2157_);
lean_dec_ref(v_a_2156_);
v_a_2318_ = lean_ctor_get(v___x_2290_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2290_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2290_);
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
v___jp_2269_:
{
lean_object* v___x_2276_; lean_object* v_a_2277_; lean_object* v___x_2278_; 
v___x_2276_ = l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__19___redArg(v_a_2268_, v___y_2273_);
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_a_2277_);
lean_dec_ref(v___x_2276_);
v___x_2278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2278_, 0, v_a_2196_);
lean_ctor_set(v___x_2278_, 1, v_a_2277_);
v_a_2203_ = v___x_2278_;
goto v___jp_2202_;
}
}
else
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2333_; 
lean_dec(v_n_2201_);
lean_dec(v_a_2196_);
lean_dec_ref(v_bs_2165_);
lean_dec(v_j_2164_);
lean_dec_ref(v_fixedArgs_2161_);
lean_dec_ref(v_a_2160_);
lean_dec_ref(v_preDefs_2159_);
lean_dec_ref(v_a_2157_);
lean_dec_ref(v_a_2156_);
v_a_2326_ = lean_ctor_get(v___x_2267_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2267_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2328_ = v___x_2267_;
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2267_);
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
v___jp_2202_:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2204_ = lean_nat_add(v_j_2164_, v_one_2200_);
lean_dec(v_j_2164_);
v___x_2205_ = lean_array_push(v_bs_2165_, v_a_2203_);
v_i_2163_ = v_n_2201_;
v_j_2164_ = v___x_2204_;
v_bs_2165_ = v___x_2205_;
goto _start;
}
}
else
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
lean_dec_ref(v_bs_2165_);
lean_dec(v_j_2164_);
lean_dec(v_i_2163_);
lean_dec_ref(v_fixedArgs_2161_);
lean_dec_ref(v_a_2160_);
lean_dec_ref(v_preDefs_2159_);
lean_dec_ref(v_a_2157_);
lean_dec_ref(v_a_2156_);
v_a_2334_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2195_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2195_);
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
else
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2349_; 
lean_dec_ref(v___x_2180_);
lean_dec_ref(v_bs_2165_);
lean_dec(v_j_2164_);
lean_dec(v_i_2163_);
lean_dec_ref(v_fixedArgs_2161_);
lean_dec_ref(v_a_2160_);
lean_dec_ref(v_preDefs_2159_);
lean_dec_ref(v_a_2157_);
lean_dec_ref(v_a_2156_);
v_a_2342_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2344_ = v___x_2181_;
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2181_);
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
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___boxed(lean_object** _args){
lean_object* v_a_2350_ = _args[0];
lean_object* v_a_2351_ = _args[1];
lean_object* v_a_2352_ = _args[2];
lean_object* v_a_2353_ = _args[3];
lean_object* v_a_2354_ = _args[4];
lean_object* v_hints_2355_ = _args[5];
lean_object* v_preDefs_2356_ = _args[6];
lean_object* v_a_2357_ = _args[7];
lean_object* v_fixedArgs_2358_ = _args[8];
lean_object* v_as_2359_ = _args[9];
lean_object* v_i_2360_ = _args[10];
lean_object* v_j_2361_ = _args[11];
lean_object* v_bs_2362_ = _args[12];
lean_object* v___y_2363_ = _args[13];
lean_object* v___y_2364_ = _args[14];
lean_object* v___y_2365_ = _args[15];
lean_object* v___y_2366_ = _args[16];
lean_object* v___y_2367_ = _args[17];
lean_object* v___y_2368_ = _args[18];
lean_object* v___y_2369_ = _args[19];
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg(v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_hints_2355_, v_preDefs_2356_, v_a_2357_, v_fixedArgs_2358_, v_as_2359_, v_i_2360_, v_j_2361_, v_bs_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec_ref(v_as_2359_);
lean_dec_ref(v_hints_2355_);
lean_dec_ref(v_a_2352_);
lean_dec_ref(v_a_2351_);
lean_dec_ref(v_a_2350_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20(lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_hints_2376_, lean_object* v_preDefs_2377_, lean_object* v_a_2378_, lean_object* v_fixedArgs_2379_, lean_object* v_as_2380_, lean_object* v_i_2381_, lean_object* v_j_2382_, lean_object* v_inv_2383_, lean_object* v_bs_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
lean_object* v___x_2392_; 
v___x_2392_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg(v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_hints_2376_, v_preDefs_2377_, v_a_2378_, v_fixedArgs_2379_, v_as_2380_, v_i_2381_, v_j_2382_, v_bs_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___boxed(lean_object** _args){
lean_object* v_a_2393_ = _args[0];
lean_object* v_a_2394_ = _args[1];
lean_object* v_a_2395_ = _args[2];
lean_object* v_a_2396_ = _args[3];
lean_object* v_a_2397_ = _args[4];
lean_object* v_hints_2398_ = _args[5];
lean_object* v_preDefs_2399_ = _args[6];
lean_object* v_a_2400_ = _args[7];
lean_object* v_fixedArgs_2401_ = _args[8];
lean_object* v_as_2402_ = _args[9];
lean_object* v_i_2403_ = _args[10];
lean_object* v_j_2404_ = _args[11];
lean_object* v_inv_2405_ = _args[12];
lean_object* v_bs_2406_ = _args[13];
lean_object* v___y_2407_ = _args[14];
lean_object* v___y_2408_ = _args[15];
lean_object* v___y_2409_ = _args[16];
lean_object* v___y_2410_ = _args[17];
lean_object* v___y_2411_ = _args[18];
lean_object* v___y_2412_ = _args[19];
lean_object* v___y_2413_ = _args[20];
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20(v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_hints_2398_, v_preDefs_2399_, v_a_2400_, v_fixedArgs_2401_, v_as_2402_, v_i_2403_, v_j_2404_, v_inv_2405_, v_bs_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec_ref(v_as_2402_);
lean_dec_ref(v_hints_2398_);
lean_dec_ref(v_a_2395_);
lean_dec_ref(v_a_2394_);
lean_dec_ref(v_a_2393_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11___redArg(lean_object* v___x_2415_, lean_object* v_fixedArgs_2416_, lean_object* v_as_2417_, lean_object* v_i_2418_, lean_object* v_j_2419_, lean_object* v_bs_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_){
_start:
{
lean_object* v_zero_2426_; uint8_t v_isZero_2427_; 
v_zero_2426_ = lean_unsigned_to_nat(0u);
v_isZero_2427_ = lean_nat_dec_eq(v_i_2418_, v_zero_2426_);
if (v_isZero_2427_ == 1)
{
lean_object* v___x_2428_; 
lean_dec(v_j_2419_);
lean_dec(v_i_2418_);
lean_dec_ref(v_fixedArgs_2416_);
v___x_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2428_, 0, v_bs_2420_);
return v___x_2428_;
}
else
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
v___x_2429_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1);
v___x_2430_ = lean_array_fget_borrowed(v_as_2417_, v_j_2419_);
v___x_2431_ = lean_array_get_borrowed(v___x_2429_, v___x_2415_, v_j_2419_);
lean_inc_ref(v_fixedArgs_2416_);
lean_inc(v___x_2430_);
lean_inc(v___x_2431_);
v___x_2432_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_2431_, v___x_2430_, v_fixedArgs_2416_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v_a_2433_; lean_object* v_one_2434_; lean_object* v_n_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
lean_inc(v_a_2433_);
lean_dec_ref(v___x_2432_);
v_one_2434_ = lean_unsigned_to_nat(1u);
v_n_2435_ = lean_nat_sub(v_i_2418_, v_one_2434_);
lean_dec(v_i_2418_);
v___x_2436_ = lean_nat_add(v_j_2419_, v_one_2434_);
lean_dec(v_j_2419_);
v___x_2437_ = lean_array_push(v_bs_2420_, v_a_2433_);
v_i_2418_ = v_n_2435_;
v_j_2419_ = v___x_2436_;
v_bs_2420_ = v___x_2437_;
goto _start;
}
else
{
lean_object* v_a_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2446_; 
lean_dec_ref(v_bs_2420_);
lean_dec(v_j_2419_);
lean_dec(v_i_2418_);
lean_dec_ref(v_fixedArgs_2416_);
v_a_2439_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2441_ = v___x_2432_;
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_a_2439_);
lean_dec(v___x_2432_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2444_; 
if (v_isShared_2442_ == 0)
{
v___x_2444_ = v___x_2441_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_a_2439_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11___redArg___boxed(lean_object* v___x_2447_, lean_object* v_fixedArgs_2448_, lean_object* v_as_2449_, lean_object* v_i_2450_, lean_object* v_j_2451_, lean_object* v_bs_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
lean_object* v_res_2458_; 
v_res_2458_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11___redArg(v___x_2447_, v_fixedArgs_2448_, v_as_2449_, v_i_2450_, v_j_2451_, v_bs_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
lean_dec(v___y_2456_);
lean_dec_ref(v___y_2455_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
lean_dec_ref(v_as_2449_);
lean_dec_ref(v___x_2447_);
return v_res_2458_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__12___redArg(lean_object* v___x_2459_, lean_object* v_fixedArgs_2460_, lean_object* v_as_2461_, lean_object* v_i_2462_, lean_object* v_j_2463_, lean_object* v_bs_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_){
_start:
{
lean_object* v_zero_2470_; uint8_t v_isZero_2471_; 
v_zero_2470_ = lean_unsigned_to_nat(0u);
v_isZero_2471_ = lean_nat_dec_eq(v_i_2462_, v_zero_2470_);
if (v_isZero_2471_ == 1)
{
lean_object* v___x_2472_; 
lean_dec(v_j_2463_);
lean_dec(v_i_2462_);
lean_dec_ref(v_fixedArgs_2460_);
v___x_2472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2472_, 0, v_bs_2464_);
return v___x_2472_;
}
else
{
lean_object* v___x_2473_; lean_object* v_type_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2473_ = lean_array_fget_borrowed(v_as_2461_, v_j_2463_);
v_type_2474_ = lean_ctor_get(v___x_2473_, 6);
v___x_2475_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1);
v___x_2476_ = lean_array_get_borrowed(v___x_2475_, v___x_2459_, v_j_2463_);
lean_inc_ref(v_fixedArgs_2460_);
lean_inc_ref(v_type_2474_);
lean_inc(v___x_2476_);
v___x_2477_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v___x_2476_, v_type_2474_, v_fixedArgs_2460_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_);
if (lean_obj_tag(v___x_2477_) == 0)
{
lean_object* v_a_2478_; lean_object* v_one_2479_; lean_object* v_n_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v_a_2478_ = lean_ctor_get(v___x_2477_, 0);
lean_inc(v_a_2478_);
lean_dec_ref(v___x_2477_);
v_one_2479_ = lean_unsigned_to_nat(1u);
v_n_2480_ = lean_nat_sub(v_i_2462_, v_one_2479_);
lean_dec(v_i_2462_);
v___x_2481_ = lean_nat_add(v_j_2463_, v_one_2479_);
lean_dec(v_j_2463_);
v___x_2482_ = lean_array_push(v_bs_2464_, v_a_2478_);
v_i_2462_ = v_n_2480_;
v_j_2463_ = v___x_2481_;
v_bs_2464_ = v___x_2482_;
goto _start;
}
else
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2491_; 
lean_dec_ref(v_bs_2464_);
lean_dec(v_j_2463_);
lean_dec(v_i_2462_);
lean_dec_ref(v_fixedArgs_2460_);
v_a_2484_ = lean_ctor_get(v___x_2477_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2486_ = v___x_2477_;
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2477_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2489_; 
if (v_isShared_2487_ == 0)
{
v___x_2489_ = v___x_2486_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_a_2484_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__12___redArg___boxed(lean_object* v___x_2492_, lean_object* v_fixedArgs_2493_, lean_object* v_as_2494_, lean_object* v_i_2495_, lean_object* v_j_2496_, lean_object* v_bs_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__12___redArg(v___x_2492_, v_fixedArgs_2493_, v_as_2494_, v_i_2495_, v_j_2496_, v_bs_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
lean_dec_ref(v_as_2494_);
lean_dec_ref(v___x_2492_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__24(size_t v_sz_2504_, size_t v_i_2505_, lean_object* v_bs_2506_){
_start:
{
uint8_t v___x_2507_; 
v___x_2507_ = lean_usize_dec_lt(v_i_2505_, v_sz_2504_);
if (v___x_2507_ == 0)
{
return v_bs_2506_;
}
else
{
lean_object* v_v_2508_; uint8_t v_fixpointType_2509_; lean_object* v___x_2510_; lean_object* v_bs_x27_2511_; size_t v___x_2512_; size_t v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v_v_2508_ = lean_array_uget_borrowed(v_bs_2506_, v_i_2505_);
v_fixpointType_2509_ = lean_ctor_get_uint8(v_v_2508_, sizeof(void*)*2);
v___x_2510_ = lean_unsigned_to_nat(0u);
v_bs_x27_2511_ = lean_array_uset(v_bs_2506_, v_i_2505_, v___x_2510_);
v___x_2512_ = ((size_t)1ULL);
v___x_2513_ = lean_usize_add(v_i_2505_, v___x_2512_);
v___x_2514_ = lean_box(v_fixpointType_2509_);
v___x_2515_ = lean_array_uset(v_bs_x27_2511_, v_i_2505_, v___x_2514_);
v_i_2505_ = v___x_2513_;
v_bs_2506_ = v___x_2515_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__24___boxed(lean_object* v_sz_2517_, lean_object* v_i_2518_, lean_object* v_bs_2519_){
_start:
{
size_t v_sz_boxed_2520_; size_t v_i_boxed_2521_; lean_object* v_res_2522_; 
v_sz_boxed_2520_ = lean_unbox_usize(v_sz_2517_);
lean_dec(v_sz_2517_);
v_i_boxed_2521_ = lean_unbox_usize(v_i_2518_);
lean_dec(v_i_2518_);
v_res_2522_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__24(v_sz_boxed_2520_, v_i_boxed_2521_, v_bs_2519_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__23___redArg(size_t v_sz_2523_, size_t v_i_2524_, lean_object* v_bs_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_){
_start:
{
uint8_t v___x_2531_; 
v___x_2531_ = lean_usize_dec_lt(v_i_2524_, v_sz_2523_);
if (v___x_2531_ == 0)
{
lean_object* v___x_2532_; 
v___x_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2532_, 0, v_bs_2525_);
return v___x_2532_;
}
else
{
lean_object* v_v_2533_; lean_object* v___x_2534_; 
v_v_2533_ = lean_array_uget_borrowed(v_bs_2525_, v_i_2524_);
lean_inc(v_v_2533_);
v___x_2534_ = l_Lean_Elab_Mutual_cleanPreDef(v_v_2533_, v___x_2531_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_);
if (lean_obj_tag(v___x_2534_) == 0)
{
lean_object* v_a_2535_; lean_object* v___x_2536_; lean_object* v_bs_x27_2537_; size_t v___x_2538_; size_t v___x_2539_; lean_object* v___x_2540_; 
v_a_2535_ = lean_ctor_get(v___x_2534_, 0);
lean_inc(v_a_2535_);
lean_dec_ref(v___x_2534_);
v___x_2536_ = lean_unsigned_to_nat(0u);
v_bs_x27_2537_ = lean_array_uset(v_bs_2525_, v_i_2524_, v___x_2536_);
v___x_2538_ = ((size_t)1ULL);
v___x_2539_ = lean_usize_add(v_i_2524_, v___x_2538_);
v___x_2540_ = lean_array_uset(v_bs_x27_2537_, v_i_2524_, v_a_2535_);
v_i_2524_ = v___x_2539_;
v_bs_2525_ = v___x_2540_;
goto _start;
}
else
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2549_; 
lean_dec_ref(v_bs_2525_);
v_a_2542_ = lean_ctor_get(v___x_2534_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2534_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2544_ = v___x_2534_;
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2534_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2547_; 
if (v_isShared_2545_ == 0)
{
v___x_2547_ = v___x_2544_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_a_2542_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__23___redArg___boxed(lean_object* v_sz_2550_, lean_object* v_i_2551_, lean_object* v_bs_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
size_t v_sz_boxed_2558_; size_t v_i_boxed_2559_; lean_object* v_res_2560_; 
v_sz_boxed_2558_ = lean_unbox_usize(v_sz_2550_);
lean_dec(v_sz_2550_);
v_i_boxed_2559_ = lean_unbox_usize(v_i_2551_);
lean_dec(v_i_2551_);
v_res_2560_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__23___redArg(v_sz_boxed_2558_, v_i_boxed_2559_, v_bs_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
lean_dec(v___y_2556_);
lean_dec_ref(v___y_2555_);
lean_dec(v___y_2554_);
lean_dec_ref(v___y_2553_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__22___redArg___lam__0(lean_object* v___x_2561_, lean_object* v___x_2562_, lean_object* v___y_2563_, lean_object* v___x_2564_, lean_object* v_j_2565_, lean_object* v_a_2566_, uint8_t v_isZero_2567_, uint8_t v___x_2568_, uint8_t v___x_2569_, lean_object* v_ref_2570_, uint8_t v_kind_2571_, lean_object* v_levelParams_2572_, lean_object* v_modifiers_2573_, lean_object* v_declName_2574_, lean_object* v_binders_2575_, lean_object* v_numSectionVars_2576_, lean_object* v_type_2577_, lean_object* v_termination_2578_, lean_object* v_params_2579_, lean_object* v_x_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_){
_start:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2588_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v___x_2561_, v_params_2579_);
v___x_2589_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v___x_2561_, v_params_2579_);
v___x_2590_ = lean_box(0);
v___x_2591_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__0(v___x_2562_, v___x_2590_);
v___x_2592_ = l_Lean_mkConst(v___y_2563_, v___x_2591_);
v___x_2593_ = l_Lean_mkAppN(v___x_2592_, v___x_2588_);
lean_dec_ref(v___x_2588_);
v___x_2594_ = l_Lean_Meta_PProdN_proj(v___x_2564_, v_j_2565_, v_a_2566_, v___x_2593_);
v___x_2595_ = l_Lean_mkAppN(v___x_2594_, v___x_2589_);
lean_dec_ref(v___x_2589_);
v___x_2596_ = l_Lean_Meta_mkLambdaFVars(v_params_2579_, v___x_2595_, v_isZero_2567_, v___x_2568_, v___x_2568_, v___x_2568_, v___x_2569_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_);
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_object* v_a_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2605_; 
v_a_2597_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2599_ = v___x_2596_;
v_isShared_2600_ = v_isSharedCheck_2605_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_a_2597_);
lean_dec(v___x_2596_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2605_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v___x_2601_; lean_object* v___x_2603_; 
v___x_2601_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_2601_, 0, v_ref_2570_);
lean_ctor_set(v___x_2601_, 1, v_levelParams_2572_);
lean_ctor_set(v___x_2601_, 2, v_modifiers_2573_);
lean_ctor_set(v___x_2601_, 3, v_declName_2574_);
lean_ctor_set(v___x_2601_, 4, v_binders_2575_);
lean_ctor_set(v___x_2601_, 5, v_numSectionVars_2576_);
lean_ctor_set(v___x_2601_, 6, v_type_2577_);
lean_ctor_set(v___x_2601_, 7, v_a_2597_);
lean_ctor_set(v___x_2601_, 8, v_termination_2578_);
lean_ctor_set_uint8(v___x_2601_, sizeof(void*)*9, v_kind_2571_);
if (v_isShared_2600_ == 0)
{
lean_ctor_set(v___x_2599_, 0, v___x_2601_);
v___x_2603_ = v___x_2599_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2601_);
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
lean_dec_ref(v_termination_2578_);
lean_dec_ref(v_type_2577_);
lean_dec(v_numSectionVars_2576_);
lean_dec(v_binders_2575_);
lean_dec(v_declName_2574_);
lean_dec_ref(v_modifiers_2573_);
lean_dec(v_levelParams_2572_);
lean_dec(v_ref_2570_);
v_a_2606_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2608_ = v___x_2596_;
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2596_);
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__22___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_2614_ = _args[0];
lean_object* v___x_2615_ = _args[1];
lean_object* v___y_2616_ = _args[2];
lean_object* v___x_2617_ = _args[3];
lean_object* v_j_2618_ = _args[4];
lean_object* v_a_2619_ = _args[5];
lean_object* v_isZero_2620_ = _args[6];
lean_object* v___x_2621_ = _args[7];
lean_object* v___x_2622_ = _args[8];
lean_object* v_ref_2623_ = _args[9];
lean_object* v_kind_2624_ = _args[10];
lean_object* v_levelParams_2625_ = _args[11];
lean_object* v_modifiers_2626_ = _args[12];
lean_object* v_declName_2627_ = _args[13];
lean_object* v_binders_2628_ = _args[14];
lean_object* v_numSectionVars_2629_ = _args[15];
lean_object* v_type_2630_ = _args[16];
lean_object* v_termination_2631_ = _args[17];
lean_object* v_params_2632_ = _args[18];
lean_object* v_x_2633_ = _args[19];
lean_object* v___y_2634_ = _args[20];
lean_object* v___y_2635_ = _args[21];
lean_object* v___y_2636_ = _args[22];
lean_object* v___y_2637_ = _args[23];
lean_object* v___y_2638_ = _args[24];
lean_object* v___y_2639_ = _args[25];
lean_object* v___y_2640_ = _args[26];
_start:
{
uint8_t v_isZero_boxed_2641_; uint8_t v___x_54680__boxed_2642_; uint8_t v___x_54681__boxed_2643_; uint8_t v_kind_boxed_2644_; lean_object* v_res_2645_; 
v_isZero_boxed_2641_ = lean_unbox(v_isZero_2620_);
v___x_54680__boxed_2642_ = lean_unbox(v___x_2621_);
v___x_54681__boxed_2643_ = lean_unbox(v___x_2622_);
v_kind_boxed_2644_ = lean_unbox(v_kind_2624_);
v_res_2645_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__22___redArg___lam__0(v___x_2614_, v___x_2615_, v___y_2616_, v___x_2617_, v_j_2618_, v_a_2619_, v_isZero_boxed_2641_, v___x_54680__boxed_2642_, v___x_54681__boxed_2643_, v_ref_2623_, v_kind_boxed_2644_, v_levelParams_2625_, v_modifiers_2626_, v_declName_2627_, v_binders_2628_, v_numSectionVars_2629_, v_type_2630_, v_termination_2631_, v_params_2632_, v_x_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec_ref(v_x_2633_);
lean_dec_ref(v_params_2632_);
lean_dec(v_j_2618_);
lean_dec(v___x_2617_);
lean_dec_ref(v___x_2614_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__22___redArg(lean_object* v___x_2646_, lean_object* v___x_2647_, lean_object* v___y_2648_, lean_object* v___x_2649_, lean_object* v_a_2650_, lean_object* v_as_2651_, lean_object* v_i_2652_, lean_object* v_j_2653_, lean_object* v_bs_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_){
_start:
{
lean_object* v_zero_2662_; uint8_t v_isZero_2663_; 
v_zero_2662_ = lean_unsigned_to_nat(0u);
v_isZero_2663_ = lean_nat_dec_eq(v_i_2652_, v_zero_2662_);
if (v_isZero_2663_ == 1)
{
lean_object* v___x_2664_; 
lean_dec(v_j_2653_);
lean_dec(v_i_2652_);
lean_dec_ref(v_a_2650_);
lean_dec(v___x_2649_);
lean_dec(v___y_2648_);
lean_dec(v___x_2647_);
v___x_2664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2664_, 0, v_bs_2654_);
return v___x_2664_;
}
else
{
lean_object* v___x_2665_; lean_object* v_ref_2666_; uint8_t v_kind_2667_; lean_object* v_levelParams_2668_; lean_object* v_modifiers_2669_; lean_object* v_declName_2670_; lean_object* v_binders_2671_; lean_object* v_numSectionVars_2672_; lean_object* v_type_2673_; lean_object* v_termination_2674_; lean_object* v___x_2675_; uint8_t v___x_2676_; uint8_t v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___f_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2665_ = lean_array_fget_borrowed(v_as_2651_, v_j_2653_);
v_ref_2666_ = lean_ctor_get(v___x_2665_, 0);
v_kind_2667_ = lean_ctor_get_uint8(v___x_2665_, sizeof(void*)*9);
v_levelParams_2668_ = lean_ctor_get(v___x_2665_, 1);
v_modifiers_2669_ = lean_ctor_get(v___x_2665_, 2);
v_declName_2670_ = lean_ctor_get(v___x_2665_, 3);
v_binders_2671_ = lean_ctor_get(v___x_2665_, 4);
v_numSectionVars_2672_ = lean_ctor_get(v___x_2665_, 5);
v_type_2673_ = lean_ctor_get(v___x_2665_, 6);
v_termination_2674_ = lean_ctor_get(v___x_2665_, 8);
v___x_2675_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1);
v___x_2676_ = 1;
v___x_2677_ = 1;
v___x_2678_ = lean_array_get_borrowed(v___x_2675_, v___x_2646_, v_j_2653_);
v___x_2679_ = lean_box(v_isZero_2663_);
v___x_2680_ = lean_box(v___x_2676_);
v___x_2681_ = lean_box(v___x_2677_);
v___x_2682_ = lean_box(v_kind_2667_);
lean_inc_ref(v_termination_2674_);
lean_inc_ref(v_type_2673_);
lean_inc(v_numSectionVars_2672_);
lean_inc(v_binders_2671_);
lean_inc(v_declName_2670_);
lean_inc_ref(v_modifiers_2669_);
lean_inc(v_levelParams_2668_);
lean_inc(v_ref_2666_);
lean_inc_ref(v_a_2650_);
lean_inc(v_j_2653_);
lean_inc(v___x_2649_);
lean_inc(v___y_2648_);
lean_inc(v___x_2647_);
lean_inc(v___x_2678_);
v___f_2683_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__22___redArg___lam__0___boxed), 27, 18);
lean_closure_set(v___f_2683_, 0, v___x_2678_);
lean_closure_set(v___f_2683_, 1, v___x_2647_);
lean_closure_set(v___f_2683_, 2, v___y_2648_);
lean_closure_set(v___f_2683_, 3, v___x_2649_);
lean_closure_set(v___f_2683_, 4, v_j_2653_);
lean_closure_set(v___f_2683_, 5, v_a_2650_);
lean_closure_set(v___f_2683_, 6, v___x_2679_);
lean_closure_set(v___f_2683_, 7, v___x_2680_);
lean_closure_set(v___f_2683_, 8, v___x_2681_);
lean_closure_set(v___f_2683_, 9, v_ref_2666_);
lean_closure_set(v___f_2683_, 10, v___x_2682_);
lean_closure_set(v___f_2683_, 11, v_levelParams_2668_);
lean_closure_set(v___f_2683_, 12, v_modifiers_2669_);
lean_closure_set(v___f_2683_, 13, v_declName_2670_);
lean_closure_set(v___f_2683_, 14, v_binders_2671_);
lean_closure_set(v___f_2683_, 15, v_numSectionVars_2672_);
lean_closure_set(v___f_2683_, 16, v_type_2673_);
lean_closure_set(v___f_2683_, 17, v_termination_2674_);
v___x_2684_ = lean_array_get_size(v___x_2678_);
v___x_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2684_);
lean_inc_ref(v_type_2673_);
v___x_2686_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__21___redArg(v_type_2673_, v___x_2685_, v___f_2683_, v_isZero_2663_, v_isZero_2663_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_);
if (lean_obj_tag(v___x_2686_) == 0)
{
lean_object* v_a_2687_; lean_object* v_one_2688_; lean_object* v_n_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
v_a_2687_ = lean_ctor_get(v___x_2686_, 0);
lean_inc(v_a_2687_);
lean_dec_ref(v___x_2686_);
v_one_2688_ = lean_unsigned_to_nat(1u);
v_n_2689_ = lean_nat_sub(v_i_2652_, v_one_2688_);
lean_dec(v_i_2652_);
v___x_2690_ = lean_nat_add(v_j_2653_, v_one_2688_);
lean_dec(v_j_2653_);
v___x_2691_ = lean_array_push(v_bs_2654_, v_a_2687_);
v_i_2652_ = v_n_2689_;
v_j_2653_ = v___x_2690_;
v_bs_2654_ = v___x_2691_;
goto _start;
}
else
{
lean_object* v_a_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2700_; 
lean_dec_ref(v_bs_2654_);
lean_dec(v_j_2653_);
lean_dec(v_i_2652_);
lean_dec_ref(v_a_2650_);
lean_dec(v___x_2649_);
lean_dec(v___y_2648_);
lean_dec(v___x_2647_);
v_a_2693_ = lean_ctor_get(v___x_2686_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2695_ = v___x_2686_;
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_a_2693_);
lean_dec(v___x_2686_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2698_; 
if (v_isShared_2696_ == 0)
{
v___x_2698_ = v___x_2695_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_a_2693_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__22___redArg___boxed(lean_object* v___x_2701_, lean_object* v___x_2702_, lean_object* v___y_2703_, lean_object* v___x_2704_, lean_object* v_a_2705_, lean_object* v_as_2706_, lean_object* v_i_2707_, lean_object* v_j_2708_, lean_object* v_bs_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__22___redArg(v___x_2701_, v___x_2702_, v___y_2703_, v___x_2704_, v_a_2705_, v_as_2706_, v_i_2707_, v_j_2708_, v_bs_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec_ref(v_as_2706_);
lean_dec_ref(v___x_2701_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__18_spec__22___redArg___lam__0(lean_object* v___y_2718_, uint8_t v_isExporting_2719_, lean_object* v___x_2720_, lean_object* v___y_2721_, lean_object* v___x_2722_, lean_object* v_a_x3f_2723_){
_start:
{
lean_object* v___x_2725_; lean_object* v_env_2726_; lean_object* v_nextMacroScope_2727_; lean_object* v_ngen_2728_; lean_object* v_auxDeclNGen_2729_; lean_object* v_traceState_2730_; lean_object* v_messages_2731_; lean_object* v_infoState_2732_; lean_object* v_snapshotTasks_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2758_; 
v___x_2725_ = lean_st_ref_take(v___y_2718_);
v_env_2726_ = lean_ctor_get(v___x_2725_, 0);
v_nextMacroScope_2727_ = lean_ctor_get(v___x_2725_, 1);
v_ngen_2728_ = lean_ctor_get(v___x_2725_, 2);
v_auxDeclNGen_2729_ = lean_ctor_get(v___x_2725_, 3);
v_traceState_2730_ = lean_ctor_get(v___x_2725_, 4);
v_messages_2731_ = lean_ctor_get(v___x_2725_, 6);
v_infoState_2732_ = lean_ctor_get(v___x_2725_, 7);
v_snapshotTasks_2733_ = lean_ctor_get(v___x_2725_, 8);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2758_ == 0)
{
lean_object* v_unused_2759_; 
v_unused_2759_ = lean_ctor_get(v___x_2725_, 5);
lean_dec(v_unused_2759_);
v___x_2735_ = v___x_2725_;
v_isShared_2736_ = v_isSharedCheck_2758_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_snapshotTasks_2733_);
lean_inc(v_infoState_2732_);
lean_inc(v_messages_2731_);
lean_inc(v_traceState_2730_);
lean_inc(v_auxDeclNGen_2729_);
lean_inc(v_ngen_2728_);
lean_inc(v_nextMacroScope_2727_);
lean_inc(v_env_2726_);
lean_dec(v___x_2725_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2758_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2737_; lean_object* v___x_2739_; 
v___x_2737_ = l_Lean_Environment_setExporting(v_env_2726_, v_isExporting_2719_);
if (v_isShared_2736_ == 0)
{
lean_ctor_set(v___x_2735_, 5, v___x_2720_);
lean_ctor_set(v___x_2735_, 0, v___x_2737_);
v___x_2739_ = v___x_2735_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v___x_2737_);
lean_ctor_set(v_reuseFailAlloc_2757_, 1, v_nextMacroScope_2727_);
lean_ctor_set(v_reuseFailAlloc_2757_, 2, v_ngen_2728_);
lean_ctor_set(v_reuseFailAlloc_2757_, 3, v_auxDeclNGen_2729_);
lean_ctor_set(v_reuseFailAlloc_2757_, 4, v_traceState_2730_);
lean_ctor_set(v_reuseFailAlloc_2757_, 5, v___x_2720_);
lean_ctor_set(v_reuseFailAlloc_2757_, 6, v_messages_2731_);
lean_ctor_set(v_reuseFailAlloc_2757_, 7, v_infoState_2732_);
lean_ctor_set(v_reuseFailAlloc_2757_, 8, v_snapshotTasks_2733_);
v___x_2739_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v_mctx_2742_; lean_object* v_zetaDeltaFVarIds_2743_; lean_object* v_postponed_2744_; lean_object* v_diag_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2755_; 
v___x_2740_ = lean_st_ref_set(v___y_2718_, v___x_2739_);
v___x_2741_ = lean_st_ref_take(v___y_2721_);
v_mctx_2742_ = lean_ctor_get(v___x_2741_, 0);
v_zetaDeltaFVarIds_2743_ = lean_ctor_get(v___x_2741_, 2);
v_postponed_2744_ = lean_ctor_get(v___x_2741_, 3);
v_diag_2745_ = lean_ctor_get(v___x_2741_, 4);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2755_ == 0)
{
lean_object* v_unused_2756_; 
v_unused_2756_ = lean_ctor_get(v___x_2741_, 1);
lean_dec(v_unused_2756_);
v___x_2747_ = v___x_2741_;
v_isShared_2748_ = v_isSharedCheck_2755_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_diag_2745_);
lean_inc(v_postponed_2744_);
lean_inc(v_zetaDeltaFVarIds_2743_);
lean_inc(v_mctx_2742_);
lean_dec(v___x_2741_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2755_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___x_2750_; 
if (v_isShared_2748_ == 0)
{
lean_ctor_set(v___x_2747_, 1, v___x_2722_);
v___x_2750_ = v___x_2747_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_mctx_2742_);
lean_ctor_set(v_reuseFailAlloc_2754_, 1, v___x_2722_);
lean_ctor_set(v_reuseFailAlloc_2754_, 2, v_zetaDeltaFVarIds_2743_);
lean_ctor_set(v_reuseFailAlloc_2754_, 3, v_postponed_2744_);
lean_ctor_set(v_reuseFailAlloc_2754_, 4, v_diag_2745_);
v___x_2750_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2751_ = lean_st_ref_set(v___y_2721_, v___x_2750_);
v___x_2752_ = lean_box(0);
v___x_2753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2752_);
return v___x_2753_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__18_spec__22___redArg___lam__0___boxed(lean_object* v___y_2760_, lean_object* v_isExporting_2761_, lean_object* v___x_2762_, lean_object* v___y_2763_, lean_object* v___x_2764_, lean_object* v_a_x3f_2765_, lean_object* v___y_2766_){
_start:
{
uint8_t v_isExporting_boxed_2767_; lean_object* v_res_2768_; 
v_isExporting_boxed_2767_ = lean_unbox(v_isExporting_2761_);
v_res_2768_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__18_spec__22___redArg___lam__0(v___y_2760_, v_isExporting_boxed_2767_, v___x_2762_, v___y_2763_, v___x_2764_, v_a_x3f_2765_);
lean_dec(v_a_x3f_2765_);
lean_dec(v___y_2763_);
lean_dec(v___y_2760_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__18_spec__22___redArg(lean_object* v_x_2769_, uint8_t v_isExporting_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v___x_2778_; lean_object* v_env_2779_; uint8_t v_isExporting_2780_; lean_object* v___x_2781_; lean_object* v_env_2782_; lean_object* v_nextMacroScope_2783_; lean_object* v_ngen_2784_; lean_object* v_auxDeclNGen_2785_; lean_object* v_traceState_2786_; lean_object* v_messages_2787_; lean_object* v_infoState_2788_; lean_object* v_snapshotTasks_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2843_; 
v___x_2778_ = lean_st_ref_get(v___y_2776_);
v_env_2779_ = lean_ctor_get(v___x_2778_, 0);
lean_inc_ref(v_env_2779_);
lean_dec(v___x_2778_);
v_isExporting_2780_ = lean_ctor_get_uint8(v_env_2779_, sizeof(void*)*8);
lean_dec_ref(v_env_2779_);
v___x_2781_ = lean_st_ref_take(v___y_2776_);
v_env_2782_ = lean_ctor_get(v___x_2781_, 0);
v_nextMacroScope_2783_ = lean_ctor_get(v___x_2781_, 1);
v_ngen_2784_ = lean_ctor_get(v___x_2781_, 2);
v_auxDeclNGen_2785_ = lean_ctor_get(v___x_2781_, 3);
v_traceState_2786_ = lean_ctor_get(v___x_2781_, 4);
v_messages_2787_ = lean_ctor_get(v___x_2781_, 6);
v_infoState_2788_ = lean_ctor_get(v___x_2781_, 7);
v_snapshotTasks_2789_ = lean_ctor_get(v___x_2781_, 8);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2843_ == 0)
{
lean_object* v_unused_2844_; 
v_unused_2844_ = lean_ctor_get(v___x_2781_, 5);
lean_dec(v_unused_2844_);
v___x_2791_ = v___x_2781_;
v_isShared_2792_ = v_isSharedCheck_2843_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_snapshotTasks_2789_);
lean_inc(v_infoState_2788_);
lean_inc(v_messages_2787_);
lean_inc(v_traceState_2786_);
lean_inc(v_auxDeclNGen_2785_);
lean_inc(v_ngen_2784_);
lean_inc(v_nextMacroScope_2783_);
lean_inc(v_env_2782_);
lean_dec(v___x_2781_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2843_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2796_; 
v___x_2793_ = l_Lean_Environment_setExporting(v_env_2782_, v_isExporting_2770_);
v___x_2794_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2);
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 5, v___x_2794_);
lean_ctor_set(v___x_2791_, 0, v___x_2793_);
v___x_2796_ = v___x_2791_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v___x_2793_);
lean_ctor_set(v_reuseFailAlloc_2842_, 1, v_nextMacroScope_2783_);
lean_ctor_set(v_reuseFailAlloc_2842_, 2, v_ngen_2784_);
lean_ctor_set(v_reuseFailAlloc_2842_, 3, v_auxDeclNGen_2785_);
lean_ctor_set(v_reuseFailAlloc_2842_, 4, v_traceState_2786_);
lean_ctor_set(v_reuseFailAlloc_2842_, 5, v___x_2794_);
lean_ctor_set(v_reuseFailAlloc_2842_, 6, v_messages_2787_);
lean_ctor_set(v_reuseFailAlloc_2842_, 7, v_infoState_2788_);
lean_ctor_set(v_reuseFailAlloc_2842_, 8, v_snapshotTasks_2789_);
v___x_2796_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v_mctx_2799_; lean_object* v_zetaDeltaFVarIds_2800_; lean_object* v_postponed_2801_; lean_object* v_diag_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2840_; 
v___x_2797_ = lean_st_ref_set(v___y_2776_, v___x_2796_);
v___x_2798_ = lean_st_ref_take(v___y_2774_);
v_mctx_2799_ = lean_ctor_get(v___x_2798_, 0);
v_zetaDeltaFVarIds_2800_ = lean_ctor_get(v___x_2798_, 2);
v_postponed_2801_ = lean_ctor_get(v___x_2798_, 3);
v_diag_2802_ = lean_ctor_get(v___x_2798_, 4);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2840_ == 0)
{
lean_object* v_unused_2841_; 
v_unused_2841_ = lean_ctor_get(v___x_2798_, 1);
lean_dec(v_unused_2841_);
v___x_2804_ = v___x_2798_;
v_isShared_2805_ = v_isSharedCheck_2840_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_diag_2802_);
lean_inc(v_postponed_2801_);
lean_inc(v_zetaDeltaFVarIds_2800_);
lean_inc(v_mctx_2799_);
lean_dec(v___x_2798_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2840_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2806_; lean_object* v___x_2808_; 
v___x_2806_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3);
if (v_isShared_2805_ == 0)
{
lean_ctor_set(v___x_2804_, 1, v___x_2806_);
v___x_2808_ = v___x_2804_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_mctx_2799_);
lean_ctor_set(v_reuseFailAlloc_2839_, 1, v___x_2806_);
lean_ctor_set(v_reuseFailAlloc_2839_, 2, v_zetaDeltaFVarIds_2800_);
lean_ctor_set(v_reuseFailAlloc_2839_, 3, v_postponed_2801_);
lean_ctor_set(v_reuseFailAlloc_2839_, 4, v_diag_2802_);
v___x_2808_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
lean_object* v___x_2809_; lean_object* v_r_2810_; 
v___x_2809_ = lean_st_ref_set(v___y_2774_, v___x_2808_);
lean_inc(v___y_2776_);
lean_inc_ref(v___y_2775_);
lean_inc(v___y_2774_);
lean_inc_ref(v___y_2773_);
lean_inc(v___y_2772_);
lean_inc_ref(v___y_2771_);
v_r_2810_ = lean_apply_7(v_x_2769_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, lean_box(0));
if (lean_obj_tag(v_r_2810_) == 0)
{
lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2827_; 
v_a_2811_ = lean_ctor_get(v_r_2810_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v_r_2810_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2813_ = v_r_2810_;
v_isShared_2814_ = v_isSharedCheck_2827_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_dec(v_r_2810_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2827_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2816_; 
lean_inc(v_a_2811_);
if (v_isShared_2814_ == 0)
{
lean_ctor_set_tag(v___x_2813_, 1);
v___x_2816_ = v___x_2813_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_a_2811_);
v___x_2816_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
lean_object* v___x_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2824_; 
v___x_2817_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__18_spec__22___redArg___lam__0(v___y_2776_, v_isExporting_2780_, v___x_2794_, v___y_2774_, v___x_2806_, v___x_2816_);
lean_dec_ref(v___x_2816_);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2824_ == 0)
{
lean_object* v_unused_2825_; 
v_unused_2825_ = lean_ctor_get(v___x_2817_, 0);
lean_dec(v_unused_2825_);
v___x_2819_ = v___x_2817_;
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
else
{
lean_dec(v___x_2817_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2822_; 
if (v_isShared_2820_ == 0)
{
lean_ctor_set(v___x_2819_, 0, v_a_2811_);
v___x_2822_ = v___x_2819_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_a_2811_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
}
}
else
{
lean_object* v_a_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2837_; 
v_a_2828_ = lean_ctor_get(v_r_2810_, 0);
lean_inc(v_a_2828_);
lean_dec_ref(v_r_2810_);
v___x_2829_ = lean_box(0);
v___x_2830_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__18_spec__22___redArg___lam__0(v___y_2776_, v_isExporting_2780_, v___x_2794_, v___y_2774_, v___x_2806_, v___x_2829_);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2837_ == 0)
{
lean_object* v_unused_2838_; 
v_unused_2838_ = lean_ctor_get(v___x_2830_, 0);
lean_dec(v_unused_2838_);
v___x_2832_ = v___x_2830_;
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
else
{
lean_dec(v___x_2830_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___x_2835_; 
if (v_isShared_2833_ == 0)
{
lean_ctor_set_tag(v___x_2832_, 1);
lean_ctor_set(v___x_2832_, 0, v_a_2828_);
v___x_2835_ = v___x_2832_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_a_2828_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__18_spec__22___redArg___boxed(lean_object* v_x_2845_, lean_object* v_isExporting_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_){
_start:
{
uint8_t v_isExporting_boxed_2854_; lean_object* v_res_2855_; 
v_isExporting_boxed_2854_ = lean_unbox(v_isExporting_2846_);
v_res_2855_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__18_spec__22___redArg(v_x_2845_, v_isExporting_boxed_2854_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
return v_res_2855_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__18___redArg(lean_object* v_x_2856_, uint8_t v_when_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_){
_start:
{
if (v_when_2857_ == 0)
{
lean_object* v___x_2865_; 
lean_inc(v___y_2863_);
lean_inc_ref(v___y_2862_);
lean_inc(v___y_2861_);
lean_inc_ref(v___y_2860_);
lean_inc(v___y_2859_);
lean_inc_ref(v___y_2858_);
v___x_2865_ = lean_apply_7(v_x_2856_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, lean_box(0));
return v___x_2865_;
}
else
{
uint8_t v___x_2866_; lean_object* v___x_2867_; 
v___x_2866_ = 0;
v___x_2867_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__18_spec__22___redArg(v_x_2856_, v___x_2866_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
return v___x_2867_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__18___redArg___boxed(lean_object* v_x_2868_, lean_object* v_when_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
uint8_t v_when_boxed_2877_; lean_object* v_res_2878_; 
v_when_boxed_2877_ = lean_unbox(v_when_2869_);
v_res_2878_ = l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__18___redArg(v_x_2868_, v_when_boxed_2877_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
return v_res_2878_;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2879_ = l_Lean_instInhabitedExpr;
v___x_2880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2879_);
lean_ctor_set(v___x_2880_, 1, v___x_2879_);
return v___x_2880_;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2886_ = ((lean_object*)(l_Lean_Elab_partialFixpoint___lam__0___closed__4));
v___x_2887_ = l_Lean_stringToMessageData(v___x_2886_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_partialFixpoint___lam__0(lean_object* v_a_2888_, lean_object* v_perms_2889_, lean_object* v___x_2890_, lean_object* v_preDefs_2891_, lean_object* v___x_2892_, lean_object* v___x_2893_, size_t v___x_2894_, lean_object* v___x_2895_, lean_object* v_a_2896_, uint8_t v___x_2897_, lean_object* v_hints_2898_, lean_object* v___x_2899_, lean_object* v_docCtx_2900_, size_t v_sz_2901_, lean_object* v_fixedArgs_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_){
_start:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2910_ = lean_array_get_size(v_a_2888_);
v___x_2911_ = lean_mk_empty_array_with_capacity(v___x_2910_);
lean_inc(v___x_2890_);
lean_inc_ref(v_fixedArgs_2902_);
v___x_2912_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11___redArg(v_perms_2889_, v_fixedArgs_2902_, v_a_2888_, v___x_2910_, v___x_2890_, v___x_2911_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_object* v_a_2913_; lean_object* v___x_2914_; 
v_a_2913_ = lean_ctor_get(v___x_2912_, 0);
lean_inc(v_a_2913_);
lean_dec_ref(v___x_2912_);
lean_inc_ref(v___x_2893_);
lean_inc(v___x_2890_);
lean_inc(v___x_2892_);
lean_inc_ref(v_fixedArgs_2902_);
v___x_2914_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__12___redArg(v_perms_2889_, v_fixedArgs_2902_, v_preDefs_2891_, v___x_2892_, v___x_2890_, v___x_2893_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_object* v_a_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; 
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
lean_inc(v_a_2915_);
lean_dec_ref(v___x_2914_);
v___x_2916_ = l_Lean_Level_ofNat(v___x_2890_);
lean_inc(v_a_2915_);
v___x_2917_ = l_Lean_Meta_PProdN_pack(v___x_2916_, v_a_2915_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_object* v_a_2918_; size_t v_sz_2919_; lean_object* v___x_2920_; 
v_a_2918_ = lean_ctor_get(v___x_2917_, 0);
lean_inc(v_a_2918_);
lean_dec_ref(v___x_2917_);
v_sz_2919_ = lean_array_size(v_a_2913_);
v___x_2920_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__13(v_sz_2919_, v___x_2894_, v_a_2913_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v_a_2921_; lean_object* v___x_2922_; 
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc(v_a_2921_);
lean_dec_ref(v___x_2920_);
lean_inc(v_a_2921_);
v___x_2922_ = l_Lean_Meta_mkPackedPPRodInstance(v_a_2921_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v_a_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v_a_2923_ = lean_ctor_get(v___x_2922_, 0);
lean_inc(v_a_2923_);
lean_dec_ref(v___x_2922_);
v___x_2924_ = lean_box(0);
lean_inc(v_a_2923_);
v___x_2925_ = l_Lean_Meta_toPartialOrder(v_a_2923_, v___x_2924_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_object* v_a_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; 
v_a_2926_ = lean_ctor_get(v___x_2925_, 0);
lean_inc(v_a_2926_);
lean_dec_ref(v___x_2925_);
lean_inc(v___x_2890_);
lean_inc(v_a_2918_);
lean_inc_ref_n(v_preDefs_2891_, 2);
lean_inc_n(v___x_2892_, 2);
lean_inc_ref(v_a_2896_);
lean_inc_ref(v_fixedArgs_2902_);
lean_inc_ref(v_perms_2889_);
v___x_2927_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__17___boxed), 19, 12);
lean_closure_set(v___x_2927_, 0, v_perms_2889_);
lean_closure_set(v___x_2927_, 1, v_fixedArgs_2902_);
lean_closure_set(v___x_2927_, 2, v___x_2895_);
lean_closure_set(v___x_2927_, 3, v_a_2896_);
lean_closure_set(v___x_2927_, 4, v___x_2892_);
lean_closure_set(v___x_2927_, 5, v_preDefs_2891_);
lean_closure_set(v___x_2927_, 6, v_a_2918_);
lean_closure_set(v___x_2927_, 7, v_preDefs_2891_);
lean_closure_set(v___x_2927_, 8, v___x_2892_);
lean_closure_set(v___x_2927_, 9, v___x_2890_);
lean_closure_set(v___x_2927_, 10, lean_box(0));
lean_closure_set(v___x_2927_, 11, v___x_2893_);
v___x_2928_ = l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__18___redArg(v___x_2927_, v___x_2897_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
if (lean_obj_tag(v___x_2928_) == 0)
{
lean_object* v_a_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; 
v_a_2929_ = lean_ctor_get(v___x_2928_, 0);
lean_inc(v_a_2929_);
lean_dec_ref(v___x_2928_);
v___x_2930_ = lean_mk_empty_array_with_capacity(v___x_2892_);
lean_inc_ref(v___x_2930_);
lean_inc(v___x_2890_);
lean_inc(v___x_2892_);
lean_inc_ref(v_fixedArgs_2902_);
lean_inc_ref(v_a_2896_);
lean_inc_ref_n(v_preDefs_2891_, 2);
lean_inc_ref(v_hints_2898_);
lean_inc(v_a_2918_);
v___x_2931_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___boxed), 21, 14);
lean_closure_set(v___x_2931_, 0, v_a_2915_);
lean_closure_set(v___x_2931_, 1, v_a_2929_);
lean_closure_set(v___x_2931_, 2, v_a_2921_);
lean_closure_set(v___x_2931_, 3, v_a_2918_);
lean_closure_set(v___x_2931_, 4, v_a_2926_);
lean_closure_set(v___x_2931_, 5, v_hints_2898_);
lean_closure_set(v___x_2931_, 6, v_preDefs_2891_);
lean_closure_set(v___x_2931_, 7, v_a_2896_);
lean_closure_set(v___x_2931_, 8, v_fixedArgs_2902_);
lean_closure_set(v___x_2931_, 9, v_preDefs_2891_);
lean_closure_set(v___x_2931_, 10, v___x_2892_);
lean_closure_set(v___x_2931_, 11, v___x_2890_);
lean_closure_set(v___x_2931_, 12, lean_box(0));
lean_closure_set(v___x_2931_, 13, v___x_2930_);
v___x_2932_ = l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__18___redArg(v___x_2931_, v___x_2897_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v_a_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
v_a_2933_ = lean_ctor_get(v___x_2932_, 0);
lean_inc(v_a_2933_);
lean_dec_ref(v___x_2932_);
v___x_2934_ = lean_obj_once(&l_Lean_Elab_partialFixpoint___lam__0___closed__0, &l_Lean_Elab_partialFixpoint___lam__0___closed__0_once, _init_l_Lean_Elab_partialFixpoint___lam__0___closed__0);
v___x_2935_ = ((lean_object*)(l_Lean_Elab_partialFixpoint___lam__0___closed__1));
v___x_2936_ = l_Lean_Meta_PProdN_genMk___redArg(v___x_2934_, v___x_2935_, v_a_2933_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v_a_2937_; lean_object* v_snd_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_3057_; 
v_a_2937_ = lean_ctor_get(v___x_2936_, 0);
lean_inc(v_a_2937_);
lean_dec_ref(v___x_2936_);
v_snd_2938_ = lean_ctor_get(v_a_2937_, 1);
v_isSharedCheck_3057_ = !lean_is_exclusive(v_a_2937_);
if (v_isSharedCheck_3057_ == 0)
{
lean_object* v_unused_3058_; 
v_unused_3058_ = lean_ctor_get(v_a_2937_, 0);
lean_dec(v_unused_3058_);
v___x_2940_ = v_a_2937_;
v_isShared_2941_ = v_isSharedCheck_3057_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_snd_2938_);
lean_dec(v_a_2937_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_3057_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2942_; 
lean_inc(v_a_2918_);
v___x_2942_ = l_Lean_Meta_mkFixOfMonFun(v_a_2918_, v_a_2923_, v_snd_2938_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v_a_2943_; lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; uint8_t v___y_3024_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v_a_3041_; uint8_t v___x_3042_; 
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
lean_inc(v_a_2943_);
lean_dec_ref(v___x_2942_);
v___x_3039_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__7));
v___x_3040_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_partialFixpoint_spec__2___redArg(v___x_3039_, v___y_2907_);
v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
lean_inc(v_a_3041_);
lean_dec_ref(v___x_3040_);
v___x_3042_ = lean_unbox(v_a_3041_);
lean_dec(v_a_3041_);
if (v___x_3042_ == 0)
{
lean_del_object(v___x_2940_);
v___y_3030_ = v___y_2903_;
v___y_3031_ = v___y_2904_;
v___y_3032_ = v___y_2905_;
v___y_3033_ = v___y_2906_;
v___y_3034_ = v___y_2907_;
v___y_3035_ = v___y_2908_;
goto v___jp_3029_;
}
else
{
lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3046_; 
v___x_3043_ = lean_obj_once(&l_Lean_Elab_partialFixpoint___lam__0___closed__5, &l_Lean_Elab_partialFixpoint___lam__0___closed__5_once, _init_l_Lean_Elab_partialFixpoint___lam__0___closed__5);
lean_inc(v_a_2943_);
v___x_3044_ = l_Lean_MessageData_ofExpr(v_a_2943_);
if (v_isShared_2941_ == 0)
{
lean_ctor_set_tag(v___x_2940_, 7);
lean_ctor_set(v___x_2940_, 1, v___x_3044_);
lean_ctor_set(v___x_2940_, 0, v___x_3043_);
v___x_3046_ = v___x_2940_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v___x_3043_);
lean_ctor_set(v_reuseFailAlloc_3048_, 1, v___x_3044_);
v___x_3046_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
lean_object* v___x_3047_; 
v___x_3047_ = l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__3___redArg(v___x_3039_, v___x_3046_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_dec_ref(v___x_3047_);
v___y_3030_ = v___y_2903_;
v___y_3031_ = v___y_2904_;
v___y_3032_ = v___y_2905_;
v___y_3033_ = v___y_2906_;
v___y_3034_ = v___y_2907_;
v___y_3035_ = v___y_2908_;
goto v___jp_3029_;
}
else
{
lean_dec(v_a_2943_);
lean_dec_ref(v___x_2930_);
lean_dec(v_a_2918_);
lean_dec_ref(v_fixedArgs_2902_);
lean_dec_ref(v_docCtx_2900_);
lean_dec_ref(v___x_2899_);
lean_dec_ref(v_hints_2898_);
lean_dec_ref(v_a_2896_);
lean_dec(v___x_2892_);
lean_dec_ref(v_preDefs_2891_);
lean_dec(v___x_2890_);
lean_dec_ref(v_perms_2889_);
return v___x_3047_;
}
}
}
v___jp_2944_:
{
uint8_t v___x_2952_; uint8_t v___x_2953_; lean_object* v___x_2954_; 
v___x_2952_ = 0;
v___x_2953_ = 1;
lean_inc(v_a_2918_);
v___x_2954_ = l_Lean_Meta_mkForallFVars(v_fixedArgs_2902_, v_a_2918_, v___x_2952_, v___x_2897_, v___x_2897_, v___x_2953_, v___y_2949_, v___y_2945_, v___y_2948_, v___y_2946_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_object* v_a_2955_; lean_object* v___x_2956_; 
v_a_2955_ = lean_ctor_get(v___x_2954_, 0);
lean_inc(v_a_2955_);
lean_dec_ref(v___x_2954_);
v___x_2956_ = l_Lean_Meta_mkLambdaFVars(v_fixedArgs_2902_, v_a_2943_, v___x_2952_, v___x_2897_, v___x_2952_, v___x_2897_, v___x_2953_, v___y_2949_, v___y_2945_, v___y_2948_, v___y_2946_);
lean_dec_ref(v_fixedArgs_2902_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_a_2957_; lean_object* v_ref_2958_; uint8_t v_kind_2959_; lean_object* v_levelParams_2960_; lean_object* v_modifiers_2961_; lean_object* v_binders_2962_; lean_object* v_numSectionVars_2963_; lean_object* v_termination_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2997_; 
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
lean_inc(v_a_2957_);
lean_dec_ref(v___x_2956_);
v_ref_2958_ = lean_ctor_get(v___x_2899_, 0);
v_kind_2959_ = lean_ctor_get_uint8(v___x_2899_, sizeof(void*)*9);
v_levelParams_2960_ = lean_ctor_get(v___x_2899_, 1);
v_modifiers_2961_ = lean_ctor_get(v___x_2899_, 2);
v_binders_2962_ = lean_ctor_get(v___x_2899_, 4);
v_numSectionVars_2963_ = lean_ctor_get(v___x_2899_, 5);
v_termination_2964_ = lean_ctor_get(v___x_2899_, 8);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2997_ == 0)
{
lean_object* v_unused_2998_; lean_object* v_unused_2999_; lean_object* v_unused_3000_; 
v_unused_2998_ = lean_ctor_get(v___x_2899_, 7);
lean_dec(v_unused_2998_);
v_unused_2999_ = lean_ctor_get(v___x_2899_, 6);
lean_dec(v_unused_2999_);
v_unused_3000_ = lean_ctor_get(v___x_2899_, 3);
lean_dec(v_unused_3000_);
v___x_2966_ = v___x_2899_;
v_isShared_2967_ = v_isSharedCheck_2997_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_termination_2964_);
lean_inc(v_numSectionVars_2963_);
lean_inc(v_binders_2962_);
lean_inc(v_modifiers_2961_);
lean_inc(v_levelParams_2960_);
lean_inc(v_ref_2958_);
lean_dec(v___x_2899_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2997_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2968_; 
lean_inc(v___x_2892_);
lean_inc(v___y_2951_);
lean_inc(v_levelParams_2960_);
v___x_2968_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__22___redArg(v_perms_2889_, v_levelParams_2960_, v___y_2951_, v___x_2892_, v_a_2918_, v_preDefs_2891_, v___x_2892_, v___x_2890_, v___x_2930_, v___y_2950_, v___y_2947_, v___y_2949_, v___y_2945_, v___y_2948_, v___y_2946_);
lean_dec_ref(v_perms_2889_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v_a_2969_; lean_object* v___x_2971_; 
v_a_2969_ = lean_ctor_get(v___x_2968_, 0);
lean_inc(v_a_2969_);
lean_dec_ref(v___x_2968_);
lean_inc(v___y_2951_);
if (v_isShared_2967_ == 0)
{
lean_ctor_set(v___x_2966_, 7, v_a_2957_);
lean_ctor_set(v___x_2966_, 6, v_a_2955_);
lean_ctor_set(v___x_2966_, 3, v___y_2951_);
v___x_2971_ = v___x_2966_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_ref_2958_);
lean_ctor_set(v_reuseFailAlloc_2988_, 1, v_levelParams_2960_);
lean_ctor_set(v_reuseFailAlloc_2988_, 2, v_modifiers_2961_);
lean_ctor_set(v_reuseFailAlloc_2988_, 3, v___y_2951_);
lean_ctor_set(v_reuseFailAlloc_2988_, 4, v_binders_2962_);
lean_ctor_set(v_reuseFailAlloc_2988_, 5, v_numSectionVars_2963_);
lean_ctor_set(v_reuseFailAlloc_2988_, 6, v_a_2955_);
lean_ctor_set(v_reuseFailAlloc_2988_, 7, v_a_2957_);
lean_ctor_set(v_reuseFailAlloc_2988_, 8, v_termination_2964_);
lean_ctor_set_uint8(v_reuseFailAlloc_2988_, sizeof(void*)*9, v_kind_2959_);
v___x_2971_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
lean_object* v___x_2972_; 
lean_inc_ref(v___y_2948_);
lean_inc_ref(v_preDefs_2891_);
lean_inc_ref(v_docCtx_2900_);
v___x_2972_ = l_Lean_Elab_Mutual_addPreDefsFromUnary(v_docCtx_2900_, v_preDefs_2891_, v_a_2969_, v___x_2971_, v___x_2897_, v___y_2950_, v___y_2947_, v___y_2949_, v___y_2945_, v___y_2948_, v___y_2946_);
lean_dec(v_a_2969_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_object* v___x_2973_; 
lean_dec_ref(v___x_2972_);
lean_inc_ref(v_preDefs_2891_);
v___x_2973_ = l_Lean_Elab_addAndCompilePartialRec(v_docCtx_2900_, v_preDefs_2891_, v___y_2950_, v___y_2947_, v___y_2949_, v___y_2945_, v___y_2948_, v___y_2946_);
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_object* v___x_2974_; 
lean_dec_ref(v___x_2973_);
v___x_2974_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__23___redArg(v_sz_2901_, v___x_2894_, v_preDefs_2891_, v___y_2949_, v___y_2945_, v___y_2948_, v___y_2946_);
if (lean_obj_tag(v___x_2974_) == 0)
{
lean_object* v_a_2975_; size_t v_sz_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
v_a_2975_ = lean_ctor_get(v___x_2974_, 0);
lean_inc(v_a_2975_);
lean_dec_ref(v___x_2974_);
v_sz_2976_ = lean_array_size(v_hints_2898_);
v___x_2977_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__24(v_sz_2976_, v___x_2894_, v_hints_2898_);
lean_inc(v_a_2975_);
v___x_2978_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo(v_a_2975_, v___y_2951_, v_a_2896_, v___x_2977_, v___y_2949_, v___y_2945_, v___y_2948_, v___y_2946_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v___x_2979_; 
lean_dec_ref(v___x_2978_);
v___x_2979_ = l_Lean_Elab_Mutual_addPreDefAttributes(v_a_2975_, v___y_2950_, v___y_2947_, v___y_2949_, v___y_2945_, v___y_2948_, v___y_2946_);
return v___x_2979_;
}
else
{
lean_dec(v_a_2975_);
return v___x_2978_;
}
}
else
{
lean_object* v_a_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2987_; 
lean_dec(v___y_2951_);
lean_dec_ref(v_hints_2898_);
lean_dec_ref(v_a_2896_);
v_a_2980_ = lean_ctor_get(v___x_2974_, 0);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2982_ = v___x_2974_;
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_a_2980_);
lean_dec(v___x_2974_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2985_; 
if (v_isShared_2983_ == 0)
{
v___x_2985_ = v___x_2982_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_a_2980_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
}
}
}
}
else
{
lean_dec(v___y_2951_);
lean_dec_ref(v_hints_2898_);
lean_dec_ref(v_a_2896_);
lean_dec_ref(v_preDefs_2891_);
return v___x_2973_;
}
}
else
{
lean_dec(v___y_2951_);
lean_dec_ref(v_docCtx_2900_);
lean_dec_ref(v_hints_2898_);
lean_dec_ref(v_a_2896_);
lean_dec_ref(v_preDefs_2891_);
return v___x_2972_;
}
}
}
else
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
lean_del_object(v___x_2966_);
lean_dec_ref(v_termination_2964_);
lean_dec(v_numSectionVars_2963_);
lean_dec(v_binders_2962_);
lean_dec_ref(v_modifiers_2961_);
lean_dec(v_levelParams_2960_);
lean_dec(v_ref_2958_);
lean_dec(v_a_2957_);
lean_dec(v_a_2955_);
lean_dec(v___y_2951_);
lean_dec_ref(v_docCtx_2900_);
lean_dec_ref(v_hints_2898_);
lean_dec_ref(v_a_2896_);
lean_dec_ref(v_preDefs_2891_);
v_a_2989_ = lean_ctor_get(v___x_2968_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2991_ = v___x_2968_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v___x_2968_);
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
v_reuseFailAlloc_2995_ = lean_alloc_ctor(1, 1, 0);
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
}
}
else
{
lean_object* v_a_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3008_; 
lean_dec(v_a_2955_);
lean_dec(v___y_2951_);
lean_dec_ref(v___x_2930_);
lean_dec(v_a_2918_);
lean_dec_ref(v_docCtx_2900_);
lean_dec_ref(v___x_2899_);
lean_dec_ref(v_hints_2898_);
lean_dec_ref(v_a_2896_);
lean_dec(v___x_2892_);
lean_dec_ref(v_preDefs_2891_);
lean_dec(v___x_2890_);
lean_dec_ref(v_perms_2889_);
v_a_3001_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_3008_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_3003_ = v___x_2956_;
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_a_3001_);
lean_dec(v___x_2956_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3006_; 
if (v_isShared_3004_ == 0)
{
v___x_3006_ = v___x_3003_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_a_3001_);
v___x_3006_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
return v___x_3006_;
}
}
}
}
else
{
lean_object* v_a_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3016_; 
lean_dec(v___y_2951_);
lean_dec(v_a_2943_);
lean_dec_ref(v___x_2930_);
lean_dec(v_a_2918_);
lean_dec_ref(v_fixedArgs_2902_);
lean_dec_ref(v_docCtx_2900_);
lean_dec_ref(v___x_2899_);
lean_dec_ref(v_hints_2898_);
lean_dec_ref(v_a_2896_);
lean_dec(v___x_2892_);
lean_dec_ref(v_preDefs_2891_);
lean_dec(v___x_2890_);
lean_dec_ref(v_perms_2889_);
v_a_3009_ = lean_ctor_get(v___x_2954_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_3011_ = v___x_2954_;
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_a_3009_);
lean_dec(v___x_2954_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3014_; 
if (v_isShared_3012_ == 0)
{
v___x_3014_ = v___x_3011_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v_a_3009_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
}
}
v___jp_3017_:
{
if (v___y_3024_ == 0)
{
lean_object* v_declName_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v_declName_3025_ = lean_ctor_get(v___x_2899_, 3);
v___x_3026_ = ((lean_object*)(l_Lean_Elab_partialFixpoint___lam__0___closed__3));
lean_inc(v_declName_3025_);
v___x_3027_ = l_Lean_Name_append(v_declName_3025_, v___x_3026_);
v___y_2945_ = v___y_3018_;
v___y_2946_ = v___y_3019_;
v___y_2947_ = v___y_3020_;
v___y_2948_ = v___y_3021_;
v___y_2949_ = v___y_3022_;
v___y_2950_ = v___y_3023_;
v___y_2951_ = v___x_3027_;
goto v___jp_2944_;
}
else
{
lean_object* v_declName_3028_; 
v_declName_3028_ = lean_ctor_get(v___x_2899_, 3);
lean_inc(v_declName_3028_);
v___y_2945_ = v___y_3018_;
v___y_2946_ = v___y_3019_;
v___y_2947_ = v___y_3020_;
v___y_2948_ = v___y_3021_;
v___y_2949_ = v___y_3022_;
v___y_2950_ = v___y_3023_;
v___y_2951_ = v_declName_3028_;
goto v___jp_2944_;
}
}
v___jp_3029_:
{
lean_object* v___x_3036_; uint8_t v___x_3037_; 
v___x_3036_ = lean_unsigned_to_nat(1u);
v___x_3037_ = lean_nat_dec_eq(v___x_2892_, v___x_3036_);
if (v___x_3037_ == 0)
{
v___y_3018_ = v___y_3033_;
v___y_3019_ = v___y_3035_;
v___y_3020_ = v___y_3031_;
v___y_3021_ = v___y_3034_;
v___y_3022_ = v___y_3032_;
v___y_3023_ = v___y_3030_;
v___y_3024_ = v___x_3037_;
goto v___jp_3017_;
}
else
{
uint8_t v___x_3038_; 
lean_inc_ref(v_a_2896_);
v___x_3038_ = l_Lean_Elab_FixedParamPerms_fixedArePrefix(v_a_2896_);
v___y_3018_ = v___y_3033_;
v___y_3019_ = v___y_3035_;
v___y_3020_ = v___y_3031_;
v___y_3021_ = v___y_3034_;
v___y_3022_ = v___y_3032_;
v___y_3023_ = v___y_3030_;
v___y_3024_ = v___x_3038_;
goto v___jp_3017_;
}
}
}
else
{
lean_object* v_a_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3056_; 
lean_del_object(v___x_2940_);
lean_dec_ref(v___x_2930_);
lean_dec(v_a_2918_);
lean_dec_ref(v_fixedArgs_2902_);
lean_dec_ref(v_docCtx_2900_);
lean_dec_ref(v___x_2899_);
lean_dec_ref(v_hints_2898_);
lean_dec_ref(v_a_2896_);
lean_dec(v___x_2892_);
lean_dec_ref(v_preDefs_2891_);
lean_dec(v___x_2890_);
lean_dec_ref(v_perms_2889_);
v_a_3049_ = lean_ctor_get(v___x_2942_, 0);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3051_ = v___x_2942_;
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_a_3049_);
lean_dec(v___x_2942_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3054_; 
if (v_isShared_3052_ == 0)
{
v___x_3054_ = v___x_3051_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_3049_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
}
}
else
{
lean_object* v_a_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3066_; 
lean_dec_ref(v___x_2930_);
lean_dec(v_a_2923_);
lean_dec(v_a_2918_);
lean_dec_ref(v_fixedArgs_2902_);
lean_dec_ref(v_docCtx_2900_);
lean_dec_ref(v___x_2899_);
lean_dec_ref(v_hints_2898_);
lean_dec_ref(v_a_2896_);
lean_dec(v___x_2892_);
lean_dec_ref(v_preDefs_2891_);
lean_dec(v___x_2890_);
lean_dec_ref(v_perms_2889_);
v_a_3059_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3061_ = v___x_2936_;
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_a_3059_);
lean_dec(v___x_2936_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3064_; 
if (v_isShared_3062_ == 0)
{
v___x_3064_ = v___x_3061_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_a_3059_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
return v___x_3064_;
}
}
}
}
else
{
lean_object* v_a_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3074_; 
lean_dec_ref(v___x_2930_);
lean_dec(v_a_2923_);
lean_dec(v_a_2918_);
lean_dec_ref(v_fixedArgs_2902_);
lean_dec_ref(v_docCtx_2900_);
lean_dec_ref(v___x_2899_);
lean_dec_ref(v_hints_2898_);
lean_dec_ref(v_a_2896_);
lean_dec(v___x_2892_);
lean_dec_ref(v_preDefs_2891_);
lean_dec(v___x_2890_);
lean_dec_ref(v_perms_2889_);
v_a_3067_ = lean_ctor_get(v___x_2932_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3069_ = v___x_2932_;
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_a_3067_);
lean_dec(v___x_2932_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3072_; 
if (v_isShared_3070_ == 0)
{
v___x_3072_ = v___x_3069_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_a_3067_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
}
}
else
{
lean_object* v_a_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3082_; 
lean_dec(v_a_2926_);
lean_dec(v_a_2923_);
lean_dec(v_a_2921_);
lean_dec(v_a_2918_);
lean_dec(v_a_2915_);
lean_dec_ref(v_fixedArgs_2902_);
lean_dec_ref(v_docCtx_2900_);
lean_dec_ref(v___x_2899_);
lean_dec_ref(v_hints_2898_);
lean_dec_ref(v_a_2896_);
lean_dec(v___x_2892_);
lean_dec_ref(v_preDefs_2891_);
lean_dec(v___x_2890_);
lean_dec_ref(v_perms_2889_);
v_a_3075_ = lean_ctor_get(v___x_2928_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_2928_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3077_ = v___x_2928_;
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_a_3075_);
lean_dec(v___x_2928_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3080_; 
if (v_isShared_3078_ == 0)
{
v___x_3080_ = v___x_3077_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_a_3075_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
}
}
else
{
lean_object* v_a_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3090_; 
lean_dec(v_a_2923_);
lean_dec(v_a_2921_);
lean_dec(v_a_2918_);
lean_dec(v_a_2915_);
lean_dec_ref(v_fixedArgs_2902_);
lean_dec_ref(v_docCtx_2900_);
lean_dec_ref(v___x_2899_);
lean_dec_ref(v_hints_2898_);
lean_dec_ref(v_a_2896_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___x_2893_);
lean_dec(v___x_2892_);
lean_dec_ref(v_preDefs_2891_);
lean_dec(v___x_2890_);
lean_dec_ref(v_perms_2889_);
v_a_3083_ = lean_ctor_get(v___x_2925_, 0);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_2925_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3085_ = v___x_2925_;
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_a_3083_);
lean_dec(v___x_2925_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3088_; 
if (v_isShared_3086_ == 0)
{
v___x_3088_ = v___x_3085_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_a_3083_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
}
else
{
lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3098_; 
lean_dec(v_a_2921_);
lean_dec(v_a_2918_);
lean_dec(v_a_2915_);
lean_dec_ref(v_fixedArgs_2902_);
lean_dec_ref(v_docCtx_2900_);
lean_dec_ref(v___x_2899_);
lean_dec_ref(v_hints_2898_);
lean_dec_ref(v_a_2896_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___x_2893_);
lean_dec(v___x_2892_);
lean_dec_ref(v_preDefs_2891_);
lean_dec(v___x_2890_);
lean_dec_ref(v_perms_2889_);
v_a_3091_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3093_ = v___x_2922_;
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3091_);
lean_dec(v___x_2922_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3096_; 
if (v_isShared_3094_ == 0)
{
v___x_3096_ = v___x_3093_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_a_3091_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
}
else
{
lean_object* v_a_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3106_; 
lean_dec(v_a_2918_);
lean_dec(v_a_2915_);
lean_dec_ref(v_fixedArgs_2902_);
lean_dec_ref(v_docCtx_2900_);
lean_dec_ref(v___x_2899_);
lean_dec_ref(v_hints_2898_);
lean_dec_ref(v_a_2896_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___x_2893_);
lean_dec(v___x_2892_);
lean_dec_ref(v_preDefs_2891_);
lean_dec(v___x_2890_);
lean_dec_ref(v_perms_2889_);
v_a_3099_ = lean_ctor_get(v___x_2920_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3101_ = v___x_2920_;
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_a_3099_);
lean_dec(v___x_2920_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3104_; 
if (v_isShared_3102_ == 0)
{
v___x_3104_ = v___x_3101_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_a_3099_);
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
else
{
lean_object* v_a_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3114_; 
lean_dec(v_a_2915_);
lean_dec(v_a_2913_);
lean_dec_ref(v_fixedArgs_2902_);
lean_dec_ref(v_docCtx_2900_);
lean_dec_ref(v___x_2899_);
lean_dec_ref(v_hints_2898_);
lean_dec_ref(v_a_2896_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___x_2893_);
lean_dec(v___x_2892_);
lean_dec_ref(v_preDefs_2891_);
lean_dec(v___x_2890_);
lean_dec_ref(v_perms_2889_);
v_a_3107_ = lean_ctor_get(v___x_2917_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_2917_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3109_ = v___x_2917_;
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_a_3107_);
lean_dec(v___x_2917_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3112_; 
if (v_isShared_3110_ == 0)
{
v___x_3112_ = v___x_3109_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v_a_3107_);
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
else
{
lean_object* v_a_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3122_; 
lean_dec(v_a_2913_);
lean_dec_ref(v_fixedArgs_2902_);
lean_dec_ref(v_docCtx_2900_);
lean_dec_ref(v___x_2899_);
lean_dec_ref(v_hints_2898_);
lean_dec_ref(v_a_2896_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___x_2893_);
lean_dec(v___x_2892_);
lean_dec_ref(v_preDefs_2891_);
lean_dec(v___x_2890_);
lean_dec_ref(v_perms_2889_);
v_a_3115_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3117_ = v___x_2914_;
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_a_3115_);
lean_dec(v___x_2914_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3120_; 
if (v_isShared_3118_ == 0)
{
v___x_3120_ = v___x_3117_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_a_3115_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
}
else
{
lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3130_; 
lean_dec_ref(v_fixedArgs_2902_);
lean_dec_ref(v_docCtx_2900_);
lean_dec_ref(v___x_2899_);
lean_dec_ref(v_hints_2898_);
lean_dec_ref(v_a_2896_);
lean_dec_ref(v___x_2895_);
lean_dec_ref(v___x_2893_);
lean_dec(v___x_2892_);
lean_dec_ref(v_preDefs_2891_);
lean_dec(v___x_2890_);
lean_dec_ref(v_perms_2889_);
v_a_3123_ = lean_ctor_get(v___x_2912_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3125_ = v___x_2912_;
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_2912_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3128_; 
if (v_isShared_3126_ == 0)
{
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
return v___x_3128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_partialFixpoint___lam__0___boxed(lean_object** _args){
lean_object* v_a_3131_ = _args[0];
lean_object* v_perms_3132_ = _args[1];
lean_object* v___x_3133_ = _args[2];
lean_object* v_preDefs_3134_ = _args[3];
lean_object* v___x_3135_ = _args[4];
lean_object* v___x_3136_ = _args[5];
lean_object* v___x_3137_ = _args[6];
lean_object* v___x_3138_ = _args[7];
lean_object* v_a_3139_ = _args[8];
lean_object* v___x_3140_ = _args[9];
lean_object* v_hints_3141_ = _args[10];
lean_object* v___x_3142_ = _args[11];
lean_object* v_docCtx_3143_ = _args[12];
lean_object* v_sz_3144_ = _args[13];
lean_object* v_fixedArgs_3145_ = _args[14];
lean_object* v___y_3146_ = _args[15];
lean_object* v___y_3147_ = _args[16];
lean_object* v___y_3148_ = _args[17];
lean_object* v___y_3149_ = _args[18];
lean_object* v___y_3150_ = _args[19];
lean_object* v___y_3151_ = _args[20];
lean_object* v___y_3152_ = _args[21];
_start:
{
size_t v___x_55126__boxed_3153_; uint8_t v___x_55129__boxed_3154_; size_t v_sz_boxed_3155_; lean_object* v_res_3156_; 
v___x_55126__boxed_3153_ = lean_unbox_usize(v___x_3137_);
lean_dec(v___x_3137_);
v___x_55129__boxed_3154_ = lean_unbox(v___x_3140_);
v_sz_boxed_3155_ = lean_unbox_usize(v_sz_3144_);
lean_dec(v_sz_3144_);
v_res_3156_ = l_Lean_Elab_partialFixpoint___lam__0(v_a_3131_, v_perms_3132_, v___x_3133_, v_preDefs_3134_, v___x_3135_, v___x_3136_, v___x_55126__boxed_3153_, v___x_3138_, v_a_3139_, v___x_55129__boxed_3154_, v_hints_3141_, v___x_3142_, v_docCtx_3143_, v_sz_boxed_3155_, v_fixedArgs_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3147_);
lean_dec_ref(v___y_3146_);
lean_dec_ref(v_a_3131_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__5(lean_object* v_a_3157_, lean_object* v_a_3158_){
_start:
{
if (lean_obj_tag(v_a_3157_) == 0)
{
lean_object* v___x_3159_; 
v___x_3159_ = l_List_reverse___redArg(v_a_3158_);
return v___x_3159_;
}
else
{
lean_object* v_head_3160_; lean_object* v_tail_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3170_; 
v_head_3160_ = lean_ctor_get(v_a_3157_, 0);
v_tail_3161_ = lean_ctor_get(v_a_3157_, 1);
v_isSharedCheck_3170_ = !lean_is_exclusive(v_a_3157_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3163_ = v_a_3157_;
v_isShared_3164_ = v_isSharedCheck_3170_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_tail_3161_);
lean_inc(v_head_3160_);
lean_dec(v_a_3157_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3170_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3165_; lean_object* v___x_3167_; 
v___x_3165_ = l_Lean_MessageData_ofExpr(v_head_3160_);
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 1, v_a_3158_);
lean_ctor_set(v___x_3163_, 0, v___x_3165_);
v___x_3167_ = v___x_3163_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v___x_3165_);
lean_ctor_set(v_reuseFailAlloc_3169_, 1, v_a_3158_);
v___x_3167_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
v_a_3157_ = v_tail_3161_;
v_a_3158_ = v___x_3167_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3172_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__0));
v___x_3173_ = l_Lean_stringToMessageData(v___x_3172_);
return v___x_3173_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_3175_; lean_object* v___x_3176_; 
v___x_3175_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__2));
v___x_3176_ = l_Lean_stringToMessageData(v___x_3175_);
return v___x_3176_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__11(void){
_start:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3189_ = lean_box(0);
v___x_3190_ = lean_unsigned_to_nat(2u);
v___x_3191_ = lean_mk_empty_array_with_capacity(v___x_3190_);
v___x_3192_ = lean_array_push(v___x_3191_, v___x_3189_);
return v___x_3192_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2(lean_object* v_declName_3195_, lean_object* v_type_3196_, lean_object* v_xs_3197_, lean_object* v___x_3198_, lean_object* v___x_3199_, lean_object* v_____r_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_){
_start:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3208_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__1, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__1_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__1);
v___x_3209_ = l_Lean_MessageData_ofName(v_declName_3195_);
v___x_3210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3208_);
lean_ctor_set(v___x_3210_, 1, v___x_3209_);
v___x_3211_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__3, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__3_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__3);
v___x_3212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3210_);
lean_ctor_set(v___x_3212_, 1, v___x_3211_);
v___x_3213_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__4));
v___x_3214_ = l_Lean_Elab_mkInhabitantFor(v___x_3212_, v___x_3213_, v_type_3196_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
if (lean_obj_tag(v___x_3214_) == 0)
{
lean_object* v_a_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; 
v_a_3215_ = lean_ctor_get(v___x_3214_, 0);
lean_inc(v_a_3215_);
lean_dec_ref(v___x_3214_);
v___x_3216_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__7));
v___x_3217_ = l_Lean_mkAppN(v_a_3215_, v_xs_3197_);
v___x_3218_ = lean_unsigned_to_nat(1u);
v___x_3219_ = lean_mk_empty_array_with_capacity(v___x_3218_);
v___x_3220_ = lean_array_push(v___x_3219_, v___x_3217_);
v___x_3221_ = l_Lean_Meta_mkAppM(v___x_3216_, v___x_3220_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
if (lean_obj_tag(v___x_3221_) == 0)
{
lean_object* v_a_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3246_; 
v_a_3222_ = lean_ctor_get(v___x_3221_, 0);
v_isSharedCheck_3246_ = !lean_is_exclusive(v___x_3221_);
if (v_isSharedCheck_3246_ == 0)
{
v___x_3224_ = v___x_3221_;
v_isShared_3225_ = v_isSharedCheck_3246_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_a_3222_);
lean_dec(v___x_3221_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3246_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v___x_3226_; lean_object* v___x_3228_; 
v___x_3226_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__10));
if (v_isShared_3225_ == 0)
{
lean_ctor_set_tag(v___x_3224_, 1);
v___x_3228_ = v___x_3224_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v_a_3222_);
v___x_3228_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3229_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__11, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__11_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__11);
v___x_3230_ = lean_array_push(v___x_3229_, v___x_3228_);
v___x_3231_ = l_Lean_Meta_mkAppOptM(v___x_3226_, v___x_3230_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_object* v_a_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3244_; 
v_a_3232_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3234_ = v___x_3231_;
v_isShared_3235_ = v_isSharedCheck_3244_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_a_3232_);
lean_dec(v___x_3231_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3244_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3240_; 
v___x_3236_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__12));
v___x_3237_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___closed__13));
v___x_3238_ = l_Lean_Name_mkStr4(v___x_3198_, v___x_3199_, v___x_3236_, v___x_3237_);
if (v_isShared_3235_ == 0)
{
lean_ctor_set_tag(v___x_3234_, 1);
v___x_3240_ = v___x_3234_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v_a_3232_);
v___x_3240_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
lean_object* v___x_3241_; lean_object* v___x_3242_; 
v___x_3241_ = lean_array_push(v___x_3229_, v___x_3240_);
v___x_3242_ = l_Lean_Meta_mkAppOptM(v___x_3238_, v___x_3241_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
return v___x_3242_;
}
}
}
else
{
lean_dec_ref(v___x_3199_);
lean_dec_ref(v___x_3198_);
return v___x_3231_;
}
}
}
}
else
{
lean_dec_ref(v___x_3199_);
lean_dec_ref(v___x_3198_);
return v___x_3221_;
}
}
else
{
lean_dec_ref(v___x_3199_);
lean_dec_ref(v___x_3198_);
return v___x_3214_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___boxed(lean_object* v_declName_3247_, lean_object* v_type_3248_, lean_object* v_xs_3249_, lean_object* v___x_3250_, lean_object* v___x_3251_, lean_object* v_____r_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_){
_start:
{
lean_object* v_res_3260_; 
v_res_3260_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2(v_declName_3247_, v_type_3248_, v_xs_3249_, v___x_3250_, v___x_3251_, v_____r_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_);
lean_dec(v___y_3258_);
lean_dec_ref(v___y_3257_);
lean_dec(v___y_3256_);
lean_dec_ref(v___y_3255_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec_ref(v_xs_3249_);
return v_res_3260_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_3262_; lean_object* v___x_3263_; 
v___x_3262_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__0));
v___x_3263_ = l_Lean_stringToMessageData(v___x_3262_);
return v___x_3263_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__3(void){
_start:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; 
v___x_3265_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__2));
v___x_3266_ = l_Lean_stringToMessageData(v___x_3265_);
return v___x_3266_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__7(void){
_start:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; 
v___x_3273_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__6));
v___x_3274_ = l_Lean_stringToMessageData(v___x_3273_);
return v___x_3274_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__9(void){
_start:
{
lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3276_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__8));
v___x_3277_ = l_Lean_stringToMessageData(v___x_3276_);
return v___x_3277_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__11(void){
_start:
{
lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3279_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__10));
v___x_3280_ = l_Lean_stringToMessageData(v___x_3279_);
return v___x_3280_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3(uint8_t v_isZero_3281_, lean_object* v_declName_3282_, lean_object* v_type_3283_, uint8_t v_fixpointType_3284_, lean_object* v___f_3285_, lean_object* v___f_3286_, lean_object* v_value_3287_, lean_object* v_xs_3288_, lean_object* v___body_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_){
_start:
{
lean_object* v_inst_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v_cls_3313_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; uint8_t v___y_3323_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v___x_3384_; lean_object* v_a_3385_; uint8_t v___x_3386_; 
v_cls_3313_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__7));
v___x_3384_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_partialFixpoint_spec__2___redArg(v_cls_3313_, v___y_3294_);
v_a_3385_ = lean_ctor_get(v___x_3384_, 0);
lean_inc(v_a_3385_);
lean_dec_ref(v___x_3384_);
v___x_3386_ = lean_unbox(v_a_3385_);
lean_dec(v_a_3385_);
if (v___x_3386_ == 0)
{
lean_dec_ref(v___body_3289_);
lean_dec_ref(v_value_3287_);
v___y_3359_ = v___y_3290_;
v___y_3360_ = v___y_3291_;
v___y_3361_ = v___y_3292_;
v___y_3362_ = v___y_3293_;
v___y_3363_ = v___y_3294_;
v___y_3364_ = v___y_3295_;
goto v___jp_3358_;
}
else
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3387_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__7, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__7_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__7);
v___x_3388_ = l_Lean_MessageData_ofExpr(v_value_3287_);
v___x_3389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3387_);
lean_ctor_set(v___x_3389_, 1, v___x_3388_);
v___x_3390_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__9, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__9_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__9);
v___x_3391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3391_, 0, v___x_3389_);
lean_ctor_set(v___x_3391_, 1, v___x_3390_);
lean_inc_ref(v_xs_3288_);
v___x_3392_ = lean_array_to_list(v_xs_3288_);
v___x_3393_ = lean_box(0);
v___x_3394_ = l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__5(v___x_3392_, v___x_3393_);
v___x_3395_ = l_Lean_MessageData_ofList(v___x_3394_);
v___x_3396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3391_);
lean_ctor_set(v___x_3396_, 1, v___x_3395_);
v___x_3397_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__11, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__11_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__11);
v___x_3398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3398_, 0, v___x_3396_);
lean_ctor_set(v___x_3398_, 1, v___x_3397_);
v___x_3399_ = l_Lean_MessageData_ofExpr(v___body_3289_);
v___x_3400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3400_, 0, v___x_3398_);
lean_ctor_set(v___x_3400_, 1, v___x_3399_);
v___x_3401_ = l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__3___redArg(v_cls_3313_, v___x_3400_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_);
if (lean_obj_tag(v___x_3401_) == 0)
{
lean_dec_ref(v___x_3401_);
v___y_3359_ = v___y_3290_;
v___y_3360_ = v___y_3291_;
v___y_3361_ = v___y_3292_;
v___y_3362_ = v___y_3293_;
v___y_3363_ = v___y_3294_;
v___y_3364_ = v___y_3295_;
goto v___jp_3358_;
}
else
{
lean_object* v_a_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3409_; 
lean_dec_ref(v_xs_3288_);
lean_dec_ref(v___f_3286_);
lean_dec_ref(v___f_3285_);
lean_dec_ref(v_type_3283_);
lean_dec(v_declName_3282_);
v_a_3402_ = lean_ctor_get(v___x_3401_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3401_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3404_ = v___x_3401_;
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_a_3402_);
lean_dec(v___x_3401_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3407_; 
if (v_isShared_3405_ == 0)
{
v___x_3407_ = v___x_3404_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_a_3402_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
}
v___jp_3297_:
{
uint8_t v___x_3303_; uint8_t v___x_3304_; lean_object* v___x_3305_; 
v___x_3303_ = 1;
v___x_3304_ = 1;
v___x_3305_ = l_Lean_Meta_mkLambdaFVars(v_xs_3288_, v_inst_3298_, v_isZero_3281_, v___x_3303_, v_isZero_3281_, v___x_3303_, v___x_3304_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_);
lean_dec_ref(v_xs_3288_);
return v___x_3305_;
}
v___jp_3306_:
{
if (lean_obj_tag(v___y_3311_) == 0)
{
lean_object* v_a_3312_; 
v_a_3312_ = lean_ctor_get(v___y_3311_, 0);
lean_inc(v_a_3312_);
lean_dec_ref(v___y_3311_);
v_inst_3298_ = v_a_3312_;
v___y_3299_ = v___y_3307_;
v___y_3300_ = v___y_3310_;
v___y_3301_ = v___y_3309_;
v___y_3302_ = v___y_3308_;
goto v___jp_3297_;
}
else
{
lean_dec_ref(v_xs_3288_);
return v___y_3311_;
}
}
v___jp_3314_:
{
if (v___y_3323_ == 0)
{
lean_object* v___x_3324_; lean_object* v_a_3325_; uint8_t v___x_3326_; 
lean_dec_ref(v___y_3316_);
v___x_3324_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_partialFixpoint_spec__2___redArg(v_cls_3313_, v___y_3320_);
v_a_3325_ = lean_ctor_get(v___x_3324_, 0);
lean_inc(v_a_3325_);
lean_dec_ref(v___x_3324_);
v___x_3326_ = lean_unbox(v_a_3325_);
lean_dec(v_a_3325_);
if (v___x_3326_ == 0)
{
lean_object* v___x_3327_; lean_object* v___x_3328_; 
lean_dec(v_declName_3282_);
v___x_3327_ = lean_box(0);
lean_inc(v___y_3318_);
lean_inc_ref(v___y_3320_);
lean_inc(v___y_3321_);
lean_inc_ref(v___y_3317_);
lean_inc(v___y_3322_);
lean_inc_ref(v___y_3319_);
v___x_3328_ = lean_apply_8(v___y_3315_, v___x_3327_, v___y_3319_, v___y_3322_, v___y_3317_, v___y_3321_, v___y_3320_, v___y_3318_, lean_box(0));
v___y_3307_ = v___y_3317_;
v___y_3308_ = v___y_3318_;
v___y_3309_ = v___y_3320_;
v___y_3310_ = v___y_3321_;
v___y_3311_ = v___x_3328_;
goto v___jp_3306_;
}
else
{
lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
v___x_3329_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__1, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__1_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__1);
v___x_3330_ = l_Lean_MessageData_ofName(v_declName_3282_);
v___x_3331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3329_);
lean_ctor_set(v___x_3331_, 1, v___x_3330_);
v___x_3332_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__3, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__3_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__3);
v___x_3333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3333_, 0, v___x_3331_);
lean_ctor_set(v___x_3333_, 1, v___x_3332_);
v___x_3334_ = l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__3___redArg(v_cls_3313_, v___x_3333_, v___y_3317_, v___y_3321_, v___y_3320_, v___y_3318_);
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_object* v_a_3335_; lean_object* v___x_3336_; 
v_a_3335_ = lean_ctor_get(v___x_3334_, 0);
lean_inc(v_a_3335_);
lean_dec_ref(v___x_3334_);
lean_inc(v___y_3318_);
lean_inc_ref(v___y_3320_);
lean_inc(v___y_3321_);
lean_inc_ref(v___y_3317_);
lean_inc(v___y_3322_);
lean_inc_ref(v___y_3319_);
v___x_3336_ = lean_apply_8(v___y_3315_, v_a_3335_, v___y_3319_, v___y_3322_, v___y_3317_, v___y_3321_, v___y_3320_, v___y_3318_, lean_box(0));
v___y_3307_ = v___y_3317_;
v___y_3308_ = v___y_3318_;
v___y_3309_ = v___y_3320_;
v___y_3310_ = v___y_3321_;
v___y_3311_ = v___x_3336_;
goto v___jp_3306_;
}
else
{
lean_object* v_a_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3344_; 
lean_dec_ref(v___y_3315_);
lean_dec_ref(v_xs_3288_);
v_a_3337_ = lean_ctor_get(v___x_3334_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3339_ = v___x_3334_;
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_a_3337_);
lean_dec(v___x_3334_);
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
v_reuseFailAlloc_3343_ = lean_alloc_ctor(1, 1, 0);
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
}
}
else
{
lean_dec_ref(v___y_3315_);
lean_dec_ref(v_xs_3288_);
lean_dec(v_declName_3282_);
return v___y_3316_;
}
}
v___jp_3345_:
{
if (lean_obj_tag(v___y_3353_) == 0)
{
lean_object* v_a_3354_; 
lean_dec_ref(v___y_3346_);
lean_dec(v_declName_3282_);
v_a_3354_ = lean_ctor_get(v___y_3353_, 0);
lean_inc(v_a_3354_);
lean_dec_ref(v___y_3353_);
v_inst_3298_ = v_a_3354_;
v___y_3299_ = v___y_3347_;
v___y_3300_ = v___y_3352_;
v___y_3301_ = v___y_3350_;
v___y_3302_ = v___y_3348_;
goto v___jp_3297_;
}
else
{
lean_object* v_a_3355_; uint8_t v___x_3356_; 
v_a_3355_ = lean_ctor_get(v___y_3353_, 0);
v___x_3356_ = l_Lean_Exception_isInterrupt(v_a_3355_);
if (v___x_3356_ == 0)
{
uint8_t v___x_3357_; 
lean_inc(v_a_3355_);
v___x_3357_ = l_Lean_Exception_isRuntime(v_a_3355_);
v___y_3315_ = v___y_3346_;
v___y_3316_ = v___y_3353_;
v___y_3317_ = v___y_3347_;
v___y_3318_ = v___y_3348_;
v___y_3319_ = v___y_3349_;
v___y_3320_ = v___y_3350_;
v___y_3321_ = v___y_3352_;
v___y_3322_ = v___y_3351_;
v___y_3323_ = v___x_3357_;
goto v___jp_3314_;
}
else
{
v___y_3315_ = v___y_3346_;
v___y_3316_ = v___y_3353_;
v___y_3317_ = v___y_3347_;
v___y_3318_ = v___y_3348_;
v___y_3319_ = v___y_3349_;
v___y_3320_ = v___y_3350_;
v___y_3321_ = v___y_3352_;
v___y_3322_ = v___y_3351_;
v___y_3323_ = v___x_3356_;
goto v___jp_3314_;
}
}
}
v___jp_3358_:
{
lean_object* v___x_3365_; 
lean_inc_ref(v_type_3283_);
v___x_3365_ = l_Lean_Meta_instantiateForall(v_type_3283_, v_xs_3288_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
if (lean_obj_tag(v___x_3365_) == 0)
{
switch(v_fixpointType_3284_)
{
case 0:
{
lean_object* v_a_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___f_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; 
lean_dec_ref(v___f_3286_);
lean_dec_ref(v___f_3285_);
v_a_3366_ = lean_ctor_get(v___x_3365_, 0);
lean_inc(v_a_3366_);
lean_dec_ref(v___x_3365_);
v___x_3367_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__2));
v___x_3368_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__3));
lean_inc_ref(v_xs_3288_);
lean_inc(v_declName_3282_);
v___f_3369_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__2___boxed), 13, 5);
lean_closure_set(v___f_3369_, 0, v_declName_3282_);
lean_closure_set(v___f_3369_, 1, v_type_3283_);
lean_closure_set(v___f_3369_, 2, v_xs_3288_);
lean_closure_set(v___f_3369_, 3, v___x_3367_);
lean_closure_set(v___f_3369_, 4, v___x_3368_);
v___x_3370_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___closed__5));
v___x_3371_ = lean_unsigned_to_nat(1u);
v___x_3372_ = lean_mk_empty_array_with_capacity(v___x_3371_);
v___x_3373_ = lean_array_push(v___x_3372_, v_a_3366_);
v___x_3374_ = l_Lean_Meta_mkAppM(v___x_3370_, v___x_3373_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
if (lean_obj_tag(v___x_3374_) == 0)
{
lean_object* v_a_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; 
v_a_3375_ = lean_ctor_get(v___x_3374_, 0);
lean_inc(v_a_3375_);
lean_dec_ref(v___x_3374_);
v___x_3376_ = lean_box(0);
v___x_3377_ = l_Lean_Meta_synthInstance(v_a_3375_, v___x_3376_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
v___y_3346_ = v___f_3369_;
v___y_3347_ = v___y_3361_;
v___y_3348_ = v___y_3364_;
v___y_3349_ = v___y_3359_;
v___y_3350_ = v___y_3363_;
v___y_3351_ = v___y_3360_;
v___y_3352_ = v___y_3362_;
v___y_3353_ = v___x_3377_;
goto v___jp_3345_;
}
else
{
v___y_3346_ = v___f_3369_;
v___y_3347_ = v___y_3361_;
v___y_3348_ = v___y_3364_;
v___y_3349_ = v___y_3359_;
v___y_3350_ = v___y_3363_;
v___y_3351_ = v___y_3360_;
v___y_3352_ = v___y_3362_;
v___y_3353_ = v___x_3374_;
goto v___jp_3345_;
}
}
case 1:
{
lean_object* v_a_3378_; lean_object* v___x_3379_; 
lean_dec_ref(v___f_3286_);
lean_dec_ref(v_type_3283_);
lean_dec(v_declName_3282_);
v_a_3378_ = lean_ctor_get(v___x_3365_, 0);
lean_inc(v_a_3378_);
lean_dec_ref(v___x_3365_);
v___x_3379_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__4___redArg(v_a_3378_, v___f_3285_, v_isZero_3281_, v_isZero_3281_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
if (lean_obj_tag(v___x_3379_) == 0)
{
lean_object* v_a_3380_; 
v_a_3380_ = lean_ctor_get(v___x_3379_, 0);
lean_inc(v_a_3380_);
lean_dec_ref(v___x_3379_);
v_inst_3298_ = v_a_3380_;
v___y_3299_ = v___y_3361_;
v___y_3300_ = v___y_3362_;
v___y_3301_ = v___y_3363_;
v___y_3302_ = v___y_3364_;
goto v___jp_3297_;
}
else
{
lean_dec_ref(v_xs_3288_);
return v___x_3379_;
}
}
default: 
{
lean_object* v_a_3381_; lean_object* v___x_3382_; 
lean_dec_ref(v___f_3285_);
lean_dec_ref(v_type_3283_);
lean_dec(v_declName_3282_);
v_a_3381_ = lean_ctor_get(v___x_3365_, 0);
lean_inc(v_a_3381_);
lean_dec_ref(v___x_3365_);
v___x_3382_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__4___redArg(v_a_3381_, v___f_3286_, v_isZero_3281_, v_isZero_3281_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v_a_3383_; 
v_a_3383_ = lean_ctor_get(v___x_3382_, 0);
lean_inc(v_a_3383_);
lean_dec_ref(v___x_3382_);
v_inst_3298_ = v_a_3383_;
v___y_3299_ = v___y_3361_;
v___y_3300_ = v___y_3362_;
v___y_3301_ = v___y_3363_;
v___y_3302_ = v___y_3364_;
goto v___jp_3297_;
}
else
{
lean_dec_ref(v_xs_3288_);
return v___x_3382_;
}
}
}
}
else
{
lean_dec_ref(v_xs_3288_);
lean_dec_ref(v___f_3286_);
lean_dec_ref(v___f_3285_);
lean_dec_ref(v_type_3283_);
lean_dec(v_declName_3282_);
return v___x_3365_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___boxed(lean_object* v_isZero_3410_, lean_object* v_declName_3411_, lean_object* v_type_3412_, lean_object* v_fixpointType_3413_, lean_object* v___f_3414_, lean_object* v___f_3415_, lean_object* v_value_3416_, lean_object* v_xs_3417_, lean_object* v___body_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_){
_start:
{
uint8_t v_isZero_boxed_3426_; uint8_t v_fixpointType_boxed_3427_; lean_object* v_res_3428_; 
v_isZero_boxed_3426_ = lean_unbox(v_isZero_3410_);
v_fixpointType_boxed_3427_ = lean_unbox(v_fixpointType_3413_);
v_res_3428_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3(v_isZero_boxed_3426_, v_declName_3411_, v_type_3412_, v_fixpointType_boxed_3427_, v___f_3414_, v___f_3415_, v_value_3416_, v_xs_3417_, v___body_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_);
lean_dec(v___y_3424_);
lean_dec_ref(v___y_3423_);
lean_dec(v___y_3422_);
lean_dec_ref(v___y_3421_);
lean_dec(v___y_3420_);
lean_dec_ref(v___y_3419_);
return v_res_3428_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11(lean_object* v_opts_3429_, lean_object* v_opt_3430_){
_start:
{
lean_object* v_name_3431_; lean_object* v_defValue_3432_; lean_object* v_map_3433_; lean_object* v___x_3434_; 
v_name_3431_ = lean_ctor_get(v_opt_3430_, 0);
v_defValue_3432_ = lean_ctor_get(v_opt_3430_, 1);
v_map_3433_ = lean_ctor_get(v_opts_3429_, 0);
v___x_3434_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3433_, v_name_3431_);
if (lean_obj_tag(v___x_3434_) == 0)
{
uint8_t v___x_3435_; 
v___x_3435_ = lean_unbox(v_defValue_3432_);
return v___x_3435_;
}
else
{
lean_object* v_val_3436_; 
v_val_3436_ = lean_ctor_get(v___x_3434_, 0);
lean_inc(v_val_3436_);
lean_dec_ref(v___x_3434_);
if (lean_obj_tag(v_val_3436_) == 1)
{
uint8_t v_v_3437_; 
v_v_3437_ = lean_ctor_get_uint8(v_val_3436_, 0);
lean_dec_ref(v_val_3436_);
return v_v_3437_;
}
else
{
uint8_t v___x_3438_; 
lean_dec(v_val_3436_);
v___x_3438_ = lean_unbox(v_defValue_3432_);
return v___x_3438_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___boxed(lean_object* v_opts_3439_, lean_object* v_opt_3440_){
_start:
{
uint8_t v_res_3441_; lean_object* v_r_3442_; 
v_res_3441_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11(v_opts_3439_, v_opt_3440_);
lean_dec_ref(v_opt_3440_);
lean_dec_ref(v_opts_3439_);
v_r_3442_ = lean_box(v_res_3441_);
return v_r_3442_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__12___closed__0(void){
_start:
{
lean_object* v___x_3443_; lean_object* v___x_3444_; 
v___x_3443_ = lean_box(1);
v___x_3444_ = l_Lean_MessageData_ofFormat(v___x_3443_);
return v___x_3444_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__12___closed__3(void){
_start:
{
lean_object* v___x_3448_; lean_object* v___x_3449_; 
v___x_3448_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__12___closed__2));
v___x_3449_ = l_Lean_MessageData_ofFormat(v___x_3448_);
return v___x_3449_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__12(lean_object* v_x_3450_, lean_object* v_x_3451_){
_start:
{
if (lean_obj_tag(v_x_3451_) == 0)
{
return v_x_3450_;
}
else
{
lean_object* v_head_3452_; lean_object* v_tail_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3475_; 
v_head_3452_ = lean_ctor_get(v_x_3451_, 0);
v_tail_3453_ = lean_ctor_get(v_x_3451_, 1);
v_isSharedCheck_3475_ = !lean_is_exclusive(v_x_3451_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3455_ = v_x_3451_;
v_isShared_3456_ = v_isSharedCheck_3475_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_tail_3453_);
lean_inc(v_head_3452_);
lean_dec(v_x_3451_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3475_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v_before_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3473_; 
v_before_3457_ = lean_ctor_get(v_head_3452_, 0);
v_isSharedCheck_3473_ = !lean_is_exclusive(v_head_3452_);
if (v_isSharedCheck_3473_ == 0)
{
lean_object* v_unused_3474_; 
v_unused_3474_ = lean_ctor_get(v_head_3452_, 1);
lean_dec(v_unused_3474_);
v___x_3459_ = v_head_3452_;
v_isShared_3460_ = v_isSharedCheck_3473_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_before_3457_);
lean_dec(v_head_3452_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3473_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3461_; lean_object* v___x_3463_; 
v___x_3461_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__12___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__12___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__12___closed__0);
if (v_isShared_3460_ == 0)
{
lean_ctor_set_tag(v___x_3459_, 7);
lean_ctor_set(v___x_3459_, 1, v___x_3461_);
lean_ctor_set(v___x_3459_, 0, v_x_3450_);
v___x_3463_ = v___x_3459_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_x_3450_);
lean_ctor_set(v_reuseFailAlloc_3472_, 1, v___x_3461_);
v___x_3463_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
lean_object* v___x_3464_; lean_object* v___x_3466_; 
v___x_3464_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__12___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__12___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__12___closed__3);
if (v_isShared_3456_ == 0)
{
lean_ctor_set_tag(v___x_3455_, 7);
lean_ctor_set(v___x_3455_, 1, v___x_3464_);
lean_ctor_set(v___x_3455_, 0, v___x_3463_);
v___x_3466_ = v___x_3455_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v___x_3463_);
lean_ctor_set(v_reuseFailAlloc_3471_, 1, v___x_3464_);
v___x_3466_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; 
v___x_3467_ = l_Lean_MessageData_ofSyntax(v_before_3457_);
v___x_3468_ = l_Lean_indentD(v___x_3467_);
v___x_3469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3466_);
lean_ctor_set(v___x_3469_, 1, v___x_3468_);
v_x_3450_ = v___x_3469_;
v_x_3451_ = v_tail_3453_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_3479_; lean_object* v___x_3480_; 
v___x_3479_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__1));
v___x_3480_ = l_Lean_MessageData_ofFormat(v___x_3479_);
return v___x_3480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg(lean_object* v_msgData_3481_, lean_object* v_macroStack_3482_, lean_object* v___y_3483_){
_start:
{
lean_object* v_options_3485_; lean_object* v___x_3486_; uint8_t v___x_3487_; 
v_options_3485_ = lean_ctor_get(v___y_3483_, 2);
v___x_3486_ = l_Lean_Elab_pp_macroStack;
v___x_3487_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11(v_options_3485_, v___x_3486_);
if (v___x_3487_ == 0)
{
lean_object* v___x_3488_; 
lean_dec(v_macroStack_3482_);
v___x_3488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3488_, 0, v_msgData_3481_);
return v___x_3488_;
}
else
{
if (lean_obj_tag(v_macroStack_3482_) == 0)
{
lean_object* v___x_3489_; 
v___x_3489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3489_, 0, v_msgData_3481_);
return v___x_3489_;
}
else
{
lean_object* v_head_3490_; lean_object* v_after_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3506_; 
v_head_3490_ = lean_ctor_get(v_macroStack_3482_, 0);
lean_inc(v_head_3490_);
v_after_3491_ = lean_ctor_get(v_head_3490_, 1);
v_isSharedCheck_3506_ = !lean_is_exclusive(v_head_3490_);
if (v_isSharedCheck_3506_ == 0)
{
lean_object* v_unused_3507_; 
v_unused_3507_ = lean_ctor_get(v_head_3490_, 0);
lean_dec(v_unused_3507_);
v___x_3493_ = v_head_3490_;
v_isShared_3494_ = v_isSharedCheck_3506_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_after_3491_);
lean_dec(v_head_3490_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3506_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3495_; lean_object* v___x_3497_; 
v___x_3495_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__12___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__12___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__12___closed__0);
if (v_isShared_3494_ == 0)
{
lean_ctor_set_tag(v___x_3493_, 7);
lean_ctor_set(v___x_3493_, 1, v___x_3495_);
lean_ctor_set(v___x_3493_, 0, v_msgData_3481_);
v___x_3497_ = v___x_3493_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_msgData_3481_);
lean_ctor_set(v_reuseFailAlloc_3505_, 1, v___x_3495_);
v___x_3497_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v_msgData_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___x_3498_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__2);
v___x_3499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3497_);
lean_ctor_set(v___x_3499_, 1, v___x_3498_);
v___x_3500_ = l_Lean_MessageData_ofSyntax(v_after_3491_);
v___x_3501_ = l_Lean_indentD(v___x_3500_);
v_msgData_3502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_3502_, 0, v___x_3499_);
lean_ctor_set(v_msgData_3502_, 1, v___x_3501_);
v___x_3503_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__12(v_msgData_3502_, v_macroStack_3482_);
v___x_3504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3504_, 0, v___x_3503_);
return v___x_3504_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_3508_, lean_object* v_macroStack_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_){
_start:
{
lean_object* v_res_3512_; 
v_res_3512_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg(v_msgData_3508_, v_macroStack_3509_, v___y_3510_);
lean_dec_ref(v___y_3510_);
return v_res_3512_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___redArg(lean_object* v_msg_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_){
_start:
{
lean_object* v_ref_3521_; lean_object* v___x_3522_; lean_object* v_a_3523_; lean_object* v_macroStack_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v_a_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3535_; 
v_ref_3521_ = lean_ctor_get(v___y_3518_, 5);
v___x_3522_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6_spec__7(v_msg_3513_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_);
v_a_3523_ = lean_ctor_get(v___x_3522_, 0);
lean_inc(v_a_3523_);
lean_dec_ref(v___x_3522_);
v_macroStack_3524_ = lean_ctor_get(v___y_3514_, 1);
lean_inc(v_macroStack_3524_);
lean_dec_ref(v___y_3514_);
lean_inc(v_macroStack_3524_);
v___x_3525_ = l_Lean_Elab_getBetterRef(v_ref_3521_, v_macroStack_3524_);
v___x_3526_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg(v_a_3523_, v_macroStack_3524_, v___y_3518_);
v_a_3527_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3535_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3529_ = v___x_3526_;
v_isShared_3530_ = v_isSharedCheck_3535_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_a_3527_);
lean_dec(v___x_3526_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3535_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
lean_object* v___x_3531_; lean_object* v___x_3533_; 
v___x_3531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3531_, 0, v___x_3525_);
lean_ctor_set(v___x_3531_, 1, v_a_3527_);
if (v_isShared_3530_ == 0)
{
lean_ctor_set_tag(v___x_3529_, 1);
lean_ctor_set(v___x_3529_, 0, v___x_3531_);
v___x_3533_ = v___x_3529_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v___x_3531_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
return v___x_3533_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___redArg___boxed(lean_object* v_msg_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_){
_start:
{
lean_object* v_res_3544_; 
v_res_3544_ = l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___redArg(v_msg_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_);
lean_dec(v___y_3542_);
lean_dec_ref(v___y_3541_);
lean_dec(v___y_3540_);
lean_dec_ref(v___y_3539_);
lean_dec(v___y_3538_);
return v_res_3544_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3552_ = lean_box(0);
v___x_3553_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___closed__2));
v___x_3554_ = l_Lean_mkConst(v___x_3553_, v___x_3552_);
return v___x_3554_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3556_; lean_object* v___x_3557_; 
v___x_3556_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___closed__4));
v___x_3557_ = l_Lean_stringToMessageData(v___x_3556_);
return v___x_3557_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0(lean_object* v_xs_3558_, lean_object* v_e_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_){
_start:
{
uint8_t v___x_3570_; 
v___x_3570_ = l_Lean_Expr_isProp(v_e_3559_);
if (v___x_3570_ == 0)
{
lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v_a_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3580_; 
lean_dec_ref(v_xs_3558_);
v___x_3571_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___closed__5, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___closed__5_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___closed__5);
lean_inc_ref(v___y_3560_);
v___x_3572_ = l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___redArg(v___x_3571_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_);
v_a_3573_ = lean_ctor_get(v___x_3572_, 0);
v_isSharedCheck_3580_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3575_ = v___x_3572_;
v_isShared_3576_ = v_isSharedCheck_3580_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_a_3573_);
lean_dec(v___x_3572_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3580_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v___x_3578_; 
if (v_isShared_3576_ == 0)
{
v___x_3578_ = v___x_3575_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_a_3573_);
v___x_3578_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
return v___x_3578_;
}
}
}
else
{
goto v___jp_3567_;
}
v___jp_3567_:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3568_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___closed__3, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___closed__3_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___closed__3);
v___x_3569_ = l_Lean_Meta_mkInstPiOfInstsForall(v_xs_3558_, v___x_3568_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_);
return v___x_3569_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0___boxed(lean_object* v_xs_3581_, lean_object* v_e_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_){
_start:
{
lean_object* v_res_3590_; 
v_res_3590_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__0(v_xs_3581_, v_e_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec(v___y_3586_);
lean_dec_ref(v___y_3585_);
lean_dec(v___y_3584_);
lean_dec_ref(v___y_3583_);
lean_dec_ref(v_e_3582_);
return v_res_3590_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__1___closed__2(void){
_start:
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3597_ = lean_box(0);
v___x_3598_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__1___closed__1));
v___x_3599_ = l_Lean_mkConst(v___x_3598_, v___x_3597_);
return v___x_3599_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__1___closed__4(void){
_start:
{
lean_object* v___x_3601_; lean_object* v___x_3602_; 
v___x_3601_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__1___closed__3));
v___x_3602_ = l_Lean_stringToMessageData(v___x_3601_);
return v___x_3602_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__1(lean_object* v_xs_3603_, lean_object* v_e_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_){
_start:
{
uint8_t v___x_3615_; 
v___x_3615_ = l_Lean_Expr_isProp(v_e_3604_);
if (v___x_3615_ == 0)
{
lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v_a_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3625_; 
lean_dec_ref(v_xs_3603_);
v___x_3616_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__1___closed__4, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__1___closed__4_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__1___closed__4);
lean_inc_ref(v___y_3605_);
v___x_3617_ = l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___redArg(v___x_3616_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_);
v_a_3618_ = lean_ctor_get(v___x_3617_, 0);
v_isSharedCheck_3625_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3620_ = v___x_3617_;
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_a_3618_);
lean_dec(v___x_3617_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3623_; 
if (v_isShared_3621_ == 0)
{
v___x_3623_ = v___x_3620_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_a_3618_);
v___x_3623_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
return v___x_3623_;
}
}
}
else
{
goto v___jp_3612_;
}
v___jp_3612_:
{
lean_object* v___x_3613_; lean_object* v___x_3614_; 
v___x_3613_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__1___closed__2, &l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__1___closed__2_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__1___closed__2);
v___x_3614_ = l_Lean_Meta_mkInstPiOfInstsForall(v_xs_3603_, v___x_3613_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_);
return v___x_3614_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__1___boxed(lean_object* v_xs_3626_, lean_object* v_e_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_){
_start:
{
lean_object* v_res_3635_; 
v_res_3635_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__1(v_xs_3626_, v_e_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
lean_dec(v___y_3631_);
lean_dec_ref(v___y_3630_);
lean_dec(v___y_3629_);
lean_dec_ref(v___y_3628_);
lean_dec_ref(v_e_3627_);
return v_res_3635_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg(lean_object* v_hints_3638_, lean_object* v_as_3639_, lean_object* v_i_3640_, lean_object* v_j_3641_, lean_object* v_bs_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_){
_start:
{
lean_object* v_zero_3650_; uint8_t v_isZero_3651_; 
v_zero_3650_ = lean_unsigned_to_nat(0u);
v_isZero_3651_ = lean_nat_dec_eq(v_i_3640_, v_zero_3650_);
if (v_isZero_3651_ == 1)
{
lean_object* v___x_3652_; 
lean_dec(v_j_3641_);
lean_dec(v_i_3640_);
v___x_3652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3652_, 0, v_bs_3642_);
return v___x_3652_;
}
else
{
lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v_ref_3655_; uint8_t v_fixpointType_3656_; lean_object* v___x_3657_; lean_object* v_declName_3658_; lean_object* v_type_3659_; lean_object* v_value_3660_; lean_object* v_fileName_3661_; lean_object* v_fileMap_3662_; lean_object* v_options_3663_; lean_object* v_currRecDepth_3664_; lean_object* v_maxRecDepth_3665_; lean_object* v_ref_3666_; lean_object* v_currNamespace_3667_; lean_object* v_openDecls_3668_; lean_object* v_initHeartbeats_3669_; lean_object* v_maxHeartbeats_3670_; lean_object* v_quotContext_3671_; lean_object* v_currMacroScope_3672_; uint8_t v_diag_3673_; lean_object* v_cancelTk_x3f_3674_; uint8_t v_suppressElabErrors_3675_; lean_object* v_inheritedTraceOptions_3676_; lean_object* v___f_3677_; lean_object* v___f_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___f_3681_; lean_object* v_ref_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; 
v___x_3653_ = l_Lean_Elab_instInhabitedPartialFixpoint_default;
v___x_3654_ = lean_array_get_borrowed(v___x_3653_, v_hints_3638_, v_j_3641_);
v_ref_3655_ = lean_ctor_get(v___x_3654_, 0);
v_fixpointType_3656_ = lean_ctor_get_uint8(v___x_3654_, sizeof(void*)*2);
v___x_3657_ = lean_array_fget_borrowed(v_as_3639_, v_j_3641_);
v_declName_3658_ = lean_ctor_get(v___x_3657_, 3);
v_type_3659_ = lean_ctor_get(v___x_3657_, 6);
v_value_3660_ = lean_ctor_get(v___x_3657_, 7);
v_fileName_3661_ = lean_ctor_get(v___y_3647_, 0);
v_fileMap_3662_ = lean_ctor_get(v___y_3647_, 1);
v_options_3663_ = lean_ctor_get(v___y_3647_, 2);
v_currRecDepth_3664_ = lean_ctor_get(v___y_3647_, 3);
v_maxRecDepth_3665_ = lean_ctor_get(v___y_3647_, 4);
v_ref_3666_ = lean_ctor_get(v___y_3647_, 5);
v_currNamespace_3667_ = lean_ctor_get(v___y_3647_, 6);
v_openDecls_3668_ = lean_ctor_get(v___y_3647_, 7);
v_initHeartbeats_3669_ = lean_ctor_get(v___y_3647_, 8);
v_maxHeartbeats_3670_ = lean_ctor_get(v___y_3647_, 9);
v_quotContext_3671_ = lean_ctor_get(v___y_3647_, 10);
v_currMacroScope_3672_ = lean_ctor_get(v___y_3647_, 11);
v_diag_3673_ = lean_ctor_get_uint8(v___y_3647_, sizeof(void*)*14);
v_cancelTk_x3f_3674_ = lean_ctor_get(v___y_3647_, 12);
v_suppressElabErrors_3675_ = lean_ctor_get_uint8(v___y_3647_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3676_ = lean_ctor_get(v___y_3647_, 13);
v___f_3677_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___closed__0));
v___f_3678_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___closed__1));
v___x_3679_ = lean_box(v_isZero_3651_);
v___x_3680_ = lean_box(v_fixpointType_3656_);
lean_inc_ref(v_value_3660_);
lean_inc_ref(v_type_3659_);
lean_inc(v_declName_3658_);
v___f_3681_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___lam__3___boxed), 16, 7);
lean_closure_set(v___f_3681_, 0, v___x_3679_);
lean_closure_set(v___f_3681_, 1, v_declName_3658_);
lean_closure_set(v___f_3681_, 2, v_type_3659_);
lean_closure_set(v___f_3681_, 3, v___x_3680_);
lean_closure_set(v___f_3681_, 4, v___f_3677_);
lean_closure_set(v___f_3681_, 5, v___f_3678_);
lean_closure_set(v___f_3681_, 6, v_value_3660_);
v_ref_3682_ = l_Lean_replaceRef(v_ref_3655_, v_ref_3666_);
lean_inc_ref(v_inheritedTraceOptions_3676_);
lean_inc(v_cancelTk_x3f_3674_);
lean_inc(v_currMacroScope_3672_);
lean_inc(v_quotContext_3671_);
lean_inc(v_maxHeartbeats_3670_);
lean_inc(v_initHeartbeats_3669_);
lean_inc(v_openDecls_3668_);
lean_inc(v_currNamespace_3667_);
lean_inc(v_maxRecDepth_3665_);
lean_inc(v_currRecDepth_3664_);
lean_inc_ref(v_options_3663_);
lean_inc_ref(v_fileMap_3662_);
lean_inc_ref(v_fileName_3661_);
v___x_3683_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3683_, 0, v_fileName_3661_);
lean_ctor_set(v___x_3683_, 1, v_fileMap_3662_);
lean_ctor_set(v___x_3683_, 2, v_options_3663_);
lean_ctor_set(v___x_3683_, 3, v_currRecDepth_3664_);
lean_ctor_set(v___x_3683_, 4, v_maxRecDepth_3665_);
lean_ctor_set(v___x_3683_, 5, v_ref_3682_);
lean_ctor_set(v___x_3683_, 6, v_currNamespace_3667_);
lean_ctor_set(v___x_3683_, 7, v_openDecls_3668_);
lean_ctor_set(v___x_3683_, 8, v_initHeartbeats_3669_);
lean_ctor_set(v___x_3683_, 9, v_maxHeartbeats_3670_);
lean_ctor_set(v___x_3683_, 10, v_quotContext_3671_);
lean_ctor_set(v___x_3683_, 11, v_currMacroScope_3672_);
lean_ctor_set(v___x_3683_, 12, v_cancelTk_x3f_3674_);
lean_ctor_set(v___x_3683_, 13, v_inheritedTraceOptions_3676_);
lean_ctor_set_uint8(v___x_3683_, sizeof(void*)*14, v_diag_3673_);
lean_ctor_set_uint8(v___x_3683_, sizeof(void*)*14 + 1, v_suppressElabErrors_3675_);
lean_inc_ref(v_value_3660_);
v___x_3684_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__6___redArg(v_value_3660_, v___f_3681_, v_isZero_3651_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___x_3683_, v___y_3648_);
lean_dec_ref(v___x_3683_);
if (lean_obj_tag(v___x_3684_) == 0)
{
lean_object* v_a_3685_; lean_object* v_one_3686_; lean_object* v_n_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; 
v_a_3685_ = lean_ctor_get(v___x_3684_, 0);
lean_inc(v_a_3685_);
lean_dec_ref(v___x_3684_);
v_one_3686_ = lean_unsigned_to_nat(1u);
v_n_3687_ = lean_nat_sub(v_i_3640_, v_one_3686_);
lean_dec(v_i_3640_);
v___x_3688_ = lean_nat_add(v_j_3641_, v_one_3686_);
lean_dec(v_j_3641_);
v___x_3689_ = lean_array_push(v_bs_3642_, v_a_3685_);
v_i_3640_ = v_n_3687_;
v_j_3641_ = v___x_3688_;
v_bs_3642_ = v___x_3689_;
goto _start;
}
else
{
lean_object* v_a_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3698_; 
lean_dec_ref(v_bs_3642_);
lean_dec(v_j_3641_);
lean_dec(v_i_3640_);
v_a_3691_ = lean_ctor_get(v___x_3684_, 0);
v_isSharedCheck_3698_ = !lean_is_exclusive(v___x_3684_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3693_ = v___x_3684_;
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_a_3691_);
lean_dec(v___x_3684_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___x_3696_; 
if (v_isShared_3694_ == 0)
{
v___x_3696_ = v___x_3693_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_a_3691_);
v___x_3696_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
return v___x_3696_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg___boxed(lean_object* v_hints_3699_, lean_object* v_as_3700_, lean_object* v_i_3701_, lean_object* v_j_3702_, lean_object* v_bs_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_){
_start:
{
lean_object* v_res_3711_; 
v_res_3711_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg(v_hints_3699_, v_as_3700_, v_i_3701_, v_j_3702_, v_bs_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_);
lean_dec(v___y_3709_);
lean_dec_ref(v___y_3708_);
lean_dec(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec_ref(v_as_3700_);
lean_dec_ref(v_hints_3699_);
return v_res_3711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0_spec__0(lean_object* v_as_3712_, size_t v_i_3713_, size_t v_stop_3714_, lean_object* v_b_3715_){
_start:
{
lean_object* v___y_3717_; uint8_t v___x_3721_; 
v___x_3721_ = lean_usize_dec_eq(v_i_3713_, v_stop_3714_);
if (v___x_3721_ == 0)
{
lean_object* v___x_3722_; lean_object* v_termination_3723_; lean_object* v_partialFixpoint_x3f_3724_; 
v___x_3722_ = lean_array_uget_borrowed(v_as_3712_, v_i_3713_);
v_termination_3723_ = lean_ctor_get(v___x_3722_, 8);
v_partialFixpoint_x3f_3724_ = lean_ctor_get(v_termination_3723_, 3);
if (lean_obj_tag(v_partialFixpoint_x3f_3724_) == 0)
{
v___y_3717_ = v_b_3715_;
goto v___jp_3716_;
}
else
{
lean_object* v_val_3725_; lean_object* v___x_3726_; 
v_val_3725_ = lean_ctor_get(v_partialFixpoint_x3f_3724_, 0);
lean_inc(v_val_3725_);
v___x_3726_ = lean_array_push(v_b_3715_, v_val_3725_);
v___y_3717_ = v___x_3726_;
goto v___jp_3716_;
}
}
else
{
return v_b_3715_;
}
v___jp_3716_:
{
size_t v___x_3718_; size_t v___x_3719_; 
v___x_3718_ = ((size_t)1ULL);
v___x_3719_ = lean_usize_add(v_i_3713_, v___x_3718_);
v_i_3713_ = v___x_3719_;
v_b_3715_ = v___y_3717_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0_spec__0___boxed(lean_object* v_as_3727_, lean_object* v_i_3728_, lean_object* v_stop_3729_, lean_object* v_b_3730_){
_start:
{
size_t v_i_boxed_3731_; size_t v_stop_boxed_3732_; lean_object* v_res_3733_; 
v_i_boxed_3731_ = lean_unbox_usize(v_i_3728_);
lean_dec(v_i_3728_);
v_stop_boxed_3732_ = lean_unbox_usize(v_stop_3729_);
lean_dec(v_stop_3729_);
v_res_3733_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0_spec__0(v_as_3727_, v_i_boxed_3731_, v_stop_boxed_3732_, v_b_3730_);
lean_dec_ref(v_as_3727_);
return v_res_3733_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0(lean_object* v_as_3736_, lean_object* v_start_3737_, lean_object* v_stop_3738_){
_start:
{
lean_object* v___x_3739_; uint8_t v___x_3740_; 
v___x_3739_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0___closed__0));
v___x_3740_ = lean_nat_dec_lt(v_start_3737_, v_stop_3738_);
if (v___x_3740_ == 0)
{
return v___x_3739_;
}
else
{
lean_object* v___x_3741_; uint8_t v___x_3742_; 
v___x_3741_ = lean_array_get_size(v_as_3736_);
v___x_3742_ = lean_nat_dec_le(v_stop_3738_, v___x_3741_);
if (v___x_3742_ == 0)
{
uint8_t v___x_3743_; 
v___x_3743_ = lean_nat_dec_lt(v_start_3737_, v___x_3741_);
if (v___x_3743_ == 0)
{
return v___x_3739_;
}
else
{
size_t v___x_3744_; size_t v___x_3745_; lean_object* v___x_3746_; 
v___x_3744_ = lean_usize_of_nat(v_start_3737_);
v___x_3745_ = lean_usize_of_nat(v___x_3741_);
v___x_3746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0_spec__0(v_as_3736_, v___x_3744_, v___x_3745_, v___x_3739_);
return v___x_3746_;
}
}
else
{
size_t v___x_3747_; size_t v___x_3748_; lean_object* v___x_3749_; 
v___x_3747_ = lean_usize_of_nat(v_start_3737_);
v___x_3748_ = lean_usize_of_nat(v_stop_3738_);
v___x_3749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0_spec__0(v_as_3736_, v___x_3747_, v___x_3748_, v___x_3739_);
return v___x_3749_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0___boxed(lean_object* v_as_3750_, lean_object* v_start_3751_, lean_object* v_stop_3752_){
_start:
{
lean_object* v_res_3753_; 
v_res_3753_ = l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0(v_as_3750_, v_start_3751_, v_stop_3752_);
lean_dec(v_stop_3752_);
lean_dec(v_start_3751_);
lean_dec_ref(v_as_3750_);
return v_res_3753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__8(size_t v_sz_3754_, size_t v_i_3755_, lean_object* v_bs_3756_){
_start:
{
uint8_t v___x_3757_; 
v___x_3757_ = lean_usize_dec_lt(v_i_3755_, v_sz_3754_);
if (v___x_3757_ == 0)
{
return v_bs_3756_;
}
else
{
lean_object* v_v_3758_; lean_object* v_declName_3759_; lean_object* v___x_3760_; lean_object* v_bs_x27_3761_; size_t v___x_3762_; size_t v___x_3763_; lean_object* v___x_3764_; 
v_v_3758_ = lean_array_uget_borrowed(v_bs_3756_, v_i_3755_);
v_declName_3759_ = lean_ctor_get(v_v_3758_, 3);
lean_inc(v_declName_3759_);
v___x_3760_ = lean_unsigned_to_nat(0u);
v_bs_x27_3761_ = lean_array_uset(v_bs_3756_, v_i_3755_, v___x_3760_);
v___x_3762_ = ((size_t)1ULL);
v___x_3763_ = lean_usize_add(v_i_3755_, v___x_3762_);
v___x_3764_ = lean_array_uset(v_bs_x27_3761_, v_i_3755_, v_declName_3759_);
v_i_3755_ = v___x_3763_;
v_bs_3756_ = v___x_3764_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__8___boxed(lean_object* v_sz_3766_, lean_object* v_i_3767_, lean_object* v_bs_3768_){
_start:
{
size_t v_sz_boxed_3769_; size_t v_i_boxed_3770_; lean_object* v_res_3771_; 
v_sz_boxed_3769_ = lean_unbox_usize(v_sz_3766_);
lean_dec(v_sz_3766_);
v_i_boxed_3770_ = lean_unbox_usize(v_i_3767_);
lean_dec(v_i_3767_);
v_res_3771_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__8(v_sz_boxed_3769_, v_i_boxed_3770_, v_bs_3768_);
return v_res_3771_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27_spec__32(lean_object* v_as_3772_, size_t v_i_3773_, size_t v_stop_3774_){
_start:
{
uint8_t v___x_3775_; 
v___x_3775_ = lean_usize_dec_eq(v_i_3773_, v_stop_3774_);
if (v___x_3775_ == 0)
{
lean_object* v___x_3776_; uint8_t v_fixpointType_3777_; uint8_t v___x_3778_; 
v___x_3776_ = lean_array_uget_borrowed(v_as_3772_, v_i_3773_);
v_fixpointType_3777_ = lean_ctor_get_uint8(v___x_3776_, sizeof(void*)*2);
v___x_3778_ = l_Lean_Elab_isLatticeTheoretic(v_fixpointType_3777_);
if (v___x_3778_ == 0)
{
size_t v___x_3779_; size_t v___x_3780_; 
v___x_3779_ = ((size_t)1ULL);
v___x_3780_ = lean_usize_add(v_i_3773_, v___x_3779_);
v_i_3773_ = v___x_3780_;
goto _start;
}
else
{
return v___x_3778_;
}
}
else
{
uint8_t v___x_3782_; 
v___x_3782_ = 0;
return v___x_3782_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27_spec__32___boxed(lean_object* v_as_3783_, lean_object* v_i_3784_, lean_object* v_stop_3785_){
_start:
{
size_t v_i_boxed_3786_; size_t v_stop_boxed_3787_; uint8_t v_res_3788_; lean_object* v_r_3789_; 
v_i_boxed_3786_ = lean_unbox_usize(v_i_3784_);
lean_dec(v_i_3784_);
v_stop_boxed_3787_ = lean_unbox_usize(v_stop_3785_);
lean_dec(v_stop_3785_);
v_res_3788_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27_spec__32(v_as_3783_, v_i_boxed_3786_, v_stop_boxed_3787_);
lean_dec_ref(v_as_3783_);
v_r_3789_ = lean_box(v_res_3788_);
return v_r_3789_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27(lean_object* v_as_3790_, size_t v_i_3791_, size_t v_stop_3792_){
_start:
{
uint8_t v___x_3793_; 
v___x_3793_ = lean_usize_dec_eq(v_i_3791_, v_stop_3792_);
if (v___x_3793_ == 0)
{
lean_object* v___x_3794_; uint8_t v_fixpointType_3795_; uint8_t v___x_3796_; 
v___x_3794_ = lean_array_uget_borrowed(v_as_3790_, v_i_3791_);
v_fixpointType_3795_ = lean_ctor_get_uint8(v___x_3794_, sizeof(void*)*2);
v___x_3796_ = l_Lean_Elab_isLatticeTheoretic(v_fixpointType_3795_);
if (v___x_3796_ == 0)
{
size_t v___x_3797_; size_t v___x_3798_; uint8_t v___x_3799_; 
v___x_3797_ = ((size_t)1ULL);
v___x_3798_ = lean_usize_add(v_i_3791_, v___x_3797_);
v___x_3799_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27_spec__32(v_as_3790_, v___x_3798_, v_stop_3792_);
return v___x_3799_;
}
else
{
return v___x_3796_;
}
}
else
{
uint8_t v___x_3800_; 
v___x_3800_ = 0;
return v___x_3800_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27___boxed(lean_object* v_as_3801_, lean_object* v_i_3802_, lean_object* v_stop_3803_){
_start:
{
size_t v_i_boxed_3804_; size_t v_stop_boxed_3805_; uint8_t v_res_3806_; lean_object* v_r_3807_; 
v_i_boxed_3804_ = lean_unbox_usize(v_i_3802_);
lean_dec(v_i_3802_);
v_stop_boxed_3805_ = lean_unbox_usize(v_stop_3803_);
lean_dec(v_stop_3803_);
v_res_3806_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27(v_as_3801_, v_i_boxed_3804_, v_stop_boxed_3805_);
lean_dec_ref(v_as_3801_);
v_r_3807_ = lean_box(v_res_3806_);
return v_r_3807_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__28_spec__34(uint8_t v___x_3808_, lean_object* v_as_3809_, size_t v_i_3810_, size_t v_stop_3811_){
_start:
{
uint8_t v___x_3812_; 
v___x_3812_ = lean_usize_dec_eq(v_i_3810_, v_stop_3811_);
if (v___x_3812_ == 0)
{
lean_object* v___x_3813_; uint8_t v_fixpointType_3814_; uint8_t v___x_3815_; uint8_t v___y_3817_; uint8_t v___x_3821_; 
v___x_3813_ = lean_array_uget_borrowed(v_as_3809_, v_i_3810_);
v_fixpointType_3814_ = lean_ctor_get_uint8(v___x_3813_, sizeof(void*)*2);
v___x_3815_ = 1;
v___x_3821_ = l_Lean_Elab_isLatticeTheoretic(v_fixpointType_3814_);
if (v___x_3821_ == 0)
{
v___y_3817_ = v___x_3808_;
goto v___jp_3816_;
}
else
{
v___y_3817_ = v___x_3812_;
goto v___jp_3816_;
}
v___jp_3816_:
{
if (v___y_3817_ == 0)
{
size_t v___x_3818_; size_t v___x_3819_; 
v___x_3818_ = ((size_t)1ULL);
v___x_3819_ = lean_usize_add(v_i_3810_, v___x_3818_);
v_i_3810_ = v___x_3819_;
goto _start;
}
else
{
return v___x_3815_;
}
}
}
else
{
uint8_t v___x_3822_; 
v___x_3822_ = 0;
return v___x_3822_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__28_spec__34___boxed(lean_object* v___x_3823_, lean_object* v_as_3824_, lean_object* v_i_3825_, lean_object* v_stop_3826_){
_start:
{
uint8_t v___x_56682__boxed_3827_; size_t v_i_boxed_3828_; size_t v_stop_boxed_3829_; uint8_t v_res_3830_; lean_object* v_r_3831_; 
v___x_56682__boxed_3827_ = lean_unbox(v___x_3823_);
v_i_boxed_3828_ = lean_unbox_usize(v_i_3825_);
lean_dec(v_i_3825_);
v_stop_boxed_3829_ = lean_unbox_usize(v_stop_3826_);
lean_dec(v_stop_3826_);
v_res_3830_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__28_spec__34(v___x_56682__boxed_3827_, v_as_3824_, v_i_boxed_3828_, v_stop_boxed_3829_);
lean_dec_ref(v_as_3824_);
v_r_3831_ = lean_box(v_res_3830_);
return v_r_3831_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__28(uint8_t v___x_3832_, lean_object* v_as_3833_, size_t v_i_3834_, size_t v_stop_3835_){
_start:
{
uint8_t v___x_3836_; 
v___x_3836_ = lean_usize_dec_eq(v_i_3834_, v_stop_3835_);
if (v___x_3836_ == 0)
{
lean_object* v___x_3837_; uint8_t v_fixpointType_3838_; uint8_t v___x_3839_; uint8_t v___y_3841_; uint8_t v___x_3845_; 
v___x_3837_ = lean_array_uget_borrowed(v_as_3833_, v_i_3834_);
v_fixpointType_3838_ = lean_ctor_get_uint8(v___x_3837_, sizeof(void*)*2);
v___x_3839_ = 1;
v___x_3845_ = l_Lean_Elab_isLatticeTheoretic(v_fixpointType_3838_);
if (v___x_3845_ == 0)
{
v___y_3841_ = v___x_3832_;
goto v___jp_3840_;
}
else
{
v___y_3841_ = v___x_3836_;
goto v___jp_3840_;
}
v___jp_3840_:
{
if (v___y_3841_ == 0)
{
size_t v___x_3842_; size_t v___x_3843_; uint8_t v___x_3844_; 
v___x_3842_ = ((size_t)1ULL);
v___x_3843_ = lean_usize_add(v_i_3834_, v___x_3842_);
v___x_3844_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__28_spec__34(v___x_3832_, v_as_3833_, v___x_3843_, v_stop_3835_);
return v___x_3844_;
}
else
{
return v___x_3839_;
}
}
}
else
{
uint8_t v___x_3846_; 
v___x_3846_ = 0;
return v___x_3846_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__28___boxed(lean_object* v___x_3847_, lean_object* v_as_3848_, lean_object* v_i_3849_, lean_object* v_stop_3850_){
_start:
{
uint8_t v___x_56705__boxed_3851_; size_t v_i_boxed_3852_; size_t v_stop_boxed_3853_; uint8_t v_res_3854_; lean_object* v_r_3855_; 
v___x_56705__boxed_3851_ = lean_unbox(v___x_3847_);
v_i_boxed_3852_ = lean_unbox_usize(v_i_3849_);
lean_dec(v_i_3849_);
v_stop_boxed_3853_ = lean_unbox_usize(v_stop_3850_);
lean_dec(v_stop_3850_);
v_res_3854_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__28(v___x_56705__boxed_3851_, v_as_3848_, v_i_boxed_3852_, v_stop_boxed_3853_);
lean_dec_ref(v_as_3848_);
v_r_3855_ = lean_box(v_res_3854_);
return v_r_3855_;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___closed__1(void){
_start:
{
lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; 
v___x_3857_ = ((lean_object*)(l_Lean_Elab_partialFixpoint___closed__0));
v___x_3858_ = lean_unsigned_to_nat(2u);
v___x_3859_ = lean_unsigned_to_nat(82u);
v___x_3860_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__7));
v___x_3861_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__0));
v___x_3862_ = l_mkPanicMessageWithDecl(v___x_3861_, v___x_3860_, v___x_3859_, v___x_3858_, v___x_3857_);
return v___x_3862_;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___closed__3(void){
_start:
{
lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; 
v___x_3864_ = ((lean_object*)(l_Lean_Elab_partialFixpoint___closed__2));
v___x_3865_ = lean_unsigned_to_nat(4u);
v___x_3866_ = lean_unsigned_to_nat(86u);
v___x_3867_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___lam__0___closed__7));
v___x_3868_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__0));
v___x_3869_ = l_mkPanicMessageWithDecl(v___x_3868_, v___x_3867_, v___x_3866_, v___x_3865_, v___x_3864_);
return v___x_3869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_partialFixpoint(lean_object* v_docCtx_3872_, lean_object* v_preDefs_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_, lean_object* v_a_3876_, lean_object* v_a_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_){
_start:
{
lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v_hints_3883_; lean_object* v___x_3884_; uint8_t v___x_3885_; lean_object* v___y_3887_; lean_object* v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; lean_object* v___y_3891_; lean_object* v___y_3892_; 
v___x_3881_ = lean_unsigned_to_nat(0u);
v___x_3882_ = lean_array_get_size(v_preDefs_3873_);
v_hints_3883_ = l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0(v_preDefs_3873_, v___x_3881_, v___x_3882_);
v___x_3884_ = lean_array_get_size(v_hints_3883_);
v___x_3885_ = lean_nat_dec_eq(v___x_3882_, v___x_3884_);
if (v___x_3885_ == 0)
{
lean_object* v___x_3928_; lean_object* v___x_3929_; 
lean_dec_ref(v_hints_3883_);
lean_dec_ref(v_preDefs_3873_);
lean_dec_ref(v_docCtx_3872_);
v___x_3928_ = lean_obj_once(&l_Lean_Elab_partialFixpoint___closed__1, &l_Lean_Elab_partialFixpoint___closed__1_once, _init_l_Lean_Elab_partialFixpoint___closed__1);
v___x_3929_ = l_panic___at___00Lean_Elab_partialFixpoint_spec__26(v___x_3928_, v_a_3874_, v_a_3875_, v_a_3876_, v_a_3877_, v_a_3878_, v_a_3879_);
return v___x_3929_;
}
else
{
uint8_t v___x_3930_; 
v___x_3930_ = lean_nat_dec_lt(v___x_3881_, v___x_3884_);
if (v___x_3930_ == 0)
{
v___y_3887_ = v_a_3874_;
v___y_3888_ = v_a_3875_;
v___y_3889_ = v_a_3876_;
v___y_3890_ = v_a_3877_;
v___y_3891_ = v_a_3878_;
v___y_3892_ = v_a_3879_;
goto v___jp_3886_;
}
else
{
if (v___x_3930_ == 0)
{
v___y_3887_ = v_a_3874_;
v___y_3888_ = v_a_3875_;
v___y_3889_ = v_a_3876_;
v___y_3890_ = v_a_3877_;
v___y_3891_ = v_a_3878_;
v___y_3892_ = v_a_3879_;
goto v___jp_3886_;
}
else
{
size_t v___x_3931_; size_t v___x_3932_; uint8_t v___x_3933_; 
v___x_3931_ = ((size_t)0ULL);
v___x_3932_ = lean_usize_of_nat(v___x_3884_);
v___x_3933_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27(v_hints_3883_, v___x_3931_, v___x_3932_);
if (v___x_3933_ == 0)
{
v___y_3887_ = v_a_3874_;
v___y_3888_ = v_a_3875_;
v___y_3889_ = v_a_3876_;
v___y_3890_ = v_a_3877_;
v___y_3891_ = v_a_3878_;
v___y_3892_ = v_a_3879_;
goto v___jp_3886_;
}
else
{
if (v___x_3930_ == 0)
{
v___y_3887_ = v_a_3874_;
v___y_3888_ = v_a_3875_;
v___y_3889_ = v_a_3876_;
v___y_3890_ = v_a_3877_;
v___y_3891_ = v_a_3878_;
v___y_3892_ = v_a_3879_;
goto v___jp_3886_;
}
else
{
if (v___x_3930_ == 0)
{
v___y_3887_ = v_a_3874_;
v___y_3888_ = v_a_3875_;
v___y_3889_ = v_a_3876_;
v___y_3890_ = v_a_3877_;
v___y_3891_ = v_a_3878_;
v___y_3892_ = v_a_3879_;
goto v___jp_3886_;
}
else
{
uint8_t v___x_3934_; 
v___x_3934_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__28(v___x_3933_, v_hints_3883_, v___x_3931_, v___x_3932_);
if (v___x_3934_ == 0)
{
v___y_3887_ = v_a_3874_;
v___y_3888_ = v_a_3875_;
v___y_3889_ = v_a_3876_;
v___y_3890_ = v_a_3877_;
v___y_3891_ = v_a_3878_;
v___y_3892_ = v_a_3879_;
goto v___jp_3886_;
}
else
{
lean_object* v___x_3935_; lean_object* v___x_3936_; 
lean_dec_ref(v_hints_3883_);
lean_dec_ref(v_preDefs_3873_);
lean_dec_ref(v_docCtx_3872_);
v___x_3935_ = lean_obj_once(&l_Lean_Elab_partialFixpoint___closed__3, &l_Lean_Elab_partialFixpoint___closed__3_once, _init_l_Lean_Elab_partialFixpoint___closed__3);
v___x_3936_ = l_panic___at___00Lean_Elab_partialFixpoint_spec__26(v___x_3935_, v_a_3874_, v_a_3875_, v_a_3876_, v_a_3877_, v_a_3878_, v_a_3879_);
return v___x_3936_;
}
}
}
}
}
}
}
v___jp_3886_:
{
lean_object* v___x_3893_; lean_object* v___x_3894_; 
v___x_3893_ = lean_mk_empty_array_with_capacity(v___x_3882_);
lean_inc_ref(v___x_3893_);
v___x_3894_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg(v_hints_3883_, v_preDefs_3873_, v___x_3882_, v___x_3881_, v___x_3893_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_);
if (lean_obj_tag(v___x_3894_) == 0)
{
lean_object* v_a_3895_; size_t v_sz_3896_; size_t v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; 
v_a_3895_ = lean_ctor_get(v___x_3894_, 0);
lean_inc(v_a_3895_);
lean_dec_ref(v___x_3894_);
v_sz_3896_ = lean_array_size(v_preDefs_3873_);
v___x_3897_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_3873_);
v___x_3898_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__8(v_sz_3896_, v___x_3897_, v_preDefs_3873_);
lean_inc_ref(v_preDefs_3873_);
v___x_3899_ = l_Lean_Elab_getFixedParamPerms(v_preDefs_3873_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_);
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v_a_3900_; lean_object* v_perms_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v_type_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___f_3910_; lean_object* v___x_3911_; 
v_a_3900_ = lean_ctor_get(v___x_3899_, 0);
lean_inc(v_a_3900_);
lean_dec_ref(v___x_3899_);
v_perms_3901_ = lean_ctor_get(v_a_3900_, 1);
lean_inc_ref(v_perms_3901_);
v___x_3902_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_3903_ = lean_array_get(v___x_3902_, v_preDefs_3873_, v___x_3881_);
v_type_3904_ = lean_ctor_get(v___x_3903_, 6);
lean_inc_ref(v_type_3904_);
v___x_3905_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1);
v___x_3906_ = lean_array_get(v___x_3905_, v_perms_3901_, v___x_3881_);
v___x_3907_ = ((lean_object*)(l_Lean_Elab_partialFixpoint___boxed__const__1));
v___x_3908_ = lean_box(v___x_3885_);
v___x_3909_ = lean_box_usize(v_sz_3896_);
v___f_3910_ = lean_alloc_closure((void*)(l_Lean_Elab_partialFixpoint___lam__0___boxed), 22, 14);
lean_closure_set(v___f_3910_, 0, v_a_3895_);
lean_closure_set(v___f_3910_, 1, v_perms_3901_);
lean_closure_set(v___f_3910_, 2, v___x_3881_);
lean_closure_set(v___f_3910_, 3, v_preDefs_3873_);
lean_closure_set(v___f_3910_, 4, v___x_3882_);
lean_closure_set(v___f_3910_, 5, v___x_3893_);
lean_closure_set(v___f_3910_, 6, v___x_3907_);
lean_closure_set(v___f_3910_, 7, v___x_3898_);
lean_closure_set(v___f_3910_, 8, v_a_3900_);
lean_closure_set(v___f_3910_, 9, v___x_3908_);
lean_closure_set(v___f_3910_, 10, v_hints_3883_);
lean_closure_set(v___f_3910_, 11, v___x_3903_);
lean_closure_set(v___f_3910_, 12, v_docCtx_3872_);
lean_closure_set(v___f_3910_, 13, v___x_3909_);
v___x_3911_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__25___redArg(v___x_3906_, v_type_3904_, v___f_3910_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_);
return v___x_3911_;
}
else
{
lean_object* v_a_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3919_; 
lean_dec_ref(v___x_3898_);
lean_dec(v_a_3895_);
lean_dec_ref(v___x_3893_);
lean_dec_ref(v_hints_3883_);
lean_dec_ref(v_preDefs_3873_);
lean_dec_ref(v_docCtx_3872_);
v_a_3912_ = lean_ctor_get(v___x_3899_, 0);
v_isSharedCheck_3919_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_3919_ == 0)
{
v___x_3914_ = v___x_3899_;
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_a_3912_);
lean_dec(v___x_3899_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
lean_object* v___x_3917_; 
if (v_isShared_3915_ == 0)
{
v___x_3917_ = v___x_3914_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v_a_3912_);
v___x_3917_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
return v___x_3917_;
}
}
}
}
else
{
lean_object* v_a_3920_; lean_object* v___x_3922_; uint8_t v_isShared_3923_; uint8_t v_isSharedCheck_3927_; 
lean_dec_ref(v___x_3893_);
lean_dec_ref(v_hints_3883_);
lean_dec_ref(v_preDefs_3873_);
lean_dec_ref(v_docCtx_3872_);
v_a_3920_ = lean_ctor_get(v___x_3894_, 0);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___x_3894_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3922_ = v___x_3894_;
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
else
{
lean_inc(v_a_3920_);
lean_dec(v___x_3894_);
v___x_3922_ = lean_box(0);
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
v_resetjp_3921_:
{
lean_object* v___x_3925_; 
if (v_isShared_3923_ == 0)
{
v___x_3925_ = v___x_3922_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_a_3920_);
v___x_3925_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
return v___x_3925_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_partialFixpoint___boxed(lean_object* v_docCtx_3937_, lean_object* v_preDefs_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_){
_start:
{
lean_object* v_res_3946_; 
v_res_3946_ = l_Lean_Elab_partialFixpoint(v_docCtx_3937_, v_preDefs_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_);
lean_dec(v_a_3944_);
lean_dec_ref(v_a_3943_);
lean_dec(v_a_3942_);
lean_dec_ref(v_a_3941_);
lean_dec(v_a_3940_);
lean_dec_ref(v_a_3939_);
return v_res_3946_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1(lean_object* v_00_u03b1_3947_, lean_object* v_msg_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_){
_start:
{
lean_object* v___x_3956_; 
lean_inc_ref(v___y_3949_);
v___x_3956_ = l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___redArg(v_msg_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
return v___x_3956_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___boxed(lean_object* v_00_u03b1_3957_, lean_object* v_msg_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_){
_start:
{
lean_object* v_res_3966_; 
v_res_3966_ = l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1(v_00_u03b1_3957_, v_msg_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
lean_dec(v___y_3964_);
lean_dec_ref(v___y_3963_);
lean_dec(v___y_3962_);
lean_dec_ref(v___y_3961_);
lean_dec(v___y_3960_);
lean_dec_ref(v___y_3959_);
return v_res_3966_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__3(lean_object* v_cls_3967_, lean_object* v_msg_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_){
_start:
{
lean_object* v___x_3976_; 
v___x_3976_ = l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__3___redArg(v_cls_3967_, v_msg_3968_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_);
return v___x_3976_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__3___boxed(lean_object* v_cls_3977_, lean_object* v_msg_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_){
_start:
{
lean_object* v_res_3986_; 
v_res_3986_ = l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__3(v_cls_3977_, v_msg_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_);
lean_dec(v___y_3984_);
lean_dec_ref(v___y_3983_);
lean_dec(v___y_3982_);
lean_dec_ref(v___y_3981_);
lean_dec(v___y_3980_);
lean_dec_ref(v___y_3979_);
return v_res_3986_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7(lean_object* v_hints_3987_, lean_object* v_as_3988_, lean_object* v_i_3989_, lean_object* v_j_3990_, lean_object* v_inv_3991_, lean_object* v_bs_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_){
_start:
{
lean_object* v___x_4000_; 
v___x_4000_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___redArg(v_hints_3987_, v_as_3988_, v_i_3989_, v_j_3990_, v_bs_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_);
return v___x_4000_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7___boxed(lean_object* v_hints_4001_, lean_object* v_as_4002_, lean_object* v_i_4003_, lean_object* v_j_4004_, lean_object* v_inv_4005_, lean_object* v_bs_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_){
_start:
{
lean_object* v_res_4014_; 
v_res_4014_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__7(v_hints_4001_, v_as_4002_, v_i_4003_, v_j_4004_, v_inv_4005_, v_bs_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_);
lean_dec(v___y_4012_);
lean_dec_ref(v___y_4011_);
lean_dec(v___y_4010_);
lean_dec_ref(v___y_4009_);
lean_dec(v___y_4008_);
lean_dec_ref(v___y_4007_);
lean_dec_ref(v_as_4002_);
lean_dec_ref(v_hints_4001_);
return v_res_4014_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11(lean_object* v___x_4015_, lean_object* v_fixedArgs_4016_, lean_object* v_as_4017_, lean_object* v_i_4018_, lean_object* v_j_4019_, lean_object* v_inv_4020_, lean_object* v_bs_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_){
_start:
{
lean_object* v___x_4029_; 
v___x_4029_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11___redArg(v___x_4015_, v_fixedArgs_4016_, v_as_4017_, v_i_4018_, v_j_4019_, v_bs_4021_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_);
return v___x_4029_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11___boxed(lean_object* v___x_4030_, lean_object* v_fixedArgs_4031_, lean_object* v_as_4032_, lean_object* v_i_4033_, lean_object* v_j_4034_, lean_object* v_inv_4035_, lean_object* v_bs_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_){
_start:
{
lean_object* v_res_4044_; 
v_res_4044_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__11(v___x_4030_, v_fixedArgs_4031_, v_as_4032_, v_i_4033_, v_j_4034_, v_inv_4035_, v_bs_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_);
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
lean_dec(v___y_4040_);
lean_dec_ref(v___y_4039_);
lean_dec(v___y_4038_);
lean_dec_ref(v___y_4037_);
lean_dec_ref(v_as_4032_);
lean_dec_ref(v___x_4030_);
return v_res_4044_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__12(lean_object* v___x_4045_, lean_object* v_fixedArgs_4046_, lean_object* v_as_4047_, lean_object* v_i_4048_, lean_object* v_j_4049_, lean_object* v_inv_4050_, lean_object* v_bs_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_){
_start:
{
lean_object* v___x_4059_; 
v___x_4059_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__12___redArg(v___x_4045_, v_fixedArgs_4046_, v_as_4047_, v_i_4048_, v_j_4049_, v_bs_4051_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_);
return v___x_4059_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__12___boxed(lean_object* v___x_4060_, lean_object* v_fixedArgs_4061_, lean_object* v_as_4062_, lean_object* v_i_4063_, lean_object* v_j_4064_, lean_object* v_inv_4065_, lean_object* v_bs_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_){
_start:
{
lean_object* v_res_4074_; 
v_res_4074_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__12(v___x_4060_, v_fixedArgs_4061_, v_as_4062_, v_i_4063_, v_j_4064_, v_inv_4065_, v_bs_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_);
lean_dec(v___y_4072_);
lean_dec_ref(v___y_4071_);
lean_dec(v___y_4070_);
lean_dec_ref(v___y_4069_);
lean_dec(v___y_4068_);
lean_dec_ref(v___y_4067_);
lean_dec_ref(v_as_4062_);
lean_dec_ref(v___x_4060_);
return v_res_4074_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__14(lean_object* v_as_4075_, size_t v_i_4076_, size_t v_stop_4077_, lean_object* v_b_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_){
_start:
{
lean_object* v___x_4086_; 
v___x_4086_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__14___redArg(v_as_4075_, v_i_4076_, v_stop_4077_, v_b_4078_, v___y_4083_, v___y_4084_);
return v___x_4086_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__14___boxed(lean_object* v_as_4087_, lean_object* v_i_4088_, lean_object* v_stop_4089_, lean_object* v_b_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_){
_start:
{
size_t v_i_boxed_4098_; size_t v_stop_boxed_4099_; lean_object* v_res_4100_; 
v_i_boxed_4098_ = lean_unbox_usize(v_i_4088_);
lean_dec(v_i_4088_);
v_stop_boxed_4099_ = lean_unbox_usize(v_stop_4089_);
lean_dec(v_stop_4089_);
v_res_4100_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__14(v_as_4087_, v_i_boxed_4098_, v_stop_boxed_4099_, v_b_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_);
lean_dec(v___y_4096_);
lean_dec_ref(v___y_4095_);
lean_dec(v___y_4094_);
lean_dec_ref(v___y_4093_);
lean_dec(v___y_4092_);
lean_dec_ref(v___y_4091_);
lean_dec_ref(v_as_4087_);
return v_res_4100_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__15_spec__17(lean_object* v_env_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_){
_start:
{
lean_object* v___x_4109_; 
v___x_4109_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__15_spec__17___redArg(v_env_4101_, v___y_4105_, v___y_4107_);
return v___x_4109_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__15_spec__17___boxed(lean_object* v_env_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_){
_start:
{
lean_object* v_res_4118_; 
v_res_4118_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__15_spec__17(v_env_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_);
lean_dec(v___y_4116_);
lean_dec_ref(v___y_4115_);
lean_dec(v___y_4114_);
lean_dec_ref(v___y_4113_);
lean_dec(v___y_4112_);
lean_dec_ref(v___y_4111_);
return v_res_4118_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__15(lean_object* v_00_u03b1_4119_, lean_object* v_env_4120_, lean_object* v_x_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_){
_start:
{
lean_object* v___x_4129_; 
v___x_4129_ = l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__15___redArg(v_env_4120_, v_x_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_);
return v___x_4129_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__15___boxed(lean_object* v_00_u03b1_4130_, lean_object* v_env_4131_, lean_object* v_x_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_){
_start:
{
lean_object* v_res_4140_; 
v_res_4140_ = l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__15(v_00_u03b1_4130_, v_env_4131_, v_x_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_);
lean_dec(v___y_4138_);
lean_dec_ref(v___y_4137_);
lean_dec(v___y_4136_);
lean_dec_ref(v___y_4135_);
lean_dec(v___y_4134_);
lean_dec_ref(v___y_4133_);
return v_res_4140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__16_spec__19(lean_object* v_00_u03b1_4141_, lean_object* v_name_4142_, uint8_t v_bi_4143_, lean_object* v_type_4144_, lean_object* v_k_4145_, uint8_t v_kind_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_){
_start:
{
lean_object* v___x_4154_; 
v___x_4154_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__16_spec__19___redArg(v_name_4142_, v_bi_4143_, v_type_4144_, v_k_4145_, v_kind_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_);
return v___x_4154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__16_spec__19___boxed(lean_object* v_00_u03b1_4155_, lean_object* v_name_4156_, lean_object* v_bi_4157_, lean_object* v_type_4158_, lean_object* v_k_4159_, lean_object* v_kind_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_){
_start:
{
uint8_t v_bi_boxed_4168_; uint8_t v_kind_boxed_4169_; lean_object* v_res_4170_; 
v_bi_boxed_4168_ = lean_unbox(v_bi_4157_);
v_kind_boxed_4169_ = lean_unbox(v_kind_4160_);
v_res_4170_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__16_spec__19(v_00_u03b1_4155_, v_name_4156_, v_bi_boxed_4168_, v_type_4158_, v_k_4159_, v_kind_boxed_4169_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_);
lean_dec(v___y_4166_);
lean_dec_ref(v___y_4165_);
lean_dec(v___y_4164_);
lean_dec_ref(v___y_4163_);
lean_dec(v___y_4162_);
lean_dec_ref(v___y_4161_);
return v_res_4170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__16(lean_object* v_00_u03b1_4171_, lean_object* v_name_4172_, lean_object* v_type_4173_, lean_object* v_k_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_){
_start:
{
lean_object* v___x_4182_; 
v___x_4182_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__16___redArg(v_name_4172_, v_type_4173_, v_k_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_);
return v___x_4182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__16___boxed(lean_object* v_00_u03b1_4183_, lean_object* v_name_4184_, lean_object* v_type_4185_, lean_object* v_k_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_){
_start:
{
lean_object* v_res_4194_; 
v_res_4194_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__16(v_00_u03b1_4183_, v_name_4184_, v_type_4185_, v_k_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
lean_dec(v___y_4192_);
lean_dec_ref(v___y_4191_);
lean_dec(v___y_4190_);
lean_dec_ref(v___y_4189_);
lean_dec(v___y_4188_);
lean_dec_ref(v___y_4187_);
return v_res_4194_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__18_spec__22(lean_object* v_00_u03b1_4195_, lean_object* v_x_4196_, uint8_t v_isExporting_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_){
_start:
{
lean_object* v___x_4205_; 
v___x_4205_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__18_spec__22___redArg(v_x_4196_, v_isExporting_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_);
return v___x_4205_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__18_spec__22___boxed(lean_object* v_00_u03b1_4206_, lean_object* v_x_4207_, lean_object* v_isExporting_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_){
_start:
{
uint8_t v_isExporting_boxed_4216_; lean_object* v_res_4217_; 
v_isExporting_boxed_4216_ = lean_unbox(v_isExporting_4208_);
v_res_4217_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__18_spec__22(v_00_u03b1_4206_, v_x_4207_, v_isExporting_boxed_4216_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_);
lean_dec(v___y_4214_);
lean_dec_ref(v___y_4213_);
lean_dec(v___y_4212_);
lean_dec_ref(v___y_4211_);
lean_dec(v___y_4210_);
lean_dec_ref(v___y_4209_);
return v_res_4217_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__18(lean_object* v_00_u03b1_4218_, lean_object* v_x_4219_, uint8_t v_when_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_){
_start:
{
lean_object* v___x_4228_; 
v___x_4228_ = l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__18___redArg(v_x_4219_, v_when_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_);
return v___x_4228_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__18___boxed(lean_object* v_00_u03b1_4229_, lean_object* v_x_4230_, lean_object* v_when_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_){
_start:
{
uint8_t v_when_boxed_4239_; lean_object* v_res_4240_; 
v_when_boxed_4239_ = lean_unbox(v_when_4231_);
v_res_4240_ = l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__18(v_00_u03b1_4229_, v_x_4230_, v_when_boxed_4239_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_);
lean_dec(v___y_4237_);
lean_dec_ref(v___y_4236_);
lean_dec(v___y_4235_);
lean_dec_ref(v___y_4234_);
lean_dec(v___y_4233_);
lean_dec_ref(v___y_4232_);
return v_res_4240_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__22(lean_object* v___x_4241_, lean_object* v___x_4242_, lean_object* v___y_4243_, lean_object* v___x_4244_, lean_object* v_a_4245_, lean_object* v_as_4246_, lean_object* v_i_4247_, lean_object* v_j_4248_, lean_object* v_inv_4249_, lean_object* v_bs_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_){
_start:
{
lean_object* v___x_4258_; 
v___x_4258_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__22___redArg(v___x_4241_, v___x_4242_, v___y_4243_, v___x_4244_, v_a_4245_, v_as_4246_, v_i_4247_, v_j_4248_, v_bs_4250_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_);
return v___x_4258_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__22___boxed(lean_object** _args){
lean_object* v___x_4259_ = _args[0];
lean_object* v___x_4260_ = _args[1];
lean_object* v___y_4261_ = _args[2];
lean_object* v___x_4262_ = _args[3];
lean_object* v_a_4263_ = _args[4];
lean_object* v_as_4264_ = _args[5];
lean_object* v_i_4265_ = _args[6];
lean_object* v_j_4266_ = _args[7];
lean_object* v_inv_4267_ = _args[8];
lean_object* v_bs_4268_ = _args[9];
lean_object* v___y_4269_ = _args[10];
lean_object* v___y_4270_ = _args[11];
lean_object* v___y_4271_ = _args[12];
lean_object* v___y_4272_ = _args[13];
lean_object* v___y_4273_ = _args[14];
lean_object* v___y_4274_ = _args[15];
lean_object* v___y_4275_ = _args[16];
_start:
{
lean_object* v_res_4276_; 
v_res_4276_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__22(v___x_4259_, v___x_4260_, v___y_4261_, v___x_4262_, v_a_4263_, v_as_4264_, v_i_4265_, v_j_4266_, v_inv_4267_, v_bs_4268_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_);
lean_dec(v___y_4274_);
lean_dec_ref(v___y_4273_);
lean_dec(v___y_4272_);
lean_dec_ref(v___y_4271_);
lean_dec(v___y_4270_);
lean_dec_ref(v___y_4269_);
lean_dec_ref(v_as_4264_);
lean_dec_ref(v___x_4259_);
return v_res_4276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__23(size_t v_sz_4277_, size_t v_i_4278_, lean_object* v_bs_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_){
_start:
{
lean_object* v___x_4287_; 
v___x_4287_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__23___redArg(v_sz_4277_, v_i_4278_, v_bs_4279_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_);
return v___x_4287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__23___boxed(lean_object* v_sz_4288_, lean_object* v_i_4289_, lean_object* v_bs_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_){
_start:
{
size_t v_sz_boxed_4298_; size_t v_i_boxed_4299_; lean_object* v_res_4300_; 
v_sz_boxed_4298_ = lean_unbox_usize(v_sz_4288_);
lean_dec(v_sz_4288_);
v_i_boxed_4299_ = lean_unbox_usize(v_i_4289_);
lean_dec(v_i_4289_);
v_res_4300_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__23(v_sz_boxed_4298_, v_i_boxed_4299_, v_bs_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_);
lean_dec(v___y_4296_);
lean_dec_ref(v___y_4295_);
lean_dec(v___y_4294_);
lean_dec_ref(v___y_4293_);
lean_dec(v___y_4292_);
lean_dec_ref(v___y_4291_);
return v_res_4300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2(lean_object* v_msgData_4301_, lean_object* v_macroStack_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_){
_start:
{
lean_object* v___x_4310_; 
v___x_4310_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg(v_msgData_4301_, v_macroStack_4302_, v___y_4307_);
return v___x_4310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___boxed(lean_object* v_msgData_4311_, lean_object* v_macroStack_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_){
_start:
{
lean_object* v_res_4320_; 
v_res_4320_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2(v_msgData_4311_, v_macroStack_4312_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_);
lean_dec(v___y_4318_);
lean_dec_ref(v___y_4317_);
lean_dec(v___y_4316_);
lean_dec_ref(v___y_4315_);
lean_dec(v___y_4314_);
lean_dec_ref(v___y_4313_);
return v_res_4320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4384_; uint8_t v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; 
v___x_4384_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_partialFixpoint_spec__20___redArg___closed__7));
v___x_4385_ = 0;
v___x_4386_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__25_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_));
v___x_4387_ = l_Lean_registerTraceClass(v___x_4384_, v___x_4385_, v___x_4386_);
return v___x_4387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2____boxed(lean_object* v_a_4388_){
_start:
{
lean_object* v_res_4389_; 
v_res_4389_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_();
return v_res_4389_;
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
