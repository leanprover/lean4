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
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_mkInhabitantFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_hasRecAppSyntax___boxed(lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_Lean_getRecAppSyntax_x3f(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_andList(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
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
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkInstPiOfInstsForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_pickVarying___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_PProdN_proj(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Mutual_cleanPreDef(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedPartialFixpoint_default;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Elab_isLatticeTheoretic(uint8_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_pickFixed___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
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
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_PProdN_pack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__10___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__11___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__23(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__23___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "f"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 68, 183, 24, 128, 148, 178, 23)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__16___boxed(lean_object**);
static const lean_string_object l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9___closed__0_value;
static lean_once_cell_t l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9___closed__1;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_hasRecAppSyntax___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Cannot eliminate recursive call `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__2;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "` enclosed in"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__4;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__6;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Elab.partialFixpoint"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "getRecAppSyntax\? failed"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__9;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Cannot eliminate recursive call in"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__10_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__11;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Tried to apply "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__12_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__13;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = ", but failed.\nPossible cause: A missing `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__14_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__15;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "MonoBind"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__16_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__3_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__17_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__16_value),LEAN_SCALAR_PTR_LITERAL(150, 25, 7, 134, 163, 66, 53, 232)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__17 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__17_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "` instance.\nUse `set_option trace.Elab.Tactic.monotonicity true` to debug."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__18 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__18_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__19;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__20;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__2(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Could not prove '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "' to be monotone in its recursive calls:"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "partialFixpoint"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(21, 214, 78, 192, 157, 92, 193, 45)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__8_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__9_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "monotonicity proof for "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__11_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__12;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__13_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__14;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_partialFixpoint___lam__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "ReverseImplicationOrder"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "instCompleteLattice"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__3_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__2_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 161, 0, 6, 7, 21, 122, 42)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__2_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(58, 218, 120, 132, 216, 84, 59, 130)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "`coinductive_fixpoint` can be only used to define predicates"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "failed to compile definition '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "' using `partial_fixpoint`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__3;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Nonempty"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(142, 191, 110, 220, 210, 100, 152, 183)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__7_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__6_value),LEAN_SCALAR_PTR_LITERAL(113, 209, 180, 93, 84, 117, 67, 110)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Classical"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ofNonempty"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__8_value),LEAN_SCALAR_PTR_LITERAL(40, 236, 220, 79, 38, 141, 161, 150)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__10_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__9_value),LEAN_SCALAR_PTR_LITERAL(197, 41, 144, 91, 215, 43, 73, 12)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__10_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__11;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "FlatOrder"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__12_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instCCPO"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__13_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__4(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "No CCPO instance found for "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = ", trying inhabitation"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "CCPO"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__3_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__5_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(19, 35, 8, 63, 189, 207, 68, 204)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "preDef.value: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__7;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = ", xs: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__9;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = ", _body: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__10_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__11;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ImplicationOrder"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__3_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(106, 240, 34, 128, 168, 240, 126, 19)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(89, 9, 5, 228, 125, 57, 241, 212)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__2;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "`inductive_fixpoint` can be only used to define predicates"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___closed__0_value;
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__10(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__11(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__3_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__2_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
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
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__16_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__15_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(165, 120, 90, 26, 169, 90, 9, 167)}};
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
lean_dec_ref_known(v___x_232_, 1);
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
lean_dec_ref_known(v___x_307_, 1);
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
lean_dec_ref_known(v___x_330_, 1);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___redArg___lam__0(lean_object* v_v_360_, lean_object* v___x_361_, lean_object* v_fixedArgs_362_, uint8_t v___x_363_, lean_object* v_xs_364_, lean_object* v_x_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v_levelParams_371_; lean_object* v_declName_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; uint8_t v___x_378_; uint8_t v___x_379_; lean_object* v___x_380_; 
v_levelParams_371_ = lean_ctor_get(v_v_360_, 1);
lean_inc(v_levelParams_371_);
v_declName_372_ = lean_ctor_get(v_v_360_, 3);
lean_inc(v_declName_372_);
lean_dec(v_v_360_);
lean_inc_ref(v_xs_364_);
v___x_373_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(v___x_361_, v_fixedArgs_362_, v_xs_364_);
v___x_374_ = lean_box(0);
v___x_375_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__0(v_levelParams_371_, v___x_374_);
v___x_376_ = l_Lean_Expr_const___override(v_declName_372_, v___x_375_);
v___x_377_ = l_Lean_mkAppN(v___x_376_, v___x_373_);
lean_dec_ref(v___x_373_);
v___x_378_ = 0;
v___x_379_ = 1;
v___x_380_ = l_Lean_Meta_mkLambdaFVars(v_xs_364_, v___x_377_, v___x_378_, v___x_363_, v___x_363_, v___x_363_, v___x_379_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
lean_dec_ref(v_xs_364_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___redArg___lam__0___boxed(lean_object* v_v_381_, lean_object* v___x_382_, lean_object* v_fixedArgs_383_, lean_object* v___x_384_, lean_object* v_xs_385_, lean_object* v_x_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
uint8_t v___x_5318__boxed_392_; lean_object* v_res_393_; 
v___x_5318__boxed_392_ = lean_unbox(v___x_384_);
v_res_393_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___redArg___lam__0(v_v_381_, v___x_382_, v_fixedArgs_383_, v___x_5318__boxed_392_, v_xs_385_, v_x_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec_ref(v_x_386_);
lean_dec_ref(v_fixedArgs_383_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___redArg(lean_object* v_fixedParamPerms_394_, lean_object* v_fixedArgs_395_, size_t v_sz_396_, size_t v_i_397_, lean_object* v_bs_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
uint8_t v___x_404_; 
v___x_404_ = lean_usize_dec_lt(v_i_397_, v_sz_396_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; 
lean_dec_ref(v_fixedArgs_395_);
v___x_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_405_, 0, v_bs_398_);
return v___x_405_;
}
else
{
lean_object* v_v_406_; lean_object* v_perms_407_; lean_object* v_value_408_; lean_object* v___x_409_; lean_object* v_bs_x27_410_; lean_object* v___y_412_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v_v_406_ = lean_array_uget(v_bs_398_, v_i_397_);
v_perms_407_ = lean_ctor_get(v_fixedParamPerms_394_, 1);
v_value_408_ = lean_ctor_get(v_v_406_, 7);
v___x_409_ = lean_unsigned_to_nat(0u);
v_bs_x27_410_ = lean_array_uset(v_bs_398_, v_i_397_, v___x_409_);
v___x_426_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1);
v___x_427_ = lean_usize_to_nat(v_i_397_);
v___x_428_ = lean_array_get_borrowed(v___x_426_, v_perms_407_, v___x_427_);
lean_dec(v___x_427_);
lean_inc_ref(v_fixedArgs_395_);
lean_inc_ref(v_value_408_);
lean_inc(v___x_428_);
v___x_429_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_428_, v_value_408_, v_fixedArgs_395_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; lean_object* v___x_431_; lean_object* v___f_432_; uint8_t v___x_433_; lean_object* v___x_434_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_a_430_);
lean_dec_ref_known(v___x_429_, 1);
v___x_431_ = lean_box(v___x_404_);
lean_inc_ref(v_fixedArgs_395_);
lean_inc(v___x_428_);
v___f_432_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_432_, 0, v_v_406_);
lean_closure_set(v___f_432_, 1, v___x_428_);
lean_closure_set(v___f_432_, 2, v_fixedArgs_395_);
lean_closure_set(v___f_432_, 3, v___x_431_);
v___x_433_ = 0;
v___x_434_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__1___redArg(v_a_430_, v___f_432_, v___x_433_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
v___y_412_ = v___x_434_;
goto v___jp_411_;
}
else
{
lean_dec(v_v_406_);
v___y_412_ = v___x_429_;
goto v___jp_411_;
}
v___jp_411_:
{
if (lean_obj_tag(v___y_412_) == 0)
{
lean_object* v_a_413_; size_t v___x_414_; size_t v___x_415_; lean_object* v___x_416_; 
v_a_413_ = lean_ctor_get(v___y_412_, 0);
lean_inc(v_a_413_);
lean_dec_ref_known(v___y_412_, 1);
v___x_414_ = ((size_t)1ULL);
v___x_415_ = lean_usize_add(v_i_397_, v___x_414_);
v___x_416_ = lean_array_uset(v_bs_x27_410_, v_i_397_, v_a_413_);
v_i_397_ = v___x_415_;
v_bs_398_ = v___x_416_;
goto _start;
}
else
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
lean_dec_ref(v_bs_x27_410_);
lean_dec_ref(v_fixedArgs_395_);
v_a_418_ = lean_ctor_get(v___y_412_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___y_412_);
if (v_isSharedCheck_425_ == 0)
{
v___x_420_ = v___y_412_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___y_412_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_418_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___redArg___boxed(lean_object* v_fixedParamPerms_435_, lean_object* v_fixedArgs_436_, lean_object* v_sz_437_, lean_object* v_i_438_, lean_object* v_bs_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
size_t v_sz_boxed_445_; size_t v_i_boxed_446_; lean_object* v_res_447_; 
v_sz_boxed_445_ = lean_unbox_usize(v_sz_437_);
lean_dec(v_sz_437_);
v_i_boxed_446_ = lean_unbox_usize(v_i_438_);
lean_dec(v_i_438_);
v_res_447_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___redArg(v_fixedParamPerms_435_, v_fixedArgs_436_, v_sz_boxed_445_, v_i_boxed_446_, v_bs_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec_ref(v_fixedParamPerms_435_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___lam__2(lean_object* v_preDefs_448_, lean_object* v_fixedParamPerms_449_, lean_object* v_fixedArgs_450_, lean_object* v___x_451_, lean_object* v___x_452_, lean_object* v_F_453_, lean_object* v_k_454_, lean_object* v___x_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
lean_object* v___y_500_; uint8_t v___x_509_; 
v___x_509_ = lean_nat_dec_lt(v___x_451_, v___x_455_);
if (v___x_509_ == 0)
{
goto v___jp_461_;
}
else
{
lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_510_ = lean_box(0);
v___x_511_ = lean_nat_dec_le(v___x_455_, v___x_455_);
if (v___x_511_ == 0)
{
if (v___x_509_ == 0)
{
goto v___jp_461_;
}
else
{
size_t v___x_512_; size_t v___x_513_; lean_object* v___x_514_; 
v___x_512_ = ((size_t)0ULL);
v___x_513_ = lean_usize_of_nat(v___x_455_);
v___x_514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__4___redArg(v_preDefs_448_, v___x_512_, v___x_513_, v___x_510_, v___y_458_, v___y_459_);
v___y_500_ = v___x_514_;
goto v___jp_499_;
}
}
else
{
size_t v___x_515_; size_t v___x_516_; lean_object* v___x_517_; 
v___x_515_ = ((size_t)0ULL);
v___x_516_ = lean_usize_of_nat(v___x_455_);
v___x_517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__4___redArg(v_preDefs_448_, v___x_515_, v___x_516_, v___x_510_, v___y_458_, v___y_459_);
v___y_500_ = v___x_517_;
goto v___jp_499_;
}
}
v___jp_461_:
{
size_t v_sz_462_; size_t v___x_463_; lean_object* v___x_464_; 
v_sz_462_ = lean_array_size(v_preDefs_448_);
v___x_463_ = ((size_t)0ULL);
v___x_464_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___redArg(v_fixedParamPerms_449_, v_fixedArgs_450_, v_sz_462_, v___x_463_, v_preDefs_448_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_a_465_);
lean_dec_ref_known(v___x_464_, 1);
v___x_466_ = l_Lean_Level_ofNat(v___x_451_);
v___x_467_ = l_Lean_Meta_PProdN_mk(v___x_466_, v_a_465_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v_a_468_; lean_object* v___f_469_; lean_object* v___x_470_; uint8_t v___x_471_; lean_object* v___x_472_; 
v_a_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_a_468_);
lean_dec_ref_known(v___x_467_, 1);
v___f_469_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_469_, 0, v___x_452_);
lean_closure_set(v___f_469_, 1, v___x_451_);
lean_closure_set(v___f_469_, 2, v_a_468_);
v___x_470_ = lean_unsigned_to_nat(1u);
v___x_471_ = 0;
v___x_472_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__3___redArg(v_F_453_, v___x_470_, v___f_469_, v___x_471_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_474_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_a_473_);
lean_dec_ref_known(v___x_472_, 1);
v___x_474_ = lean_apply_6(v_k_454_, v_a_473_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, lean_box(0));
return v___x_474_;
}
else
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec_ref(v_k_454_);
v_a_475_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___x_472_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_472_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
else
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_490_; 
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec_ref(v_k_454_);
lean_dec_ref(v_F_453_);
lean_dec_ref(v___x_452_);
lean_dec(v___x_451_);
v_a_483_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_490_ == 0)
{
v___x_485_ = v___x_467_;
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_467_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_486_ == 0)
{
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_483_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
else
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec_ref(v_k_454_);
lean_dec_ref(v_F_453_);
lean_dec_ref(v___x_452_);
lean_dec(v___x_451_);
v_a_491_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_464_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_464_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
v___jp_499_:
{
if (lean_obj_tag(v___y_500_) == 0)
{
lean_dec_ref_known(v___y_500_, 1);
goto v___jp_461_;
}
else
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_508_; 
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec_ref(v_k_454_);
lean_dec_ref(v_F_453_);
lean_dec_ref(v___x_452_);
lean_dec(v___x_451_);
lean_dec_ref(v_fixedArgs_450_);
lean_dec_ref(v_preDefs_448_);
v_a_501_ = lean_ctor_get(v___y_500_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___y_500_);
if (v_isSharedCheck_508_ == 0)
{
v___x_503_ = v___y_500_;
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___y_500_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_501_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___lam__2___boxed(lean_object* v_preDefs_518_, lean_object* v_fixedParamPerms_519_, lean_object* v_fixedArgs_520_, lean_object* v___x_521_, lean_object* v___x_522_, lean_object* v_F_523_, lean_object* v_k_524_, lean_object* v___x_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___lam__2(v_preDefs_518_, v_fixedParamPerms_519_, v_fixedArgs_520_, v___x_521_, v___x_522_, v_F_523_, v_k_524_, v___x_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
lean_dec(v___x_525_);
lean_dec_ref(v_fixedParamPerms_519_);
return v_res_531_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_532_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__0, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__0);
v___x_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
return v___x_534_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__1);
v___x_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
return v___x_536_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__1, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__1);
v___x_538_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
lean_ctor_set(v___x_538_, 2, v___x_537_);
lean_ctor_set(v___x_538_, 3, v___x_537_);
lean_ctor_set(v___x_538_, 4, v___x_537_);
lean_ctor_set(v___x_538_, 5, v___x_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg(lean_object* v_env_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v___x_543_; lean_object* v_nextMacroScope_544_; lean_object* v_ngen_545_; lean_object* v_auxDeclNGen_546_; lean_object* v_traceState_547_; lean_object* v_messages_548_; lean_object* v_infoState_549_; lean_object* v_snapshotTasks_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_576_; 
v___x_543_ = lean_st_ref_take(v___y_541_);
v_nextMacroScope_544_ = lean_ctor_get(v___x_543_, 1);
v_ngen_545_ = lean_ctor_get(v___x_543_, 2);
v_auxDeclNGen_546_ = lean_ctor_get(v___x_543_, 3);
v_traceState_547_ = lean_ctor_get(v___x_543_, 4);
v_messages_548_ = lean_ctor_get(v___x_543_, 6);
v_infoState_549_ = lean_ctor_get(v___x_543_, 7);
v_snapshotTasks_550_ = lean_ctor_get(v___x_543_, 8);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_576_ == 0)
{
lean_object* v_unused_577_; lean_object* v_unused_578_; 
v_unused_577_ = lean_ctor_get(v___x_543_, 5);
lean_dec(v_unused_577_);
v_unused_578_ = lean_ctor_get(v___x_543_, 0);
lean_dec(v_unused_578_);
v___x_552_ = v___x_543_;
v_isShared_553_ = v_isSharedCheck_576_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_snapshotTasks_550_);
lean_inc(v_infoState_549_);
lean_inc(v_messages_548_);
lean_inc(v_traceState_547_);
lean_inc(v_auxDeclNGen_546_);
lean_inc(v_ngen_545_);
lean_inc(v_nextMacroScope_544_);
lean_dec(v___x_543_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_576_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_554_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 5, v___x_554_);
lean_ctor_set(v___x_552_, 0, v_env_539_);
v___x_556_ = v___x_552_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_env_539_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v_nextMacroScope_544_);
lean_ctor_set(v_reuseFailAlloc_575_, 2, v_ngen_545_);
lean_ctor_set(v_reuseFailAlloc_575_, 3, v_auxDeclNGen_546_);
lean_ctor_set(v_reuseFailAlloc_575_, 4, v_traceState_547_);
lean_ctor_set(v_reuseFailAlloc_575_, 5, v___x_554_);
lean_ctor_set(v_reuseFailAlloc_575_, 6, v_messages_548_);
lean_ctor_set(v_reuseFailAlloc_575_, 7, v_infoState_549_);
lean_ctor_set(v_reuseFailAlloc_575_, 8, v_snapshotTasks_550_);
v___x_556_ = v_reuseFailAlloc_575_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v_mctx_559_; lean_object* v_zetaDeltaFVarIds_560_; lean_object* v_postponed_561_; lean_object* v_diag_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_573_; 
v___x_557_ = lean_st_ref_set(v___y_541_, v___x_556_);
v___x_558_ = lean_st_ref_take(v___y_540_);
v_mctx_559_ = lean_ctor_get(v___x_558_, 0);
v_zetaDeltaFVarIds_560_ = lean_ctor_get(v___x_558_, 2);
v_postponed_561_ = lean_ctor_get(v___x_558_, 3);
v_diag_562_ = lean_ctor_get(v___x_558_, 4);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_573_ == 0)
{
lean_object* v_unused_574_; 
v_unused_574_ = lean_ctor_get(v___x_558_, 1);
lean_dec(v_unused_574_);
v___x_564_ = v___x_558_;
v_isShared_565_ = v_isSharedCheck_573_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_diag_562_);
lean_inc(v_postponed_561_);
lean_inc(v_zetaDeltaFVarIds_560_);
lean_inc(v_mctx_559_);
lean_dec(v___x_558_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_573_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_566_; lean_object* v___x_568_; 
v___x_566_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 1, v___x_566_);
v___x_568_ = v___x_564_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_mctx_559_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v___x_566_);
lean_ctor_set(v_reuseFailAlloc_572_, 2, v_zetaDeltaFVarIds_560_);
lean_ctor_set(v_reuseFailAlloc_572_, 3, v_postponed_561_);
lean_ctor_set(v_reuseFailAlloc_572_, 4, v_diag_562_);
v___x_568_ = v_reuseFailAlloc_572_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_569_ = lean_st_ref_set(v___y_540_, v___x_568_);
v___x_570_ = lean_box(0);
v___x_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
return v___x_571_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___boxed(lean_object* v_env_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg(v_env_579_, v___y_580_, v___y_581_);
lean_dec(v___y_581_);
lean_dec(v___y_580_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5___redArg(lean_object* v_env_584_, lean_object* v_x_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v___x_591_; lean_object* v_env_592_; lean_object* v_a_594_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_591_ = lean_st_ref_get(v___y_589_);
v_env_592_ = lean_ctor_get(v___x_591_, 0);
lean_inc_ref(v_env_592_);
lean_dec(v___x_591_);
v___x_604_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg(v_env_584_, v___y_587_, v___y_589_);
lean_dec_ref(v___x_604_);
lean_inc(v___y_589_);
lean_inc_ref(v___y_588_);
lean_inc(v___y_587_);
lean_inc_ref(v___y_586_);
v___x_605_ = lean_apply_5(v_x_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, lean_box(0));
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v_a_606_; lean_object* v___x_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
v_a_606_ = lean_ctor_get(v___x_605_, 0);
lean_inc(v_a_606_);
lean_dec_ref_known(v___x_605_, 1);
v___x_607_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg(v_env_592_, v___y_587_, v___y_589_);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_614_ == 0)
{
lean_object* v_unused_615_; 
v_unused_615_ = lean_ctor_get(v___x_607_, 0);
lean_dec(v_unused_615_);
v___x_609_ = v___x_607_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_dec(v___x_607_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 0, v_a_606_);
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_a_606_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
else
{
lean_object* v_a_616_; 
v_a_616_ = lean_ctor_get(v___x_605_, 0);
lean_inc(v_a_616_);
lean_dec_ref_known(v___x_605_, 1);
v_a_594_ = v_a_616_;
goto v___jp_593_;
}
v___jp_593_:
{
lean_object* v___x_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
v___x_595_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg(v_env_592_, v___y_587_, v___y_589_);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_602_ == 0)
{
lean_object* v_unused_603_; 
v_unused_603_ = lean_ctor_get(v___x_595_, 0);
lean_dec(v_unused_603_);
v___x_597_ = v___x_595_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_dec(v___x_595_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
lean_ctor_set_tag(v___x_597_, 1);
lean_ctor_set(v___x_597_, 0, v_a_594_);
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_594_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5___redArg___boxed(lean_object* v_env_617_, lean_object* v_x_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5___redArg(v_env_617_, v_x_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6_spec__7(lean_object* v_msgData_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v___x_631_; lean_object* v_env_632_; lean_object* v___x_633_; lean_object* v_mctx_634_; lean_object* v_lctx_635_; lean_object* v_options_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_631_ = lean_st_ref_get(v___y_629_);
v_env_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc_ref(v_env_632_);
lean_dec(v___x_631_);
v___x_633_ = lean_st_ref_get(v___y_627_);
v_mctx_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc_ref(v_mctx_634_);
lean_dec(v___x_633_);
v_lctx_635_ = lean_ctor_get(v___y_626_, 2);
v_options_636_ = lean_ctor_get(v___y_628_, 2);
lean_inc_ref(v_options_636_);
lean_inc_ref(v_lctx_635_);
v___x_637_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_637_, 0, v_env_632_);
lean_ctor_set(v___x_637_, 1, v_mctx_634_);
lean_ctor_set(v___x_637_, 2, v_lctx_635_);
lean_ctor_set(v___x_637_, 3, v_options_636_);
v___x_638_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
lean_ctor_set(v___x_638_, 1, v_msgData_625_);
v___x_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6_spec__7___boxed(lean_object* v_msgData_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6_spec__7(v_msgData_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg(lean_object* v_msg_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v_ref_653_; lean_object* v___x_654_; lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_663_; 
v_ref_653_ = lean_ctor_get(v___y_650_, 5);
v___x_654_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6_spec__7(v_msg_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
v_a_655_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_663_ == 0)
{
v___x_657_ = v___x_654_;
v_isShared_658_ = v_isSharedCheck_663_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_654_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_663_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; lean_object* v___x_661_; 
lean_inc(v_ref_653_);
v___x_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_659_, 0, v_ref_653_);
lean_ctor_set(v___x_659_, 1, v_a_655_);
if (v_isShared_658_ == 0)
{
lean_ctor_set_tag(v___x_657_, 1);
lean_ctor_set(v___x_657_, 0, v___x_659_);
v___x_661_ = v___x_657_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg___boxed(lean_object* v_msg_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg(v_msg_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
return v_res_670_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___closed__1(void){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___closed__0));
v___x_673_ = l_Lean_stringToMessageData(v___x_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg(lean_object* v_preDefs_674_, lean_object* v_fixedParamPerms_675_, lean_object* v_fixedArgs_676_, lean_object* v_F_677_, lean_object* v_k_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
lean_object* v___x_684_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; uint8_t v___x_697_; 
v___x_684_ = l_Lean_instInhabitedExpr;
v___x_697_ = l_Lean_Expr_isLambda(v_F_677_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
lean_dec_ref(v_k_678_);
lean_dec_ref(v_fixedArgs_676_);
lean_dec_ref(v_fixedParamPerms_675_);
lean_dec_ref(v_preDefs_674_);
v___x_698_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___closed__1);
v___x_699_ = l_Lean_indentExpr(v_F_677_);
v___x_700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_698_);
lean_ctor_set(v___x_700_, 1, v___x_699_);
v___x_701_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg(v___x_700_, v_a_679_, v_a_680_, v_a_681_, v_a_682_);
v_a_702_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_709_ == 0)
{
v___x_704_ = v___x_701_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_701_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_a_702_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
else
{
v___y_686_ = v_a_679_;
v___y_687_ = v_a_680_;
v___y_688_ = v_a_681_;
v___y_689_ = v_a_682_;
goto v___jp_685_;
}
v___jp_685_:
{
lean_object* v___x_690_; lean_object* v_env_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___f_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_690_ = lean_st_ref_get(v___y_689_);
v_env_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc_ref(v_env_691_);
lean_dec(v___x_690_);
v___x_692_ = lean_unsigned_to_nat(0u);
v___x_693_ = lean_array_get_size(v_preDefs_674_);
v___f_694_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___lam__2___boxed), 13, 8);
lean_closure_set(v___f_694_, 0, v_preDefs_674_);
lean_closure_set(v___f_694_, 1, v_fixedParamPerms_675_);
lean_closure_set(v___f_694_, 2, v_fixedArgs_676_);
lean_closure_set(v___f_694_, 3, v___x_692_);
lean_closure_set(v___f_694_, 4, v___x_684_);
lean_closure_set(v___f_694_, 5, v_F_677_);
lean_closure_set(v___f_694_, 6, v_k_678_);
lean_closure_set(v___f_694_, 7, v___x_693_);
v___x_695_ = l_Lean_Environment_unlockAsync(v_env_691_);
v___x_696_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5___redArg(v___x_695_, v___f_694_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
return v___x_696_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg___boxed(lean_object* v_preDefs_710_, lean_object* v_fixedParamPerms_711_, lean_object* v_fixedArgs_712_, lean_object* v_F_713_, lean_object* v_k_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg(v_preDefs_710_, v_fixedParamPerms_711_, v_fixedArgs_712_, v_F_713_, v_k_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps(lean_object* v_00_u03b1_721_, lean_object* v_preDefs_722_, lean_object* v_fixedParamPerms_723_, lean_object* v_fixedArgs_724_, lean_object* v_F_725_, lean_object* v_k_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg(v_preDefs_722_, v_fixedParamPerms_723_, v_fixedArgs_724_, v_F_725_, v_k_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___boxed(lean_object* v_00_u03b1_733_, lean_object* v_preDefs_734_, lean_object* v_fixedParamPerms_735_, lean_object* v_fixedArgs_736_, lean_object* v_F_737_, lean_object* v_k_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps(v_00_u03b1_733_, v_preDefs_734_, v_fixedParamPerms_735_, v_fixedArgs_736_, v_F_737_, v_k_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
lean_dec(v_a_740_);
lean_dec_ref(v_a_739_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2(lean_object* v_fixedParamPerms_745_, lean_object* v_fixedArgs_746_, lean_object* v_as_747_, size_t v_sz_748_, size_t v_i_749_, lean_object* v_bs_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___redArg(v_fixedParamPerms_745_, v_fixedArgs_746_, v_sz_748_, v_i_749_, v_bs_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2___boxed(lean_object* v_fixedParamPerms_757_, lean_object* v_fixedArgs_758_, lean_object* v_as_759_, lean_object* v_sz_760_, lean_object* v_i_761_, lean_object* v_bs_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
size_t v_sz_boxed_768_; size_t v_i_boxed_769_; lean_object* v_res_770_; 
v_sz_boxed_768_ = lean_unbox_usize(v_sz_760_);
lean_dec(v_sz_760_);
v_i_boxed_769_ = lean_unbox_usize(v_i_761_);
lean_dec(v_i_761_);
v_res_770_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__2(v_fixedParamPerms_757_, v_fixedArgs_758_, v_as_759_, v_sz_boxed_768_, v_i_boxed_769_, v_bs_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec_ref(v_as_759_);
lean_dec_ref(v_fixedParamPerms_757_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__4(lean_object* v_as_771_, size_t v_i_772_, size_t v_stop_773_, lean_object* v_b_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__4___redArg(v_as_771_, v_i_772_, v_stop_773_, v_b_774_, v___y_777_, v___y_778_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__4___boxed(lean_object* v_as_781_, lean_object* v_i_782_, lean_object* v_stop_783_, lean_object* v_b_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
size_t v_i_boxed_790_; size_t v_stop_boxed_791_; lean_object* v_res_792_; 
v_i_boxed_790_ = lean_unbox_usize(v_i_782_);
lean_dec(v_i_782_);
v_stop_boxed_791_ = lean_unbox_usize(v_stop_783_);
lean_dec(v_stop_783_);
v_res_792_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__4(v_as_781_, v_i_boxed_790_, v_stop_boxed_791_, v_b_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec_ref(v_as_781_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5(lean_object* v_env_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg(v_env_793_, v___y_795_, v___y_797_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___boxed(lean_object* v_env_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5(v_env_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5(lean_object* v_00_u03b1_807_, lean_object* v_env_808_, lean_object* v_x_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5___redArg(v_env_808_, v_x_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5___boxed(lean_object* v_00_u03b1_816_, lean_object* v_env_817_, lean_object* v_x_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5(v_00_u03b1_816_, v_env_817_, v_x_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6(lean_object* v_00_u03b1_825_, lean_object* v_msg_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg(v_msg_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___boxed(lean_object* v_00_u03b1_833_, lean_object* v_msg_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6(v_00_u03b1_833_, v_msg_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
return v_res_840_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__1(void){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_842_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__0));
v___x_843_ = l_Lean_stringToMessageData(v___x_842_);
return v___x_843_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__9(void){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_858_ = lean_box(0);
v___x_859_ = lean_unsigned_to_nat(10u);
v___x_860_ = lean_mk_empty_array_with_capacity(v___x_859_);
v___x_861_ = lean_array_push(v___x_860_, v___x_858_);
return v___x_861_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__10(void){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_862_ = lean_box(0);
v___x_863_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__9, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__9);
v___x_864_ = lean_array_push(v___x_863_, v___x_862_);
return v___x_864_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__11(void){
_start:
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_865_ = lean_box(0);
v___x_866_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__10, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__10);
v___x_867_ = lean_array_push(v___x_866_, v___x_865_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd(lean_object* v_x_868_, lean_object* v_x_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_){
_start:
{
lean_object* v_fst_875_; lean_object* v_snd_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_979_; 
v_fst_875_ = lean_ctor_get(v_x_868_, 0);
v_snd_876_ = lean_ctor_get(v_x_868_, 1);
v_isSharedCheck_979_ = !lean_is_exclusive(v_x_868_);
if (v_isSharedCheck_979_ == 0)
{
v___x_878_ = v_x_868_;
v_isShared_879_ = v_isSharedCheck_979_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_snd_876_);
lean_inc(v_fst_875_);
lean_dec(v_x_868_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_979_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v_fst_891_; lean_object* v_snd_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_978_; 
v_fst_891_ = lean_ctor_get(v_x_869_, 0);
v_snd_892_ = lean_ctor_get(v_x_869_, 1);
v_isSharedCheck_978_ = !lean_is_exclusive(v_x_869_);
if (v_isSharedCheck_978_ == 0)
{
v___x_894_ = v_x_869_;
v_isShared_895_ = v_isSharedCheck_978_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_snd_892_);
lean_inc(v_fst_891_);
lean_dec(v_x_869_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_978_;
goto v_resetjp_893_;
}
v___jp_880_:
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_888_; 
v___x_885_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__1);
v___x_886_ = l_Lean_indentExpr(v_snd_876_);
if (v_isShared_879_ == 0)
{
lean_ctor_set_tag(v___x_878_, 7);
lean_ctor_set(v___x_878_, 1, v___x_886_);
lean_ctor_set(v___x_878_, 0, v___x_885_);
v___x_888_ = v___x_878_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_885_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v___x_886_);
v___x_888_ = v_reuseFailAlloc_890_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_object* v___x_889_; 
v___x_889_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg(v___x_888_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
return v___x_889_;
}
}
v_resetjp_893_:
{
lean_object* v___y_897_; lean_object* v___y_898_; lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v___x_905_; uint8_t v___x_906_; 
v___x_905_ = l_Lean_Expr_cleanupAnnotations(v_fst_875_);
v___x_906_ = l_Lean_Expr_isApp(v___x_905_);
if (v___x_906_ == 0)
{
lean_dec_ref(v___x_905_);
lean_del_object(v___x_894_);
lean_dec(v_snd_892_);
lean_dec(v_fst_891_);
v___y_881_ = v_a_870_;
v___y_882_ = v_a_871_;
v___y_883_ = v_a_872_;
v___y_884_ = v_a_873_;
goto v___jp_880_;
}
else
{
lean_object* v___x_907_; uint8_t v___x_908_; 
v___x_907_ = l_Lean_Expr_appFnCleanup___redArg(v___x_905_);
v___x_908_ = l_Lean_Expr_isApp(v___x_907_);
if (v___x_908_ == 0)
{
lean_dec_ref(v___x_907_);
lean_del_object(v___x_894_);
lean_dec(v_snd_892_);
lean_dec(v_fst_891_);
v___y_881_ = v_a_870_;
v___y_882_ = v_a_871_;
v___y_883_ = v_a_872_;
v___y_884_ = v_a_873_;
goto v___jp_880_;
}
else
{
lean_object* v_arg_909_; lean_object* v___x_910_; uint8_t v___x_911_; 
v_arg_909_ = lean_ctor_get(v___x_907_, 1);
lean_inc_ref(v_arg_909_);
v___x_910_ = l_Lean_Expr_appFnCleanup___redArg(v___x_907_);
v___x_911_ = l_Lean_Expr_isApp(v___x_910_);
if (v___x_911_ == 0)
{
lean_dec_ref(v___x_910_);
lean_dec_ref(v_arg_909_);
lean_del_object(v___x_894_);
lean_dec(v_snd_892_);
lean_dec(v_fst_891_);
v___y_881_ = v_a_870_;
v___y_882_ = v_a_871_;
v___y_883_ = v_a_872_;
v___y_884_ = v_a_873_;
goto v___jp_880_;
}
else
{
lean_object* v___x_912_; uint8_t v___x_913_; 
v___x_912_ = l_Lean_Expr_appFnCleanup___redArg(v___x_910_);
v___x_913_ = l_Lean_Expr_isApp(v___x_912_);
if (v___x_913_ == 0)
{
lean_dec_ref(v___x_912_);
lean_dec_ref(v_arg_909_);
lean_del_object(v___x_894_);
lean_dec(v_snd_892_);
lean_dec(v_fst_891_);
v___y_881_ = v_a_870_;
v___y_882_ = v_a_871_;
v___y_883_ = v_a_872_;
v___y_884_ = v_a_873_;
goto v___jp_880_;
}
else
{
lean_object* v_arg_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
v_arg_914_ = lean_ctor_get(v___x_912_, 1);
lean_inc_ref(v_arg_914_);
v___x_915_ = l_Lean_Expr_appFnCleanup___redArg(v___x_912_);
v___x_916_ = l_Lean_Expr_isApp(v___x_915_);
if (v___x_916_ == 0)
{
lean_dec_ref(v___x_915_);
lean_dec_ref(v_arg_914_);
lean_dec_ref(v_arg_909_);
lean_del_object(v___x_894_);
lean_dec(v_snd_892_);
lean_dec(v_fst_891_);
v___y_881_ = v_a_870_;
v___y_882_ = v_a_871_;
v___y_883_ = v_a_872_;
v___y_884_ = v_a_873_;
goto v___jp_880_;
}
else
{
lean_object* v___x_917_; lean_object* v___x_918_; uint8_t v___x_919_; 
v___x_917_ = l_Lean_Expr_appFnCleanup___redArg(v___x_915_);
v___x_918_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__5));
v___x_919_ = l_Lean_Expr_isConstOf(v___x_917_, v___x_918_);
lean_dec_ref(v___x_917_);
if (v___x_919_ == 0)
{
lean_dec_ref(v_arg_914_);
lean_dec_ref(v_arg_909_);
lean_del_object(v___x_894_);
lean_dec(v_snd_892_);
lean_dec(v_fst_891_);
v___y_881_ = v_a_870_;
v___y_882_ = v_a_871_;
v___y_883_ = v_a_872_;
v___y_884_ = v_a_873_;
goto v___jp_880_;
}
else
{
lean_object* v___x_920_; uint8_t v___x_921_; 
lean_del_object(v___x_878_);
v___x_920_ = l_Lean_Expr_cleanupAnnotations(v_fst_891_);
v___x_921_ = l_Lean_Expr_isApp(v___x_920_);
if (v___x_921_ == 0)
{
lean_dec_ref(v___x_920_);
lean_dec_ref(v_arg_914_);
lean_dec_ref(v_arg_909_);
lean_del_object(v___x_894_);
lean_dec(v_snd_876_);
v___y_897_ = v_a_870_;
v___y_898_ = v_a_871_;
v___y_899_ = v_a_872_;
v___y_900_ = v_a_873_;
goto v___jp_896_;
}
else
{
lean_object* v___x_922_; uint8_t v___x_923_; 
v___x_922_ = l_Lean_Expr_appFnCleanup___redArg(v___x_920_);
v___x_923_ = l_Lean_Expr_isApp(v___x_922_);
if (v___x_923_ == 0)
{
lean_dec_ref(v___x_922_);
lean_dec_ref(v_arg_914_);
lean_dec_ref(v_arg_909_);
lean_del_object(v___x_894_);
lean_dec(v_snd_876_);
v___y_897_ = v_a_870_;
v___y_898_ = v_a_871_;
v___y_899_ = v_a_872_;
v___y_900_ = v_a_873_;
goto v___jp_896_;
}
else
{
lean_object* v_arg_924_; lean_object* v___x_925_; uint8_t v___x_926_; 
v_arg_924_ = lean_ctor_get(v___x_922_, 1);
lean_inc_ref(v_arg_924_);
v___x_925_ = l_Lean_Expr_appFnCleanup___redArg(v___x_922_);
v___x_926_ = l_Lean_Expr_isApp(v___x_925_);
if (v___x_926_ == 0)
{
lean_dec_ref(v___x_925_);
lean_dec_ref(v_arg_924_);
lean_dec_ref(v_arg_914_);
lean_dec_ref(v_arg_909_);
lean_del_object(v___x_894_);
lean_dec(v_snd_876_);
v___y_897_ = v_a_870_;
v___y_898_ = v_a_871_;
v___y_899_ = v_a_872_;
v___y_900_ = v_a_873_;
goto v___jp_896_;
}
else
{
lean_object* v___x_927_; uint8_t v___x_928_; 
v___x_927_ = l_Lean_Expr_appFnCleanup___redArg(v___x_925_);
v___x_928_ = l_Lean_Expr_isApp(v___x_927_);
if (v___x_928_ == 0)
{
lean_dec_ref(v___x_927_);
lean_dec_ref(v_arg_924_);
lean_dec_ref(v_arg_914_);
lean_dec_ref(v_arg_909_);
lean_del_object(v___x_894_);
lean_dec(v_snd_876_);
v___y_897_ = v_a_870_;
v___y_898_ = v_a_871_;
v___y_899_ = v_a_872_;
v___y_900_ = v_a_873_;
goto v___jp_896_;
}
else
{
lean_object* v___x_929_; uint8_t v___x_930_; 
v___x_929_ = l_Lean_Expr_appFnCleanup___redArg(v___x_927_);
v___x_930_ = l_Lean_Expr_isApp(v___x_929_);
if (v___x_930_ == 0)
{
lean_dec_ref(v___x_929_);
lean_dec_ref(v_arg_924_);
lean_dec_ref(v_arg_914_);
lean_dec_ref(v_arg_909_);
lean_del_object(v___x_894_);
lean_dec(v_snd_876_);
v___y_897_ = v_a_870_;
v___y_898_ = v_a_871_;
v___y_899_ = v_a_872_;
v___y_900_ = v_a_873_;
goto v___jp_896_;
}
else
{
lean_object* v___x_931_; uint8_t v___x_932_; 
v___x_931_ = l_Lean_Expr_appFnCleanup___redArg(v___x_929_);
v___x_932_ = l_Lean_Expr_isConstOf(v___x_931_, v___x_918_);
lean_dec_ref(v___x_931_);
if (v___x_932_ == 0)
{
lean_dec_ref(v_arg_924_);
lean_dec_ref(v_arg_914_);
lean_dec_ref(v_arg_909_);
lean_del_object(v___x_894_);
lean_dec(v_snd_876_);
v___y_897_ = v_a_870_;
v___y_898_ = v_a_871_;
v___y_899_ = v_a_872_;
v___y_900_ = v_a_873_;
goto v___jp_896_;
}
else
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_933_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__8));
v___x_934_ = lean_box(0);
v___x_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_935_, 0, v_arg_909_);
v___x_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_936_, 0, v_arg_924_);
v___x_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_937_, 0, v_arg_914_);
v___x_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_938_, 0, v_snd_876_);
v___x_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_939_, 0, v_snd_892_);
v___x_940_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__11, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__11_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__11);
v___x_941_ = lean_array_push(v___x_940_, v___x_935_);
v___x_942_ = lean_array_push(v___x_941_, v___x_936_);
v___x_943_ = lean_array_push(v___x_942_, v___x_937_);
v___x_944_ = lean_array_push(v___x_943_, v___x_934_);
v___x_945_ = lean_array_push(v___x_944_, v___x_934_);
v___x_946_ = lean_array_push(v___x_945_, v___x_938_);
v___x_947_ = lean_array_push(v___x_946_, v___x_939_);
v___x_948_ = l_Lean_Meta_mkAppOptM(v___x_933_, v___x_947_, v_a_870_, v_a_871_, v_a_872_, v_a_873_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v___x_950_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc_n(v_a_949_, 2);
lean_dec_ref_known(v___x_948_, 1);
lean_inc(v_a_873_);
lean_inc_ref(v_a_872_);
lean_inc(v_a_871_);
lean_inc_ref(v_a_870_);
v___x_950_ = lean_infer_type(v_a_949_, v_a_870_, v_a_871_, v_a_872_, v_a_873_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_961_; 
v_a_951_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_961_ == 0)
{
v___x_953_ = v___x_950_;
v_isShared_954_ = v_isSharedCheck_961_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_950_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_961_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_956_; 
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 1, v_a_949_);
lean_ctor_set(v___x_894_, 0, v_a_951_);
v___x_956_ = v___x_894_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_951_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v_a_949_);
v___x_956_ = v_reuseFailAlloc_960_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
lean_object* v___x_958_; 
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 0, v___x_956_);
v___x_958_ = v___x_953_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v___x_956_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
else
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_969_; 
lean_dec(v_a_949_);
lean_del_object(v___x_894_);
v_a_962_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_969_ == 0)
{
v___x_964_ = v___x_950_;
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_950_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_967_; 
if (v_isShared_965_ == 0)
{
v___x_967_ = v___x_964_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_962_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
else
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_977_; 
lean_del_object(v___x_894_);
v_a_970_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_977_ == 0)
{
v___x_972_ = v___x_948_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_948_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_975_; 
if (v_isShared_973_ == 0)
{
v___x_975_ = v___x_972_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_a_970_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
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
v___jp_896_:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_901_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__1);
v___x_902_ = l_Lean_indentExpr(v_snd_892_);
v___x_903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_901_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg(v___x_903_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
return v___x_904_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___boxed(lean_object* v_x_980_, lean_object* v_x_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd(v_x_980_, v_x_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_);
lean_dec(v_a_985_);
lean_dec_ref(v_a_984_);
lean_dec(v_a_983_);
lean_dec_ref(v_a_982_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg___lam__0(lean_object* v_k_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v_b_991_, lean_object* v_c_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v___x_998_; 
lean_inc(v___y_996_);
lean_inc_ref(v___y_995_);
lean_inc(v___y_994_);
lean_inc_ref(v___y_993_);
lean_inc(v___y_990_);
lean_inc_ref(v___y_989_);
v___x_998_ = lean_apply_9(v_k_988_, v_b_991_, v_c_992_, v___y_989_, v___y_990_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, lean_box(0));
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg___lam__0___boxed(lean_object* v_k_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v_b_1002_, lean_object* v_c_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg___lam__0(v_k_999_, v___y_1000_, v___y_1001_, v_b_1002_, v_c_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg(lean_object* v_type_1010_, lean_object* v_k_1011_, uint8_t v_cleanupAnnotations_1012_, uint8_t v_whnfType_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v___f_1021_; lean_object* v___x_1022_; 
lean_inc(v___y_1015_);
lean_inc_ref(v___y_1014_);
v___f_1021_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1021_, 0, v_k_1011_);
lean_closure_set(v___f_1021_, 1, v___y_1014_);
lean_closure_set(v___f_1021_, 2, v___y_1015_);
v___x_1022_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1010_, v___f_1021_, v_cleanupAnnotations_1012_, v_whnfType_1013_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
if (lean_obj_tag(v___x_1022_) == 0)
{
return v___x_1022_;
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_1022_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1022_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg___boxed(lean_object* v_type_1031_, lean_object* v_k_1032_, lean_object* v_cleanupAnnotations_1033_, lean_object* v_whnfType_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1042_; uint8_t v_whnfType_boxed_1043_; lean_object* v_res_1044_; 
v_cleanupAnnotations_boxed_1042_ = lean_unbox(v_cleanupAnnotations_1033_);
v_whnfType_boxed_1043_ = lean_unbox(v_whnfType_1034_);
v_res_1044_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg(v_type_1031_, v_k_1032_, v_cleanupAnnotations_boxed_1042_, v_whnfType_boxed_1043_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3(lean_object* v_00_u03b1_1045_, lean_object* v_type_1046_, lean_object* v_k_1047_, uint8_t v_cleanupAnnotations_1048_, uint8_t v_whnfType_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg(v_type_1046_, v_k_1047_, v_cleanupAnnotations_1048_, v_whnfType_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___boxed(lean_object* v_00_u03b1_1058_, lean_object* v_type_1059_, lean_object* v_k_1060_, lean_object* v_cleanupAnnotations_1061_, lean_object* v_whnfType_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1070_; uint8_t v_whnfType_boxed_1071_; lean_object* v_res_1072_; 
v_cleanupAnnotations_boxed_1070_ = lean_unbox(v_cleanupAnnotations_1061_);
v_whnfType_boxed_1071_ = lean_unbox(v_whnfType_1062_);
v_res_1072_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3(v_00_u03b1_1058_, v_type_1059_, v_k_1060_, v_cleanupAnnotations_boxed_1070_, v_whnfType_boxed_1071_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5___redArg(lean_object* v_e_1073_, lean_object* v_k_1074_, uint8_t v_cleanupAnnotations_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v___f_1083_; uint8_t v___x_1084_; uint8_t v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
lean_inc(v___y_1077_);
lean_inc_ref(v___y_1076_);
v___f_1083_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1083_, 0, v_k_1074_);
lean_closure_set(v___f_1083_, 1, v___y_1076_);
lean_closure_set(v___f_1083_, 2, v___y_1077_);
v___x_1084_ = 1;
v___x_1085_ = 0;
v___x_1086_ = lean_box(0);
v___x_1087_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1073_, v___x_1084_, v___x_1085_, v___x_1084_, v___x_1085_, v___x_1086_, v___f_1083_, v_cleanupAnnotations_1075_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
if (lean_obj_tag(v___x_1087_) == 0)
{
return v___x_1087_;
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1087_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1087_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5___redArg___boxed(lean_object* v_e_1096_, lean_object* v_k_1097_, lean_object* v_cleanupAnnotations_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1106_; lean_object* v_res_1107_; 
v_cleanupAnnotations_boxed_1106_ = lean_unbox(v_cleanupAnnotations_1098_);
v_res_1107_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5___redArg(v_e_1096_, v_k_1097_, v_cleanupAnnotations_boxed_1106_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5(lean_object* v_00_u03b1_1108_, lean_object* v_e_1109_, lean_object* v_k_1110_, uint8_t v_cleanupAnnotations_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5___redArg(v_e_1109_, v_k_1110_, v_cleanupAnnotations_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5___boxed(lean_object* v_00_u03b1_1120_, lean_object* v_e_1121_, lean_object* v_k_1122_, lean_object* v_cleanupAnnotations_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1131_; lean_object* v_res_1132_; 
v_cleanupAnnotations_boxed_1131_ = lean_unbox(v_cleanupAnnotations_1123_);
v_res_1132_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5(v_00_u03b1_1120_, v_e_1121_, v_k_1122_, v_cleanupAnnotations_boxed_1131_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__8___redArg(lean_object* v_msg_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v___f_1139_; lean_object* v___x_41426__overap_1140_; lean_object* v___x_1141_; 
v___f_1139_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps_spec__0___closed__0));
v___x_41426__overap_1140_ = lean_panic_fn_borrowed(v___f_1139_, v_msg_1133_);
lean_inc(v___y_1137_);
lean_inc_ref(v___y_1136_);
lean_inc(v___y_1135_);
lean_inc_ref(v___y_1134_);
v___x_1141_ = lean_apply_5(v___x_41426__overap_1140_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, lean_box(0));
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__8___redArg___boxed(lean_object* v_msg_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_panic___at___00Lean_Elab_partialFixpoint_spec__8___redArg(v_msg_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__8(lean_object* v_00_u03b1_1149_, lean_object* v_msg_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = l_panic___at___00Lean_Elab_partialFixpoint_spec__8___redArg(v_msg_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__8___boxed(lean_object* v_00_u03b1_1157_, lean_object* v_msg_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_panic___at___00Lean_Elab_partialFixpoint_spec__8(v_00_u03b1_1157_, v_msg_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18___redArg(lean_object* v_e_1165_, lean_object* v___y_1166_){
_start:
{
uint8_t v___x_1168_; 
v___x_1168_ = l_Lean_Expr_hasMVar(v_e_1165_);
if (v___x_1168_ == 0)
{
lean_object* v___x_1169_; 
v___x_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1169_, 0, v_e_1165_);
return v___x_1169_;
}
else
{
lean_object* v___x_1170_; lean_object* v_mctx_1171_; lean_object* v___x_1172_; lean_object* v_fst_1173_; lean_object* v_snd_1174_; lean_object* v___x_1175_; lean_object* v_cache_1176_; lean_object* v_zetaDeltaFVarIds_1177_; lean_object* v_postponed_1178_; lean_object* v_diag_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1188_; 
v___x_1170_ = lean_st_ref_get(v___y_1166_);
v_mctx_1171_ = lean_ctor_get(v___x_1170_, 0);
lean_inc_ref(v_mctx_1171_);
lean_dec(v___x_1170_);
v___x_1172_ = l_Lean_instantiateMVarsCore(v_mctx_1171_, v_e_1165_);
v_fst_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_fst_1173_);
v_snd_1174_ = lean_ctor_get(v___x_1172_, 1);
lean_inc(v_snd_1174_);
lean_dec_ref(v___x_1172_);
v___x_1175_ = lean_st_ref_take(v___y_1166_);
v_cache_1176_ = lean_ctor_get(v___x_1175_, 1);
v_zetaDeltaFVarIds_1177_ = lean_ctor_get(v___x_1175_, 2);
v_postponed_1178_ = lean_ctor_get(v___x_1175_, 3);
v_diag_1179_ = lean_ctor_get(v___x_1175_, 4);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1188_ == 0)
{
lean_object* v_unused_1189_; 
v_unused_1189_ = lean_ctor_get(v___x_1175_, 0);
lean_dec(v_unused_1189_);
v___x_1181_ = v___x_1175_;
v_isShared_1182_ = v_isSharedCheck_1188_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_diag_1179_);
lean_inc(v_postponed_1178_);
lean_inc(v_zetaDeltaFVarIds_1177_);
lean_inc(v_cache_1176_);
lean_dec(v___x_1175_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1188_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 0, v_snd_1174_);
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_snd_1174_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v_cache_1176_);
lean_ctor_set(v_reuseFailAlloc_1187_, 2, v_zetaDeltaFVarIds_1177_);
lean_ctor_set(v_reuseFailAlloc_1187_, 3, v_postponed_1178_);
lean_ctor_set(v_reuseFailAlloc_1187_, 4, v_diag_1179_);
v___x_1184_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1185_ = lean_st_ref_set(v___y_1166_, v___x_1184_);
v___x_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1186_, 0, v_fst_1173_);
return v___x_1186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18___redArg___boxed(lean_object* v_e_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18___redArg(v_e_1190_, v___y_1191_);
lean_dec(v___y_1191_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18(lean_object* v_e_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18___redArg(v_e_1194_, v___y_1198_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18___boxed(lean_object* v_e_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18(v_e_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__20___redArg(lean_object* v_type_1212_, lean_object* v_maxFVars_x3f_1213_, lean_object* v_k_1214_, uint8_t v_cleanupAnnotations_1215_, uint8_t v_whnfType_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v___f_1224_; lean_object* v___x_1225_; 
lean_inc(v___y_1218_);
lean_inc_ref(v___y_1217_);
v___f_1224_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1224_, 0, v_k_1214_);
lean_closure_set(v___f_1224_, 1, v___y_1217_);
lean_closure_set(v___f_1224_, 2, v___y_1218_);
v___x_1225_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1212_, v_maxFVars_x3f_1213_, v___f_1224_, v_cleanupAnnotations_1215_, v_whnfType_1216_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
if (lean_obj_tag(v___x_1225_) == 0)
{
return v___x_1225_;
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1225_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1225_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__20___redArg___boxed(lean_object* v_type_1234_, lean_object* v_maxFVars_x3f_1235_, lean_object* v_k_1236_, lean_object* v_cleanupAnnotations_1237_, lean_object* v_whnfType_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1246_; uint8_t v_whnfType_boxed_1247_; lean_object* v_res_1248_; 
v_cleanupAnnotations_boxed_1246_ = lean_unbox(v_cleanupAnnotations_1237_);
v_whnfType_boxed_1247_ = lean_unbox(v_whnfType_1238_);
v_res_1248_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__20___redArg(v_type_1234_, v_maxFVars_x3f_1235_, v_k_1236_, v_cleanupAnnotations_boxed_1246_, v_whnfType_boxed_1247_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__20(lean_object* v_00_u03b1_1249_, lean_object* v_type_1250_, lean_object* v_maxFVars_x3f_1251_, lean_object* v_k_1252_, uint8_t v_cleanupAnnotations_1253_, uint8_t v_whnfType_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__20___redArg(v_type_1250_, v_maxFVars_x3f_1251_, v_k_1252_, v_cleanupAnnotations_1253_, v_whnfType_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__20___boxed(lean_object* v_00_u03b1_1263_, lean_object* v_type_1264_, lean_object* v_maxFVars_x3f_1265_, lean_object* v_k_1266_, lean_object* v_cleanupAnnotations_1267_, lean_object* v_whnfType_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1276_; uint8_t v_whnfType_boxed_1277_; lean_object* v_res_1278_; 
v_cleanupAnnotations_boxed_1276_ = lean_unbox(v_cleanupAnnotations_1267_);
v_whnfType_boxed_1277_ = lean_unbox(v_whnfType_1268_);
v_res_1278_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__20(v_00_u03b1_1263_, v_type_1264_, v_maxFVars_x3f_1265_, v_k_1266_, v_cleanupAnnotations_boxed_1276_, v_whnfType_boxed_1277_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg___lam__0(lean_object* v_k_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v_b_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v___x_1288_; 
lean_inc(v___y_1286_);
lean_inc_ref(v___y_1285_);
lean_inc(v___y_1284_);
lean_inc_ref(v___y_1283_);
lean_inc(v___y_1281_);
lean_inc_ref(v___y_1280_);
v___x_1288_ = lean_apply_8(v_k_1279_, v_b_1282_, v___y_1280_, v___y_1281_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, lean_box(0));
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg___lam__0___boxed(lean_object* v_k_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v_b_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg___lam__0(v_k_1289_, v___y_1290_, v___y_1291_, v_b_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg(lean_object* v_perm_1299_, lean_object* v_type_1300_, lean_object* v_k_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v___f_1309_; lean_object* v___x_1310_; 
lean_inc(v___y_1303_);
lean_inc_ref(v___y_1302_);
v___f_1309_ = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1309_, 0, v_k_1301_);
lean_closure_set(v___f_1309_, 1, v___y_1302_);
lean_closure_set(v___f_1309_, 2, v___y_1303_);
v___x_1310_ = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl(lean_box(0), v_perm_1299_, v_type_1300_, v___f_1309_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
if (lean_obj_tag(v___x_1310_) == 0)
{
return v___x_1310_;
}
else
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1310_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1310_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1311_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg___boxed(lean_object* v_perm_1319_, lean_object* v_type_1320_, lean_object* v_k_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg(v_perm_1319_, v_type_1320_, v_k_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24(lean_object* v_00_u03b1_1330_, lean_object* v_perm_1331_, lean_object* v_type_1332_, lean_object* v_k_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg(v_perm_1331_, v_type_1332_, v_k_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___boxed(lean_object* v_00_u03b1_1342_, lean_object* v_perm_1343_, lean_object* v_type_1344_, lean_object* v_k_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24(v_00_u03b1_1342_, v_perm_1343_, v_type_1344_, v_k_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
return v_res_1353_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_partialFixpoint_spec__25___closed__0(void){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__25(lean_object* v_msg_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_47388__overap_1364_; lean_object* v___x_1365_; 
v___x_1363_ = lean_obj_once(&l_panic___at___00Lean_Elab_partialFixpoint_spec__25___closed__0, &l_panic___at___00Lean_Elab_partialFixpoint_spec__25___closed__0_once, _init_l_panic___at___00Lean_Elab_partialFixpoint_spec__25___closed__0);
v___x_47388__overap_1364_ = lean_panic_fn_borrowed(v___x_1363_, v_msg_1355_);
lean_inc(v___y_1361_);
lean_inc_ref(v___y_1360_);
lean_inc(v___y_1359_);
lean_inc_ref(v___y_1358_);
lean_inc(v___y_1357_);
lean_inc_ref(v___y_1356_);
v___x_1365_ = lean_apply_7(v___x_47388__overap_1364_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, lean_box(0));
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_partialFixpoint_spec__25___boxed(lean_object* v_msg_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l_panic___at___00Lean_Elab_partialFixpoint_spec__25(v_msg_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
return v_res_1374_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1375_; double v___x_1376_; 
v___x_1375_ = lean_unsigned_to_nat(0u);
v___x_1376_ = lean_float_of_nat(v___x_1375_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg(lean_object* v_cls_1380_, lean_object* v_msg_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v_ref_1387_; lean_object* v___x_1388_; lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1433_; 
v_ref_1387_ = lean_ctor_get(v___y_1384_, 5);
v___x_1388_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6_spec__7(v_msg_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1391_ = v___x_1388_;
v_isShared_1392_ = v_isSharedCheck_1433_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1388_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1433_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1393_; lean_object* v_traceState_1394_; lean_object* v_env_1395_; lean_object* v_nextMacroScope_1396_; lean_object* v_ngen_1397_; lean_object* v_auxDeclNGen_1398_; lean_object* v_cache_1399_; lean_object* v_messages_1400_; lean_object* v_infoState_1401_; lean_object* v_snapshotTasks_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1432_; 
v___x_1393_ = lean_st_ref_take(v___y_1385_);
v_traceState_1394_ = lean_ctor_get(v___x_1393_, 4);
v_env_1395_ = lean_ctor_get(v___x_1393_, 0);
v_nextMacroScope_1396_ = lean_ctor_get(v___x_1393_, 1);
v_ngen_1397_ = lean_ctor_get(v___x_1393_, 2);
v_auxDeclNGen_1398_ = lean_ctor_get(v___x_1393_, 3);
v_cache_1399_ = lean_ctor_get(v___x_1393_, 5);
v_messages_1400_ = lean_ctor_get(v___x_1393_, 6);
v_infoState_1401_ = lean_ctor_get(v___x_1393_, 7);
v_snapshotTasks_1402_ = lean_ctor_get(v___x_1393_, 8);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1404_ = v___x_1393_;
v_isShared_1405_ = v_isSharedCheck_1432_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_snapshotTasks_1402_);
lean_inc(v_infoState_1401_);
lean_inc(v_messages_1400_);
lean_inc(v_cache_1399_);
lean_inc(v_traceState_1394_);
lean_inc(v_auxDeclNGen_1398_);
lean_inc(v_ngen_1397_);
lean_inc(v_nextMacroScope_1396_);
lean_inc(v_env_1395_);
lean_dec(v___x_1393_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1432_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
uint64_t v_tid_1406_; lean_object* v_traces_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1431_; 
v_tid_1406_ = lean_ctor_get_uint64(v_traceState_1394_, sizeof(void*)*1);
v_traces_1407_ = lean_ctor_get(v_traceState_1394_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v_traceState_1394_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1409_ = v_traceState_1394_;
v_isShared_1410_ = v_isSharedCheck_1431_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_traces_1407_);
lean_dec(v_traceState_1394_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1431_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1411_; double v___x_1412_; uint8_t v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1421_; 
v___x_1411_ = lean_box(0);
v___x_1412_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__0);
v___x_1413_ = 0;
v___x_1414_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__1));
v___x_1415_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1415_, 0, v_cls_1380_);
lean_ctor_set(v___x_1415_, 1, v___x_1411_);
lean_ctor_set(v___x_1415_, 2, v___x_1414_);
lean_ctor_set_float(v___x_1415_, sizeof(void*)*3, v___x_1412_);
lean_ctor_set_float(v___x_1415_, sizeof(void*)*3 + 8, v___x_1412_);
lean_ctor_set_uint8(v___x_1415_, sizeof(void*)*3 + 16, v___x_1413_);
v___x_1416_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__2));
v___x_1417_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1415_);
lean_ctor_set(v___x_1417_, 1, v_a_1389_);
lean_ctor_set(v___x_1417_, 2, v___x_1416_);
lean_inc(v_ref_1387_);
v___x_1418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1418_, 0, v_ref_1387_);
lean_ctor_set(v___x_1418_, 1, v___x_1417_);
v___x_1419_ = l_Lean_PersistentArray_push___redArg(v_traces_1407_, v___x_1418_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 0, v___x_1419_);
v___x_1421_ = v___x_1409_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1419_);
lean_ctor_set_uint64(v_reuseFailAlloc_1430_, sizeof(void*)*1, v_tid_1406_);
v___x_1421_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
lean_object* v___x_1423_; 
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 4, v___x_1421_);
v___x_1423_ = v___x_1404_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_env_1395_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v_nextMacroScope_1396_);
lean_ctor_set(v_reuseFailAlloc_1429_, 2, v_ngen_1397_);
lean_ctor_set(v_reuseFailAlloc_1429_, 3, v_auxDeclNGen_1398_);
lean_ctor_set(v_reuseFailAlloc_1429_, 4, v___x_1421_);
lean_ctor_set(v_reuseFailAlloc_1429_, 5, v_cache_1399_);
lean_ctor_set(v_reuseFailAlloc_1429_, 6, v_messages_1400_);
lean_ctor_set(v_reuseFailAlloc_1429_, 7, v_infoState_1401_);
lean_ctor_set(v_reuseFailAlloc_1429_, 8, v_snapshotTasks_1402_);
v___x_1423_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1427_; 
v___x_1424_ = lean_st_ref_set(v___y_1385_, v___x_1423_);
v___x_1425_ = lean_box(0);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 0, v___x_1425_);
v___x_1427_ = v___x_1391_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1425_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___boxed(lean_object* v_cls_1434_, lean_object* v_msg_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg(v_cls_1434_, v_msg_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__22___redArg(size_t v_sz_1442_, size_t v_i_1443_, lean_object* v_bs_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
uint8_t v___x_1450_; 
v___x_1450_ = lean_usize_dec_lt(v_i_1443_, v_sz_1442_);
if (v___x_1450_ == 0)
{
lean_object* v___x_1451_; 
v___x_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1451_, 0, v_bs_1444_);
return v___x_1451_;
}
else
{
lean_object* v_v_1452_; lean_object* v___x_1453_; 
v_v_1452_ = lean_array_uget_borrowed(v_bs_1444_, v_i_1443_);
lean_inc(v_v_1452_);
v___x_1453_ = l_Lean_Elab_Mutual_cleanPreDef(v_v_1452_, v___x_1450_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v_a_1454_; lean_object* v___x_1455_; lean_object* v_bs_x27_1456_; size_t v___x_1457_; size_t v___x_1458_; lean_object* v___x_1459_; 
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
lean_inc(v_a_1454_);
lean_dec_ref_known(v___x_1453_, 1);
v___x_1455_ = lean_unsigned_to_nat(0u);
v_bs_x27_1456_ = lean_array_uset(v_bs_1444_, v_i_1443_, v___x_1455_);
v___x_1457_ = ((size_t)1ULL);
v___x_1458_ = lean_usize_add(v_i_1443_, v___x_1457_);
v___x_1459_ = lean_array_uset(v_bs_x27_1456_, v_i_1443_, v_a_1454_);
v_i_1443_ = v___x_1458_;
v_bs_1444_ = v___x_1459_;
goto _start;
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
lean_dec_ref(v_bs_1444_);
v_a_1461_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___x_1453_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1453_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1461_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__22___redArg___boxed(lean_object* v_sz_1469_, lean_object* v_i_1470_, lean_object* v_bs_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
size_t v_sz_boxed_1477_; size_t v_i_boxed_1478_; lean_object* v_res_1479_; 
v_sz_boxed_1477_ = lean_unbox_usize(v_sz_1469_);
lean_dec(v_sz_1469_);
v_i_boxed_1478_ = lean_unbox_usize(v_i_1470_);
lean_dec(v_i_1470_);
v_res_1479_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__22___redArg(v_sz_boxed_1477_, v_i_boxed_1478_, v_bs_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12___lam__0(lean_object* v_xs_1480_, lean_object* v_inst_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v___x_1489_; 
v___x_1489_ = l_Lean_Meta_mkInstPiOfInstsForall(v_xs_1480_, v_inst_1481_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12___lam__0___boxed(lean_object* v_xs_1490_, lean_object* v_inst_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12___lam__0(v_xs_1490_, v_inst_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12(size_t v_sz_1501_, size_t v_i_1502_, lean_object* v_bs_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
uint8_t v___x_1511_; 
v___x_1511_ = lean_usize_dec_lt(v_i_1502_, v_sz_1501_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1512_; 
v___x_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1512_, 0, v_bs_1503_);
return v___x_1512_;
}
else
{
lean_object* v___f_1513_; lean_object* v_v_1514_; uint8_t v___x_1515_; lean_object* v___x_1516_; 
v___f_1513_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12___closed__0));
v_v_1514_ = lean_array_uget_borrowed(v_bs_1503_, v_i_1502_);
v___x_1515_ = 0;
lean_inc(v_v_1514_);
v___x_1516_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5___redArg(v_v_1514_, v___f_1513_, v___x_1515_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v___x_1518_; lean_object* v_bs_x27_1519_; size_t v___x_1520_; size_t v___x_1521_; lean_object* v___x_1522_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1517_);
lean_dec_ref_known(v___x_1516_, 1);
v___x_1518_ = lean_unsigned_to_nat(0u);
v_bs_x27_1519_ = lean_array_uset(v_bs_1503_, v_i_1502_, v___x_1518_);
v___x_1520_ = ((size_t)1ULL);
v___x_1521_ = lean_usize_add(v_i_1502_, v___x_1520_);
v___x_1522_ = lean_array_uset(v_bs_x27_1519_, v_i_1502_, v_a_1517_);
v_i_1502_ = v___x_1521_;
v_bs_1503_ = v___x_1522_;
goto _start;
}
else
{
lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1531_; 
lean_dec_ref(v_bs_1503_);
v_a_1524_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1526_ = v___x_1516_;
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v___x_1516_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1529_; 
if (v_isShared_1527_ == 0)
{
v___x_1529_ = v___x_1526_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_a_1524_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12___boxed(lean_object* v_sz_1532_, lean_object* v_i_1533_, lean_object* v_bs_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
size_t v_sz_boxed_1542_; size_t v_i_boxed_1543_; lean_object* v_res_1544_; 
v_sz_boxed_1542_ = lean_unbox_usize(v_sz_1532_);
lean_dec(v_sz_1532_);
v_i_boxed_1543_ = lean_unbox_usize(v_i_1533_);
lean_dec(v_i_1533_);
v_res_1544_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12(v_sz_boxed_1542_, v_i_boxed_1543_, v_bs_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__10___redArg(lean_object* v___x_1545_, lean_object* v_fixedArgs_1546_, size_t v_sz_1547_, size_t v_i_1548_, lean_object* v_bs_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
uint8_t v___x_1555_; 
v___x_1555_ = lean_usize_dec_lt(v_i_1548_, v_sz_1547_);
if (v___x_1555_ == 0)
{
lean_object* v___x_1556_; 
lean_dec_ref(v_fixedArgs_1546_);
v___x_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1556_, 0, v_bs_1549_);
return v___x_1556_;
}
else
{
lean_object* v___x_1557_; lean_object* v_v_1558_; lean_object* v___x_1559_; lean_object* v_bs_x27_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1557_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1);
v_v_1558_ = lean_array_uget(v_bs_1549_, v_i_1548_);
v___x_1559_ = lean_unsigned_to_nat(0u);
v_bs_x27_1560_ = lean_array_uset(v_bs_1549_, v_i_1548_, v___x_1559_);
v___x_1561_ = lean_usize_to_nat(v_i_1548_);
v___x_1562_ = lean_array_get_borrowed(v___x_1557_, v___x_1545_, v___x_1561_);
lean_dec(v___x_1561_);
lean_inc_ref(v_fixedArgs_1546_);
lean_inc(v___x_1562_);
v___x_1563_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_1562_, v_v_1558_, v_fixedArgs_1546_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; size_t v___x_1565_; size_t v___x_1566_; lean_object* v___x_1567_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc(v_a_1564_);
lean_dec_ref_known(v___x_1563_, 1);
v___x_1565_ = ((size_t)1ULL);
v___x_1566_ = lean_usize_add(v_i_1548_, v___x_1565_);
v___x_1567_ = lean_array_uset(v_bs_x27_1560_, v_i_1548_, v_a_1564_);
v_i_1548_ = v___x_1566_;
v_bs_1549_ = v___x_1567_;
goto _start;
}
else
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
lean_dec_ref(v_bs_x27_1560_);
lean_dec_ref(v_fixedArgs_1546_);
v_a_1569_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___x_1563_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1563_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__10___redArg___boxed(lean_object* v___x_1577_, lean_object* v_fixedArgs_1578_, lean_object* v_sz_1579_, lean_object* v_i_1580_, lean_object* v_bs_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
size_t v_sz_boxed_1587_; size_t v_i_boxed_1588_; lean_object* v_res_1589_; 
v_sz_boxed_1587_ = lean_unbox_usize(v_sz_1579_);
lean_dec(v_sz_1579_);
v_i_boxed_1588_ = lean_unbox_usize(v_i_1580_);
lean_dec(v_i_1580_);
v_res_1589_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__10___redArg(v___x_1577_, v_fixedArgs_1578_, v_sz_boxed_1587_, v_i_boxed_1588_, v_bs_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec_ref(v___x_1577_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__11___redArg(lean_object* v___x_1590_, lean_object* v_fixedArgs_1591_, size_t v_sz_1592_, size_t v_i_1593_, lean_object* v_bs_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
uint8_t v___x_1600_; 
v___x_1600_ = lean_usize_dec_lt(v_i_1593_, v_sz_1592_);
if (v___x_1600_ == 0)
{
lean_object* v___x_1601_; 
lean_dec_ref(v_fixedArgs_1591_);
v___x_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1601_, 0, v_bs_1594_);
return v___x_1601_;
}
else
{
lean_object* v_v_1602_; lean_object* v_type_1603_; lean_object* v___x_1604_; lean_object* v_bs_x27_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v_v_1602_ = lean_array_uget_borrowed(v_bs_1594_, v_i_1593_);
v_type_1603_ = lean_ctor_get(v_v_1602_, 6);
lean_inc_ref(v_type_1603_);
v___x_1604_ = lean_unsigned_to_nat(0u);
v_bs_x27_1605_ = lean_array_uset(v_bs_1594_, v_i_1593_, v___x_1604_);
v___x_1606_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1);
v___x_1607_ = lean_usize_to_nat(v_i_1593_);
v___x_1608_ = lean_array_get_borrowed(v___x_1606_, v___x_1590_, v___x_1607_);
lean_dec(v___x_1607_);
lean_inc_ref(v_fixedArgs_1591_);
lean_inc(v___x_1608_);
v___x_1609_ = l_Lean_Elab_FixedParamPerm_instantiateForall(v___x_1608_, v_type_1603_, v_fixedArgs_1591_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; size_t v___x_1611_; size_t v___x_1612_; lean_object* v___x_1613_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1610_);
lean_dec_ref_known(v___x_1609_, 1);
v___x_1611_ = ((size_t)1ULL);
v___x_1612_ = lean_usize_add(v_i_1593_, v___x_1611_);
v___x_1613_ = lean_array_uset(v_bs_x27_1605_, v_i_1593_, v_a_1610_);
v_i_1593_ = v___x_1612_;
v_bs_1594_ = v___x_1613_;
goto _start;
}
else
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
lean_dec_ref(v_bs_x27_1605_);
lean_dec_ref(v_fixedArgs_1591_);
v_a_1615_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1617_ = v___x_1609_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1609_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1620_; 
if (v_isShared_1618_ == 0)
{
v___x_1620_ = v___x_1617_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1615_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__11___redArg___boxed(lean_object* v___x_1623_, lean_object* v_fixedArgs_1624_, lean_object* v_sz_1625_, lean_object* v_i_1626_, lean_object* v_bs_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
size_t v_sz_boxed_1633_; size_t v_i_boxed_1634_; lean_object* v_res_1635_; 
v_sz_boxed_1633_ = lean_unbox_usize(v_sz_1625_);
lean_dec(v_sz_1625_);
v_i_boxed_1634_ = lean_unbox_usize(v_i_1626_);
lean_dec(v_i_1626_);
v_res_1635_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__11___redArg(v___x_1623_, v_fixedArgs_1624_, v_sz_boxed_1633_, v_i_boxed_1634_, v_bs_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec_ref(v___x_1623_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg___lam__0(lean_object* v___x_1636_, lean_object* v___x_1637_, lean_object* v___y_1638_, lean_object* v___x_1639_, lean_object* v___x_1640_, lean_object* v_a_1641_, uint8_t v___x_1642_, uint8_t v___x_1643_, uint8_t v___x_1644_, lean_object* v_ref_1645_, uint8_t v_kind_1646_, lean_object* v_levelParams_1647_, lean_object* v_modifiers_1648_, lean_object* v_declName_1649_, lean_object* v_binders_1650_, lean_object* v_numSectionVars_1651_, lean_object* v_type_1652_, lean_object* v_termination_1653_, lean_object* v_params_1654_, lean_object* v_x_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1663_ = l_Lean_Elab_FixedParamPerm_pickFixed___redArg(v___x_1636_, v_params_1654_);
v___x_1664_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v___x_1636_, v_params_1654_);
v___x_1665_ = lean_box(0);
v___x_1666_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__0(v___x_1637_, v___x_1665_);
v___x_1667_ = l_Lean_mkConst(v___y_1638_, v___x_1666_);
v___x_1668_ = l_Lean_mkAppN(v___x_1667_, v___x_1663_);
lean_dec_ref(v___x_1663_);
v___x_1669_ = l_Lean_Meta_PProdN_proj(v___x_1639_, v___x_1640_, v_a_1641_, v___x_1668_);
v___x_1670_ = l_Lean_mkAppN(v___x_1669_, v___x_1664_);
lean_dec_ref(v___x_1664_);
v___x_1671_ = l_Lean_Meta_mkLambdaFVars(v_params_1654_, v___x_1670_, v___x_1642_, v___x_1643_, v___x_1643_, v___x_1643_, v___x_1644_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1680_; 
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1674_ = v___x_1671_;
v_isShared_1675_ = v_isSharedCheck_1680_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1671_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1680_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1676_; lean_object* v___x_1678_; 
v___x_1676_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_1676_, 0, v_ref_1645_);
lean_ctor_set(v___x_1676_, 1, v_levelParams_1647_);
lean_ctor_set(v___x_1676_, 2, v_modifiers_1648_);
lean_ctor_set(v___x_1676_, 3, v_declName_1649_);
lean_ctor_set(v___x_1676_, 4, v_binders_1650_);
lean_ctor_set(v___x_1676_, 5, v_numSectionVars_1651_);
lean_ctor_set(v___x_1676_, 6, v_type_1652_);
lean_ctor_set(v___x_1676_, 7, v_a_1672_);
lean_ctor_set(v___x_1676_, 8, v_termination_1653_);
lean_ctor_set_uint8(v___x_1676_, sizeof(void*)*9, v_kind_1646_);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 0, v___x_1676_);
v___x_1678_ = v___x_1674_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v___x_1676_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
else
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
lean_dec_ref(v_termination_1653_);
lean_dec_ref(v_type_1652_);
lean_dec(v_numSectionVars_1651_);
lean_dec(v_binders_1650_);
lean_dec(v_declName_1649_);
lean_dec_ref(v_modifiers_1648_);
lean_dec(v_levelParams_1647_);
lean_dec(v_ref_1645_);
v_a_1681_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1683_ = v___x_1671_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1671_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
v___x_1686_ = v___x_1683_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_a_1681_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_1689_ = _args[0];
lean_object* v___x_1690_ = _args[1];
lean_object* v___y_1691_ = _args[2];
lean_object* v___x_1692_ = _args[3];
lean_object* v___x_1693_ = _args[4];
lean_object* v_a_1694_ = _args[5];
lean_object* v___x_1695_ = _args[6];
lean_object* v___x_1696_ = _args[7];
lean_object* v___x_1697_ = _args[8];
lean_object* v_ref_1698_ = _args[9];
lean_object* v_kind_1699_ = _args[10];
lean_object* v_levelParams_1700_ = _args[11];
lean_object* v_modifiers_1701_ = _args[12];
lean_object* v_declName_1702_ = _args[13];
lean_object* v_binders_1703_ = _args[14];
lean_object* v_numSectionVars_1704_ = _args[15];
lean_object* v_type_1705_ = _args[16];
lean_object* v_termination_1706_ = _args[17];
lean_object* v_params_1707_ = _args[18];
lean_object* v_x_1708_ = _args[19];
lean_object* v___y_1709_ = _args[20];
lean_object* v___y_1710_ = _args[21];
lean_object* v___y_1711_ = _args[22];
lean_object* v___y_1712_ = _args[23];
lean_object* v___y_1713_ = _args[24];
lean_object* v___y_1714_ = _args[25];
lean_object* v___y_1715_ = _args[26];
_start:
{
uint8_t v___x_56036__boxed_1716_; uint8_t v___x_56037__boxed_1717_; uint8_t v___x_56038__boxed_1718_; uint8_t v_kind_boxed_1719_; lean_object* v_res_1720_; 
v___x_56036__boxed_1716_ = lean_unbox(v___x_1695_);
v___x_56037__boxed_1717_ = lean_unbox(v___x_1696_);
v___x_56038__boxed_1718_ = lean_unbox(v___x_1697_);
v_kind_boxed_1719_ = lean_unbox(v_kind_1699_);
v_res_1720_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg___lam__0(v___x_1689_, v___x_1690_, v___y_1691_, v___x_1692_, v___x_1693_, v_a_1694_, v___x_56036__boxed_1716_, v___x_56037__boxed_1717_, v___x_56038__boxed_1718_, v_ref_1698_, v_kind_boxed_1719_, v_levelParams_1700_, v_modifiers_1701_, v_declName_1702_, v_binders_1703_, v_numSectionVars_1704_, v_type_1705_, v_termination_1706_, v_params_1707_, v_x_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec_ref(v_x_1708_);
lean_dec_ref(v_params_1707_);
lean_dec(v___x_1693_);
lean_dec(v___x_1692_);
lean_dec_ref(v___x_1689_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg(lean_object* v___x_1721_, lean_object* v___x_1722_, lean_object* v___y_1723_, lean_object* v___x_1724_, lean_object* v_a_1725_, size_t v_sz_1726_, size_t v_i_1727_, lean_object* v_bs_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
uint8_t v___x_1736_; 
v___x_1736_ = lean_usize_dec_lt(v_i_1727_, v_sz_1726_);
if (v___x_1736_ == 0)
{
lean_object* v___x_1737_; 
lean_dec_ref(v_a_1725_);
lean_dec(v___x_1724_);
lean_dec(v___y_1723_);
lean_dec(v___x_1722_);
v___x_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1737_, 0, v_bs_1728_);
return v___x_1737_;
}
else
{
lean_object* v_v_1738_; lean_object* v_ref_1739_; uint8_t v_kind_1740_; lean_object* v_levelParams_1741_; lean_object* v_modifiers_1742_; lean_object* v_declName_1743_; lean_object* v_binders_1744_; lean_object* v_numSectionVars_1745_; lean_object* v_type_1746_; lean_object* v_termination_1747_; lean_object* v___x_1748_; lean_object* v_bs_x27_1749_; lean_object* v___x_1750_; uint8_t v___x_1751_; uint8_t v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___f_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v_v_1738_ = lean_array_uget_borrowed(v_bs_1728_, v_i_1727_);
v_ref_1739_ = lean_ctor_get(v_v_1738_, 0);
lean_inc(v_ref_1739_);
v_kind_1740_ = lean_ctor_get_uint8(v_v_1738_, sizeof(void*)*9);
v_levelParams_1741_ = lean_ctor_get(v_v_1738_, 1);
lean_inc(v_levelParams_1741_);
v_modifiers_1742_ = lean_ctor_get(v_v_1738_, 2);
lean_inc_ref(v_modifiers_1742_);
v_declName_1743_ = lean_ctor_get(v_v_1738_, 3);
lean_inc(v_declName_1743_);
v_binders_1744_ = lean_ctor_get(v_v_1738_, 4);
lean_inc(v_binders_1744_);
v_numSectionVars_1745_ = lean_ctor_get(v_v_1738_, 5);
lean_inc(v_numSectionVars_1745_);
v_type_1746_ = lean_ctor_get(v_v_1738_, 6);
lean_inc_ref_n(v_type_1746_, 2);
v_termination_1747_ = lean_ctor_get(v_v_1738_, 8);
lean_inc_ref(v_termination_1747_);
v___x_1748_ = lean_unsigned_to_nat(0u);
v_bs_x27_1749_ = lean_array_uset(v_bs_1728_, v_i_1727_, v___x_1748_);
v___x_1750_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1);
v___x_1751_ = 0;
v___x_1752_ = 1;
v___x_1753_ = lean_usize_to_nat(v_i_1727_);
v___x_1754_ = lean_array_get_borrowed(v___x_1750_, v___x_1721_, v___x_1753_);
v___x_1755_ = lean_box(v___x_1751_);
v___x_1756_ = lean_box(v___x_1736_);
v___x_1757_ = lean_box(v___x_1752_);
v___x_1758_ = lean_box(v_kind_1740_);
lean_inc_ref(v_a_1725_);
lean_inc(v___x_1724_);
lean_inc(v___y_1723_);
lean_inc(v___x_1722_);
lean_inc(v___x_1754_);
v___f_1759_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg___lam__0___boxed), 27, 18);
lean_closure_set(v___f_1759_, 0, v___x_1754_);
lean_closure_set(v___f_1759_, 1, v___x_1722_);
lean_closure_set(v___f_1759_, 2, v___y_1723_);
lean_closure_set(v___f_1759_, 3, v___x_1724_);
lean_closure_set(v___f_1759_, 4, v___x_1753_);
lean_closure_set(v___f_1759_, 5, v_a_1725_);
lean_closure_set(v___f_1759_, 6, v___x_1755_);
lean_closure_set(v___f_1759_, 7, v___x_1756_);
lean_closure_set(v___f_1759_, 8, v___x_1757_);
lean_closure_set(v___f_1759_, 9, v_ref_1739_);
lean_closure_set(v___f_1759_, 10, v___x_1758_);
lean_closure_set(v___f_1759_, 11, v_levelParams_1741_);
lean_closure_set(v___f_1759_, 12, v_modifiers_1742_);
lean_closure_set(v___f_1759_, 13, v_declName_1743_);
lean_closure_set(v___f_1759_, 14, v_binders_1744_);
lean_closure_set(v___f_1759_, 15, v_numSectionVars_1745_);
lean_closure_set(v___f_1759_, 16, v_type_1746_);
lean_closure_set(v___f_1759_, 17, v_termination_1747_);
v___x_1760_ = lean_array_get_size(v___x_1754_);
v___x_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1760_);
v___x_1762_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_partialFixpoint_spec__20___redArg(v_type_1746_, v___x_1761_, v___f_1759_, v___x_1751_, v___x_1751_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; size_t v___x_1764_; size_t v___x_1765_; lean_object* v___x_1766_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
lean_inc(v_a_1763_);
lean_dec_ref_known(v___x_1762_, 1);
v___x_1764_ = ((size_t)1ULL);
v___x_1765_ = lean_usize_add(v_i_1727_, v___x_1764_);
v___x_1766_ = lean_array_uset(v_bs_x27_1749_, v_i_1727_, v_a_1763_);
v_i_1727_ = v___x_1765_;
v_bs_1728_ = v___x_1766_;
goto _start;
}
else
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
lean_dec_ref(v_bs_x27_1749_);
lean_dec_ref(v_a_1725_);
lean_dec(v___x_1724_);
lean_dec(v___y_1723_);
lean_dec(v___x_1722_);
v_a_1768_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1770_ = v___x_1762_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1762_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg___boxed(lean_object* v___x_1776_, lean_object* v___x_1777_, lean_object* v___y_1778_, lean_object* v___x_1779_, lean_object* v_a_1780_, lean_object* v_sz_1781_, lean_object* v_i_1782_, lean_object* v_bs_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
size_t v_sz_boxed_1791_; size_t v_i_boxed_1792_; lean_object* v_res_1793_; 
v_sz_boxed_1791_ = lean_unbox_usize(v_sz_1781_);
lean_dec(v_sz_1781_);
v_i_boxed_1792_ = lean_unbox_usize(v_i_1782_);
lean_dec(v_i_1782_);
v_res_1793_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg(v___x_1776_, v___x_1777_, v___y_1778_, v___x_1779_, v_a_1780_, v_sz_boxed_1791_, v_i_boxed_1792_, v_bs_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec_ref(v___x_1776_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__23(size_t v_sz_1794_, size_t v_i_1795_, lean_object* v_bs_1796_){
_start:
{
uint8_t v___x_1797_; 
v___x_1797_ = lean_usize_dec_lt(v_i_1795_, v_sz_1794_);
if (v___x_1797_ == 0)
{
return v_bs_1796_;
}
else
{
lean_object* v_v_1798_; uint8_t v_fixpointType_1799_; lean_object* v___x_1800_; lean_object* v_bs_x27_1801_; size_t v___x_1802_; size_t v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v_v_1798_ = lean_array_uget_borrowed(v_bs_1796_, v_i_1795_);
v_fixpointType_1799_ = lean_ctor_get_uint8(v_v_1798_, sizeof(void*)*2);
v___x_1800_ = lean_unsigned_to_nat(0u);
v_bs_x27_1801_ = lean_array_uset(v_bs_1796_, v_i_1795_, v___x_1800_);
v___x_1802_ = ((size_t)1ULL);
v___x_1803_ = lean_usize_add(v_i_1795_, v___x_1802_);
v___x_1804_ = lean_box(v_fixpointType_1799_);
v___x_1805_ = lean_array_uset(v_bs_x27_1801_, v_i_1795_, v___x_1804_);
v_i_1795_ = v___x_1803_;
v_bs_1796_ = v___x_1805_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__23___boxed(lean_object* v_sz_1807_, lean_object* v_i_1808_, lean_object* v_bs_1809_){
_start:
{
size_t v_sz_boxed_1810_; size_t v_i_boxed_1811_; lean_object* v_res_1812_; 
v_sz_boxed_1810_ = lean_unbox_usize(v_sz_1807_);
lean_dec(v_sz_1807_);
v_i_boxed_1811_ = lean_unbox_usize(v_i_1808_);
lean_dec(v_i_1808_);
v_res_1812_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__23(v_sz_boxed_1810_, v_i_boxed_1811_, v_bs_1809_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16___redArg(lean_object* v_env_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v___x_1817_; lean_object* v_nextMacroScope_1818_; lean_object* v_ngen_1819_; lean_object* v_auxDeclNGen_1820_; lean_object* v_traceState_1821_; lean_object* v_messages_1822_; lean_object* v_infoState_1823_; lean_object* v_snapshotTasks_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1850_; 
v___x_1817_ = lean_st_ref_take(v___y_1815_);
v_nextMacroScope_1818_ = lean_ctor_get(v___x_1817_, 1);
v_ngen_1819_ = lean_ctor_get(v___x_1817_, 2);
v_auxDeclNGen_1820_ = lean_ctor_get(v___x_1817_, 3);
v_traceState_1821_ = lean_ctor_get(v___x_1817_, 4);
v_messages_1822_ = lean_ctor_get(v___x_1817_, 6);
v_infoState_1823_ = lean_ctor_get(v___x_1817_, 7);
v_snapshotTasks_1824_ = lean_ctor_get(v___x_1817_, 8);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1850_ == 0)
{
lean_object* v_unused_1851_; lean_object* v_unused_1852_; 
v_unused_1851_ = lean_ctor_get(v___x_1817_, 5);
lean_dec(v_unused_1851_);
v_unused_1852_ = lean_ctor_get(v___x_1817_, 0);
lean_dec(v_unused_1852_);
v___x_1826_ = v___x_1817_;
v_isShared_1827_ = v_isSharedCheck_1850_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_snapshotTasks_1824_);
lean_inc(v_infoState_1823_);
lean_inc(v_messages_1822_);
lean_inc(v_traceState_1821_);
lean_inc(v_auxDeclNGen_1820_);
lean_inc(v_ngen_1819_);
lean_inc(v_nextMacroScope_1818_);
lean_dec(v___x_1817_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1850_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1828_; lean_object* v___x_1830_; 
v___x_1828_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2);
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 5, v___x_1828_);
lean_ctor_set(v___x_1826_, 0, v_env_1813_);
v___x_1830_ = v___x_1826_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_env_1813_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v_nextMacroScope_1818_);
lean_ctor_set(v_reuseFailAlloc_1849_, 2, v_ngen_1819_);
lean_ctor_set(v_reuseFailAlloc_1849_, 3, v_auxDeclNGen_1820_);
lean_ctor_set(v_reuseFailAlloc_1849_, 4, v_traceState_1821_);
lean_ctor_set(v_reuseFailAlloc_1849_, 5, v___x_1828_);
lean_ctor_set(v_reuseFailAlloc_1849_, 6, v_messages_1822_);
lean_ctor_set(v_reuseFailAlloc_1849_, 7, v_infoState_1823_);
lean_ctor_set(v_reuseFailAlloc_1849_, 8, v_snapshotTasks_1824_);
v___x_1830_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v_mctx_1833_; lean_object* v_zetaDeltaFVarIds_1834_; lean_object* v_postponed_1835_; lean_object* v_diag_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1847_; 
v___x_1831_ = lean_st_ref_set(v___y_1815_, v___x_1830_);
v___x_1832_ = lean_st_ref_take(v___y_1814_);
v_mctx_1833_ = lean_ctor_get(v___x_1832_, 0);
v_zetaDeltaFVarIds_1834_ = lean_ctor_get(v___x_1832_, 2);
v_postponed_1835_ = lean_ctor_get(v___x_1832_, 3);
v_diag_1836_ = lean_ctor_get(v___x_1832_, 4);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1847_ == 0)
{
lean_object* v_unused_1848_; 
v_unused_1848_ = lean_ctor_get(v___x_1832_, 1);
lean_dec(v_unused_1848_);
v___x_1838_ = v___x_1832_;
v_isShared_1839_ = v_isSharedCheck_1847_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_diag_1836_);
lean_inc(v_postponed_1835_);
lean_inc(v_zetaDeltaFVarIds_1834_);
lean_inc(v_mctx_1833_);
lean_dec(v___x_1832_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1847_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1840_; lean_object* v___x_1842_; 
v___x_1840_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 1, v___x_1840_);
v___x_1842_ = v___x_1838_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_mctx_1833_);
lean_ctor_set(v_reuseFailAlloc_1846_, 1, v___x_1840_);
lean_ctor_set(v_reuseFailAlloc_1846_, 2, v_zetaDeltaFVarIds_1834_);
lean_ctor_set(v_reuseFailAlloc_1846_, 3, v_postponed_1835_);
lean_ctor_set(v_reuseFailAlloc_1846_, 4, v_diag_1836_);
v___x_1842_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1843_ = lean_st_ref_set(v___y_1814_, v___x_1842_);
v___x_1844_ = lean_box(0);
v___x_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
return v___x_1845_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16___redArg___boxed(lean_object* v_env_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16___redArg(v_env_1853_, v___y_1854_, v___y_1855_);
lean_dec(v___y_1855_);
lean_dec(v___y_1854_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14___redArg(lean_object* v_env_1858_, lean_object* v_x_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v___x_1867_; lean_object* v_env_1868_; lean_object* v_a_1870_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1867_ = lean_st_ref_get(v___y_1865_);
v_env_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc_ref(v_env_1868_);
lean_dec(v___x_1867_);
v___x_1880_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16___redArg(v_env_1858_, v___y_1863_, v___y_1865_);
lean_dec_ref(v___x_1880_);
lean_inc(v___y_1865_);
lean_inc_ref(v___y_1864_);
lean_inc(v___y_1863_);
lean_inc_ref(v___y_1862_);
lean_inc(v___y_1861_);
lean_inc_ref(v___y_1860_);
v___x_1881_ = lean_apply_7(v_x_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, lean_box(0));
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_a_1882_; lean_object* v___x_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1890_; 
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
lean_inc(v_a_1882_);
lean_dec_ref_known(v___x_1881_, 1);
v___x_1883_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16___redArg(v_env_1868_, v___y_1863_, v___y_1865_);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1890_ == 0)
{
lean_object* v_unused_1891_; 
v_unused_1891_ = lean_ctor_get(v___x_1883_, 0);
lean_dec(v_unused_1891_);
v___x_1885_ = v___x_1883_;
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
else
{
lean_dec(v___x_1883_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 0, v_a_1882_);
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1882_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
else
{
lean_object* v_a_1892_; 
v_a_1892_ = lean_ctor_get(v___x_1881_, 0);
lean_inc(v_a_1892_);
lean_dec_ref_known(v___x_1881_, 1);
v_a_1870_ = v_a_1892_;
goto v___jp_1869_;
}
v___jp_1869_:
{
lean_object* v___x_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1878_; 
v___x_1871_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16___redArg(v_env_1868_, v___y_1863_, v___y_1865_);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1878_ == 0)
{
lean_object* v_unused_1879_; 
v_unused_1879_ = lean_ctor_get(v___x_1871_, 0);
lean_dec(v_unused_1879_);
v___x_1873_ = v___x_1871_;
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
else
{
lean_dec(v___x_1871_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1876_; 
if (v_isShared_1874_ == 0)
{
lean_ctor_set_tag(v___x_1873_, 1);
lean_ctor_set(v___x_1873_, 0, v_a_1870_);
v___x_1876_ = v___x_1873_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1870_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14___redArg___boxed(lean_object* v_env_1893_, lean_object* v_x_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14___redArg(v_env_1893_, v_x_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13___redArg(lean_object* v_as_1903_, size_t v_i_1904_, size_t v_stop_1905_, lean_object* v_b_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
uint8_t v___x_1910_; 
v___x_1910_ = lean_usize_dec_eq(v_i_1904_, v_stop_1905_);
if (v___x_1910_ == 0)
{
lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1911_ = lean_array_uget_borrowed(v_as_1903_, v_i_1904_);
v___x_1912_ = l_Lean_Elab_addAsAxiom___redArg(v___x_1911_, v___y_1907_, v___y_1908_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1913_; size_t v___x_1914_; size_t v___x_1915_; 
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
lean_inc(v_a_1913_);
lean_dec_ref_known(v___x_1912_, 1);
v___x_1914_ = ((size_t)1ULL);
v___x_1915_ = lean_usize_add(v_i_1904_, v___x_1914_);
v_i_1904_ = v___x_1915_;
v_b_1906_ = v_a_1913_;
goto _start;
}
else
{
return v___x_1912_;
}
}
else
{
lean_object* v___x_1917_; 
v___x_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1917_, 0, v_b_1906_);
return v___x_1917_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13___redArg___boxed(lean_object* v_as_1918_, lean_object* v_i_1919_, lean_object* v_stop_1920_, lean_object* v_b_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
size_t v_i_boxed_1925_; size_t v_stop_boxed_1926_; lean_object* v_res_1927_; 
v_i_boxed_1925_ = lean_unbox_usize(v_i_1919_);
lean_dec(v_i_1919_);
v_stop_boxed_1926_ = lean_unbox_usize(v_stop_1920_);
lean_dec(v_stop_1920_);
v_res_1927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13___redArg(v_as_1918_, v_i_boxed_1925_, v_stop_boxed_1926_, v_b_1921_, v___y_1922_, v___y_1923_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec_ref(v_as_1918_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__0(lean_object* v___x_1928_, lean_object* v___x_1929_, lean_object* v___x_1930_, lean_object* v_a_1931_, lean_object* v_f_1932_, lean_object* v_a_1933_, lean_object* v_preDefs_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_){
_start:
{
lean_object* v___y_1943_; uint8_t v___x_1953_; 
v___x_1953_ = lean_nat_dec_lt(v___x_1928_, v___x_1929_);
if (v___x_1953_ == 0)
{
lean_object* v___x_1954_; 
v___x_1954_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps(v___x_1930_, v_a_1931_, v_f_1932_, v_a_1933_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
return v___x_1954_;
}
else
{
lean_object* v___x_1955_; lean_object* v___x_1956_; uint8_t v___x_1957_; 
v___x_1955_ = lean_box(0);
v___x_1956_ = lean_array_get_size(v_preDefs_1934_);
v___x_1957_ = lean_nat_dec_le(v___x_1929_, v___x_1956_);
if (v___x_1957_ == 0)
{
uint8_t v___x_1958_; 
v___x_1958_ = lean_nat_dec_lt(v___x_1928_, v___x_1956_);
if (v___x_1958_ == 0)
{
lean_object* v___x_1959_; 
v___x_1959_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps(v___x_1930_, v_a_1931_, v_f_1932_, v_a_1933_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
return v___x_1959_;
}
else
{
size_t v___x_1960_; size_t v___x_1961_; lean_object* v___x_1962_; 
v___x_1960_ = ((size_t)0ULL);
v___x_1961_ = lean_usize_of_nat(v___x_1956_);
v___x_1962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13___redArg(v_preDefs_1934_, v___x_1960_, v___x_1961_, v___x_1955_, v___y_1939_, v___y_1940_);
v___y_1943_ = v___x_1962_;
goto v___jp_1942_;
}
}
else
{
size_t v___x_1963_; size_t v___x_1964_; lean_object* v___x_1965_; 
v___x_1963_ = ((size_t)0ULL);
v___x_1964_ = lean_usize_of_nat(v___x_1929_);
v___x_1965_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13___redArg(v_preDefs_1934_, v___x_1963_, v___x_1964_, v___x_1955_, v___y_1939_, v___y_1940_);
v___y_1943_ = v___x_1965_;
goto v___jp_1942_;
}
}
v___jp_1942_:
{
if (lean_obj_tag(v___y_1943_) == 0)
{
lean_object* v___x_1944_; 
lean_dec_ref_known(v___y_1943_, 1);
v___x_1944_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps(v___x_1930_, v_a_1931_, v_f_1932_, v_a_1933_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
return v___x_1944_;
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
lean_dec_ref(v_f_1932_);
lean_dec_ref(v_a_1931_);
lean_dec_ref(v___x_1930_);
v_a_1945_ = lean_ctor_get(v___y_1943_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___y_1943_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___y_1943_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___y_1943_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__0___boxed(lean_object* v___x_1966_, lean_object* v___x_1967_, lean_object* v___x_1968_, lean_object* v_a_1969_, lean_object* v_f_1970_, lean_object* v_a_1971_, lean_object* v_preDefs_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__0(v___x_1966_, v___x_1967_, v___x_1968_, v_a_1969_, v_f_1970_, v_a_1971_, v_preDefs_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec_ref(v_preDefs_1972_);
lean_dec_ref(v_a_1971_);
lean_dec(v___x_1967_);
lean_dec(v___x_1966_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__1(lean_object* v___x_1981_, lean_object* v___x_1982_, lean_object* v___x_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_preDefs_1986_, uint8_t v___x_1987_, lean_object* v_f_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
lean_object* v___x_1996_; lean_object* v_env_1997_; lean_object* v___f_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1996_ = lean_st_ref_get(v___y_1994_);
v_env_1997_ = lean_ctor_get(v___x_1996_, 0);
lean_inc_ref(v_env_1997_);
lean_dec(v___x_1996_);
lean_inc_ref(v_f_1988_);
v___f_1998_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_1998_, 0, v___x_1981_);
lean_closure_set(v___f_1998_, 1, v___x_1982_);
lean_closure_set(v___f_1998_, 2, v___x_1983_);
lean_closure_set(v___f_1998_, 3, v_a_1984_);
lean_closure_set(v___f_1998_, 4, v_f_1988_);
lean_closure_set(v___f_1998_, 5, v_a_1985_);
lean_closure_set(v___f_1998_, 6, v_preDefs_1986_);
v___x_1999_ = l_Lean_Environment_unlockAsync(v_env_1997_);
v___x_2000_ = l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14___redArg(v___x_1999_, v___f_1998_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; uint8_t v___x_2005_; uint8_t v___x_2006_; lean_object* v___x_2007_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
lean_inc(v_a_2001_);
lean_dec_ref_known(v___x_2000_, 1);
v___x_2002_ = lean_unsigned_to_nat(1u);
v___x_2003_ = lean_mk_empty_array_with_capacity(v___x_2002_);
v___x_2004_ = lean_array_push(v___x_2003_, v_f_1988_);
v___x_2005_ = 0;
v___x_2006_ = 1;
v___x_2007_ = l_Lean_Meta_mkLambdaFVars(v___x_2004_, v_a_2001_, v___x_2005_, v___x_1987_, v___x_2005_, v___x_1987_, v___x_2006_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
lean_dec_ref(v___x_2004_);
return v___x_2007_;
}
else
{
lean_dec_ref(v_f_1988_);
return v___x_2000_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__1___boxed(lean_object* v___x_2008_, lean_object* v___x_2009_, lean_object* v___x_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_preDefs_2013_, lean_object* v___x_2014_, lean_object* v_f_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
uint8_t v___x_56509__boxed_2023_; lean_object* v_res_2024_; 
v___x_56509__boxed_2023_ = lean_unbox(v___x_2014_);
v_res_2024_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__1(v___x_2008_, v___x_2009_, v___x_2010_, v_a_2011_, v_a_2012_, v_preDefs_2013_, v___x_56509__boxed_2023_, v_f_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg___lam__0(lean_object* v_k_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v_b_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_){
_start:
{
lean_object* v___x_2034_; 
lean_inc(v___y_2032_);
lean_inc_ref(v___y_2031_);
lean_inc(v___y_2030_);
lean_inc_ref(v___y_2029_);
lean_inc(v___y_2027_);
lean_inc_ref(v___y_2026_);
v___x_2034_ = lean_apply_8(v_k_2025_, v_b_2028_, v___y_2026_, v___y_2027_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, lean_box(0));
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg___lam__0___boxed(lean_object* v_k_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v_b_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg___lam__0(v_k_2035_, v___y_2036_, v___y_2037_, v_b_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg(lean_object* v_name_2045_, uint8_t v_bi_2046_, lean_object* v_type_2047_, lean_object* v_k_2048_, uint8_t v_kind_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_){
_start:
{
lean_object* v___f_2057_; lean_object* v___x_2058_; 
lean_inc(v___y_2051_);
lean_inc_ref(v___y_2050_);
v___f_2057_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2057_, 0, v_k_2048_);
lean_closure_set(v___f_2057_, 1, v___y_2050_);
lean_closure_set(v___f_2057_, 2, v___y_2051_);
v___x_2058_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2045_, v_bi_2046_, v_type_2047_, v___f_2057_, v_kind_2049_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_);
if (lean_obj_tag(v___x_2058_) == 0)
{
return v___x_2058_;
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_2058_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2058_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg___boxed(lean_object* v_name_2067_, lean_object* v_bi_2068_, lean_object* v_type_2069_, lean_object* v_k_2070_, lean_object* v_kind_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
uint8_t v_bi_boxed_2079_; uint8_t v_kind_boxed_2080_; lean_object* v_res_2081_; 
v_bi_boxed_2079_ = lean_unbox(v_bi_2068_);
v_kind_boxed_2080_ = lean_unbox(v_kind_2071_);
v_res_2081_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg(v_name_2067_, v_bi_boxed_2079_, v_type_2069_, v_k_2070_, v_kind_boxed_2080_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15___redArg(lean_object* v_name_2082_, lean_object* v_type_2083_, lean_object* v_k_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_){
_start:
{
uint8_t v___x_2092_; uint8_t v___x_2093_; lean_object* v___x_2094_; 
v___x_2092_ = 0;
v___x_2093_ = 0;
v___x_2094_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg(v_name_2082_, v___x_2092_, v_type_2083_, v_k_2084_, v___x_2093_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15___redArg___boxed(lean_object* v_name_2095_, lean_object* v_type_2096_, lean_object* v_k_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15___redArg(v_name_2095_, v_type_2096_, v_k_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg(lean_object* v___x_2109_, lean_object* v_fixedArgs_2110_, lean_object* v___x_2111_, lean_object* v_a_2112_, lean_object* v___x_2113_, lean_object* v_preDefs_2114_, lean_object* v_a_2115_, size_t v_sz_2116_, size_t v_i_2117_, lean_object* v_bs_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
uint8_t v___x_2126_; 
v___x_2126_ = lean_usize_dec_lt(v_i_2117_, v_sz_2116_);
if (v___x_2126_ == 0)
{
lean_object* v___x_2127_; 
lean_dec_ref(v_a_2115_);
lean_dec_ref(v_preDefs_2114_);
lean_dec(v___x_2113_);
lean_dec_ref(v_a_2112_);
lean_dec_ref(v___x_2111_);
lean_dec_ref(v_fixedArgs_2110_);
v___x_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2127_, 0, v_bs_2118_);
return v___x_2127_;
}
else
{
lean_object* v_v_2128_; lean_object* v_value_2129_; lean_object* v___x_2130_; lean_object* v_bs_x27_2131_; lean_object* v___y_2133_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v_v_2128_ = lean_array_uget_borrowed(v_bs_2118_, v_i_2117_);
v_value_2129_ = lean_ctor_get(v_v_2128_, 7);
lean_inc_ref(v_value_2129_);
v___x_2130_ = lean_unsigned_to_nat(0u);
v_bs_x27_2131_ = lean_array_uset(v_bs_2118_, v_i_2117_, v___x_2130_);
v___x_2147_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1);
v___x_2148_ = lean_usize_to_nat(v_i_2117_);
v___x_2149_ = lean_array_get_borrowed(v___x_2147_, v___x_2109_, v___x_2148_);
lean_dec(v___x_2148_);
lean_inc_ref(v_fixedArgs_2110_);
lean_inc(v___x_2149_);
v___x_2150_ = l_Lean_Elab_FixedParamPerm_instantiateLambda(v___x_2149_, v_value_2129_, v_fixedArgs_2110_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v_a_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
lean_inc(v_a_2151_);
lean_dec_ref_known(v___x_2150_, 1);
v___x_2152_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___closed__1));
v___x_2153_ = l_Lean_Core_mkFreshUserName(v___x_2152_, v___y_2123_, v___y_2124_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v_a_2154_; lean_object* v___x_2155_; lean_object* v___f_2156_; lean_object* v___x_2157_; 
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
lean_inc(v_a_2154_);
lean_dec_ref_known(v___x_2153_, 1);
v___x_2155_ = lean_box(v___x_2126_);
lean_inc_ref(v_preDefs_2114_);
lean_inc_ref(v_a_2112_);
lean_inc_ref(v___x_2111_);
lean_inc(v___x_2113_);
v___f_2156_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___lam__1___boxed), 15, 7);
lean_closure_set(v___f_2156_, 0, v___x_2130_);
lean_closure_set(v___f_2156_, 1, v___x_2113_);
lean_closure_set(v___f_2156_, 2, v___x_2111_);
lean_closure_set(v___f_2156_, 3, v_a_2112_);
lean_closure_set(v___f_2156_, 4, v_a_2151_);
lean_closure_set(v___f_2156_, 5, v_preDefs_2114_);
lean_closure_set(v___f_2156_, 6, v___x_2155_);
lean_inc_ref(v_a_2115_);
v___x_2157_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15___redArg(v_a_2154_, v_a_2115_, v___f_2156_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
v___y_2133_ = v___x_2157_;
goto v___jp_2132_;
}
else
{
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2165_; 
lean_dec(v_a_2151_);
lean_dec_ref(v_bs_x27_2131_);
lean_dec_ref(v_a_2115_);
lean_dec_ref(v_preDefs_2114_);
lean_dec(v___x_2113_);
lean_dec_ref(v_a_2112_);
lean_dec_ref(v___x_2111_);
lean_dec_ref(v_fixedArgs_2110_);
v_a_2158_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2160_ = v___x_2153_;
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___x_2153_);
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
else
{
v___y_2133_ = v___x_2150_;
goto v___jp_2132_;
}
v___jp_2132_:
{
if (lean_obj_tag(v___y_2133_) == 0)
{
lean_object* v_a_2134_; size_t v___x_2135_; size_t v___x_2136_; lean_object* v___x_2137_; 
v_a_2134_ = lean_ctor_get(v___y_2133_, 0);
lean_inc(v_a_2134_);
lean_dec_ref_known(v___y_2133_, 1);
v___x_2135_ = ((size_t)1ULL);
v___x_2136_ = lean_usize_add(v_i_2117_, v___x_2135_);
v___x_2137_ = lean_array_uset(v_bs_x27_2131_, v_i_2117_, v_a_2134_);
v_i_2117_ = v___x_2136_;
v_bs_2118_ = v___x_2137_;
goto _start;
}
else
{
lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2146_; 
lean_dec_ref(v_bs_x27_2131_);
lean_dec_ref(v_a_2115_);
lean_dec_ref(v_preDefs_2114_);
lean_dec(v___x_2113_);
lean_dec_ref(v_a_2112_);
lean_dec_ref(v___x_2111_);
lean_dec_ref(v_fixedArgs_2110_);
v_a_2139_ = lean_ctor_get(v___y_2133_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___y_2133_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2141_ = v___y_2133_;
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_dec(v___y_2133_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2144_; 
if (v_isShared_2142_ == 0)
{
v___x_2144_ = v___x_2141_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_a_2139_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg___boxed(lean_object** _args){
lean_object* v___x_2166_ = _args[0];
lean_object* v_fixedArgs_2167_ = _args[1];
lean_object* v___x_2168_ = _args[2];
lean_object* v_a_2169_ = _args[3];
lean_object* v___x_2170_ = _args[4];
lean_object* v_preDefs_2171_ = _args[5];
lean_object* v_a_2172_ = _args[6];
lean_object* v_sz_2173_ = _args[7];
lean_object* v_i_2174_ = _args[8];
lean_object* v_bs_2175_ = _args[9];
lean_object* v___y_2176_ = _args[10];
lean_object* v___y_2177_ = _args[11];
lean_object* v___y_2178_ = _args[12];
lean_object* v___y_2179_ = _args[13];
lean_object* v___y_2180_ = _args[14];
lean_object* v___y_2181_ = _args[15];
lean_object* v___y_2182_ = _args[16];
_start:
{
size_t v_sz_boxed_2183_; size_t v_i_boxed_2184_; lean_object* v_res_2185_; 
v_sz_boxed_2183_ = lean_unbox_usize(v_sz_2173_);
lean_dec(v_sz_2173_);
v_i_boxed_2184_ = lean_unbox_usize(v_i_2174_);
lean_dec(v_i_2174_);
v_res_2185_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg(v___x_2166_, v_fixedArgs_2167_, v___x_2168_, v_a_2169_, v___x_2170_, v_preDefs_2171_, v_a_2172_, v_sz_boxed_2183_, v_i_boxed_2184_, v_bs_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec_ref(v___x_2166_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__16(lean_object* v___x_2186_, lean_object* v_fixedArgs_2187_, lean_object* v___x_2188_, lean_object* v_a_2189_, lean_object* v___x_2190_, lean_object* v_preDefs_2191_, lean_object* v_a_2192_, lean_object* v_as_2193_, size_t v_sz_2194_, size_t v_i_2195_, lean_object* v_bs_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__16___redArg(v___x_2186_, v_fixedArgs_2187_, v___x_2188_, v_a_2189_, v___x_2190_, v_preDefs_2191_, v_a_2192_, v_sz_2194_, v_i_2195_, v_bs_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__16___boxed(lean_object** _args){
lean_object* v___x_2205_ = _args[0];
lean_object* v_fixedArgs_2206_ = _args[1];
lean_object* v___x_2207_ = _args[2];
lean_object* v_a_2208_ = _args[3];
lean_object* v___x_2209_ = _args[4];
lean_object* v_preDefs_2210_ = _args[5];
lean_object* v_a_2211_ = _args[6];
lean_object* v_as_2212_ = _args[7];
lean_object* v_sz_2213_ = _args[8];
lean_object* v_i_2214_ = _args[9];
lean_object* v_bs_2215_ = _args[10];
lean_object* v___y_2216_ = _args[11];
lean_object* v___y_2217_ = _args[12];
lean_object* v___y_2218_ = _args[13];
lean_object* v___y_2219_ = _args[14];
lean_object* v___y_2220_ = _args[15];
lean_object* v___y_2221_ = _args[16];
lean_object* v___y_2222_ = _args[17];
_start:
{
size_t v_sz_boxed_2223_; size_t v_i_boxed_2224_; lean_object* v_res_2225_; 
v_sz_boxed_2223_ = lean_unbox_usize(v_sz_2213_);
lean_dec(v_sz_2213_);
v_i_boxed_2224_ = lean_unbox_usize(v_i_2214_);
lean_dec(v_i_2214_);
v_res_2225_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__16(v___x_2205_, v_fixedArgs_2206_, v___x_2207_, v_a_2208_, v___x_2209_, v_preDefs_2210_, v_a_2211_, v_as_2212_, v_sz_boxed_2223_, v_i_boxed_2224_, v_bs_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec_ref(v_as_2212_);
lean_dec_ref(v___x_2205_);
return v_res_2225_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9___closed__1(void){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2227_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9___closed__0));
v___x_2228_ = l_Lean_stringToMessageData(v___x_2227_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9(lean_object* v_a_2229_, lean_object* v_a_2230_){
_start:
{
if (lean_obj_tag(v_a_2229_) == 0)
{
lean_object* v___x_2231_; 
v___x_2231_ = l_List_reverse___redArg(v_a_2230_);
return v___x_2231_;
}
else
{
lean_object* v_head_2232_; lean_object* v_tail_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2246_; 
v_head_2232_ = lean_ctor_get(v_a_2229_, 0);
v_tail_2233_ = lean_ctor_get(v_a_2229_, 1);
v_isSharedCheck_2246_ = !lean_is_exclusive(v_a_2229_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2235_ = v_a_2229_;
v_isShared_2236_ = v_isSharedCheck_2246_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_tail_2233_);
lean_inc(v_head_2232_);
lean_dec(v_a_2229_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2246_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2237_; uint8_t v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2243_; 
v___x_2237_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9___closed__1, &l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9___closed__1);
v___x_2238_ = 0;
v___x_2239_ = l_Lean_MessageData_ofConstName(v_head_2232_, v___x_2238_);
v___x_2240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2237_);
lean_ctor_set(v___x_2240_, 1, v___x_2239_);
v___x_2241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2240_);
lean_ctor_set(v___x_2241_, 1, v___x_2237_);
if (v_isShared_2236_ == 0)
{
lean_ctor_set(v___x_2235_, 1, v_a_2230_);
lean_ctor_set(v___x_2235_, 0, v___x_2241_);
v___x_2243_ = v___x_2235_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v___x_2241_);
lean_ctor_set(v_reuseFailAlloc_2245_, 1, v_a_2230_);
v___x_2243_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
v_a_2229_ = v_tail_2233_;
v_a_2230_ = v___x_2243_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2249_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__1));
v___x_2250_ = l_Lean_stringToMessageData(v___x_2249_);
return v___x_2250_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2252_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__3));
v___x_2253_ = l_Lean_stringToMessageData(v___x_2252_);
return v___x_2253_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__6(void){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__5));
v___x_2256_ = l_Lean_stringToMessageData(v___x_2255_);
return v___x_2256_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__9(void){
_start:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2259_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__8));
v___x_2260_ = lean_unsigned_to_nat(52u);
v___x_2261_ = lean_unsigned_to_nat(148u);
v___x_2262_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__7));
v___x_2263_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__0));
v___x_2264_ = l_mkPanicMessageWithDecl(v___x_2263_, v___x_2262_, v___x_2261_, v___x_2260_, v___x_2259_);
return v___x_2264_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__11(void){
_start:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2266_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__10));
v___x_2267_ = l_Lean_stringToMessageData(v___x_2266_);
return v___x_2267_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__13(void){
_start:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2269_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__12));
v___x_2270_ = l_Lean_stringToMessageData(v___x_2269_);
return v___x_2270_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__15(void){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2272_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__14));
v___x_2273_ = l_Lean_stringToMessageData(v___x_2272_);
return v___x_2273_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__19(void){
_start:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2280_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__18));
v___x_2281_ = l_Lean_stringToMessageData(v___x_2280_);
return v___x_2281_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__20(void){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2282_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg___closed__1));
v___x_2283_ = l_Lean_stringToMessageData(v___x_2282_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0(lean_object* v_monoThms_2284_, lean_object* v_t_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v___y_2292_; lean_object* v___x_2336_; lean_object* v___x_2337_; uint8_t v___x_2338_; 
v___x_2336_ = lean_array_get_size(v_monoThms_2284_);
v___x_2337_ = lean_unsigned_to_nat(0u);
v___x_2338_ = lean_nat_dec_eq(v___x_2336_, v___x_2337_);
if (v___x_2338_ == 0)
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2339_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__13, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__13_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__13);
v___x_2340_ = lean_array_to_list(v_monoThms_2284_);
v___x_2341_ = lean_box(0);
v___x_2342_ = l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__9(v___x_2340_, v___x_2341_);
v___x_2343_ = l_Lean_MessageData_andList(v___x_2342_);
v___x_2344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2339_);
lean_ctor_set(v___x_2344_, 1, v___x_2343_);
v___x_2345_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__15, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__15_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__15);
v___x_2346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2344_);
lean_ctor_set(v___x_2346_, 1, v___x_2345_);
v___x_2347_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__17));
v___x_2348_ = l_Lean_MessageData_ofConstName(v___x_2347_, v___x_2338_);
v___x_2349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2346_);
lean_ctor_set(v___x_2349_, 1, v___x_2348_);
v___x_2350_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__19, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__19_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__19);
v___x_2351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2349_);
lean_ctor_set(v___x_2351_, 1, v___x_2350_);
v___y_2292_ = v___x_2351_;
goto v___jp_2291_;
}
else
{
lean_object* v___x_2352_; 
lean_dec_ref(v_monoThms_2284_);
v___x_2352_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__20, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__20_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__20);
v___y_2292_ = v___x_2352_;
goto v___jp_2291_;
}
v___jp_2291_:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2293_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__0));
v___x_2294_ = lean_find_expr(v___x_2293_, v_t_2285_);
if (lean_obj_tag(v___x_2294_) == 1)
{
lean_object* v_val_2295_; lean_object* v___x_2296_; 
v_val_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_val_2295_);
lean_dec_ref_known(v___x_2294_, 1);
v___x_2296_ = l_Lean_getRecAppSyntax_x3f(v_val_2295_);
lean_dec(v_val_2295_);
if (lean_obj_tag(v___x_2296_) == 1)
{
lean_object* v_val_2297_; lean_object* v_fileName_2298_; lean_object* v_fileMap_2299_; lean_object* v_options_2300_; lean_object* v_currRecDepth_2301_; lean_object* v_maxRecDepth_2302_; lean_object* v_ref_2303_; lean_object* v_currNamespace_2304_; lean_object* v_openDecls_2305_; lean_object* v_initHeartbeats_2306_; lean_object* v_maxHeartbeats_2307_; lean_object* v_quotContext_2308_; lean_object* v_currMacroScope_2309_; uint8_t v_diag_2310_; lean_object* v_cancelTk_x3f_2311_; uint8_t v_suppressElabErrors_2312_; lean_object* v_inheritedTraceOptions_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v_ref_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v_val_2297_ = lean_ctor_get(v___x_2296_, 0);
lean_inc_n(v_val_2297_, 2);
lean_dec_ref_known(v___x_2296_, 1);
v_fileName_2298_ = lean_ctor_get(v___y_2288_, 0);
v_fileMap_2299_ = lean_ctor_get(v___y_2288_, 1);
v_options_2300_ = lean_ctor_get(v___y_2288_, 2);
v_currRecDepth_2301_ = lean_ctor_get(v___y_2288_, 3);
v_maxRecDepth_2302_ = lean_ctor_get(v___y_2288_, 4);
v_ref_2303_ = lean_ctor_get(v___y_2288_, 5);
v_currNamespace_2304_ = lean_ctor_get(v___y_2288_, 6);
v_openDecls_2305_ = lean_ctor_get(v___y_2288_, 7);
v_initHeartbeats_2306_ = lean_ctor_get(v___y_2288_, 8);
v_maxHeartbeats_2307_ = lean_ctor_get(v___y_2288_, 9);
v_quotContext_2308_ = lean_ctor_get(v___y_2288_, 10);
v_currMacroScope_2309_ = lean_ctor_get(v___y_2288_, 11);
v_diag_2310_ = lean_ctor_get_uint8(v___y_2288_, sizeof(void*)*14);
v_cancelTk_x3f_2311_ = lean_ctor_get(v___y_2288_, 12);
v_suppressElabErrors_2312_ = lean_ctor_get_uint8(v___y_2288_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2313_ = lean_ctor_get(v___y_2288_, 13);
v___x_2314_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__2);
v___x_2315_ = l_Lean_MessageData_ofSyntax(v_val_2297_);
v___x_2316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2314_);
lean_ctor_set(v___x_2316_, 1, v___x_2315_);
v___x_2317_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__4);
v___x_2318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2316_);
lean_ctor_set(v___x_2318_, 1, v___x_2317_);
v___x_2319_ = l_Lean_indentExpr(v_t_2285_);
v___x_2320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2318_);
lean_ctor_set(v___x_2320_, 1, v___x_2319_);
v___x_2321_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__6);
v___x_2322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2320_);
lean_ctor_set(v___x_2322_, 1, v___x_2321_);
v___x_2323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2322_);
lean_ctor_set(v___x_2323_, 1, v___y_2292_);
v_ref_2324_ = l_Lean_replaceRef(v_val_2297_, v_ref_2303_);
lean_dec(v_val_2297_);
lean_inc_ref(v_inheritedTraceOptions_2313_);
lean_inc(v_cancelTk_x3f_2311_);
lean_inc(v_currMacroScope_2309_);
lean_inc(v_quotContext_2308_);
lean_inc(v_maxHeartbeats_2307_);
lean_inc(v_initHeartbeats_2306_);
lean_inc(v_openDecls_2305_);
lean_inc(v_currNamespace_2304_);
lean_inc(v_maxRecDepth_2302_);
lean_inc(v_currRecDepth_2301_);
lean_inc_ref(v_options_2300_);
lean_inc_ref(v_fileMap_2299_);
lean_inc_ref(v_fileName_2298_);
v___x_2325_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2325_, 0, v_fileName_2298_);
lean_ctor_set(v___x_2325_, 1, v_fileMap_2299_);
lean_ctor_set(v___x_2325_, 2, v_options_2300_);
lean_ctor_set(v___x_2325_, 3, v_currRecDepth_2301_);
lean_ctor_set(v___x_2325_, 4, v_maxRecDepth_2302_);
lean_ctor_set(v___x_2325_, 5, v_ref_2324_);
lean_ctor_set(v___x_2325_, 6, v_currNamespace_2304_);
lean_ctor_set(v___x_2325_, 7, v_openDecls_2305_);
lean_ctor_set(v___x_2325_, 8, v_initHeartbeats_2306_);
lean_ctor_set(v___x_2325_, 9, v_maxHeartbeats_2307_);
lean_ctor_set(v___x_2325_, 10, v_quotContext_2308_);
lean_ctor_set(v___x_2325_, 11, v_currMacroScope_2309_);
lean_ctor_set(v___x_2325_, 12, v_cancelTk_x3f_2311_);
lean_ctor_set(v___x_2325_, 13, v_inheritedTraceOptions_2313_);
lean_ctor_set_uint8(v___x_2325_, sizeof(void*)*14, v_diag_2310_);
lean_ctor_set_uint8(v___x_2325_, sizeof(void*)*14 + 1, v_suppressElabErrors_2312_);
v___x_2326_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg(v___x_2323_, v___y_2286_, v___y_2287_, v___x_2325_, v___y_2289_);
lean_dec_ref_known(v___x_2325_, 14);
return v___x_2326_;
}
else
{
lean_object* v___x_2327_; lean_object* v___x_2328_; 
lean_dec(v___x_2296_);
lean_dec_ref(v___y_2292_);
lean_dec_ref(v_t_2285_);
v___x_2327_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__9);
v___x_2328_ = l_panic___at___00Lean_Elab_partialFixpoint_spec__8___redArg(v___x_2327_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
return v___x_2328_;
}
}
else
{
lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
lean_dec(v___x_2294_);
v___x_2329_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__11, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__11);
v___x_2330_ = l_Lean_indentExpr(v_t_2285_);
v___x_2331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2329_);
lean_ctor_set(v___x_2331_, 1, v___x_2330_);
v___x_2332_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__6, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__6);
v___x_2333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2331_);
lean_ctor_set(v___x_2333_, 1, v___x_2332_);
v___x_2334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2333_);
lean_ctor_set(v___x_2334_, 1, v___y_2292_);
v___x_2335_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6___redArg(v___x_2334_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
return v___x_2335_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___boxed(lean_object* v_monoThms_2353_, lean_object* v_t_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_){
_start:
{
lean_object* v_res_2360_; 
v_res_2360_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0(v_monoThms_2353_, v_t_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__1(lean_object* v_preDefs_2361_, lean_object* v_a_2362_, lean_object* v_fixedArgs_2363_, lean_object* v_00_u03b1_2364_, lean_object* v_f_2365_, lean_object* v_monoThms_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_){
_start:
{
lean_object* v___f_2372_; lean_object* v___x_2373_; 
v___f_2372_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2372_, 0, v_monoThms_2366_);
v___x_2373_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___redArg(v_preDefs_2361_, v_a_2362_, v_fixedArgs_2363_, v_f_2365_, v___f_2372_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__1___boxed(lean_object* v_preDefs_2374_, lean_object* v_a_2375_, lean_object* v_fixedArgs_2376_, lean_object* v_00_u03b1_2377_, lean_object* v_f_2378_, lean_object* v_monoThms_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
lean_object* v_res_2385_; 
v_res_2385_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__1(v_preDefs_2374_, v_a_2375_, v_fixedArgs_2376_, v_00_u03b1_2377_, v_f_2378_, v_monoThms_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__3(lean_object* v___f_2386_, lean_object* v___x_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
lean_object* v___x_2393_; 
v___x_2393_ = l_Lean_Meta_Monotonicity_solveMono(v___f_2386_, v___x_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__3___boxed(lean_object* v___f_2394_, lean_object* v___x_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
lean_object* v_res_2401_; 
v_res_2401_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__3(v___f_2394_, v___x_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
return v_res_2401_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__2(lean_object* v___x_2402_, lean_object* v_e_2403_){
_start:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2404_ = l_Lean_indentD(v_e_2403_);
v___x_2405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2402_);
lean_ctor_set(v___x_2405_, 1, v___x_2404_);
return v___x_2405_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__1(void){
_start:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2407_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__0));
v___x_2408_ = l_Lean_stringToMessageData(v___x_2407_);
return v___x_2408_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__3(void){
_start:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2410_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__2));
v___x_2411_ = l_Lean_stringToMessageData(v___x_2410_);
return v___x_2411_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10(void){
_start:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2422_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7));
v___x_2423_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__9));
v___x_2424_ = l_Lean_Name_append(v___x_2423_, v___x_2422_);
return v___x_2424_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__12(void){
_start:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2426_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__11));
v___x_2427_ = l_Lean_stringToMessageData(v___x_2426_);
return v___x_2427_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__14(void){
_start:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; 
v___x_2429_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__13));
v___x_2430_ = l_Lean_stringToMessageData(v___x_2429_);
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg(lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_hints_2436_, lean_object* v_preDefs_2437_, lean_object* v_a_2438_, lean_object* v_fixedArgs_2439_, size_t v_sz_2440_, size_t v_i_2441_, lean_object* v_bs_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_){
_start:
{
uint8_t v___x_2450_; 
v___x_2450_ = lean_usize_dec_lt(v_i_2441_, v_sz_2440_);
if (v___x_2450_ == 0)
{
lean_object* v___x_2451_; 
lean_dec_ref(v_fixedArgs_2439_);
lean_dec_ref(v_a_2438_);
lean_dec_ref(v_preDefs_2437_);
lean_dec_ref(v_a_2435_);
lean_dec_ref(v_a_2434_);
v___x_2451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2451_, 0, v_bs_2442_);
return v___x_2451_;
}
else
{
lean_object* v_v_2452_; lean_object* v___x_2453_; lean_object* v_bs_x27_2454_; lean_object* v_a_2456_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v_v_2452_ = lean_array_uget(v_bs_2442_, v_i_2441_);
v___x_2453_ = lean_unsigned_to_nat(0u);
v_bs_x27_2454_ = lean_array_uset(v_bs_2442_, v_i_2441_, v___x_2453_);
v___x_2461_ = lean_usize_to_nat(v_i_2441_);
v___x_2462_ = l_Lean_instInhabitedExpr;
v___x_2463_ = lean_array_get_borrowed(v___x_2462_, v_a_2431_, v___x_2461_);
v___x_2464_ = lean_array_get_borrowed(v___x_2462_, v_a_2432_, v___x_2461_);
lean_inc(v___x_2463_);
v___x_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2463_);
lean_inc_ref(v___x_2465_);
lean_inc(v___x_2464_);
v___x_2466_ = l_Lean_Meta_toPartialOrder(v___x_2464_, v___x_2465_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v_a_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_a_2467_);
lean_dec_ref_known(v___x_2466_, 1);
v___x_2468_ = lean_array_get_borrowed(v___x_2462_, v_a_2433_, v___x_2461_);
v___x_2469_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__5));
lean_inc_ref(v_a_2434_);
v___x_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2470_, 0, v_a_2434_);
lean_inc_ref(v_a_2435_);
v___x_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2471_, 0, v_a_2435_);
v___x_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2472_, 0, v_a_2467_);
lean_inc(v___x_2468_);
v___x_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2468_);
v___x_2474_ = lean_unsigned_to_nat(5u);
v___x_2475_ = lean_mk_empty_array_with_capacity(v___x_2474_);
v___x_2476_ = lean_array_push(v___x_2475_, v___x_2470_);
v___x_2477_ = lean_array_push(v___x_2476_, v___x_2471_);
v___x_2478_ = lean_array_push(v___x_2477_, v___x_2465_);
v___x_2479_ = lean_array_push(v___x_2478_, v___x_2472_);
v___x_2480_ = lean_array_push(v___x_2479_, v___x_2473_);
v___x_2481_ = l_Lean_Meta_mkAppOptM(v___x_2469_, v___x_2480_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_object* v_a_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v_term_x3f_2485_; 
v_a_2482_ = lean_ctor_get(v___x_2481_, 0);
lean_inc(v_a_2482_);
lean_dec_ref_known(v___x_2481_, 1);
v___x_2483_ = l_Lean_Elab_instInhabitedPartialFixpoint_default;
v___x_2484_ = lean_array_get_borrowed(v___x_2483_, v_hints_2436_, v___x_2461_);
lean_dec(v___x_2461_);
v_term_x3f_2485_ = lean_ctor_get(v___x_2484_, 1);
lean_inc(v_term_x3f_2485_);
if (lean_obj_tag(v_term_x3f_2485_) == 1)
{
lean_object* v_val_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2551_; 
lean_dec(v_v_2452_);
v_val_2486_ = lean_ctor_get(v_term_x3f_2485_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v_term_x3f_2485_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2488_ = v_term_x3f_2485_;
v_isShared_2489_ = v_isSharedCheck_2551_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_val_2486_);
lean_dec(v_term_x3f_2485_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2551_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
lean_inc(v_a_2482_);
if (v_isShared_2489_ == 0)
{
lean_ctor_set(v___x_2488_, 0, v_a_2482_);
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2482_);
v___x_2491_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; uint8_t v___x_2496_; lean_object* v___x_2497_; 
v___x_2492_ = lean_box(0);
v___x_2493_ = lean_box(v___x_2450_);
v___x_2494_ = lean_box(v___x_2450_);
v___x_2495_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_2495_, 0, v_val_2486_);
lean_closure_set(v___x_2495_, 1, v___x_2491_);
lean_closure_set(v___x_2495_, 2, v___x_2493_);
lean_closure_set(v___x_2495_, 3, v___x_2494_);
lean_closure_set(v___x_2495_, 4, v___x_2492_);
v___x_2496_ = 1;
v___x_2497_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_2495_, v___x_2496_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v_a_2498_; lean_object* v___x_2499_; 
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_a_2498_);
lean_dec_ref_known(v___x_2497_, 1);
v___x_2499_ = l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18___redArg(v_a_2498_, v___y_2446_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v_a_2500_; lean_object* v___x_2501_; 
v_a_2500_ = lean_ctor_get(v___x_2499_, 0);
lean_inc_n(v_a_2500_, 2);
lean_dec_ref_known(v___x_2499_, 1);
v___x_2501_ = l_Lean_Meta_getMVars(v_a_2500_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
if (lean_obj_tag(v___x_2501_) == 0)
{
lean_object* v_a_2502_; lean_object* v___x_2503_; uint8_t v___x_2504_; 
v_a_2502_ = lean_ctor_get(v___x_2501_, 0);
lean_inc(v_a_2502_);
lean_dec_ref_known(v___x_2501_, 1);
v___x_2503_ = lean_array_get_size(v_a_2502_);
v___x_2504_ = lean_nat_dec_eq(v___x_2503_, v___x_2453_);
if (v___x_2504_ == 0)
{
lean_object* v___x_2505_; 
lean_dec(v_a_2500_);
v___x_2505_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_2502_, v___x_2492_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
lean_dec(v_a_2502_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v___x_2506_; 
lean_dec_ref_known(v___x_2505_, 1);
lean_inc(v_a_2482_);
v___x_2506_ = l_Lean_Meta_mkSorry(v_a_2482_, v___x_2450_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
if (lean_obj_tag(v___x_2506_) == 0)
{
lean_object* v_a_2507_; lean_object* v___x_2508_; 
v_a_2507_ = lean_ctor_get(v___x_2506_, 0);
lean_inc(v_a_2507_);
lean_dec_ref_known(v___x_2506_, 1);
v___x_2508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2508_, 0, v_a_2482_);
lean_ctor_set(v___x_2508_, 1, v_a_2507_);
v_a_2456_ = v___x_2508_;
goto v___jp_2455_;
}
else
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2516_; 
lean_dec(v_a_2482_);
lean_dec_ref(v_bs_x27_2454_);
lean_dec_ref(v_fixedArgs_2439_);
lean_dec_ref(v_a_2438_);
lean_dec_ref(v_preDefs_2437_);
lean_dec_ref(v_a_2435_);
lean_dec_ref(v_a_2434_);
v_a_2509_ = lean_ctor_get(v___x_2506_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2511_ = v___x_2506_;
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2506_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2514_; 
if (v_isShared_2512_ == 0)
{
v___x_2514_ = v___x_2511_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_a_2509_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
}
else
{
lean_object* v_a_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2524_; 
lean_dec(v_a_2482_);
lean_dec_ref(v_bs_x27_2454_);
lean_dec_ref(v_fixedArgs_2439_);
lean_dec_ref(v_a_2438_);
lean_dec_ref(v_preDefs_2437_);
lean_dec_ref(v_a_2435_);
lean_dec_ref(v_a_2434_);
v_a_2517_ = lean_ctor_get(v___x_2505_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2519_ = v___x_2505_;
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_a_2517_);
lean_dec(v___x_2505_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2522_; 
if (v_isShared_2520_ == 0)
{
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
return v___x_2522_;
}
}
}
}
else
{
lean_object* v___x_2525_; 
lean_dec(v_a_2502_);
v___x_2525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2525_, 0, v_a_2482_);
lean_ctor_set(v___x_2525_, 1, v_a_2500_);
v_a_2456_ = v___x_2525_;
goto v___jp_2455_;
}
}
else
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
lean_dec(v_a_2500_);
lean_dec(v_a_2482_);
lean_dec_ref(v_bs_x27_2454_);
lean_dec_ref(v_fixedArgs_2439_);
lean_dec_ref(v_a_2438_);
lean_dec_ref(v_preDefs_2437_);
lean_dec_ref(v_a_2435_);
lean_dec_ref(v_a_2434_);
v_a_2526_ = lean_ctor_get(v___x_2501_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2501_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v___x_2501_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2501_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2526_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
}
else
{
lean_object* v_a_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2541_; 
lean_dec(v_a_2482_);
lean_dec_ref(v_bs_x27_2454_);
lean_dec_ref(v_fixedArgs_2439_);
lean_dec_ref(v_a_2438_);
lean_dec_ref(v_preDefs_2437_);
lean_dec_ref(v_a_2435_);
lean_dec_ref(v_a_2434_);
v_a_2534_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2536_ = v___x_2499_;
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_a_2534_);
lean_dec(v___x_2499_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2539_; 
if (v_isShared_2537_ == 0)
{
v___x_2539_ = v___x_2536_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_a_2534_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
}
else
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2549_; 
lean_dec(v_a_2482_);
lean_dec_ref(v_bs_x27_2454_);
lean_dec_ref(v_fixedArgs_2439_);
lean_dec_ref(v_a_2438_);
lean_dec_ref(v_preDefs_2437_);
lean_dec_ref(v_a_2435_);
lean_dec_ref(v_a_2434_);
v_a_2542_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2544_ = v___x_2497_;
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2497_);
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
else
{
lean_object* v___x_2552_; lean_object* v___x_2553_; 
lean_dec(v_term_x3f_2485_);
v___x_2552_ = lean_box(0);
lean_inc(v_a_2482_);
v___x_2553_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2482_, v___x_2552_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v_a_2554_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v_declName_2573_; lean_object* v___f_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___f_2580_; lean_object* v___x_2581_; lean_object* v___f_2582_; lean_object* v___x_2583_; 
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
lean_inc(v_a_2554_);
lean_dec_ref_known(v___x_2553_, 1);
v_declName_2573_ = lean_ctor_get(v_v_2452_, 3);
lean_inc(v_declName_2573_);
lean_dec(v_v_2452_);
lean_inc_ref(v_fixedArgs_2439_);
lean_inc_ref(v_a_2438_);
lean_inc_ref(v_preDefs_2437_);
v___f_2574_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__1___boxed), 11, 3);
lean_closure_set(v___f_2574_, 0, v_preDefs_2437_);
lean_closure_set(v___f_2574_, 1, v_a_2438_);
lean_closure_set(v___f_2574_, 2, v_fixedArgs_2439_);
v___x_2575_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__1);
v___x_2576_ = l_Lean_MessageData_ofName(v_declName_2573_);
lean_inc_ref(v___x_2576_);
v___x_2577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2575_);
lean_ctor_set(v___x_2577_, 1, v___x_2576_);
v___x_2578_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__3);
v___x_2579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2577_);
lean_ctor_set(v___x_2579_, 1, v___x_2578_);
v___f_2580_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__2), 2, 1);
lean_closure_set(v___f_2580_, 0, v___x_2579_);
v___x_2581_ = l_Lean_Expr_mvarId_x21(v_a_2554_);
v___f_2582_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__3___boxed), 7, 2);
lean_closure_set(v___f_2582_, 0, v___f_2574_);
lean_closure_set(v___f_2582_, 1, v___x_2581_);
v___x_2583_ = l_Lean_Meta_mapErrorImp___redArg(v___f_2582_, v___f_2580_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
if (lean_obj_tag(v___x_2583_) == 0)
{
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v_options_2584_; uint8_t v_hasTrace_2585_; 
lean_dec_ref_known(v___x_2583_, 1);
v_options_2584_ = lean_ctor_get(v___y_2447_, 2);
v_hasTrace_2585_ = lean_ctor_get_uint8(v_options_2584_, sizeof(void*)*1);
if (v_hasTrace_2585_ == 0)
{
lean_dec_ref(v___x_2576_);
v___y_2556_ = v___y_2443_;
v___y_2557_ = v___y_2444_;
v___y_2558_ = v___y_2445_;
v___y_2559_ = v___y_2446_;
v___y_2560_ = v___y_2447_;
v___y_2561_ = v___y_2448_;
goto v___jp_2555_;
}
else
{
lean_object* v_inheritedTraceOptions_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; uint8_t v___x_2589_; 
v_inheritedTraceOptions_2586_ = lean_ctor_get(v___y_2447_, 13);
v___x_2587_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7));
v___x_2588_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10);
v___x_2589_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2586_, v_options_2584_, v___x_2588_);
if (v___x_2589_ == 0)
{
lean_dec_ref(v___x_2576_);
v___y_2556_ = v___y_2443_;
v___y_2557_ = v___y_2444_;
v___y_2558_ = v___y_2445_;
v___y_2559_ = v___y_2446_;
v___y_2560_ = v___y_2447_;
v___y_2561_ = v___y_2448_;
goto v___jp_2555_;
}
else
{
lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2590_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__12, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__12);
v___x_2591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2590_);
lean_ctor_set(v___x_2591_, 1, v___x_2576_);
v___x_2592_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__14, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__14_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__14);
v___x_2593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2591_);
lean_ctor_set(v___x_2593_, 1, v___x_2592_);
lean_inc(v_a_2554_);
v___x_2594_ = l_Lean_MessageData_ofExpr(v_a_2554_);
v___x_2595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2593_);
lean_ctor_set(v___x_2595_, 1, v___x_2594_);
v___x_2596_ = l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg(v___x_2587_, v___x_2595_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_dec_ref_known(v___x_2596_, 1);
v___y_2556_ = v___y_2443_;
v___y_2557_ = v___y_2444_;
v___y_2558_ = v___y_2445_;
v___y_2559_ = v___y_2446_;
v___y_2560_ = v___y_2447_;
v___y_2561_ = v___y_2448_;
goto v___jp_2555_;
}
else
{
lean_object* v_a_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2604_; 
lean_dec(v_a_2554_);
lean_dec(v_a_2482_);
lean_dec_ref(v_bs_x27_2454_);
lean_dec_ref(v_fixedArgs_2439_);
lean_dec_ref(v_a_2438_);
lean_dec_ref(v_preDefs_2437_);
lean_dec_ref(v_a_2435_);
lean_dec_ref(v_a_2434_);
v_a_2597_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2599_ = v___x_2596_;
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_a_2597_);
lean_dec(v___x_2596_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v___x_2602_; 
if (v_isShared_2600_ == 0)
{
v___x_2602_ = v___x_2599_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_a_2597_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
}
}
}
else
{
lean_object* v_a_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2612_; 
lean_dec_ref(v___x_2576_);
lean_dec(v_a_2554_);
lean_dec(v_a_2482_);
lean_dec_ref(v_bs_x27_2454_);
lean_dec_ref(v_fixedArgs_2439_);
lean_dec_ref(v_a_2438_);
lean_dec_ref(v_preDefs_2437_);
lean_dec_ref(v_a_2435_);
lean_dec_ref(v_a_2434_);
v_a_2605_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2607_ = v___x_2583_;
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_a_2605_);
lean_dec(v___x_2583_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2610_; 
if (v_isShared_2608_ == 0)
{
lean_ctor_set_tag(v___x_2607_, 1);
v___x_2610_ = v___x_2607_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_a_2605_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
else
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
lean_dec_ref(v___x_2576_);
lean_dec(v_a_2554_);
lean_dec(v_a_2482_);
lean_dec_ref(v_bs_x27_2454_);
lean_dec_ref(v_fixedArgs_2439_);
lean_dec_ref(v_a_2438_);
lean_dec_ref(v_preDefs_2437_);
lean_dec_ref(v_a_2435_);
lean_dec_ref(v_a_2434_);
v_a_2613_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2583_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2583_);
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
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
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
v___jp_2555_:
{
lean_object* v___x_2562_; 
v___x_2562_ = l_Lean_instantiateMVars___at___00Lean_Elab_partialFixpoint_spec__18___redArg(v_a_2554_, v___y_2559_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; lean_object* v___x_2564_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_a_2563_);
lean_dec_ref_known(v___x_2562_, 1);
v___x_2564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2564_, 0, v_a_2482_);
lean_ctor_set(v___x_2564_, 1, v_a_2563_);
v_a_2456_ = v___x_2564_;
goto v___jp_2455_;
}
else
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
lean_dec(v_a_2482_);
lean_dec_ref(v_bs_x27_2454_);
lean_dec_ref(v_fixedArgs_2439_);
lean_dec_ref(v_a_2438_);
lean_dec_ref(v_preDefs_2437_);
lean_dec_ref(v_a_2435_);
lean_dec_ref(v_a_2434_);
v_a_2565_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2567_ = v___x_2562_;
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2562_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2565_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
}
}
else
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
lean_dec(v_a_2482_);
lean_dec_ref(v_bs_x27_2454_);
lean_dec(v_v_2452_);
lean_dec_ref(v_fixedArgs_2439_);
lean_dec_ref(v_a_2438_);
lean_dec_ref(v_preDefs_2437_);
lean_dec_ref(v_a_2435_);
lean_dec_ref(v_a_2434_);
v_a_2621_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___x_2553_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2553_);
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
else
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2636_; 
lean_dec(v___x_2461_);
lean_dec_ref(v_bs_x27_2454_);
lean_dec(v_v_2452_);
lean_dec_ref(v_fixedArgs_2439_);
lean_dec_ref(v_a_2438_);
lean_dec_ref(v_preDefs_2437_);
lean_dec_ref(v_a_2435_);
lean_dec_ref(v_a_2434_);
v_a_2629_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2631_ = v___x_2481_;
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2481_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2634_; 
if (v_isShared_2632_ == 0)
{
v___x_2634_ = v___x_2631_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_a_2629_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
else
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
lean_dec_ref_known(v___x_2465_, 1);
lean_dec(v___x_2461_);
lean_dec_ref(v_bs_x27_2454_);
lean_dec(v_v_2452_);
lean_dec_ref(v_fixedArgs_2439_);
lean_dec_ref(v_a_2438_);
lean_dec_ref(v_preDefs_2437_);
lean_dec_ref(v_a_2435_);
lean_dec_ref(v_a_2434_);
v_a_2637_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2639_ = v___x_2466_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2466_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2642_; 
if (v_isShared_2640_ == 0)
{
v___x_2642_ = v___x_2639_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_a_2637_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
v___jp_2455_:
{
size_t v___x_2457_; size_t v___x_2458_; lean_object* v___x_2459_; 
v___x_2457_ = ((size_t)1ULL);
v___x_2458_ = lean_usize_add(v_i_2441_, v___x_2457_);
v___x_2459_ = lean_array_uset(v_bs_x27_2454_, v_i_2441_, v_a_2456_);
v_i_2441_ = v___x_2458_;
v_bs_2442_ = v___x_2459_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___boxed(lean_object** _args){
lean_object* v_a_2645_ = _args[0];
lean_object* v_a_2646_ = _args[1];
lean_object* v_a_2647_ = _args[2];
lean_object* v_a_2648_ = _args[3];
lean_object* v_a_2649_ = _args[4];
lean_object* v_hints_2650_ = _args[5];
lean_object* v_preDefs_2651_ = _args[6];
lean_object* v_a_2652_ = _args[7];
lean_object* v_fixedArgs_2653_ = _args[8];
lean_object* v_sz_2654_ = _args[9];
lean_object* v_i_2655_ = _args[10];
lean_object* v_bs_2656_ = _args[11];
lean_object* v___y_2657_ = _args[12];
lean_object* v___y_2658_ = _args[13];
lean_object* v___y_2659_ = _args[14];
lean_object* v___y_2660_ = _args[15];
lean_object* v___y_2661_ = _args[16];
lean_object* v___y_2662_ = _args[17];
lean_object* v___y_2663_ = _args[18];
_start:
{
size_t v_sz_boxed_2664_; size_t v_i_boxed_2665_; lean_object* v_res_2666_; 
v_sz_boxed_2664_ = lean_unbox_usize(v_sz_2654_);
lean_dec(v_sz_2654_);
v_i_boxed_2665_ = lean_unbox_usize(v_i_2655_);
lean_dec(v_i_2655_);
v_res_2666_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg(v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_, v_hints_2650_, v_preDefs_2651_, v_a_2652_, v_fixedArgs_2653_, v_sz_boxed_2664_, v_i_boxed_2665_, v_bs_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_);
lean_dec(v___y_2662_);
lean_dec_ref(v___y_2661_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec_ref(v_hints_2650_);
lean_dec_ref(v_a_2647_);
lean_dec_ref(v_a_2646_);
lean_dec_ref(v_a_2645_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19(lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_hints_2672_, lean_object* v_preDefs_2673_, lean_object* v_a_2674_, lean_object* v_fixedArgs_2675_, lean_object* v_as_2676_, size_t v_sz_2677_, size_t v_i_2678_, lean_object* v_bs_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_){
_start:
{
lean_object* v___x_2687_; 
v___x_2687_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg(v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_hints_2672_, v_preDefs_2673_, v_a_2674_, v_fixedArgs_2675_, v_sz_2677_, v_i_2678_, v_bs_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_);
return v___x_2687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___boxed(lean_object** _args){
lean_object* v_a_2688_ = _args[0];
lean_object* v_a_2689_ = _args[1];
lean_object* v_a_2690_ = _args[2];
lean_object* v_a_2691_ = _args[3];
lean_object* v_a_2692_ = _args[4];
lean_object* v_hints_2693_ = _args[5];
lean_object* v_preDefs_2694_ = _args[6];
lean_object* v_a_2695_ = _args[7];
lean_object* v_fixedArgs_2696_ = _args[8];
lean_object* v_as_2697_ = _args[9];
lean_object* v_sz_2698_ = _args[10];
lean_object* v_i_2699_ = _args[11];
lean_object* v_bs_2700_ = _args[12];
lean_object* v___y_2701_ = _args[13];
lean_object* v___y_2702_ = _args[14];
lean_object* v___y_2703_ = _args[15];
lean_object* v___y_2704_ = _args[16];
lean_object* v___y_2705_ = _args[17];
lean_object* v___y_2706_ = _args[18];
lean_object* v___y_2707_ = _args[19];
_start:
{
size_t v_sz_boxed_2708_; size_t v_i_boxed_2709_; lean_object* v_res_2710_; 
v_sz_boxed_2708_ = lean_unbox_usize(v_sz_2698_);
lean_dec(v_sz_2698_);
v_i_boxed_2709_ = lean_unbox_usize(v_i_2699_);
lean_dec(v_i_2699_);
v_res_2710_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19(v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_hints_2693_, v_preDefs_2694_, v_a_2695_, v_fixedArgs_2696_, v_as_2697_, v_sz_boxed_2708_, v_i_boxed_2709_, v_bs_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
lean_dec(v___y_2702_);
lean_dec_ref(v___y_2701_);
lean_dec_ref(v_as_2697_);
lean_dec_ref(v_hints_2693_);
lean_dec_ref(v_a_2690_);
lean_dec_ref(v_a_2689_);
lean_dec_ref(v_a_2688_);
return v_res_2710_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg___lam__0(lean_object* v___y_2711_, uint8_t v_isExporting_2712_, lean_object* v___x_2713_, lean_object* v___y_2714_, lean_object* v___x_2715_, lean_object* v_a_x3f_2716_){
_start:
{
lean_object* v___x_2718_; lean_object* v_env_2719_; lean_object* v_nextMacroScope_2720_; lean_object* v_ngen_2721_; lean_object* v_auxDeclNGen_2722_; lean_object* v_traceState_2723_; lean_object* v_messages_2724_; lean_object* v_infoState_2725_; lean_object* v_snapshotTasks_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2751_; 
v___x_2718_ = lean_st_ref_take(v___y_2711_);
v_env_2719_ = lean_ctor_get(v___x_2718_, 0);
v_nextMacroScope_2720_ = lean_ctor_get(v___x_2718_, 1);
v_ngen_2721_ = lean_ctor_get(v___x_2718_, 2);
v_auxDeclNGen_2722_ = lean_ctor_get(v___x_2718_, 3);
v_traceState_2723_ = lean_ctor_get(v___x_2718_, 4);
v_messages_2724_ = lean_ctor_get(v___x_2718_, 6);
v_infoState_2725_ = lean_ctor_get(v___x_2718_, 7);
v_snapshotTasks_2726_ = lean_ctor_get(v___x_2718_, 8);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2751_ == 0)
{
lean_object* v_unused_2752_; 
v_unused_2752_ = lean_ctor_get(v___x_2718_, 5);
lean_dec(v_unused_2752_);
v___x_2728_ = v___x_2718_;
v_isShared_2729_ = v_isSharedCheck_2751_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_snapshotTasks_2726_);
lean_inc(v_infoState_2725_);
lean_inc(v_messages_2724_);
lean_inc(v_traceState_2723_);
lean_inc(v_auxDeclNGen_2722_);
lean_inc(v_ngen_2721_);
lean_inc(v_nextMacroScope_2720_);
lean_inc(v_env_2719_);
lean_dec(v___x_2718_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2751_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2730_; lean_object* v___x_2732_; 
v___x_2730_ = l_Lean_Environment_setExporting(v_env_2719_, v_isExporting_2712_);
if (v_isShared_2729_ == 0)
{
lean_ctor_set(v___x_2728_, 5, v___x_2713_);
lean_ctor_set(v___x_2728_, 0, v___x_2730_);
v___x_2732_ = v___x_2728_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v___x_2730_);
lean_ctor_set(v_reuseFailAlloc_2750_, 1, v_nextMacroScope_2720_);
lean_ctor_set(v_reuseFailAlloc_2750_, 2, v_ngen_2721_);
lean_ctor_set(v_reuseFailAlloc_2750_, 3, v_auxDeclNGen_2722_);
lean_ctor_set(v_reuseFailAlloc_2750_, 4, v_traceState_2723_);
lean_ctor_set(v_reuseFailAlloc_2750_, 5, v___x_2713_);
lean_ctor_set(v_reuseFailAlloc_2750_, 6, v_messages_2724_);
lean_ctor_set(v_reuseFailAlloc_2750_, 7, v_infoState_2725_);
lean_ctor_set(v_reuseFailAlloc_2750_, 8, v_snapshotTasks_2726_);
v___x_2732_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v_mctx_2735_; lean_object* v_zetaDeltaFVarIds_2736_; lean_object* v_postponed_2737_; lean_object* v_diag_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2748_; 
v___x_2733_ = lean_st_ref_set(v___y_2711_, v___x_2732_);
v___x_2734_ = lean_st_ref_take(v___y_2714_);
v_mctx_2735_ = lean_ctor_get(v___x_2734_, 0);
v_zetaDeltaFVarIds_2736_ = lean_ctor_get(v___x_2734_, 2);
v_postponed_2737_ = lean_ctor_get(v___x_2734_, 3);
v_diag_2738_ = lean_ctor_get(v___x_2734_, 4);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2748_ == 0)
{
lean_object* v_unused_2749_; 
v_unused_2749_ = lean_ctor_get(v___x_2734_, 1);
lean_dec(v_unused_2749_);
v___x_2740_ = v___x_2734_;
v_isShared_2741_ = v_isSharedCheck_2748_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_diag_2738_);
lean_inc(v_postponed_2737_);
lean_inc(v_zetaDeltaFVarIds_2736_);
lean_inc(v_mctx_2735_);
lean_dec(v___x_2734_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2748_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2743_; 
if (v_isShared_2741_ == 0)
{
lean_ctor_set(v___x_2740_, 1, v___x_2715_);
v___x_2743_ = v___x_2740_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_mctx_2735_);
lean_ctor_set(v_reuseFailAlloc_2747_, 1, v___x_2715_);
lean_ctor_set(v_reuseFailAlloc_2747_, 2, v_zetaDeltaFVarIds_2736_);
lean_ctor_set(v_reuseFailAlloc_2747_, 3, v_postponed_2737_);
lean_ctor_set(v_reuseFailAlloc_2747_, 4, v_diag_2738_);
v___x_2743_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
v___x_2744_ = lean_st_ref_set(v___y_2714_, v___x_2743_);
v___x_2745_ = lean_box(0);
v___x_2746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2746_, 0, v___x_2745_);
return v___x_2746_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg___lam__0___boxed(lean_object* v___y_2753_, lean_object* v_isExporting_2754_, lean_object* v___x_2755_, lean_object* v___y_2756_, lean_object* v___x_2757_, lean_object* v_a_x3f_2758_, lean_object* v___y_2759_){
_start:
{
uint8_t v_isExporting_boxed_2760_; lean_object* v_res_2761_; 
v_isExporting_boxed_2760_ = lean_unbox(v_isExporting_2754_);
v_res_2761_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg___lam__0(v___y_2753_, v_isExporting_boxed_2760_, v___x_2755_, v___y_2756_, v___x_2757_, v_a_x3f_2758_);
lean_dec(v_a_x3f_2758_);
lean_dec(v___y_2756_);
lean_dec(v___y_2753_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg(lean_object* v_x_2762_, uint8_t v_isExporting_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_){
_start:
{
lean_object* v___x_2771_; lean_object* v_env_2772_; uint8_t v_isExporting_2773_; lean_object* v___x_2774_; lean_object* v_env_2775_; lean_object* v_nextMacroScope_2776_; lean_object* v_ngen_2777_; lean_object* v_auxDeclNGen_2778_; lean_object* v_traceState_2779_; lean_object* v_messages_2780_; lean_object* v_infoState_2781_; lean_object* v_snapshotTasks_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2836_; 
v___x_2771_ = lean_st_ref_get(v___y_2769_);
v_env_2772_ = lean_ctor_get(v___x_2771_, 0);
lean_inc_ref(v_env_2772_);
lean_dec(v___x_2771_);
v_isExporting_2773_ = lean_ctor_get_uint8(v_env_2772_, sizeof(void*)*8);
lean_dec_ref(v_env_2772_);
v___x_2774_ = lean_st_ref_take(v___y_2769_);
v_env_2775_ = lean_ctor_get(v___x_2774_, 0);
v_nextMacroScope_2776_ = lean_ctor_get(v___x_2774_, 1);
v_ngen_2777_ = lean_ctor_get(v___x_2774_, 2);
v_auxDeclNGen_2778_ = lean_ctor_get(v___x_2774_, 3);
v_traceState_2779_ = lean_ctor_get(v___x_2774_, 4);
v_messages_2780_ = lean_ctor_get(v___x_2774_, 6);
v_infoState_2781_ = lean_ctor_get(v___x_2774_, 7);
v_snapshotTasks_2782_ = lean_ctor_get(v___x_2774_, 8);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2836_ == 0)
{
lean_object* v_unused_2837_; 
v_unused_2837_ = lean_ctor_get(v___x_2774_, 5);
lean_dec(v_unused_2837_);
v___x_2784_ = v___x_2774_;
v_isShared_2785_ = v_isSharedCheck_2836_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_snapshotTasks_2782_);
lean_inc(v_infoState_2781_);
lean_inc(v_messages_2780_);
lean_inc(v_traceState_2779_);
lean_inc(v_auxDeclNGen_2778_);
lean_inc(v_ngen_2777_);
lean_inc(v_nextMacroScope_2776_);
lean_inc(v_env_2775_);
lean_dec(v___x_2774_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2836_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2789_; 
v___x_2786_ = l_Lean_Environment_setExporting(v_env_2775_, v_isExporting_2763_);
v___x_2787_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__2);
if (v_isShared_2785_ == 0)
{
lean_ctor_set(v___x_2784_, 5, v___x_2787_);
lean_ctor_set(v___x_2784_, 0, v___x_2786_);
v___x_2789_ = v___x_2784_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v___x_2786_);
lean_ctor_set(v_reuseFailAlloc_2835_, 1, v_nextMacroScope_2776_);
lean_ctor_set(v_reuseFailAlloc_2835_, 2, v_ngen_2777_);
lean_ctor_set(v_reuseFailAlloc_2835_, 3, v_auxDeclNGen_2778_);
lean_ctor_set(v_reuseFailAlloc_2835_, 4, v_traceState_2779_);
lean_ctor_set(v_reuseFailAlloc_2835_, 5, v___x_2787_);
lean_ctor_set(v_reuseFailAlloc_2835_, 6, v_messages_2780_);
lean_ctor_set(v_reuseFailAlloc_2835_, 7, v_infoState_2781_);
lean_ctor_set(v_reuseFailAlloc_2835_, 8, v_snapshotTasks_2782_);
v___x_2789_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v_mctx_2792_; lean_object* v_zetaDeltaFVarIds_2793_; lean_object* v_postponed_2794_; lean_object* v_diag_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2833_; 
v___x_2790_ = lean_st_ref_set(v___y_2769_, v___x_2789_);
v___x_2791_ = lean_st_ref_take(v___y_2767_);
v_mctx_2792_ = lean_ctor_get(v___x_2791_, 0);
v_zetaDeltaFVarIds_2793_ = lean_ctor_get(v___x_2791_, 2);
v_postponed_2794_ = lean_ctor_get(v___x_2791_, 3);
v_diag_2795_ = lean_ctor_get(v___x_2791_, 4);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2833_ == 0)
{
lean_object* v_unused_2834_; 
v_unused_2834_ = lean_ctor_get(v___x_2791_, 1);
lean_dec(v_unused_2834_);
v___x_2797_ = v___x_2791_;
v_isShared_2798_ = v_isSharedCheck_2833_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_diag_2795_);
lean_inc(v_postponed_2794_);
lean_inc(v_zetaDeltaFVarIds_2793_);
lean_inc(v_mctx_2792_);
lean_dec(v___x_2791_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2833_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2799_; lean_object* v___x_2801_; 
v___x_2799_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3, &l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_withEnv___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__5_spec__5___redArg___closed__3);
if (v_isShared_2798_ == 0)
{
lean_ctor_set(v___x_2797_, 1, v___x_2799_);
v___x_2801_ = v___x_2797_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_mctx_2792_);
lean_ctor_set(v_reuseFailAlloc_2832_, 1, v___x_2799_);
lean_ctor_set(v_reuseFailAlloc_2832_, 2, v_zetaDeltaFVarIds_2793_);
lean_ctor_set(v_reuseFailAlloc_2832_, 3, v_postponed_2794_);
lean_ctor_set(v_reuseFailAlloc_2832_, 4, v_diag_2795_);
v___x_2801_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
lean_object* v___x_2802_; lean_object* v_r_2803_; 
v___x_2802_ = lean_st_ref_set(v___y_2767_, v___x_2801_);
lean_inc(v___y_2769_);
lean_inc_ref(v___y_2768_);
lean_inc(v___y_2767_);
lean_inc_ref(v___y_2766_);
lean_inc(v___y_2765_);
lean_inc_ref(v___y_2764_);
v_r_2803_ = lean_apply_7(v_x_2762_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, lean_box(0));
if (lean_obj_tag(v_r_2803_) == 0)
{
lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2820_; 
v_a_2804_ = lean_ctor_get(v_r_2803_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v_r_2803_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2806_ = v_r_2803_;
v_isShared_2807_ = v_isSharedCheck_2820_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v_r_2803_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2820_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2809_; 
lean_inc(v_a_2804_);
if (v_isShared_2807_ == 0)
{
lean_ctor_set_tag(v___x_2806_, 1);
v___x_2809_ = v___x_2806_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_a_2804_);
v___x_2809_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
lean_object* v___x_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2817_; 
v___x_2810_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg___lam__0(v___y_2769_, v_isExporting_2773_, v___x_2787_, v___y_2767_, v___x_2799_, v___x_2809_);
lean_dec_ref(v___x_2809_);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2817_ == 0)
{
lean_object* v_unused_2818_; 
v_unused_2818_ = lean_ctor_get(v___x_2810_, 0);
lean_dec(v_unused_2818_);
v___x_2812_ = v___x_2810_;
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
else
{
lean_dec(v___x_2810_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2815_; 
if (v_isShared_2813_ == 0)
{
lean_ctor_set(v___x_2812_, 0, v_a_2804_);
v___x_2815_ = v___x_2812_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2804_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
}
}
}
else
{
lean_object* v_a_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2830_; 
v_a_2821_ = lean_ctor_get(v_r_2803_, 0);
lean_inc(v_a_2821_);
lean_dec_ref_known(v_r_2803_, 1);
v___x_2822_ = lean_box(0);
v___x_2823_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg___lam__0(v___y_2769_, v_isExporting_2773_, v___x_2787_, v___y_2767_, v___x_2799_, v___x_2822_);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2830_ == 0)
{
lean_object* v_unused_2831_; 
v_unused_2831_ = lean_ctor_get(v___x_2823_, 0);
lean_dec(v_unused_2831_);
v___x_2825_ = v___x_2823_;
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
else
{
lean_dec(v___x_2823_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2828_; 
if (v_isShared_2826_ == 0)
{
lean_ctor_set_tag(v___x_2825_, 1);
lean_ctor_set(v___x_2825_, 0, v_a_2821_);
v___x_2828_ = v___x_2825_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_a_2821_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg___boxed(lean_object* v_x_2838_, lean_object* v_isExporting_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_){
_start:
{
uint8_t v_isExporting_boxed_2847_; lean_object* v_res_2848_; 
v_isExporting_boxed_2847_ = lean_unbox(v_isExporting_2839_);
v_res_2848_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg(v_x_2838_, v_isExporting_boxed_2847_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17___redArg(lean_object* v_x_2849_, uint8_t v_when_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
if (v_when_2850_ == 0)
{
lean_object* v___x_2858_; 
lean_inc(v___y_2856_);
lean_inc_ref(v___y_2855_);
lean_inc(v___y_2854_);
lean_inc_ref(v___y_2853_);
lean_inc(v___y_2852_);
lean_inc_ref(v___y_2851_);
v___x_2858_ = lean_apply_7(v_x_2849_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, lean_box(0));
return v___x_2858_;
}
else
{
uint8_t v___x_2859_; lean_object* v___x_2860_; 
v___x_2859_ = 0;
v___x_2860_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg(v_x_2849_, v___x_2859_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_);
return v___x_2860_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17___redArg___boxed(lean_object* v_x_2861_, lean_object* v_when_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
uint8_t v_when_boxed_2870_; lean_object* v_res_2871_; 
v_when_boxed_2870_ = lean_unbox(v_when_2862_);
v_res_2871_ = l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17___redArg(v_x_2861_, v_when_boxed_2870_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
lean_dec(v___y_2866_);
lean_dec_ref(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
return v_res_2871_;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2872_ = l_Lean_instInhabitedExpr;
v___x_2873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2872_);
lean_ctor_set(v___x_2873_, 1, v___x_2872_);
return v___x_2873_;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2879_ = ((lean_object*)(l_Lean_Elab_partialFixpoint___lam__0___closed__4));
v___x_2880_ = l_Lean_stringToMessageData(v___x_2879_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_partialFixpoint___lam__0(lean_object* v_a_2881_, lean_object* v_perms_2882_, size_t v___x_2883_, size_t v_sz_2884_, lean_object* v_preDefs_2885_, lean_object* v___x_2886_, lean_object* v___x_2887_, lean_object* v_a_2888_, lean_object* v___x_2889_, uint8_t v___x_2890_, lean_object* v_hints_2891_, lean_object* v___x_2892_, lean_object* v_docCtx_2893_, lean_object* v_fixedArgs_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_){
_start:
{
size_t v_sz_2902_; lean_object* v___x_2903_; 
v_sz_2902_ = lean_array_size(v_a_2881_);
lean_inc_ref(v_fixedArgs_2894_);
v___x_2903_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__10___redArg(v_perms_2882_, v_fixedArgs_2894_, v_sz_2902_, v___x_2883_, v_a_2881_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; lean_object* v___x_2905_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
lean_inc(v_a_2904_);
lean_dec_ref_known(v___x_2903_, 1);
lean_inc_ref(v_preDefs_2885_);
lean_inc_ref(v_fixedArgs_2894_);
v___x_2905_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__11___redArg(v_perms_2882_, v_fixedArgs_2894_, v_sz_2884_, v___x_2883_, v_preDefs_2885_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v_a_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
lean_inc_n(v_a_2906_, 2);
lean_dec_ref_known(v___x_2905_, 1);
v___x_2907_ = l_Lean_Level_ofNat(v___x_2886_);
v___x_2908_ = l_Lean_Meta_PProdN_pack(v___x_2907_, v_a_2906_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
if (lean_obj_tag(v___x_2908_) == 0)
{
lean_object* v_a_2909_; size_t v_sz_2910_; lean_object* v___x_2911_; 
v_a_2909_ = lean_ctor_get(v___x_2908_, 0);
lean_inc(v_a_2909_);
lean_dec_ref_known(v___x_2908_, 1);
v_sz_2910_ = lean_array_size(v_a_2904_);
v___x_2911_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__12(v_sz_2910_, v___x_2883_, v_a_2904_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v_a_2912_; lean_object* v___x_2913_; 
v_a_2912_ = lean_ctor_get(v___x_2911_, 0);
lean_inc_n(v_a_2912_, 2);
lean_dec_ref_known(v___x_2911_, 1);
v___x_2913_ = l_Lean_Meta_mkPackedPPRodInstance(v_a_2912_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_object* v_a_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; 
v_a_2914_ = lean_ctor_get(v___x_2913_, 0);
lean_inc_n(v_a_2914_, 2);
lean_dec_ref_known(v___x_2913_, 1);
v___x_2915_ = lean_box(0);
v___x_2916_ = l_Lean_Meta_toPartialOrder(v_a_2914_, v___x_2915_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
if (lean_obj_tag(v___x_2916_) == 0)
{
lean_object* v_a_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; 
v_a_2917_ = lean_ctor_get(v___x_2916_, 0);
lean_inc(v_a_2917_);
lean_dec_ref_known(v___x_2916_, 1);
v___x_2918_ = lean_box_usize(v_sz_2884_);
v___x_2919_ = lean_box_usize(v___x_2883_);
lean_inc(v_a_2909_);
lean_inc_ref_n(v_preDefs_2885_, 3);
lean_inc(v___x_2889_);
lean_inc_ref(v_a_2888_);
lean_inc_ref(v_fixedArgs_2894_);
lean_inc_ref(v_perms_2882_);
v___x_2920_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__16___boxed), 18, 11);
lean_closure_set(v___x_2920_, 0, v_perms_2882_);
lean_closure_set(v___x_2920_, 1, v_fixedArgs_2894_);
lean_closure_set(v___x_2920_, 2, v___x_2887_);
lean_closure_set(v___x_2920_, 3, v_a_2888_);
lean_closure_set(v___x_2920_, 4, v___x_2889_);
lean_closure_set(v___x_2920_, 5, v_preDefs_2885_);
lean_closure_set(v___x_2920_, 6, v_a_2909_);
lean_closure_set(v___x_2920_, 7, v_preDefs_2885_);
lean_closure_set(v___x_2920_, 8, v___x_2918_);
lean_closure_set(v___x_2920_, 9, v___x_2919_);
lean_closure_set(v___x_2920_, 10, v_preDefs_2885_);
v___x_2921_ = l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17___redArg(v___x_2920_, v___x_2890_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
if (lean_obj_tag(v___x_2921_) == 0)
{
lean_object* v_a_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
v_a_2922_ = lean_ctor_get(v___x_2921_, 0);
lean_inc(v_a_2922_);
lean_dec_ref_known(v___x_2921_, 1);
v___x_2923_ = lean_box_usize(v_sz_2884_);
v___x_2924_ = lean_box_usize(v___x_2883_);
lean_inc_ref(v_fixedArgs_2894_);
lean_inc_ref(v_a_2888_);
lean_inc_ref_n(v_preDefs_2885_, 3);
lean_inc_ref(v_hints_2891_);
lean_inc(v_a_2909_);
v___x_2925_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___boxed), 20, 13);
lean_closure_set(v___x_2925_, 0, v_a_2906_);
lean_closure_set(v___x_2925_, 1, v_a_2912_);
lean_closure_set(v___x_2925_, 2, v_a_2922_);
lean_closure_set(v___x_2925_, 3, v_a_2909_);
lean_closure_set(v___x_2925_, 4, v_a_2917_);
lean_closure_set(v___x_2925_, 5, v_hints_2891_);
lean_closure_set(v___x_2925_, 6, v_preDefs_2885_);
lean_closure_set(v___x_2925_, 7, v_a_2888_);
lean_closure_set(v___x_2925_, 8, v_fixedArgs_2894_);
lean_closure_set(v___x_2925_, 9, v_preDefs_2885_);
lean_closure_set(v___x_2925_, 10, v___x_2923_);
lean_closure_set(v___x_2925_, 11, v___x_2924_);
lean_closure_set(v___x_2925_, 12, v_preDefs_2885_);
v___x_2926_ = l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17___redArg(v___x_2925_, v___x_2890_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v_a_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
lean_inc(v_a_2927_);
lean_dec_ref_known(v___x_2926_, 1);
v___x_2928_ = lean_obj_once(&l_Lean_Elab_partialFixpoint___lam__0___closed__0, &l_Lean_Elab_partialFixpoint___lam__0___closed__0_once, _init_l_Lean_Elab_partialFixpoint___lam__0___closed__0);
v___x_2929_ = ((lean_object*)(l_Lean_Elab_partialFixpoint___lam__0___closed__1));
v___x_2930_ = l_Lean_Meta_PProdN_genMk___redArg(v___x_2928_, v___x_2929_, v_a_2927_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_object* v_a_2931_; lean_object* v_snd_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_3053_; 
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
lean_inc(v_a_2931_);
lean_dec_ref_known(v___x_2930_, 1);
v_snd_2932_ = lean_ctor_get(v_a_2931_, 1);
v_isSharedCheck_3053_ = !lean_is_exclusive(v_a_2931_);
if (v_isSharedCheck_3053_ == 0)
{
lean_object* v_unused_3054_; 
v_unused_3054_ = lean_ctor_get(v_a_2931_, 0);
lean_dec(v_unused_3054_);
v___x_2934_ = v_a_2931_;
v_isShared_2935_ = v_isSharedCheck_3053_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_snd_2932_);
lean_dec(v_a_2931_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_3053_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2936_; 
lean_inc(v_a_2909_);
v___x_2936_ = l_Lean_Meta_mkFixOfMonFun(v_a_2909_, v_a_2914_, v_snd_2932_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v_a_2937_; lean_object* v___y_2939_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2944_; lean_object* v___y_2945_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; uint8_t v___y_3018_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v_options_3033_; uint8_t v_hasTrace_3034_; 
v_a_2937_ = lean_ctor_get(v___x_2936_, 0);
lean_inc(v_a_2937_);
lean_dec_ref_known(v___x_2936_, 1);
v_options_3033_ = lean_ctor_get(v___y_2899_, 2);
v_hasTrace_3034_ = lean_ctor_get_uint8(v_options_3033_, sizeof(void*)*1);
if (v_hasTrace_3034_ == 0)
{
lean_del_object(v___x_2934_);
v___y_3024_ = v___y_2895_;
v___y_3025_ = v___y_2896_;
v___y_3026_ = v___y_2897_;
v___y_3027_ = v___y_2898_;
v___y_3028_ = v___y_2899_;
v___y_3029_ = v___y_2900_;
goto v___jp_3023_;
}
else
{
lean_object* v_inheritedTraceOptions_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; uint8_t v___x_3038_; 
v_inheritedTraceOptions_3035_ = lean_ctor_get(v___y_2899_, 13);
v___x_3036_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7));
v___x_3037_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10);
v___x_3038_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3035_, v_options_3033_, v___x_3037_);
if (v___x_3038_ == 0)
{
lean_del_object(v___x_2934_);
v___y_3024_ = v___y_2895_;
v___y_3025_ = v___y_2896_;
v___y_3026_ = v___y_2897_;
v___y_3027_ = v___y_2898_;
v___y_3028_ = v___y_2899_;
v___y_3029_ = v___y_2900_;
goto v___jp_3023_;
}
else
{
lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3042_; 
v___x_3039_ = lean_obj_once(&l_Lean_Elab_partialFixpoint___lam__0___closed__5, &l_Lean_Elab_partialFixpoint___lam__0___closed__5_once, _init_l_Lean_Elab_partialFixpoint___lam__0___closed__5);
lean_inc(v_a_2937_);
v___x_3040_ = l_Lean_MessageData_ofExpr(v_a_2937_);
if (v_isShared_2935_ == 0)
{
lean_ctor_set_tag(v___x_2934_, 7);
lean_ctor_set(v___x_2934_, 1, v___x_3040_);
lean_ctor_set(v___x_2934_, 0, v___x_3039_);
v___x_3042_ = v___x_2934_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v___x_3039_);
lean_ctor_set(v_reuseFailAlloc_3044_, 1, v___x_3040_);
v___x_3042_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
lean_object* v___x_3043_; 
v___x_3043_ = l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg(v___x_3036_, v___x_3042_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_dec_ref_known(v___x_3043_, 1);
v___y_3024_ = v___y_2895_;
v___y_3025_ = v___y_2896_;
v___y_3026_ = v___y_2897_;
v___y_3027_ = v___y_2898_;
v___y_3028_ = v___y_2899_;
v___y_3029_ = v___y_2900_;
goto v___jp_3023_;
}
else
{
lean_dec(v_a_2937_);
lean_dec(v_a_2909_);
lean_dec_ref(v_fixedArgs_2894_);
lean_dec_ref(v_docCtx_2893_);
lean_dec_ref(v___x_2892_);
lean_dec_ref(v_hints_2891_);
lean_dec(v___x_2889_);
lean_dec_ref(v_a_2888_);
lean_dec_ref(v_preDefs_2885_);
lean_dec_ref(v_perms_2882_);
return v___x_3043_;
}
}
}
}
v___jp_2938_:
{
uint8_t v___x_2946_; uint8_t v___x_2947_; lean_object* v___x_2948_; 
v___x_2946_ = 0;
v___x_2947_ = 1;
lean_inc(v_a_2909_);
v___x_2948_ = l_Lean_Meta_mkForallFVars(v_fixedArgs_2894_, v_a_2909_, v___x_2946_, v___x_2890_, v___x_2890_, v___x_2947_, v___y_2943_, v___y_2944_, v___y_2942_, v___y_2941_);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_object* v_a_2949_; lean_object* v___x_2950_; 
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
lean_inc(v_a_2949_);
lean_dec_ref_known(v___x_2948_, 1);
v___x_2950_ = l_Lean_Meta_mkLambdaFVars(v_fixedArgs_2894_, v_a_2937_, v___x_2946_, v___x_2890_, v___x_2946_, v___x_2890_, v___x_2947_, v___y_2943_, v___y_2944_, v___y_2942_, v___y_2941_);
lean_dec_ref(v_fixedArgs_2894_);
if (lean_obj_tag(v___x_2950_) == 0)
{
lean_object* v_a_2951_; lean_object* v_ref_2952_; uint8_t v_kind_2953_; lean_object* v_levelParams_2954_; lean_object* v_modifiers_2955_; lean_object* v_binders_2956_; lean_object* v_numSectionVars_2957_; lean_object* v_termination_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2991_; 
v_a_2951_ = lean_ctor_get(v___x_2950_, 0);
lean_inc(v_a_2951_);
lean_dec_ref_known(v___x_2950_, 1);
v_ref_2952_ = lean_ctor_get(v___x_2892_, 0);
v_kind_2953_ = lean_ctor_get_uint8(v___x_2892_, sizeof(void*)*9);
v_levelParams_2954_ = lean_ctor_get(v___x_2892_, 1);
v_modifiers_2955_ = lean_ctor_get(v___x_2892_, 2);
v_binders_2956_ = lean_ctor_get(v___x_2892_, 4);
v_numSectionVars_2957_ = lean_ctor_get(v___x_2892_, 5);
v_termination_2958_ = lean_ctor_get(v___x_2892_, 8);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2991_ == 0)
{
lean_object* v_unused_2992_; lean_object* v_unused_2993_; lean_object* v_unused_2994_; 
v_unused_2992_ = lean_ctor_get(v___x_2892_, 7);
lean_dec(v_unused_2992_);
v_unused_2993_ = lean_ctor_get(v___x_2892_, 6);
lean_dec(v_unused_2993_);
v_unused_2994_ = lean_ctor_get(v___x_2892_, 3);
lean_dec(v_unused_2994_);
v___x_2960_ = v___x_2892_;
v_isShared_2961_ = v_isSharedCheck_2991_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_termination_2958_);
lean_inc(v_numSectionVars_2957_);
lean_inc(v_binders_2956_);
lean_inc(v_modifiers_2955_);
lean_inc(v_levelParams_2954_);
lean_inc(v_ref_2952_);
lean_dec(v___x_2892_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2991_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2962_; 
lean_inc_ref(v_preDefs_2885_);
lean_inc(v___y_2945_);
lean_inc(v_levelParams_2954_);
v___x_2962_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg(v_perms_2882_, v_levelParams_2954_, v___y_2945_, v___x_2889_, v_a_2909_, v_sz_2884_, v___x_2883_, v_preDefs_2885_, v___y_2940_, v___y_2939_, v___y_2943_, v___y_2944_, v___y_2942_, v___y_2941_);
lean_dec_ref(v_perms_2882_);
if (lean_obj_tag(v___x_2962_) == 0)
{
lean_object* v_a_2963_; lean_object* v___x_2965_; 
v_a_2963_ = lean_ctor_get(v___x_2962_, 0);
lean_inc(v_a_2963_);
lean_dec_ref_known(v___x_2962_, 1);
lean_inc(v___y_2945_);
if (v_isShared_2961_ == 0)
{
lean_ctor_set(v___x_2960_, 7, v_a_2951_);
lean_ctor_set(v___x_2960_, 6, v_a_2949_);
lean_ctor_set(v___x_2960_, 3, v___y_2945_);
v___x_2965_ = v___x_2960_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_ref_2952_);
lean_ctor_set(v_reuseFailAlloc_2982_, 1, v_levelParams_2954_);
lean_ctor_set(v_reuseFailAlloc_2982_, 2, v_modifiers_2955_);
lean_ctor_set(v_reuseFailAlloc_2982_, 3, v___y_2945_);
lean_ctor_set(v_reuseFailAlloc_2982_, 4, v_binders_2956_);
lean_ctor_set(v_reuseFailAlloc_2982_, 5, v_numSectionVars_2957_);
lean_ctor_set(v_reuseFailAlloc_2982_, 6, v_a_2949_);
lean_ctor_set(v_reuseFailAlloc_2982_, 7, v_a_2951_);
lean_ctor_set(v_reuseFailAlloc_2982_, 8, v_termination_2958_);
lean_ctor_set_uint8(v_reuseFailAlloc_2982_, sizeof(void*)*9, v_kind_2953_);
v___x_2965_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
lean_object* v___x_2966_; 
lean_inc_ref(v_preDefs_2885_);
lean_inc_ref(v_docCtx_2893_);
v___x_2966_ = l_Lean_Elab_Mutual_addPreDefsFromUnary(v_docCtx_2893_, v_preDefs_2885_, v_a_2963_, v___x_2965_, v___x_2890_, v___y_2940_, v___y_2939_, v___y_2943_, v___y_2944_, v___y_2942_, v___y_2941_);
lean_dec(v_a_2963_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v___x_2967_; 
lean_dec_ref_known(v___x_2966_, 1);
lean_inc_ref(v_preDefs_2885_);
v___x_2967_ = l_Lean_Elab_addAndCompilePartialRec(v_docCtx_2893_, v_preDefs_2885_, v___y_2940_, v___y_2939_, v___y_2943_, v___y_2944_, v___y_2942_, v___y_2941_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v___x_2968_; 
lean_dec_ref_known(v___x_2967_, 1);
v___x_2968_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__22___redArg(v_sz_2884_, v___x_2883_, v_preDefs_2885_, v___y_2943_, v___y_2944_, v___y_2942_, v___y_2941_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v_a_2969_; size_t v_sz_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; 
v_a_2969_ = lean_ctor_get(v___x_2968_, 0);
lean_inc_n(v_a_2969_, 2);
lean_dec_ref_known(v___x_2968_, 1);
v_sz_2970_ = lean_array_size(v_hints_2891_);
v___x_2971_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__23(v_sz_2970_, v___x_2883_, v_hints_2891_);
v___x_2972_ = l_Lean_Elab_PartialFixpoint_registerEqnsInfo(v_a_2969_, v___y_2945_, v_a_2888_, v___x_2971_, v___y_2943_, v___y_2944_, v___y_2942_, v___y_2941_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_object* v___x_2973_; 
lean_dec_ref_known(v___x_2972_, 1);
v___x_2973_ = l_Lean_Elab_Mutual_addPreDefAttributes(v_a_2969_, v___y_2940_, v___y_2939_, v___y_2943_, v___y_2944_, v___y_2942_, v___y_2941_);
return v___x_2973_;
}
else
{
lean_dec(v_a_2969_);
return v___x_2972_;
}
}
else
{
lean_object* v_a_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2981_; 
lean_dec(v___y_2945_);
lean_dec_ref(v_hints_2891_);
lean_dec_ref(v_a_2888_);
v_a_2974_ = lean_ctor_get(v___x_2968_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2976_ = v___x_2968_;
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_a_2974_);
lean_dec(v___x_2968_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2979_; 
if (v_isShared_2977_ == 0)
{
v___x_2979_ = v___x_2976_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_a_2974_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
return v___x_2979_;
}
}
}
}
else
{
lean_dec(v___y_2945_);
lean_dec_ref(v_hints_2891_);
lean_dec_ref(v_a_2888_);
lean_dec_ref(v_preDefs_2885_);
return v___x_2967_;
}
}
else
{
lean_dec(v___y_2945_);
lean_dec_ref(v_docCtx_2893_);
lean_dec_ref(v_hints_2891_);
lean_dec_ref(v_a_2888_);
lean_dec_ref(v_preDefs_2885_);
return v___x_2966_;
}
}
}
else
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2990_; 
lean_del_object(v___x_2960_);
lean_dec_ref(v_termination_2958_);
lean_dec(v_numSectionVars_2957_);
lean_dec(v_binders_2956_);
lean_dec_ref(v_modifiers_2955_);
lean_dec(v_levelParams_2954_);
lean_dec(v_ref_2952_);
lean_dec(v_a_2951_);
lean_dec(v_a_2949_);
lean_dec(v___y_2945_);
lean_dec_ref(v_docCtx_2893_);
lean_dec_ref(v_hints_2891_);
lean_dec_ref(v_a_2888_);
lean_dec_ref(v_preDefs_2885_);
v_a_2983_ = lean_ctor_get(v___x_2962_, 0);
v_isSharedCheck_2990_ = !lean_is_exclusive(v___x_2962_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2985_ = v___x_2962_;
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2962_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2988_; 
if (v_isShared_2986_ == 0)
{
v___x_2988_ = v___x_2985_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_a_2983_);
v___x_2988_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
return v___x_2988_;
}
}
}
}
}
else
{
lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3002_; 
lean_dec(v_a_2949_);
lean_dec(v___y_2945_);
lean_dec(v_a_2909_);
lean_dec_ref(v_docCtx_2893_);
lean_dec_ref(v___x_2892_);
lean_dec_ref(v_hints_2891_);
lean_dec(v___x_2889_);
lean_dec_ref(v_a_2888_);
lean_dec_ref(v_preDefs_2885_);
lean_dec_ref(v_perms_2882_);
v_a_2995_ = lean_ctor_get(v___x_2950_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2997_ = v___x_2950_;
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2950_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_3000_; 
if (v_isShared_2998_ == 0)
{
v___x_3000_ = v___x_2997_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_a_2995_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
}
else
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
lean_dec(v___y_2945_);
lean_dec(v_a_2937_);
lean_dec(v_a_2909_);
lean_dec_ref(v_fixedArgs_2894_);
lean_dec_ref(v_docCtx_2893_);
lean_dec_ref(v___x_2892_);
lean_dec_ref(v_hints_2891_);
lean_dec(v___x_2889_);
lean_dec_ref(v_a_2888_);
lean_dec_ref(v_preDefs_2885_);
lean_dec_ref(v_perms_2882_);
v_a_3003_ = lean_ctor_get(v___x_2948_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3005_ = v___x_2948_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_2948_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
if (v_isShared_3006_ == 0)
{
v___x_3008_ = v___x_3005_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3003_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
}
v___jp_3011_:
{
if (v___y_3018_ == 0)
{
lean_object* v_declName_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; 
v_declName_3019_ = lean_ctor_get(v___x_2892_, 3);
v___x_3020_ = ((lean_object*)(l_Lean_Elab_partialFixpoint___lam__0___closed__3));
lean_inc(v_declName_3019_);
v___x_3021_ = l_Lean_Name_append(v_declName_3019_, v___x_3020_);
v___y_2939_ = v___y_3015_;
v___y_2940_ = v___y_3014_;
v___y_2941_ = v___y_3013_;
v___y_2942_ = v___y_3012_;
v___y_2943_ = v___y_3016_;
v___y_2944_ = v___y_3017_;
v___y_2945_ = v___x_3021_;
goto v___jp_2938_;
}
else
{
lean_object* v_declName_3022_; 
v_declName_3022_ = lean_ctor_get(v___x_2892_, 3);
lean_inc(v_declName_3022_);
v___y_2939_ = v___y_3015_;
v___y_2940_ = v___y_3014_;
v___y_2941_ = v___y_3013_;
v___y_2942_ = v___y_3012_;
v___y_2943_ = v___y_3016_;
v___y_2944_ = v___y_3017_;
v___y_2945_ = v_declName_3022_;
goto v___jp_2938_;
}
}
v___jp_3023_:
{
lean_object* v___x_3030_; uint8_t v___x_3031_; 
v___x_3030_ = lean_unsigned_to_nat(1u);
v___x_3031_ = lean_nat_dec_eq(v___x_2889_, v___x_3030_);
if (v___x_3031_ == 0)
{
v___y_3012_ = v___y_3028_;
v___y_3013_ = v___y_3029_;
v___y_3014_ = v___y_3024_;
v___y_3015_ = v___y_3025_;
v___y_3016_ = v___y_3026_;
v___y_3017_ = v___y_3027_;
v___y_3018_ = v___x_3031_;
goto v___jp_3011_;
}
else
{
uint8_t v___x_3032_; 
lean_inc_ref(v_a_2888_);
v___x_3032_ = l_Lean_Elab_FixedParamPerms_fixedArePrefix(v_a_2888_);
v___y_3012_ = v___y_3028_;
v___y_3013_ = v___y_3029_;
v___y_3014_ = v___y_3024_;
v___y_3015_ = v___y_3025_;
v___y_3016_ = v___y_3026_;
v___y_3017_ = v___y_3027_;
v___y_3018_ = v___x_3032_;
goto v___jp_3011_;
}
}
}
else
{
lean_object* v_a_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3052_; 
lean_del_object(v___x_2934_);
lean_dec(v_a_2909_);
lean_dec_ref(v_fixedArgs_2894_);
lean_dec_ref(v_docCtx_2893_);
lean_dec_ref(v___x_2892_);
lean_dec_ref(v_hints_2891_);
lean_dec(v___x_2889_);
lean_dec_ref(v_a_2888_);
lean_dec_ref(v_preDefs_2885_);
lean_dec_ref(v_perms_2882_);
v_a_3045_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3047_ = v___x_2936_;
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_a_3045_);
lean_dec(v___x_2936_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3050_; 
if (v_isShared_3048_ == 0)
{
v___x_3050_ = v___x_3047_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_a_3045_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
}
}
}
else
{
lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3062_; 
lean_dec(v_a_2914_);
lean_dec(v_a_2909_);
lean_dec_ref(v_fixedArgs_2894_);
lean_dec_ref(v_docCtx_2893_);
lean_dec_ref(v___x_2892_);
lean_dec_ref(v_hints_2891_);
lean_dec(v___x_2889_);
lean_dec_ref(v_a_2888_);
lean_dec_ref(v_preDefs_2885_);
lean_dec_ref(v_perms_2882_);
v_a_3055_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3057_ = v___x_2930_;
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_dec(v___x_2930_);
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
lean_dec(v_a_2914_);
lean_dec(v_a_2909_);
lean_dec_ref(v_fixedArgs_2894_);
lean_dec_ref(v_docCtx_2893_);
lean_dec_ref(v___x_2892_);
lean_dec_ref(v_hints_2891_);
lean_dec(v___x_2889_);
lean_dec_ref(v_a_2888_);
lean_dec_ref(v_preDefs_2885_);
lean_dec_ref(v_perms_2882_);
v_a_3063_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_3065_ = v___x_2926_;
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_a_3063_);
lean_dec(v___x_2926_);
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
lean_dec(v_a_2917_);
lean_dec(v_a_2914_);
lean_dec(v_a_2912_);
lean_dec(v_a_2909_);
lean_dec(v_a_2906_);
lean_dec_ref(v_fixedArgs_2894_);
lean_dec_ref(v_docCtx_2893_);
lean_dec_ref(v___x_2892_);
lean_dec_ref(v_hints_2891_);
lean_dec(v___x_2889_);
lean_dec_ref(v_a_2888_);
lean_dec_ref(v_preDefs_2885_);
lean_dec_ref(v_perms_2882_);
v_a_3071_ = lean_ctor_get(v___x_2921_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_2921_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3073_ = v___x_2921_;
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_a_3071_);
lean_dec(v___x_2921_);
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
lean_dec(v_a_2914_);
lean_dec(v_a_2912_);
lean_dec(v_a_2909_);
lean_dec(v_a_2906_);
lean_dec_ref(v_fixedArgs_2894_);
lean_dec_ref(v_docCtx_2893_);
lean_dec_ref(v___x_2892_);
lean_dec_ref(v_hints_2891_);
lean_dec(v___x_2889_);
lean_dec_ref(v_a_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v_preDefs_2885_);
lean_dec_ref(v_perms_2882_);
v_a_3079_ = lean_ctor_get(v___x_2916_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_2916_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3081_ = v___x_2916_;
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_a_3079_);
lean_dec(v___x_2916_);
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
lean_dec(v_a_2912_);
lean_dec(v_a_2909_);
lean_dec(v_a_2906_);
lean_dec_ref(v_fixedArgs_2894_);
lean_dec_ref(v_docCtx_2893_);
lean_dec_ref(v___x_2892_);
lean_dec_ref(v_hints_2891_);
lean_dec(v___x_2889_);
lean_dec_ref(v_a_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v_preDefs_2885_);
lean_dec_ref(v_perms_2882_);
v_a_3087_ = lean_ctor_get(v___x_2913_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3089_ = v___x_2913_;
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v___x_2913_);
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
lean_dec(v_a_2909_);
lean_dec(v_a_2906_);
lean_dec_ref(v_fixedArgs_2894_);
lean_dec_ref(v_docCtx_2893_);
lean_dec_ref(v___x_2892_);
lean_dec_ref(v_hints_2891_);
lean_dec(v___x_2889_);
lean_dec_ref(v_a_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v_preDefs_2885_);
lean_dec_ref(v_perms_2882_);
v_a_3095_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3097_ = v___x_2911_;
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v___x_2911_);
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
else
{
lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3110_; 
lean_dec(v_a_2906_);
lean_dec(v_a_2904_);
lean_dec_ref(v_fixedArgs_2894_);
lean_dec_ref(v_docCtx_2893_);
lean_dec_ref(v___x_2892_);
lean_dec_ref(v_hints_2891_);
lean_dec(v___x_2889_);
lean_dec_ref(v_a_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v_preDefs_2885_);
lean_dec_ref(v_perms_2882_);
v_a_3103_ = lean_ctor_get(v___x_2908_, 0);
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3105_ = v___x_2908_;
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_dec(v___x_2908_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3108_; 
if (v_isShared_3106_ == 0)
{
v___x_3108_ = v___x_3105_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_a_3103_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
}
else
{
lean_object* v_a_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3118_; 
lean_dec(v_a_2904_);
lean_dec_ref(v_fixedArgs_2894_);
lean_dec_ref(v_docCtx_2893_);
lean_dec_ref(v___x_2892_);
lean_dec_ref(v_hints_2891_);
lean_dec(v___x_2889_);
lean_dec_ref(v_a_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v_preDefs_2885_);
lean_dec_ref(v_perms_2882_);
v_a_3111_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_3118_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3113_ = v___x_2905_;
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_a_3111_);
lean_dec(v___x_2905_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v___x_3116_; 
if (v_isShared_3114_ == 0)
{
v___x_3116_ = v___x_3113_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v_a_3111_);
v___x_3116_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
return v___x_3116_;
}
}
}
}
else
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
lean_dec_ref(v_fixedArgs_2894_);
lean_dec_ref(v_docCtx_2893_);
lean_dec_ref(v___x_2892_);
lean_dec_ref(v_hints_2891_);
lean_dec(v___x_2889_);
lean_dec_ref(v_a_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v_preDefs_2885_);
lean_dec_ref(v_perms_2882_);
v_a_3119_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3121_ = v___x_2903_;
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_2903_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3124_; 
if (v_isShared_3122_ == 0)
{
v___x_3124_ = v___x_3121_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3119_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_partialFixpoint___lam__0___boxed(lean_object** _args){
lean_object* v_a_3127_ = _args[0];
lean_object* v_perms_3128_ = _args[1];
lean_object* v___x_3129_ = _args[2];
lean_object* v_sz_3130_ = _args[3];
lean_object* v_preDefs_3131_ = _args[4];
lean_object* v___x_3132_ = _args[5];
lean_object* v___x_3133_ = _args[6];
lean_object* v_a_3134_ = _args[7];
lean_object* v___x_3135_ = _args[8];
lean_object* v___x_3136_ = _args[9];
lean_object* v_hints_3137_ = _args[10];
lean_object* v___x_3138_ = _args[11];
lean_object* v_docCtx_3139_ = _args[12];
lean_object* v_fixedArgs_3140_ = _args[13];
lean_object* v___y_3141_ = _args[14];
lean_object* v___y_3142_ = _args[15];
lean_object* v___y_3143_ = _args[16];
lean_object* v___y_3144_ = _args[17];
lean_object* v___y_3145_ = _args[18];
lean_object* v___y_3146_ = _args[19];
lean_object* v___y_3147_ = _args[20];
_start:
{
size_t v___x_57942__boxed_3148_; size_t v_sz_boxed_3149_; uint8_t v___x_57947__boxed_3150_; lean_object* v_res_3151_; 
v___x_57942__boxed_3148_ = lean_unbox_usize(v___x_3129_);
lean_dec(v___x_3129_);
v_sz_boxed_3149_ = lean_unbox_usize(v_sz_3130_);
lean_dec(v_sz_3130_);
v___x_57947__boxed_3150_ = lean_unbox(v___x_3136_);
v_res_3151_ = l_Lean_Elab_partialFixpoint___lam__0(v_a_3127_, v_perms_3128_, v___x_57942__boxed_3148_, v_sz_boxed_3149_, v_preDefs_3131_, v___x_3132_, v___x_3133_, v_a_3134_, v___x_3135_, v___x_57947__boxed_3150_, v_hints_3137_, v___x_3138_, v_docCtx_3139_, v_fixedArgs_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3145_);
lean_dec(v___y_3144_);
lean_dec_ref(v___y_3143_);
lean_dec(v___y_3142_);
lean_dec_ref(v___y_3141_);
lean_dec(v___x_3132_);
return v_res_3151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0_spec__0(lean_object* v_as_3152_, size_t v_i_3153_, size_t v_stop_3154_, lean_object* v_b_3155_){
_start:
{
lean_object* v___y_3157_; uint8_t v___x_3161_; 
v___x_3161_ = lean_usize_dec_eq(v_i_3153_, v_stop_3154_);
if (v___x_3161_ == 0)
{
lean_object* v___x_3162_; lean_object* v_termination_3163_; lean_object* v_partialFixpoint_x3f_3164_; 
v___x_3162_ = lean_array_uget_borrowed(v_as_3152_, v_i_3153_);
v_termination_3163_ = lean_ctor_get(v___x_3162_, 8);
v_partialFixpoint_x3f_3164_ = lean_ctor_get(v_termination_3163_, 3);
if (lean_obj_tag(v_partialFixpoint_x3f_3164_) == 0)
{
v___y_3157_ = v_b_3155_;
goto v___jp_3156_;
}
else
{
lean_object* v_val_3165_; lean_object* v___x_3166_; 
v_val_3165_ = lean_ctor_get(v_partialFixpoint_x3f_3164_, 0);
lean_inc(v_val_3165_);
v___x_3166_ = lean_array_push(v_b_3155_, v_val_3165_);
v___y_3157_ = v___x_3166_;
goto v___jp_3156_;
}
}
else
{
return v_b_3155_;
}
v___jp_3156_:
{
size_t v___x_3158_; size_t v___x_3159_; 
v___x_3158_ = ((size_t)1ULL);
v___x_3159_ = lean_usize_add(v_i_3153_, v___x_3158_);
v_i_3153_ = v___x_3159_;
v_b_3155_ = v___y_3157_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0_spec__0___boxed(lean_object* v_as_3167_, lean_object* v_i_3168_, lean_object* v_stop_3169_, lean_object* v_b_3170_){
_start:
{
size_t v_i_boxed_3171_; size_t v_stop_boxed_3172_; lean_object* v_res_3173_; 
v_i_boxed_3171_ = lean_unbox_usize(v_i_3168_);
lean_dec(v_i_3168_);
v_stop_boxed_3172_ = lean_unbox_usize(v_stop_3169_);
lean_dec(v_stop_3169_);
v_res_3173_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0_spec__0(v_as_3167_, v_i_boxed_3171_, v_stop_boxed_3172_, v_b_3170_);
lean_dec_ref(v_as_3167_);
return v_res_3173_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0(lean_object* v_as_3176_, lean_object* v_start_3177_, lean_object* v_stop_3178_){
_start:
{
lean_object* v___x_3179_; uint8_t v___x_3180_; 
v___x_3179_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0___closed__0));
v___x_3180_ = lean_nat_dec_lt(v_start_3177_, v_stop_3178_);
if (v___x_3180_ == 0)
{
return v___x_3179_;
}
else
{
lean_object* v___x_3181_; uint8_t v___x_3182_; 
v___x_3181_ = lean_array_get_size(v_as_3176_);
v___x_3182_ = lean_nat_dec_le(v_stop_3178_, v___x_3181_);
if (v___x_3182_ == 0)
{
uint8_t v___x_3183_; 
v___x_3183_ = lean_nat_dec_lt(v_start_3177_, v___x_3181_);
if (v___x_3183_ == 0)
{
return v___x_3179_;
}
else
{
size_t v___x_3184_; size_t v___x_3185_; lean_object* v___x_3186_; 
v___x_3184_ = lean_usize_of_nat(v_start_3177_);
v___x_3185_ = lean_usize_of_nat(v___x_3181_);
v___x_3186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0_spec__0(v_as_3176_, v___x_3184_, v___x_3185_, v___x_3179_);
return v___x_3186_;
}
}
else
{
size_t v___x_3187_; size_t v___x_3188_; lean_object* v___x_3189_; 
v___x_3187_ = lean_usize_of_nat(v_start_3177_);
v___x_3188_ = lean_usize_of_nat(v_stop_3178_);
v___x_3189_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0_spec__0(v_as_3176_, v___x_3187_, v___x_3188_, v___x_3179_);
return v___x_3189_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0___boxed(lean_object* v_as_3190_, lean_object* v_start_3191_, lean_object* v_stop_3192_){
_start:
{
lean_object* v_res_3193_; 
v_res_3193_ = l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0(v_as_3190_, v_start_3191_, v_stop_3192_);
lean_dec(v_stop_3192_);
lean_dec(v_start_3191_);
lean_dec_ref(v_as_3190_);
return v_res_3193_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27_spec__33(uint8_t v___x_3194_, lean_object* v_as_3195_, size_t v_i_3196_, size_t v_stop_3197_){
_start:
{
uint8_t v___x_3198_; 
v___x_3198_ = lean_usize_dec_eq(v_i_3196_, v_stop_3197_);
if (v___x_3198_ == 0)
{
lean_object* v___x_3199_; uint8_t v_fixpointType_3200_; uint8_t v___x_3201_; uint8_t v___y_3203_; uint8_t v___x_3207_; 
v___x_3199_ = lean_array_uget_borrowed(v_as_3195_, v_i_3196_);
v_fixpointType_3200_ = lean_ctor_get_uint8(v___x_3199_, sizeof(void*)*2);
v___x_3201_ = 1;
v___x_3207_ = l_Lean_Elab_isLatticeTheoretic(v_fixpointType_3200_);
if (v___x_3207_ == 0)
{
v___y_3203_ = v___x_3194_;
goto v___jp_3202_;
}
else
{
v___y_3203_ = v___x_3198_;
goto v___jp_3202_;
}
v___jp_3202_:
{
if (v___y_3203_ == 0)
{
size_t v___x_3204_; size_t v___x_3205_; 
v___x_3204_ = ((size_t)1ULL);
v___x_3205_ = lean_usize_add(v_i_3196_, v___x_3204_);
v_i_3196_ = v___x_3205_;
goto _start;
}
else
{
return v___x_3201_;
}
}
}
else
{
uint8_t v___x_3208_; 
v___x_3208_ = 0;
return v___x_3208_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27_spec__33___boxed(lean_object* v___x_3209_, lean_object* v_as_3210_, lean_object* v_i_3211_, lean_object* v_stop_3212_){
_start:
{
uint8_t v___x_58470__boxed_3213_; size_t v_i_boxed_3214_; size_t v_stop_boxed_3215_; uint8_t v_res_3216_; lean_object* v_r_3217_; 
v___x_58470__boxed_3213_ = lean_unbox(v___x_3209_);
v_i_boxed_3214_ = lean_unbox_usize(v_i_3211_);
lean_dec(v_i_3211_);
v_stop_boxed_3215_ = lean_unbox_usize(v_stop_3212_);
lean_dec(v_stop_3212_);
v_res_3216_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27_spec__33(v___x_58470__boxed_3213_, v_as_3210_, v_i_boxed_3214_, v_stop_boxed_3215_);
lean_dec_ref(v_as_3210_);
v_r_3217_ = lean_box(v_res_3216_);
return v_r_3217_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27(uint8_t v___x_3218_, lean_object* v_as_3219_, size_t v_i_3220_, size_t v_stop_3221_){
_start:
{
uint8_t v___x_3222_; 
v___x_3222_ = lean_usize_dec_eq(v_i_3220_, v_stop_3221_);
if (v___x_3222_ == 0)
{
lean_object* v___x_3223_; uint8_t v_fixpointType_3224_; uint8_t v___x_3225_; uint8_t v___y_3227_; uint8_t v___x_3231_; 
v___x_3223_ = lean_array_uget_borrowed(v_as_3219_, v_i_3220_);
v_fixpointType_3224_ = lean_ctor_get_uint8(v___x_3223_, sizeof(void*)*2);
v___x_3225_ = 1;
v___x_3231_ = l_Lean_Elab_isLatticeTheoretic(v_fixpointType_3224_);
if (v___x_3231_ == 0)
{
v___y_3227_ = v___x_3218_;
goto v___jp_3226_;
}
else
{
v___y_3227_ = v___x_3222_;
goto v___jp_3226_;
}
v___jp_3226_:
{
if (v___y_3227_ == 0)
{
size_t v___x_3228_; size_t v___x_3229_; uint8_t v___x_3230_; 
v___x_3228_ = ((size_t)1ULL);
v___x_3229_ = lean_usize_add(v_i_3220_, v___x_3228_);
v___x_3230_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27_spec__33(v___x_3218_, v_as_3219_, v___x_3229_, v_stop_3221_);
return v___x_3230_;
}
else
{
return v___x_3225_;
}
}
}
else
{
uint8_t v___x_3232_; 
v___x_3232_ = 0;
return v___x_3232_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27___boxed(lean_object* v___x_3233_, lean_object* v_as_3234_, lean_object* v_i_3235_, lean_object* v_stop_3236_){
_start:
{
uint8_t v___x_58493__boxed_3237_; size_t v_i_boxed_3238_; size_t v_stop_boxed_3239_; uint8_t v_res_3240_; lean_object* v_r_3241_; 
v___x_58493__boxed_3237_ = lean_unbox(v___x_3233_);
v_i_boxed_3238_ = lean_unbox_usize(v_i_3235_);
lean_dec(v_i_3235_);
v_stop_boxed_3239_ = lean_unbox_usize(v_stop_3236_);
lean_dec(v_stop_3236_);
v_res_3240_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27(v___x_58493__boxed_3237_, v_as_3234_, v_i_boxed_3238_, v_stop_boxed_3239_);
lean_dec_ref(v_as_3234_);
v_r_3241_ = lean_box(v_res_3240_);
return v_r_3241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__7(size_t v_sz_3242_, size_t v_i_3243_, lean_object* v_bs_3244_){
_start:
{
uint8_t v___x_3245_; 
v___x_3245_ = lean_usize_dec_lt(v_i_3243_, v_sz_3242_);
if (v___x_3245_ == 0)
{
return v_bs_3244_;
}
else
{
lean_object* v_v_3246_; lean_object* v_declName_3247_; lean_object* v___x_3248_; lean_object* v_bs_x27_3249_; size_t v___x_3250_; size_t v___x_3251_; lean_object* v___x_3252_; 
v_v_3246_ = lean_array_uget_borrowed(v_bs_3244_, v_i_3243_);
v_declName_3247_ = lean_ctor_get(v_v_3246_, 3);
lean_inc(v_declName_3247_);
v___x_3248_ = lean_unsigned_to_nat(0u);
v_bs_x27_3249_ = lean_array_uset(v_bs_3244_, v_i_3243_, v___x_3248_);
v___x_3250_ = ((size_t)1ULL);
v___x_3251_ = lean_usize_add(v_i_3243_, v___x_3250_);
v___x_3252_ = lean_array_uset(v_bs_x27_3249_, v_i_3243_, v_declName_3247_);
v_i_3243_ = v___x_3251_;
v_bs_3244_ = v___x_3252_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__7___boxed(lean_object* v_sz_3254_, lean_object* v_i_3255_, lean_object* v_bs_3256_){
_start:
{
size_t v_sz_boxed_3257_; size_t v_i_boxed_3258_; lean_object* v_res_3259_; 
v_sz_boxed_3257_ = lean_unbox_usize(v_sz_3254_);
lean_dec(v_sz_3254_);
v_i_boxed_3258_ = lean_unbox_usize(v_i_3255_);
lean_dec(v_i_3255_);
v_res_3259_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__7(v_sz_boxed_3257_, v_i_boxed_3258_, v_bs_3256_);
return v_res_3259_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__0(void){
_start:
{
lean_object* v___x_3260_; lean_object* v___x_3261_; 
v___x_3260_ = lean_box(1);
v___x_3261_ = l_Lean_MessageData_ofFormat(v___x_3260_);
return v___x_3261_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__3(void){
_start:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; 
v___x_3265_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__2));
v___x_3266_ = l_Lean_MessageData_ofFormat(v___x_3265_);
return v___x_3266_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11(lean_object* v_x_3267_, lean_object* v_x_3268_){
_start:
{
if (lean_obj_tag(v_x_3268_) == 0)
{
return v_x_3267_;
}
else
{
lean_object* v_head_3269_; lean_object* v_tail_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3292_; 
v_head_3269_ = lean_ctor_get(v_x_3268_, 0);
v_tail_3270_ = lean_ctor_get(v_x_3268_, 1);
v_isSharedCheck_3292_ = !lean_is_exclusive(v_x_3268_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3272_ = v_x_3268_;
v_isShared_3273_ = v_isSharedCheck_3292_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_tail_3270_);
lean_inc(v_head_3269_);
lean_dec(v_x_3268_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3292_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v_before_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3290_; 
v_before_3274_ = lean_ctor_get(v_head_3269_, 0);
v_isSharedCheck_3290_ = !lean_is_exclusive(v_head_3269_);
if (v_isSharedCheck_3290_ == 0)
{
lean_object* v_unused_3291_; 
v_unused_3291_ = lean_ctor_get(v_head_3269_, 1);
lean_dec(v_unused_3291_);
v___x_3276_ = v_head_3269_;
v_isShared_3277_ = v_isSharedCheck_3290_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_before_3274_);
lean_dec(v_head_3269_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3290_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v___x_3278_; lean_object* v___x_3280_; 
v___x_3278_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__0);
if (v_isShared_3277_ == 0)
{
lean_ctor_set_tag(v___x_3276_, 7);
lean_ctor_set(v___x_3276_, 1, v___x_3278_);
lean_ctor_set(v___x_3276_, 0, v_x_3267_);
v___x_3280_ = v___x_3276_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v_x_3267_);
lean_ctor_set(v_reuseFailAlloc_3289_, 1, v___x_3278_);
v___x_3280_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
lean_object* v___x_3281_; lean_object* v___x_3283_; 
v___x_3281_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__3);
if (v_isShared_3273_ == 0)
{
lean_ctor_set_tag(v___x_3272_, 7);
lean_ctor_set(v___x_3272_, 1, v___x_3281_);
lean_ctor_set(v___x_3272_, 0, v___x_3280_);
v___x_3283_ = v___x_3272_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v___x_3280_);
lean_ctor_set(v_reuseFailAlloc_3288_, 1, v___x_3281_);
v___x_3283_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3284_ = l_Lean_MessageData_ofSyntax(v_before_3274_);
v___x_3285_ = l_Lean_indentD(v___x_3284_);
v___x_3286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3283_);
lean_ctor_set(v___x_3286_, 1, v___x_3285_);
v_x_3267_ = v___x_3286_;
v_x_3268_ = v_tail_3270_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__10(lean_object* v_opts_3293_, lean_object* v_opt_3294_){
_start:
{
lean_object* v_name_3295_; lean_object* v_defValue_3296_; lean_object* v_map_3297_; lean_object* v___x_3298_; 
v_name_3295_ = lean_ctor_get(v_opt_3294_, 0);
v_defValue_3296_ = lean_ctor_get(v_opt_3294_, 1);
v_map_3297_ = lean_ctor_get(v_opts_3293_, 0);
v___x_3298_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3297_, v_name_3295_);
if (lean_obj_tag(v___x_3298_) == 0)
{
uint8_t v___x_3299_; 
v___x_3299_ = lean_unbox(v_defValue_3296_);
return v___x_3299_;
}
else
{
lean_object* v_val_3300_; 
v_val_3300_ = lean_ctor_get(v___x_3298_, 0);
lean_inc(v_val_3300_);
lean_dec_ref_known(v___x_3298_, 1);
if (lean_obj_tag(v_val_3300_) == 1)
{
uint8_t v_v_3301_; 
v_v_3301_ = lean_ctor_get_uint8(v_val_3300_, 0);
lean_dec_ref_known(v_val_3300_, 0);
return v_v_3301_;
}
else
{
uint8_t v___x_3302_; 
lean_dec(v_val_3300_);
v___x_3302_ = lean_unbox(v_defValue_3296_);
return v___x_3302_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__10___boxed(lean_object* v_opts_3303_, lean_object* v_opt_3304_){
_start:
{
uint8_t v_res_3305_; lean_object* v_r_3306_; 
v_res_3305_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__10(v_opts_3303_, v_opt_3304_);
lean_dec_ref(v_opt_3304_);
lean_dec_ref(v_opts_3303_);
v_r_3306_ = lean_box(v_res_3305_);
return v_r_3306_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3310_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__1));
v___x_3311_ = l_Lean_MessageData_ofFormat(v___x_3310_);
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg(lean_object* v_msgData_3312_, lean_object* v_macroStack_3313_, lean_object* v___y_3314_){
_start:
{
lean_object* v_options_3316_; lean_object* v___x_3317_; uint8_t v___x_3318_; 
v_options_3316_ = lean_ctor_get(v___y_3314_, 2);
v___x_3317_ = l_Lean_Elab_pp_macroStack;
v___x_3318_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__10(v_options_3316_, v___x_3317_);
if (v___x_3318_ == 0)
{
lean_object* v___x_3319_; 
lean_dec(v_macroStack_3313_);
v___x_3319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3319_, 0, v_msgData_3312_);
return v___x_3319_;
}
else
{
if (lean_obj_tag(v_macroStack_3313_) == 0)
{
lean_object* v___x_3320_; 
v___x_3320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3320_, 0, v_msgData_3312_);
return v___x_3320_;
}
else
{
lean_object* v_head_3321_; lean_object* v_after_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3337_; 
v_head_3321_ = lean_ctor_get(v_macroStack_3313_, 0);
lean_inc(v_head_3321_);
v_after_3322_ = lean_ctor_get(v_head_3321_, 1);
v_isSharedCheck_3337_ = !lean_is_exclusive(v_head_3321_);
if (v_isSharedCheck_3337_ == 0)
{
lean_object* v_unused_3338_; 
v_unused_3338_ = lean_ctor_get(v_head_3321_, 0);
lean_dec(v_unused_3338_);
v___x_3324_ = v_head_3321_;
v_isShared_3325_ = v_isSharedCheck_3337_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_after_3322_);
lean_dec(v_head_3321_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3337_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v___x_3326_; lean_object* v___x_3328_; 
v___x_3326_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11___closed__0);
if (v_isShared_3325_ == 0)
{
lean_ctor_set_tag(v___x_3324_, 7);
lean_ctor_set(v___x_3324_, 1, v___x_3326_);
lean_ctor_set(v___x_3324_, 0, v_msgData_3312_);
v___x_3328_ = v___x_3324_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v_msgData_3312_);
lean_ctor_set(v_reuseFailAlloc_3336_, 1, v___x_3326_);
v___x_3328_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v_msgData_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3329_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___closed__2);
v___x_3330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3328_);
lean_ctor_set(v___x_3330_, 1, v___x_3329_);
v___x_3331_ = l_Lean_MessageData_ofSyntax(v_after_3322_);
v___x_3332_ = l_Lean_indentD(v___x_3331_);
v_msgData_3333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_3333_, 0, v___x_3330_);
lean_ctor_set(v_msgData_3333_, 1, v___x_3332_);
v___x_3334_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2_spec__11(v_msgData_3333_, v_macroStack_3313_);
v___x_3335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3334_);
return v___x_3335_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_3339_, lean_object* v_macroStack_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_){
_start:
{
lean_object* v_res_3343_; 
v_res_3343_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg(v_msgData_3339_, v_macroStack_3340_, v___y_3341_);
lean_dec_ref(v___y_3341_);
return v_res_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___redArg(lean_object* v_msg_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_){
_start:
{
lean_object* v_ref_3352_; lean_object* v___x_3353_; lean_object* v_a_3354_; lean_object* v_macroStack_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v_a_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3366_; 
v_ref_3352_ = lean_ctor_get(v___y_3349_, 5);
v___x_3353_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps_spec__6_spec__7(v_msg_3344_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_);
v_a_3354_ = lean_ctor_get(v___x_3353_, 0);
lean_inc(v_a_3354_);
lean_dec_ref(v___x_3353_);
v_macroStack_3355_ = lean_ctor_get(v___y_3345_, 1);
v___x_3356_ = l_Lean_Elab_getBetterRef(v_ref_3352_, v_macroStack_3355_);
lean_inc(v_macroStack_3355_);
v___x_3357_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg(v_a_3354_, v_macroStack_3355_, v___y_3349_);
v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3360_ = v___x_3357_;
v_isShared_3361_ = v_isSharedCheck_3366_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v___x_3357_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3366_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3362_; lean_object* v___x_3364_; 
v___x_3362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3356_);
lean_ctor_set(v___x_3362_, 1, v_a_3358_);
if (v_isShared_3361_ == 0)
{
lean_ctor_set_tag(v___x_3360_, 1);
lean_ctor_set(v___x_3360_, 0, v___x_3362_);
v___x_3364_ = v___x_3360_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v___x_3362_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___redArg___boxed(lean_object* v_msg_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_){
_start:
{
lean_object* v_res_3375_; 
v_res_3375_ = l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___redArg(v_msg_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_);
lean_dec(v___y_3373_);
lean_dec_ref(v___y_3372_);
lean_dec(v___y_3371_);
lean_dec_ref(v___y_3370_);
lean_dec(v___y_3369_);
lean_dec_ref(v___y_3368_);
return v_res_3375_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3383_ = lean_box(0);
v___x_3384_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__2));
v___x_3385_ = l_Lean_mkConst(v___x_3384_, v___x_3383_);
return v___x_3385_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3387_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__4));
v___x_3388_ = l_Lean_stringToMessageData(v___x_3387_);
return v___x_3388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0(lean_object* v_xs_3389_, lean_object* v_e_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_){
_start:
{
uint8_t v___x_3401_; 
v___x_3401_ = l_Lean_Expr_isProp(v_e_3390_);
if (v___x_3401_ == 0)
{
lean_object* v___x_3402_; lean_object* v___x_3403_; 
v___x_3402_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__5);
v___x_3403_ = l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___redArg(v___x_3402_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_);
if (lean_obj_tag(v___x_3403_) == 0)
{
lean_dec_ref_known(v___x_3403_, 1);
goto v___jp_3398_;
}
else
{
lean_object* v_a_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3411_; 
lean_dec_ref(v_xs_3389_);
v_a_3404_ = lean_ctor_get(v___x_3403_, 0);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3403_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3406_ = v___x_3403_;
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_a_3404_);
lean_dec(v___x_3403_);
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
goto v___jp_3398_;
}
v___jp_3398_:
{
lean_object* v___x_3399_; lean_object* v___x_3400_; 
v___x_3399_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___closed__3);
v___x_3400_ = l_Lean_Meta_mkInstPiOfInstsForall(v_xs_3389_, v___x_3399_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_);
return v___x_3400_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0___boxed(lean_object* v_xs_3412_, lean_object* v_e_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_){
_start:
{
lean_object* v_res_3421_; 
v_res_3421_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__0(v_xs_3412_, v_e_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
lean_dec_ref(v_e_3413_);
return v_res_3421_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3423_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__0));
v___x_3424_ = l_Lean_stringToMessageData(v___x_3423_);
return v___x_3424_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3426_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__2));
v___x_3427_ = l_Lean_stringToMessageData(v___x_3426_);
return v___x_3427_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__11(void){
_start:
{
lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; 
v___x_3440_ = lean_box(0);
v___x_3441_ = lean_unsigned_to_nat(2u);
v___x_3442_ = lean_mk_empty_array_with_capacity(v___x_3441_);
v___x_3443_ = lean_array_push(v___x_3442_, v___x_3440_);
return v___x_3443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2(lean_object* v_declName_3446_, lean_object* v_type_3447_, lean_object* v_xs_3448_, lean_object* v___x_3449_, lean_object* v___x_3450_, lean_object* v_____r_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_){
_start:
{
lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; 
v___x_3459_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__1);
v___x_3460_ = l_Lean_MessageData_ofName(v_declName_3446_);
v___x_3461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3461_, 0, v___x_3459_);
lean_ctor_set(v___x_3461_, 1, v___x_3460_);
v___x_3462_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__3);
v___x_3463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3463_, 0, v___x_3461_);
lean_ctor_set(v___x_3463_, 1, v___x_3462_);
v___x_3464_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__4));
v___x_3465_ = l_Lean_Elab_mkInhabitantFor(v___x_3463_, v___x_3464_, v_type_3447_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
if (lean_obj_tag(v___x_3465_) == 0)
{
lean_object* v_a_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; 
v_a_3466_ = lean_ctor_get(v___x_3465_, 0);
lean_inc(v_a_3466_);
lean_dec_ref_known(v___x_3465_, 1);
v___x_3467_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__7));
v___x_3468_ = l_Lean_mkAppN(v_a_3466_, v_xs_3448_);
v___x_3469_ = lean_unsigned_to_nat(1u);
v___x_3470_ = lean_mk_empty_array_with_capacity(v___x_3469_);
v___x_3471_ = lean_array_push(v___x_3470_, v___x_3468_);
v___x_3472_ = l_Lean_Meta_mkAppM(v___x_3467_, v___x_3471_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
if (lean_obj_tag(v___x_3472_) == 0)
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3497_; 
v_a_3473_ = lean_ctor_get(v___x_3472_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3472_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3475_ = v___x_3472_;
v_isShared_3476_ = v_isSharedCheck_3497_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3472_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3497_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3477_; lean_object* v___x_3479_; 
v___x_3477_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__10));
if (v_isShared_3476_ == 0)
{
lean_ctor_set_tag(v___x_3475_, 1);
v___x_3479_ = v___x_3475_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_a_3473_);
v___x_3479_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; 
v___x_3480_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__11, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__11);
v___x_3481_ = lean_array_push(v___x_3480_, v___x_3479_);
v___x_3482_ = l_Lean_Meta_mkAppOptM(v___x_3477_, v___x_3481_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
if (lean_obj_tag(v___x_3482_) == 0)
{
lean_object* v_a_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3495_; 
v_a_3483_ = lean_ctor_get(v___x_3482_, 0);
v_isSharedCheck_3495_ = !lean_is_exclusive(v___x_3482_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3485_ = v___x_3482_;
v_isShared_3486_ = v_isSharedCheck_3495_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v___x_3482_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3495_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3491_; 
v___x_3487_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__12));
v___x_3488_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___closed__13));
v___x_3489_ = l_Lean_Name_mkStr4(v___x_3449_, v___x_3450_, v___x_3487_, v___x_3488_);
if (v_isShared_3486_ == 0)
{
lean_ctor_set_tag(v___x_3485_, 1);
v___x_3491_ = v___x_3485_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_a_3483_);
v___x_3491_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
lean_object* v___x_3492_; lean_object* v___x_3493_; 
v___x_3492_ = lean_array_push(v___x_3480_, v___x_3491_);
v___x_3493_ = l_Lean_Meta_mkAppOptM(v___x_3489_, v___x_3492_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
return v___x_3493_;
}
}
}
else
{
lean_dec_ref(v___x_3450_);
lean_dec_ref(v___x_3449_);
return v___x_3482_;
}
}
}
}
else
{
lean_dec_ref(v___x_3450_);
lean_dec_ref(v___x_3449_);
return v___x_3472_;
}
}
else
{
lean_dec_ref(v___x_3450_);
lean_dec_ref(v___x_3449_);
return v___x_3465_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___boxed(lean_object* v_declName_3498_, lean_object* v_type_3499_, lean_object* v_xs_3500_, lean_object* v___x_3501_, lean_object* v___x_3502_, lean_object* v_____r_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_){
_start:
{
lean_object* v_res_3511_; 
v_res_3511_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2(v_declName_3498_, v_type_3499_, v_xs_3500_, v___x_3501_, v___x_3502_, v_____r_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
lean_dec_ref(v_xs_3500_);
return v_res_3511_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__4(lean_object* v_a_3512_, lean_object* v_a_3513_){
_start:
{
if (lean_obj_tag(v_a_3512_) == 0)
{
lean_object* v___x_3514_; 
v___x_3514_ = l_List_reverse___redArg(v_a_3513_);
return v___x_3514_;
}
else
{
lean_object* v_head_3515_; lean_object* v_tail_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3525_; 
v_head_3515_ = lean_ctor_get(v_a_3512_, 0);
v_tail_3516_ = lean_ctor_get(v_a_3512_, 1);
v_isSharedCheck_3525_ = !lean_is_exclusive(v_a_3512_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3518_ = v_a_3512_;
v_isShared_3519_ = v_isSharedCheck_3525_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_tail_3516_);
lean_inc(v_head_3515_);
lean_dec(v_a_3512_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3525_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___x_3520_; lean_object* v___x_3522_; 
v___x_3520_ = l_Lean_MessageData_ofExpr(v_head_3515_);
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 1, v_a_3513_);
lean_ctor_set(v___x_3518_, 0, v___x_3520_);
v___x_3522_ = v___x_3518_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v___x_3520_);
lean_ctor_set(v_reuseFailAlloc_3524_, 1, v_a_3513_);
v___x_3522_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
v_a_3512_ = v_tail_3516_;
v_a_3513_ = v___x_3522_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_3527_; lean_object* v___x_3528_; 
v___x_3527_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__0));
v___x_3528_ = l_Lean_stringToMessageData(v___x_3527_);
return v___x_3528_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__3(void){
_start:
{
lean_object* v___x_3530_; lean_object* v___x_3531_; 
v___x_3530_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__2));
v___x_3531_ = l_Lean_stringToMessageData(v___x_3530_);
return v___x_3531_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__7(void){
_start:
{
lean_object* v___x_3538_; lean_object* v___x_3539_; 
v___x_3538_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__6));
v___x_3539_ = l_Lean_stringToMessageData(v___x_3538_);
return v___x_3539_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__9(void){
_start:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; 
v___x_3541_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__8));
v___x_3542_ = l_Lean_stringToMessageData(v___x_3541_);
return v___x_3542_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__11(void){
_start:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3544_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__10));
v___x_3545_ = l_Lean_stringToMessageData(v___x_3544_);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3(uint8_t v___x_3546_, lean_object* v_declName_3547_, lean_object* v_type_3548_, uint8_t v_fixpointType_3549_, lean_object* v___f_3550_, lean_object* v___f_3551_, lean_object* v_value_3552_, lean_object* v_xs_3553_, lean_object* v___body_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_){
_start:
{
lean_object* v_inst_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; lean_object* v___y_3566_; lean_object* v___y_3567_; lean_object* v___y_3572_; lean_object* v___y_3573_; lean_object* v___y_3574_; lean_object* v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v_options_3588_; lean_object* v_inheritedTraceOptions_3589_; uint8_t v_hasTrace_3590_; lean_object* v_cls_3591_; lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; uint8_t v___y_3601_; lean_object* v___y_3624_; lean_object* v___y_3625_; lean_object* v___y_3626_; lean_object* v___y_3627_; lean_object* v___y_3628_; lean_object* v___y_3629_; lean_object* v___y_3630_; lean_object* v___y_3631_; lean_object* v___y_3637_; lean_object* v___y_3638_; lean_object* v___y_3639_; lean_object* v___y_3640_; lean_object* v___y_3641_; lean_object* v___y_3642_; 
v_options_3588_ = lean_ctor_get(v___y_3559_, 2);
v_inheritedTraceOptions_3589_ = lean_ctor_get(v___y_3559_, 13);
v_hasTrace_3590_ = lean_ctor_get_uint8(v_options_3588_, sizeof(void*)*1);
v_cls_3591_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7));
if (v_hasTrace_3590_ == 0)
{
lean_dec_ref(v___body_3554_);
lean_dec_ref(v_value_3552_);
v___y_3637_ = v___y_3555_;
v___y_3638_ = v___y_3556_;
v___y_3639_ = v___y_3557_;
v___y_3640_ = v___y_3558_;
v___y_3641_ = v___y_3559_;
v___y_3642_ = v___y_3560_;
goto v___jp_3636_;
}
else
{
lean_object* v___x_3664_; uint8_t v___x_3665_; 
v___x_3664_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10);
v___x_3665_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3589_, v_options_3588_, v___x_3664_);
if (v___x_3665_ == 0)
{
lean_dec_ref(v___body_3554_);
lean_dec_ref(v_value_3552_);
v___y_3637_ = v___y_3555_;
v___y_3638_ = v___y_3556_;
v___y_3639_ = v___y_3557_;
v___y_3640_ = v___y_3558_;
v___y_3641_ = v___y_3559_;
v___y_3642_ = v___y_3560_;
goto v___jp_3636_;
}
else
{
lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; 
v___x_3666_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__7);
v___x_3667_ = l_Lean_MessageData_ofExpr(v_value_3552_);
v___x_3668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3668_, 0, v___x_3666_);
lean_ctor_set(v___x_3668_, 1, v___x_3667_);
v___x_3669_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__9);
v___x_3670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3670_, 0, v___x_3668_);
lean_ctor_set(v___x_3670_, 1, v___x_3669_);
lean_inc_ref(v_xs_3553_);
v___x_3671_ = lean_array_to_list(v_xs_3553_);
v___x_3672_ = lean_box(0);
v___x_3673_ = l_List_mapTR_loop___at___00Lean_Elab_partialFixpoint_spec__4(v___x_3671_, v___x_3672_);
v___x_3674_ = l_Lean_MessageData_ofList(v___x_3673_);
v___x_3675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3675_, 0, v___x_3670_);
lean_ctor_set(v___x_3675_, 1, v___x_3674_);
v___x_3676_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__11, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__11);
v___x_3677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3677_, 0, v___x_3675_);
lean_ctor_set(v___x_3677_, 1, v___x_3676_);
v___x_3678_ = l_Lean_MessageData_ofExpr(v___body_3554_);
v___x_3679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3679_, 0, v___x_3677_);
lean_ctor_set(v___x_3679_, 1, v___x_3678_);
v___x_3680_ = l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg(v_cls_3591_, v___x_3679_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_);
if (lean_obj_tag(v___x_3680_) == 0)
{
lean_dec_ref_known(v___x_3680_, 1);
v___y_3637_ = v___y_3555_;
v___y_3638_ = v___y_3556_;
v___y_3639_ = v___y_3557_;
v___y_3640_ = v___y_3558_;
v___y_3641_ = v___y_3559_;
v___y_3642_ = v___y_3560_;
goto v___jp_3636_;
}
else
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3688_; 
lean_dec_ref(v_xs_3553_);
lean_dec_ref(v___f_3551_);
lean_dec_ref(v___f_3550_);
lean_dec_ref(v_type_3548_);
lean_dec(v_declName_3547_);
v_a_3681_ = lean_ctor_get(v___x_3680_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3680_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3683_ = v___x_3680_;
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3680_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3686_; 
if (v_isShared_3684_ == 0)
{
v___x_3686_ = v___x_3683_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_a_3681_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
}
}
}
v___jp_3562_:
{
uint8_t v___x_3568_; uint8_t v___x_3569_; lean_object* v___x_3570_; 
v___x_3568_ = 0;
v___x_3569_ = 1;
v___x_3570_ = l_Lean_Meta_mkLambdaFVars(v_xs_3553_, v_inst_3563_, v___x_3568_, v___x_3546_, v___x_3568_, v___x_3546_, v___x_3569_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_);
lean_dec_ref(v_xs_3553_);
return v___x_3570_;
}
v___jp_3571_:
{
if (lean_obj_tag(v___y_3576_) == 0)
{
lean_object* v_a_3577_; 
v_a_3577_ = lean_ctor_get(v___y_3576_, 0);
lean_inc(v_a_3577_);
lean_dec_ref_known(v___y_3576_, 1);
v_inst_3563_ = v_a_3577_;
v___y_3564_ = v___y_3575_;
v___y_3565_ = v___y_3574_;
v___y_3566_ = v___y_3573_;
v___y_3567_ = v___y_3572_;
goto v___jp_3562_;
}
else
{
lean_dec_ref(v_xs_3553_);
return v___y_3576_;
}
}
v___jp_3578_:
{
lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3586_ = lean_box(0);
lean_inc(v___y_3581_);
lean_inc_ref(v___y_3582_);
lean_inc(v___y_3584_);
lean_inc_ref(v___y_3585_);
lean_inc(v___y_3583_);
lean_inc_ref(v___y_3579_);
v___x_3587_ = lean_apply_8(v___y_3580_, v___x_3586_, v___y_3579_, v___y_3583_, v___y_3585_, v___y_3584_, v___y_3582_, v___y_3581_, lean_box(0));
v___y_3572_ = v___y_3581_;
v___y_3573_ = v___y_3582_;
v___y_3574_ = v___y_3584_;
v___y_3575_ = v___y_3585_;
v___y_3576_ = v___x_3587_;
goto v___jp_3571_;
}
v___jp_3592_:
{
if (v___y_3601_ == 0)
{
lean_object* v_options_3602_; uint8_t v_hasTrace_3603_; 
lean_dec_ref(v___y_3595_);
v_options_3602_ = lean_ctor_get(v___y_3597_, 2);
v_hasTrace_3603_ = lean_ctor_get_uint8(v_options_3602_, sizeof(void*)*1);
if (v_hasTrace_3603_ == 0)
{
lean_dec(v_declName_3547_);
v___y_3579_ = v___y_3593_;
v___y_3580_ = v___y_3594_;
v___y_3581_ = v___y_3596_;
v___y_3582_ = v___y_3597_;
v___y_3583_ = v___y_3598_;
v___y_3584_ = v___y_3600_;
v___y_3585_ = v___y_3599_;
goto v___jp_3578_;
}
else
{
lean_object* v_inheritedTraceOptions_3604_; lean_object* v___x_3605_; uint8_t v___x_3606_; 
v_inheritedTraceOptions_3604_ = lean_ctor_get(v___y_3597_, 13);
v___x_3605_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__10);
v___x_3606_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3604_, v_options_3602_, v___x_3605_);
if (v___x_3606_ == 0)
{
lean_dec(v_declName_3547_);
v___y_3579_ = v___y_3593_;
v___y_3580_ = v___y_3594_;
v___y_3581_ = v___y_3596_;
v___y_3582_ = v___y_3597_;
v___y_3583_ = v___y_3598_;
v___y_3584_ = v___y_3600_;
v___y_3585_ = v___y_3599_;
goto v___jp_3578_;
}
else
{
lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; 
v___x_3607_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__1);
v___x_3608_ = l_Lean_MessageData_ofName(v_declName_3547_);
v___x_3609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3607_);
lean_ctor_set(v___x_3609_, 1, v___x_3608_);
v___x_3610_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__3);
v___x_3611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3611_, 0, v___x_3609_);
lean_ctor_set(v___x_3611_, 1, v___x_3610_);
v___x_3612_ = l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg(v_cls_3591_, v___x_3611_, v___y_3599_, v___y_3600_, v___y_3597_, v___y_3596_);
if (lean_obj_tag(v___x_3612_) == 0)
{
lean_object* v_a_3613_; lean_object* v___x_3614_; 
v_a_3613_ = lean_ctor_get(v___x_3612_, 0);
lean_inc(v_a_3613_);
lean_dec_ref_known(v___x_3612_, 1);
lean_inc(v___y_3596_);
lean_inc_ref(v___y_3597_);
lean_inc(v___y_3600_);
lean_inc_ref(v___y_3599_);
lean_inc(v___y_3598_);
lean_inc_ref(v___y_3593_);
v___x_3614_ = lean_apply_8(v___y_3594_, v_a_3613_, v___y_3593_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3597_, v___y_3596_, lean_box(0));
v___y_3572_ = v___y_3596_;
v___y_3573_ = v___y_3597_;
v___y_3574_ = v___y_3600_;
v___y_3575_ = v___y_3599_;
v___y_3576_ = v___x_3614_;
goto v___jp_3571_;
}
else
{
lean_object* v_a_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3622_; 
lean_dec_ref(v___y_3594_);
lean_dec_ref(v_xs_3553_);
v_a_3615_ = lean_ctor_get(v___x_3612_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3617_ = v___x_3612_;
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_a_3615_);
lean_dec(v___x_3612_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v___x_3620_; 
if (v_isShared_3618_ == 0)
{
v___x_3620_ = v___x_3617_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_a_3615_);
v___x_3620_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
return v___x_3620_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_3594_);
lean_dec_ref(v_xs_3553_);
lean_dec(v_declName_3547_);
return v___y_3595_;
}
}
v___jp_3623_:
{
if (lean_obj_tag(v___y_3631_) == 0)
{
lean_object* v_a_3632_; 
lean_dec_ref(v___y_3625_);
lean_dec(v_declName_3547_);
v_a_3632_ = lean_ctor_get(v___y_3631_, 0);
lean_inc(v_a_3632_);
lean_dec_ref_known(v___y_3631_, 1);
v_inst_3563_ = v_a_3632_;
v___y_3564_ = v___y_3630_;
v___y_3565_ = v___y_3629_;
v___y_3566_ = v___y_3627_;
v___y_3567_ = v___y_3626_;
goto v___jp_3562_;
}
else
{
lean_object* v_a_3633_; uint8_t v___x_3634_; 
v_a_3633_ = lean_ctor_get(v___y_3631_, 0);
v___x_3634_ = l_Lean_Exception_isInterrupt(v_a_3633_);
if (v___x_3634_ == 0)
{
uint8_t v___x_3635_; 
lean_inc(v_a_3633_);
v___x_3635_ = l_Lean_Exception_isRuntime(v_a_3633_);
v___y_3593_ = v___y_3624_;
v___y_3594_ = v___y_3625_;
v___y_3595_ = v___y_3631_;
v___y_3596_ = v___y_3626_;
v___y_3597_ = v___y_3627_;
v___y_3598_ = v___y_3628_;
v___y_3599_ = v___y_3630_;
v___y_3600_ = v___y_3629_;
v___y_3601_ = v___x_3635_;
goto v___jp_3592_;
}
else
{
v___y_3593_ = v___y_3624_;
v___y_3594_ = v___y_3625_;
v___y_3595_ = v___y_3631_;
v___y_3596_ = v___y_3626_;
v___y_3597_ = v___y_3627_;
v___y_3598_ = v___y_3628_;
v___y_3599_ = v___y_3630_;
v___y_3600_ = v___y_3629_;
v___y_3601_ = v___x_3634_;
goto v___jp_3592_;
}
}
}
v___jp_3636_:
{
lean_object* v___x_3643_; 
lean_inc_ref(v_type_3548_);
v___x_3643_ = l_Lean_Meta_instantiateForall(v_type_3548_, v_xs_3553_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_);
if (lean_obj_tag(v___x_3643_) == 0)
{
switch(v_fixpointType_3549_)
{
case 0:
{
lean_object* v_a_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___f_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; 
lean_dec_ref(v___f_3551_);
lean_dec_ref(v___f_3550_);
v_a_3644_ = lean_ctor_get(v___x_3643_, 0);
lean_inc(v_a_3644_);
lean_dec_ref_known(v___x_3643_, 1);
v___x_3645_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__2));
v___x_3646_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_mkMonoPProd___closed__3));
lean_inc_ref(v_xs_3553_);
lean_inc(v_declName_3547_);
v___f_3647_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__2___boxed), 13, 5);
lean_closure_set(v___f_3647_, 0, v_declName_3547_);
lean_closure_set(v___f_3647_, 1, v_type_3548_);
lean_closure_set(v___f_3647_, 2, v_xs_3553_);
lean_closure_set(v___f_3647_, 3, v___x_3645_);
lean_closure_set(v___f_3647_, 4, v___x_3646_);
v___x_3648_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___closed__5));
v___x_3649_ = lean_unsigned_to_nat(1u);
v___x_3650_ = lean_mk_empty_array_with_capacity(v___x_3649_);
v___x_3651_ = lean_array_push(v___x_3650_, v_a_3644_);
v___x_3652_ = l_Lean_Meta_mkAppM(v___x_3648_, v___x_3651_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_);
if (lean_obj_tag(v___x_3652_) == 0)
{
lean_object* v_a_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; 
v_a_3653_ = lean_ctor_get(v___x_3652_, 0);
lean_inc(v_a_3653_);
lean_dec_ref_known(v___x_3652_, 1);
v___x_3654_ = lean_box(0);
v___x_3655_ = l_Lean_Meta_synthInstance(v_a_3653_, v___x_3654_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_);
v___y_3624_ = v___y_3637_;
v___y_3625_ = v___f_3647_;
v___y_3626_ = v___y_3642_;
v___y_3627_ = v___y_3641_;
v___y_3628_ = v___y_3638_;
v___y_3629_ = v___y_3640_;
v___y_3630_ = v___y_3639_;
v___y_3631_ = v___x_3655_;
goto v___jp_3623_;
}
else
{
v___y_3624_ = v___y_3637_;
v___y_3625_ = v___f_3647_;
v___y_3626_ = v___y_3642_;
v___y_3627_ = v___y_3641_;
v___y_3628_ = v___y_3638_;
v___y_3629_ = v___y_3640_;
v___y_3630_ = v___y_3639_;
v___y_3631_ = v___x_3652_;
goto v___jp_3623_;
}
}
case 1:
{
lean_object* v_a_3656_; uint8_t v___x_3657_; lean_object* v___x_3658_; 
lean_dec_ref(v___f_3551_);
lean_dec_ref(v_type_3548_);
lean_dec(v_declName_3547_);
v_a_3656_ = lean_ctor_get(v___x_3643_, 0);
lean_inc(v_a_3656_);
lean_dec_ref_known(v___x_3643_, 1);
v___x_3657_ = 0;
v___x_3658_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg(v_a_3656_, v___f_3550_, v___x_3657_, v___x_3657_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_);
if (lean_obj_tag(v___x_3658_) == 0)
{
lean_object* v_a_3659_; 
v_a_3659_ = lean_ctor_get(v___x_3658_, 0);
lean_inc(v_a_3659_);
lean_dec_ref_known(v___x_3658_, 1);
v_inst_3563_ = v_a_3659_;
v___y_3564_ = v___y_3639_;
v___y_3565_ = v___y_3640_;
v___y_3566_ = v___y_3641_;
v___y_3567_ = v___y_3642_;
goto v___jp_3562_;
}
else
{
lean_dec_ref(v_xs_3553_);
return v___x_3658_;
}
}
default: 
{
lean_object* v_a_3660_; uint8_t v___x_3661_; lean_object* v___x_3662_; 
lean_dec_ref(v___f_3550_);
lean_dec_ref(v_type_3548_);
lean_dec(v_declName_3547_);
v_a_3660_ = lean_ctor_get(v___x_3643_, 0);
lean_inc(v_a_3660_);
lean_dec_ref_known(v___x_3643_, 1);
v___x_3661_ = 0;
v___x_3662_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_partialFixpoint_spec__3___redArg(v_a_3660_, v___f_3551_, v___x_3661_, v___x_3661_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_);
if (lean_obj_tag(v___x_3662_) == 0)
{
lean_object* v_a_3663_; 
v_a_3663_ = lean_ctor_get(v___x_3662_, 0);
lean_inc(v_a_3663_);
lean_dec_ref_known(v___x_3662_, 1);
v_inst_3563_ = v_a_3663_;
v___y_3564_ = v___y_3639_;
v___y_3565_ = v___y_3640_;
v___y_3566_ = v___y_3641_;
v___y_3567_ = v___y_3642_;
goto v___jp_3562_;
}
else
{
lean_dec_ref(v_xs_3553_);
return v___x_3662_;
}
}
}
}
else
{
lean_dec_ref(v_xs_3553_);
lean_dec_ref(v___f_3551_);
lean_dec_ref(v___f_3550_);
lean_dec_ref(v_type_3548_);
lean_dec(v_declName_3547_);
return v___x_3643_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___boxed(lean_object* v___x_3689_, lean_object* v_declName_3690_, lean_object* v_type_3691_, lean_object* v_fixpointType_3692_, lean_object* v___f_3693_, lean_object* v___f_3694_, lean_object* v_value_3695_, lean_object* v_xs_3696_, lean_object* v___body_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_){
_start:
{
uint8_t v___x_59084__boxed_3705_; uint8_t v_fixpointType_boxed_3706_; lean_object* v_res_3707_; 
v___x_59084__boxed_3705_ = lean_unbox(v___x_3689_);
v_fixpointType_boxed_3706_ = lean_unbox(v_fixpointType_3692_);
v_res_3707_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3(v___x_59084__boxed_3705_, v_declName_3690_, v_type_3691_, v_fixpointType_boxed_3706_, v___f_3693_, v___f_3694_, v_value_3695_, v_xs_3696_, v___body_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
lean_dec(v___y_3701_);
lean_dec_ref(v___y_3700_);
lean_dec(v___y_3699_);
lean_dec_ref(v___y_3698_);
return v_res_3707_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__2(void){
_start:
{
lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; 
v___x_3714_ = lean_box(0);
v___x_3715_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__1));
v___x_3716_ = l_Lean_mkConst(v___x_3715_, v___x_3714_);
return v___x_3716_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__4(void){
_start:
{
lean_object* v___x_3718_; lean_object* v___x_3719_; 
v___x_3718_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__3));
v___x_3719_ = l_Lean_stringToMessageData(v___x_3718_);
return v___x_3719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1(lean_object* v_xs_3720_, lean_object* v_e_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_){
_start:
{
uint8_t v___x_3732_; 
v___x_3732_ = l_Lean_Expr_isProp(v_e_3721_);
if (v___x_3732_ == 0)
{
lean_object* v___x_3733_; lean_object* v___x_3734_; 
v___x_3733_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__4);
v___x_3734_ = l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___redArg(v___x_3733_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_);
if (lean_obj_tag(v___x_3734_) == 0)
{
lean_dec_ref_known(v___x_3734_, 1);
goto v___jp_3729_;
}
else
{
lean_object* v_a_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3742_; 
lean_dec_ref(v_xs_3720_);
v_a_3735_ = lean_ctor_get(v___x_3734_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3734_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3737_ = v___x_3734_;
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_a_3735_);
lean_dec(v___x_3734_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v___x_3740_; 
if (v_isShared_3738_ == 0)
{
v___x_3740_ = v___x_3737_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_a_3735_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
}
}
else
{
goto v___jp_3729_;
}
v___jp_3729_:
{
lean_object* v___x_3730_; lean_object* v___x_3731_; 
v___x_3730_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___closed__2);
v___x_3731_ = l_Lean_Meta_mkInstPiOfInstsForall(v_xs_3720_, v___x_3730_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_);
return v___x_3731_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1___boxed(lean_object* v_xs_3743_, lean_object* v_e_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_){
_start:
{
lean_object* v_res_3752_; 
v_res_3752_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__1(v_xs_3743_, v_e_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_);
lean_dec(v___y_3750_);
lean_dec_ref(v___y_3749_);
lean_dec(v___y_3748_);
lean_dec_ref(v___y_3747_);
lean_dec(v___y_3746_);
lean_dec_ref(v___y_3745_);
lean_dec_ref(v_e_3744_);
return v_res_3752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg(lean_object* v_hints_3755_, size_t v_sz_3756_, size_t v_i_3757_, lean_object* v_bs_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_){
_start:
{
uint8_t v___x_3766_; 
v___x_3766_ = lean_usize_dec_lt(v_i_3757_, v_sz_3756_);
if (v___x_3766_ == 0)
{
lean_object* v___x_3767_; 
v___x_3767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3767_, 0, v_bs_3758_);
return v___x_3767_;
}
else
{
lean_object* v_v_3768_; lean_object* v___x_3769_; lean_object* v_bs_x27_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v_ref_3774_; uint8_t v_fixpointType_3775_; lean_object* v_declName_3776_; lean_object* v_type_3777_; lean_object* v_value_3778_; lean_object* v_fileName_3779_; lean_object* v_fileMap_3780_; lean_object* v_options_3781_; lean_object* v_currRecDepth_3782_; lean_object* v_maxRecDepth_3783_; lean_object* v_ref_3784_; lean_object* v_currNamespace_3785_; lean_object* v_openDecls_3786_; lean_object* v_initHeartbeats_3787_; lean_object* v_maxHeartbeats_3788_; lean_object* v_quotContext_3789_; lean_object* v_currMacroScope_3790_; uint8_t v_diag_3791_; lean_object* v_cancelTk_x3f_3792_; uint8_t v_suppressElabErrors_3793_; lean_object* v_inheritedTraceOptions_3794_; lean_object* v___f_3795_; lean_object* v___f_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___f_3799_; uint8_t v___x_3800_; lean_object* v_ref_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; 
v_v_3768_ = lean_array_uget(v_bs_3758_, v_i_3757_);
v___x_3769_ = lean_unsigned_to_nat(0u);
v_bs_x27_3770_ = lean_array_uset(v_bs_3758_, v_i_3757_, v___x_3769_);
v___x_3771_ = lean_usize_to_nat(v_i_3757_);
v___x_3772_ = l_Lean_Elab_instInhabitedPartialFixpoint_default;
v___x_3773_ = lean_array_get_borrowed(v___x_3772_, v_hints_3755_, v___x_3771_);
lean_dec(v___x_3771_);
v_ref_3774_ = lean_ctor_get(v___x_3773_, 0);
v_fixpointType_3775_ = lean_ctor_get_uint8(v___x_3773_, sizeof(void*)*2);
v_declName_3776_ = lean_ctor_get(v_v_3768_, 3);
lean_inc(v_declName_3776_);
v_type_3777_ = lean_ctor_get(v_v_3768_, 6);
lean_inc_ref(v_type_3777_);
v_value_3778_ = lean_ctor_get(v_v_3768_, 7);
lean_inc_ref_n(v_value_3778_, 2);
lean_dec(v_v_3768_);
v_fileName_3779_ = lean_ctor_get(v___y_3763_, 0);
v_fileMap_3780_ = lean_ctor_get(v___y_3763_, 1);
v_options_3781_ = lean_ctor_get(v___y_3763_, 2);
v_currRecDepth_3782_ = lean_ctor_get(v___y_3763_, 3);
v_maxRecDepth_3783_ = lean_ctor_get(v___y_3763_, 4);
v_ref_3784_ = lean_ctor_get(v___y_3763_, 5);
v_currNamespace_3785_ = lean_ctor_get(v___y_3763_, 6);
v_openDecls_3786_ = lean_ctor_get(v___y_3763_, 7);
v_initHeartbeats_3787_ = lean_ctor_get(v___y_3763_, 8);
v_maxHeartbeats_3788_ = lean_ctor_get(v___y_3763_, 9);
v_quotContext_3789_ = lean_ctor_get(v___y_3763_, 10);
v_currMacroScope_3790_ = lean_ctor_get(v___y_3763_, 11);
v_diag_3791_ = lean_ctor_get_uint8(v___y_3763_, sizeof(void*)*14);
v_cancelTk_x3f_3792_ = lean_ctor_get(v___y_3763_, 12);
v_suppressElabErrors_3793_ = lean_ctor_get_uint8(v___y_3763_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3794_ = lean_ctor_get(v___y_3763_, 13);
v___f_3795_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___closed__0));
v___f_3796_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___closed__1));
v___x_3797_ = lean_box(v___x_3766_);
v___x_3798_ = lean_box(v_fixpointType_3775_);
v___f_3799_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___lam__3___boxed), 16, 7);
lean_closure_set(v___f_3799_, 0, v___x_3797_);
lean_closure_set(v___f_3799_, 1, v_declName_3776_);
lean_closure_set(v___f_3799_, 2, v_type_3777_);
lean_closure_set(v___f_3799_, 3, v___x_3798_);
lean_closure_set(v___f_3799_, 4, v___f_3795_);
lean_closure_set(v___f_3799_, 5, v___f_3796_);
lean_closure_set(v___f_3799_, 6, v_value_3778_);
v___x_3800_ = 0;
v_ref_3801_ = l_Lean_replaceRef(v_ref_3774_, v_ref_3784_);
lean_inc_ref(v_inheritedTraceOptions_3794_);
lean_inc(v_cancelTk_x3f_3792_);
lean_inc(v_currMacroScope_3790_);
lean_inc(v_quotContext_3789_);
lean_inc(v_maxHeartbeats_3788_);
lean_inc(v_initHeartbeats_3787_);
lean_inc(v_openDecls_3786_);
lean_inc(v_currNamespace_3785_);
lean_inc(v_maxRecDepth_3783_);
lean_inc(v_currRecDepth_3782_);
lean_inc_ref(v_options_3781_);
lean_inc_ref(v_fileMap_3780_);
lean_inc_ref(v_fileName_3779_);
v___x_3802_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3802_, 0, v_fileName_3779_);
lean_ctor_set(v___x_3802_, 1, v_fileMap_3780_);
lean_ctor_set(v___x_3802_, 2, v_options_3781_);
lean_ctor_set(v___x_3802_, 3, v_currRecDepth_3782_);
lean_ctor_set(v___x_3802_, 4, v_maxRecDepth_3783_);
lean_ctor_set(v___x_3802_, 5, v_ref_3801_);
lean_ctor_set(v___x_3802_, 6, v_currNamespace_3785_);
lean_ctor_set(v___x_3802_, 7, v_openDecls_3786_);
lean_ctor_set(v___x_3802_, 8, v_initHeartbeats_3787_);
lean_ctor_set(v___x_3802_, 9, v_maxHeartbeats_3788_);
lean_ctor_set(v___x_3802_, 10, v_quotContext_3789_);
lean_ctor_set(v___x_3802_, 11, v_currMacroScope_3790_);
lean_ctor_set(v___x_3802_, 12, v_cancelTk_x3f_3792_);
lean_ctor_set(v___x_3802_, 13, v_inheritedTraceOptions_3794_);
lean_ctor_set_uint8(v___x_3802_, sizeof(void*)*14, v_diag_3791_);
lean_ctor_set_uint8(v___x_3802_, sizeof(void*)*14 + 1, v_suppressElabErrors_3793_);
v___x_3803_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_partialFixpoint_spec__5___redArg(v_value_3778_, v___f_3799_, v___x_3800_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___x_3802_, v___y_3764_);
lean_dec_ref_known(v___x_3802_, 14);
if (lean_obj_tag(v___x_3803_) == 0)
{
lean_object* v_a_3804_; size_t v___x_3805_; size_t v___x_3806_; lean_object* v___x_3807_; 
v_a_3804_ = lean_ctor_get(v___x_3803_, 0);
lean_inc(v_a_3804_);
lean_dec_ref_known(v___x_3803_, 1);
v___x_3805_ = ((size_t)1ULL);
v___x_3806_ = lean_usize_add(v_i_3757_, v___x_3805_);
v___x_3807_ = lean_array_uset(v_bs_x27_3770_, v_i_3757_, v_a_3804_);
v_i_3757_ = v___x_3806_;
v_bs_3758_ = v___x_3807_;
goto _start;
}
else
{
lean_object* v_a_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3816_; 
lean_dec_ref(v_bs_x27_3770_);
v_a_3809_ = lean_ctor_get(v___x_3803_, 0);
v_isSharedCheck_3816_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3816_ == 0)
{
v___x_3811_ = v___x_3803_;
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_a_3809_);
lean_dec(v___x_3803_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3814_; 
if (v_isShared_3812_ == 0)
{
v___x_3814_ = v___x_3811_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v_a_3809_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
return v___x_3814_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg___boxed(lean_object* v_hints_3817_, lean_object* v_sz_3818_, lean_object* v_i_3819_, lean_object* v_bs_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_){
_start:
{
size_t v_sz_boxed_3828_; size_t v_i_boxed_3829_; lean_object* v_res_3830_; 
v_sz_boxed_3828_ = lean_unbox_usize(v_sz_3818_);
lean_dec(v_sz_3818_);
v_i_boxed_3829_ = lean_unbox_usize(v_i_3819_);
lean_dec(v_i_3819_);
v_res_3830_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg(v_hints_3817_, v_sz_boxed_3828_, v_i_boxed_3829_, v_bs_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
lean_dec(v___y_3826_);
lean_dec_ref(v___y_3825_);
lean_dec(v___y_3824_);
lean_dec_ref(v___y_3823_);
lean_dec(v___y_3822_);
lean_dec_ref(v___y_3821_);
lean_dec_ref(v_hints_3817_);
return v_res_3830_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__26_spec__31(lean_object* v_as_3831_, size_t v_i_3832_, size_t v_stop_3833_){
_start:
{
uint8_t v___x_3834_; 
v___x_3834_ = lean_usize_dec_eq(v_i_3832_, v_stop_3833_);
if (v___x_3834_ == 0)
{
lean_object* v___x_3835_; uint8_t v_fixpointType_3836_; uint8_t v___x_3837_; 
v___x_3835_ = lean_array_uget_borrowed(v_as_3831_, v_i_3832_);
v_fixpointType_3836_ = lean_ctor_get_uint8(v___x_3835_, sizeof(void*)*2);
v___x_3837_ = l_Lean_Elab_isLatticeTheoretic(v_fixpointType_3836_);
if (v___x_3837_ == 0)
{
size_t v___x_3838_; size_t v___x_3839_; 
v___x_3838_ = ((size_t)1ULL);
v___x_3839_ = lean_usize_add(v_i_3832_, v___x_3838_);
v_i_3832_ = v___x_3839_;
goto _start;
}
else
{
return v___x_3837_;
}
}
else
{
uint8_t v___x_3841_; 
v___x_3841_ = 0;
return v___x_3841_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__26_spec__31___boxed(lean_object* v_as_3842_, lean_object* v_i_3843_, lean_object* v_stop_3844_){
_start:
{
size_t v_i_boxed_3845_; size_t v_stop_boxed_3846_; uint8_t v_res_3847_; lean_object* v_r_3848_; 
v_i_boxed_3845_ = lean_unbox_usize(v_i_3843_);
lean_dec(v_i_3843_);
v_stop_boxed_3846_ = lean_unbox_usize(v_stop_3844_);
lean_dec(v_stop_3844_);
v_res_3847_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__26_spec__31(v_as_3842_, v_i_boxed_3845_, v_stop_boxed_3846_);
lean_dec_ref(v_as_3842_);
v_r_3848_ = lean_box(v_res_3847_);
return v_r_3848_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__26(lean_object* v_as_3849_, size_t v_i_3850_, size_t v_stop_3851_){
_start:
{
uint8_t v___x_3852_; 
v___x_3852_ = lean_usize_dec_eq(v_i_3850_, v_stop_3851_);
if (v___x_3852_ == 0)
{
lean_object* v___x_3853_; uint8_t v_fixpointType_3854_; uint8_t v___x_3855_; 
v___x_3853_ = lean_array_uget_borrowed(v_as_3849_, v_i_3850_);
v_fixpointType_3854_ = lean_ctor_get_uint8(v___x_3853_, sizeof(void*)*2);
v___x_3855_ = l_Lean_Elab_isLatticeTheoretic(v_fixpointType_3854_);
if (v___x_3855_ == 0)
{
size_t v___x_3856_; size_t v___x_3857_; uint8_t v___x_3858_; 
v___x_3856_ = ((size_t)1ULL);
v___x_3857_ = lean_usize_add(v_i_3850_, v___x_3856_);
v___x_3858_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__26_spec__31(v_as_3849_, v___x_3857_, v_stop_3851_);
return v___x_3858_;
}
else
{
return v___x_3855_;
}
}
else
{
uint8_t v___x_3859_; 
v___x_3859_ = 0;
return v___x_3859_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__26___boxed(lean_object* v_as_3860_, lean_object* v_i_3861_, lean_object* v_stop_3862_){
_start:
{
size_t v_i_boxed_3863_; size_t v_stop_boxed_3864_; uint8_t v_res_3865_; lean_object* v_r_3866_; 
v_i_boxed_3863_ = lean_unbox_usize(v_i_3861_);
lean_dec(v_i_3861_);
v_stop_boxed_3864_ = lean_unbox_usize(v_stop_3862_);
lean_dec(v_stop_3862_);
v_res_3865_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__26(v_as_3860_, v_i_boxed_3863_, v_stop_boxed_3864_);
lean_dec_ref(v_as_3860_);
v_r_3866_ = lean_box(v_res_3865_);
return v_r_3866_;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___closed__1(void){
_start:
{
lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; 
v___x_3868_ = ((lean_object*)(l_Lean_Elab_partialFixpoint___closed__0));
v___x_3869_ = lean_unsigned_to_nat(2u);
v___x_3870_ = lean_unsigned_to_nat(82u);
v___x_3871_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__7));
v___x_3872_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__0));
v___x_3873_ = l_mkPanicMessageWithDecl(v___x_3872_, v___x_3871_, v___x_3870_, v___x_3869_, v___x_3868_);
return v___x_3873_;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___closed__3(void){
_start:
{
lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; 
v___x_3875_ = ((lean_object*)(l_Lean_Elab_partialFixpoint___closed__2));
v___x_3876_ = lean_unsigned_to_nat(4u);
v___x_3877_ = lean_unsigned_to_nat(86u);
v___x_3878_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___lam__0___closed__7));
v___x_3879_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___closed__0));
v___x_3880_ = l_mkPanicMessageWithDecl(v___x_3879_, v___x_3878_, v___x_3877_, v___x_3876_, v___x_3875_);
return v___x_3880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_partialFixpoint(lean_object* v_docCtx_3883_, lean_object* v_preDefs_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_){
_start:
{
lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v_hints_3894_; lean_object* v___x_3895_; uint8_t v___x_3896_; lean_object* v___y_3898_; lean_object* v___y_3899_; lean_object* v___y_3900_; lean_object* v___y_3901_; lean_object* v___y_3902_; lean_object* v___y_3903_; 
v___x_3892_ = lean_unsigned_to_nat(0u);
v___x_3893_ = lean_array_get_size(v_preDefs_3884_);
v_hints_3894_ = l_Array_filterMapM___at___00Lean_Elab_partialFixpoint_spec__0(v_preDefs_3884_, v___x_3892_, v___x_3893_);
v___x_3895_ = lean_array_get_size(v_hints_3894_);
v___x_3896_ = lean_nat_dec_eq(v___x_3893_, v___x_3895_);
if (v___x_3896_ == 0)
{
lean_object* v___x_3938_; lean_object* v___x_3939_; 
lean_dec_ref(v_hints_3894_);
lean_dec_ref(v_preDefs_3884_);
lean_dec_ref(v_docCtx_3883_);
v___x_3938_ = lean_obj_once(&l_Lean_Elab_partialFixpoint___closed__1, &l_Lean_Elab_partialFixpoint___closed__1_once, _init_l_Lean_Elab_partialFixpoint___closed__1);
v___x_3939_ = l_panic___at___00Lean_Elab_partialFixpoint_spec__25(v___x_3938_, v_a_3885_, v_a_3886_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_);
return v___x_3939_;
}
else
{
uint8_t v___x_3940_; 
v___x_3940_ = lean_nat_dec_lt(v___x_3892_, v___x_3895_);
if (v___x_3940_ == 0)
{
v___y_3898_ = v_a_3885_;
v___y_3899_ = v_a_3886_;
v___y_3900_ = v_a_3887_;
v___y_3901_ = v_a_3888_;
v___y_3902_ = v_a_3889_;
v___y_3903_ = v_a_3890_;
goto v___jp_3897_;
}
else
{
if (v___x_3940_ == 0)
{
v___y_3898_ = v_a_3885_;
v___y_3899_ = v_a_3886_;
v___y_3900_ = v_a_3887_;
v___y_3901_ = v_a_3888_;
v___y_3902_ = v_a_3889_;
v___y_3903_ = v_a_3890_;
goto v___jp_3897_;
}
else
{
size_t v___x_3941_; size_t v___x_3942_; uint8_t v___x_3943_; 
v___x_3941_ = ((size_t)0ULL);
v___x_3942_ = lean_usize_of_nat(v___x_3895_);
v___x_3943_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__26(v_hints_3894_, v___x_3941_, v___x_3942_);
if (v___x_3943_ == 0)
{
v___y_3898_ = v_a_3885_;
v___y_3899_ = v_a_3886_;
v___y_3900_ = v_a_3887_;
v___y_3901_ = v_a_3888_;
v___y_3902_ = v_a_3889_;
v___y_3903_ = v_a_3890_;
goto v___jp_3897_;
}
else
{
if (v___x_3940_ == 0)
{
v___y_3898_ = v_a_3885_;
v___y_3899_ = v_a_3886_;
v___y_3900_ = v_a_3887_;
v___y_3901_ = v_a_3888_;
v___y_3902_ = v_a_3889_;
v___y_3903_ = v_a_3890_;
goto v___jp_3897_;
}
else
{
if (v___x_3940_ == 0)
{
v___y_3898_ = v_a_3885_;
v___y_3899_ = v_a_3886_;
v___y_3900_ = v_a_3887_;
v___y_3901_ = v_a_3888_;
v___y_3902_ = v_a_3889_;
v___y_3903_ = v_a_3890_;
goto v___jp_3897_;
}
else
{
uint8_t v___x_3944_; 
v___x_3944_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_partialFixpoint_spec__27(v___x_3943_, v_hints_3894_, v___x_3941_, v___x_3942_);
if (v___x_3944_ == 0)
{
v___y_3898_ = v_a_3885_;
v___y_3899_ = v_a_3886_;
v___y_3900_ = v_a_3887_;
v___y_3901_ = v_a_3888_;
v___y_3902_ = v_a_3889_;
v___y_3903_ = v_a_3890_;
goto v___jp_3897_;
}
else
{
lean_object* v___x_3945_; lean_object* v___x_3946_; 
lean_dec_ref(v_hints_3894_);
lean_dec_ref(v_preDefs_3884_);
lean_dec_ref(v_docCtx_3883_);
v___x_3945_ = lean_obj_once(&l_Lean_Elab_partialFixpoint___closed__3, &l_Lean_Elab_partialFixpoint___closed__3_once, _init_l_Lean_Elab_partialFixpoint___closed__3);
v___x_3946_ = l_panic___at___00Lean_Elab_partialFixpoint_spec__25(v___x_3945_, v_a_3885_, v_a_3886_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_);
return v___x_3946_;
}
}
}
}
}
}
}
v___jp_3897_:
{
size_t v_sz_3904_; size_t v___x_3905_; lean_object* v___x_3906_; 
v_sz_3904_ = lean_array_size(v_preDefs_3884_);
v___x_3905_ = ((size_t)0ULL);
lean_inc_ref(v_preDefs_3884_);
v___x_3906_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg(v_hints_3894_, v_sz_3904_, v___x_3905_, v_preDefs_3884_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_);
if (lean_obj_tag(v___x_3906_) == 0)
{
lean_object* v_a_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; 
v_a_3907_ = lean_ctor_get(v___x_3906_, 0);
lean_inc(v_a_3907_);
lean_dec_ref_known(v___x_3906_, 1);
lean_inc_ref_n(v_preDefs_3884_, 2);
v___x_3908_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__7(v_sz_3904_, v___x_3905_, v_preDefs_3884_);
v___x_3909_ = l_Lean_Elab_getFixedParamPerms(v_preDefs_3884_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v_a_3910_; lean_object* v_perms_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v_type_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___f_3920_; lean_object* v___x_3921_; 
v_a_3910_ = lean_ctor_get(v___x_3909_, 0);
lean_inc(v_a_3910_);
lean_dec_ref_known(v___x_3909_, 1);
v_perms_3911_ = lean_ctor_get(v_a_3910_, 1);
lean_inc_ref(v_perms_3911_);
v___x_3912_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_3913_ = lean_array_get(v___x_3912_, v_preDefs_3884_, v___x_3892_);
v_type_3914_ = lean_ctor_get(v___x_3913_, 6);
lean_inc_ref(v_type_3914_);
v___x_3915_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lam__0___closed__1);
v___x_3916_ = lean_array_get(v___x_3915_, v_perms_3911_, v___x_3892_);
v___x_3917_ = ((lean_object*)(l_Lean_Elab_partialFixpoint___boxed__const__1));
v___x_3918_ = lean_box_usize(v_sz_3904_);
v___x_3919_ = lean_box(v___x_3896_);
v___f_3920_ = lean_alloc_closure((void*)(l_Lean_Elab_partialFixpoint___lam__0___boxed), 21, 13);
lean_closure_set(v___f_3920_, 0, v_a_3907_);
lean_closure_set(v___f_3920_, 1, v_perms_3911_);
lean_closure_set(v___f_3920_, 2, v___x_3917_);
lean_closure_set(v___f_3920_, 3, v___x_3918_);
lean_closure_set(v___f_3920_, 4, v_preDefs_3884_);
lean_closure_set(v___f_3920_, 5, v___x_3892_);
lean_closure_set(v___f_3920_, 6, v___x_3908_);
lean_closure_set(v___f_3920_, 7, v_a_3910_);
lean_closure_set(v___f_3920_, 8, v___x_3893_);
lean_closure_set(v___f_3920_, 9, v___x_3919_);
lean_closure_set(v___f_3920_, 10, v_hints_3894_);
lean_closure_set(v___f_3920_, 11, v___x_3913_);
lean_closure_set(v___f_3920_, 12, v_docCtx_3883_);
v___x_3921_ = l_Lean_Elab_FixedParamPerm_forallTelescope___at___00Lean_Elab_partialFixpoint_spec__24___redArg(v___x_3916_, v_type_3914_, v___f_3920_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_);
return v___x_3921_;
}
else
{
lean_object* v_a_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3929_; 
lean_dec_ref(v___x_3908_);
lean_dec(v_a_3907_);
lean_dec_ref(v_hints_3894_);
lean_dec_ref(v_preDefs_3884_);
lean_dec_ref(v_docCtx_3883_);
v_a_3922_ = lean_ctor_get(v___x_3909_, 0);
v_isSharedCheck_3929_ = !lean_is_exclusive(v___x_3909_);
if (v_isSharedCheck_3929_ == 0)
{
v___x_3924_ = v___x_3909_;
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_a_3922_);
lean_dec(v___x_3909_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3927_; 
if (v_isShared_3925_ == 0)
{
v___x_3927_ = v___x_3924_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v_a_3922_);
v___x_3927_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
return v___x_3927_;
}
}
}
}
else
{
lean_object* v_a_3930_; lean_object* v___x_3932_; uint8_t v_isShared_3933_; uint8_t v_isSharedCheck_3937_; 
lean_dec_ref(v_hints_3894_);
lean_dec_ref(v_preDefs_3884_);
lean_dec_ref(v_docCtx_3883_);
v_a_3930_ = lean_ctor_get(v___x_3906_, 0);
v_isSharedCheck_3937_ = !lean_is_exclusive(v___x_3906_);
if (v_isSharedCheck_3937_ == 0)
{
v___x_3932_ = v___x_3906_;
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
else
{
lean_inc(v_a_3930_);
lean_dec(v___x_3906_);
v___x_3932_ = lean_box(0);
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
v_resetjp_3931_:
{
lean_object* v___x_3935_; 
if (v_isShared_3933_ == 0)
{
v___x_3935_ = v___x_3932_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_a_3930_);
v___x_3935_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
return v___x_3935_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_partialFixpoint___boxed(lean_object* v_docCtx_3947_, lean_object* v_preDefs_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_){
_start:
{
lean_object* v_res_3956_; 
v_res_3956_ = l_Lean_Elab_partialFixpoint(v_docCtx_3947_, v_preDefs_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_);
lean_dec(v_a_3954_);
lean_dec_ref(v_a_3953_);
lean_dec(v_a_3952_);
lean_dec_ref(v_a_3951_);
lean_dec(v_a_3950_);
lean_dec_ref(v_a_3949_);
return v_res_3956_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1(lean_object* v_00_u03b1_3957_, lean_object* v_msg_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_){
_start:
{
lean_object* v___x_3966_; 
v___x_3966_ = l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___redArg(v_msg_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
return v___x_3966_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1___boxed(lean_object* v_00_u03b1_3967_, lean_object* v_msg_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_){
_start:
{
lean_object* v_res_3976_; 
v_res_3976_ = l_Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1(v_00_u03b1_3967_, v_msg_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_);
lean_dec(v___y_3974_);
lean_dec_ref(v___y_3973_);
lean_dec(v___y_3972_);
lean_dec_ref(v___y_3971_);
lean_dec(v___y_3970_);
lean_dec_ref(v___y_3969_);
return v_res_3976_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2(lean_object* v_cls_3977_, lean_object* v_msg_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_){
_start:
{
lean_object* v___x_3986_; 
v___x_3986_ = l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___redArg(v_cls_3977_, v_msg_3978_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_);
return v___x_3986_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2___boxed(lean_object* v_cls_3987_, lean_object* v_msg_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_){
_start:
{
lean_object* v_res_3996_; 
v_res_3996_ = l_Lean_addTrace___at___00Lean_Elab_partialFixpoint_spec__2(v_cls_3987_, v_msg_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_);
lean_dec(v___y_3994_);
lean_dec_ref(v___y_3993_);
lean_dec(v___y_3992_);
lean_dec_ref(v___y_3991_);
lean_dec(v___y_3990_);
lean_dec_ref(v___y_3989_);
return v_res_3996_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6(lean_object* v_hints_3997_, lean_object* v_as_3998_, size_t v_sz_3999_, size_t v_i_4000_, lean_object* v_bs_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_){
_start:
{
lean_object* v___x_4009_; 
v___x_4009_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___redArg(v_hints_3997_, v_sz_3999_, v_i_4000_, v_bs_4001_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_);
return v___x_4009_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6___boxed(lean_object* v_hints_4010_, lean_object* v_as_4011_, lean_object* v_sz_4012_, lean_object* v_i_4013_, lean_object* v_bs_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_){
_start:
{
size_t v_sz_boxed_4022_; size_t v_i_boxed_4023_; lean_object* v_res_4024_; 
v_sz_boxed_4022_ = lean_unbox_usize(v_sz_4012_);
lean_dec(v_sz_4012_);
v_i_boxed_4023_ = lean_unbox_usize(v_i_4013_);
lean_dec(v_i_4013_);
v_res_4024_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__6(v_hints_4010_, v_as_4011_, v_sz_boxed_4022_, v_i_boxed_4023_, v_bs_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_);
lean_dec(v___y_4020_);
lean_dec_ref(v___y_4019_);
lean_dec(v___y_4018_);
lean_dec_ref(v___y_4017_);
lean_dec(v___y_4016_);
lean_dec_ref(v___y_4015_);
lean_dec_ref(v_as_4011_);
lean_dec_ref(v_hints_4010_);
return v_res_4024_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__10(lean_object* v___x_4025_, lean_object* v_fixedArgs_4026_, lean_object* v_as_4027_, size_t v_sz_4028_, size_t v_i_4029_, lean_object* v_bs_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_){
_start:
{
lean_object* v___x_4038_; 
v___x_4038_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__10___redArg(v___x_4025_, v_fixedArgs_4026_, v_sz_4028_, v_i_4029_, v_bs_4030_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_);
return v___x_4038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__10___boxed(lean_object* v___x_4039_, lean_object* v_fixedArgs_4040_, lean_object* v_as_4041_, lean_object* v_sz_4042_, lean_object* v_i_4043_, lean_object* v_bs_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_){
_start:
{
size_t v_sz_boxed_4052_; size_t v_i_boxed_4053_; lean_object* v_res_4054_; 
v_sz_boxed_4052_ = lean_unbox_usize(v_sz_4042_);
lean_dec(v_sz_4042_);
v_i_boxed_4053_ = lean_unbox_usize(v_i_4043_);
lean_dec(v_i_4043_);
v_res_4054_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__10(v___x_4039_, v_fixedArgs_4040_, v_as_4041_, v_sz_boxed_4052_, v_i_boxed_4053_, v_bs_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_);
lean_dec(v___y_4050_);
lean_dec_ref(v___y_4049_);
lean_dec(v___y_4048_);
lean_dec_ref(v___y_4047_);
lean_dec(v___y_4046_);
lean_dec_ref(v___y_4045_);
lean_dec_ref(v_as_4041_);
lean_dec_ref(v___x_4039_);
return v_res_4054_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__11(lean_object* v___x_4055_, lean_object* v_fixedArgs_4056_, lean_object* v_as_4057_, size_t v_sz_4058_, size_t v_i_4059_, lean_object* v_bs_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_){
_start:
{
lean_object* v___x_4068_; 
v___x_4068_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__11___redArg(v___x_4055_, v_fixedArgs_4056_, v_sz_4058_, v_i_4059_, v_bs_4060_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
return v___x_4068_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__11___boxed(lean_object* v___x_4069_, lean_object* v_fixedArgs_4070_, lean_object* v_as_4071_, lean_object* v_sz_4072_, lean_object* v_i_4073_, lean_object* v_bs_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_){
_start:
{
size_t v_sz_boxed_4082_; size_t v_i_boxed_4083_; lean_object* v_res_4084_; 
v_sz_boxed_4082_ = lean_unbox_usize(v_sz_4072_);
lean_dec(v_sz_4072_);
v_i_boxed_4083_ = lean_unbox_usize(v_i_4073_);
lean_dec(v_i_4073_);
v_res_4084_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__11(v___x_4069_, v_fixedArgs_4070_, v_as_4071_, v_sz_boxed_4082_, v_i_boxed_4083_, v_bs_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
lean_dec(v___y_4080_);
lean_dec_ref(v___y_4079_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec_ref(v___y_4075_);
lean_dec_ref(v_as_4071_);
lean_dec_ref(v___x_4069_);
return v_res_4084_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13(lean_object* v_as_4085_, size_t v_i_4086_, size_t v_stop_4087_, lean_object* v_b_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_){
_start:
{
lean_object* v___x_4096_; 
v___x_4096_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13___redArg(v_as_4085_, v_i_4086_, v_stop_4087_, v_b_4088_, v___y_4093_, v___y_4094_);
return v___x_4096_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13___boxed(lean_object* v_as_4097_, lean_object* v_i_4098_, lean_object* v_stop_4099_, lean_object* v_b_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_){
_start:
{
size_t v_i_boxed_4108_; size_t v_stop_boxed_4109_; lean_object* v_res_4110_; 
v_i_boxed_4108_ = lean_unbox_usize(v_i_4098_);
lean_dec(v_i_4098_);
v_stop_boxed_4109_ = lean_unbox_usize(v_stop_4099_);
lean_dec(v_stop_4099_);
v_res_4110_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_partialFixpoint_spec__13(v_as_4097_, v_i_boxed_4108_, v_stop_boxed_4109_, v_b_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_);
lean_dec(v___y_4106_);
lean_dec_ref(v___y_4105_);
lean_dec(v___y_4104_);
lean_dec_ref(v___y_4103_);
lean_dec(v___y_4102_);
lean_dec_ref(v___y_4101_);
lean_dec_ref(v_as_4097_);
return v_res_4110_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16(lean_object* v_env_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_){
_start:
{
lean_object* v___x_4119_; 
v___x_4119_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16___redArg(v_env_4111_, v___y_4115_, v___y_4117_);
return v___x_4119_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16___boxed(lean_object* v_env_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_){
_start:
{
lean_object* v_res_4128_; 
v_res_4128_ = l_Lean_setEnv___at___00Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14_spec__16(v_env_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
lean_dec(v___y_4124_);
lean_dec_ref(v___y_4123_);
lean_dec(v___y_4122_);
lean_dec_ref(v___y_4121_);
return v_res_4128_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14(lean_object* v_00_u03b1_4129_, lean_object* v_env_4130_, lean_object* v_x_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_){
_start:
{
lean_object* v___x_4139_; 
v___x_4139_ = l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14___redArg(v_env_4130_, v_x_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
return v___x_4139_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14___boxed(lean_object* v_00_u03b1_4140_, lean_object* v_env_4141_, lean_object* v_x_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_){
_start:
{
lean_object* v_res_4150_; 
v_res_4150_ = l_Lean_withEnv___at___00Lean_Elab_partialFixpoint_spec__14(v_00_u03b1_4140_, v_env_4141_, v_x_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_);
lean_dec(v___y_4148_);
lean_dec_ref(v___y_4147_);
lean_dec(v___y_4146_);
lean_dec_ref(v___y_4145_);
lean_dec(v___y_4144_);
lean_dec_ref(v___y_4143_);
return v_res_4150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18(lean_object* v_00_u03b1_4151_, lean_object* v_name_4152_, uint8_t v_bi_4153_, lean_object* v_type_4154_, lean_object* v_k_4155_, uint8_t v_kind_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_){
_start:
{
lean_object* v___x_4164_; 
v___x_4164_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___redArg(v_name_4152_, v_bi_4153_, v_type_4154_, v_k_4155_, v_kind_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_);
return v___x_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18___boxed(lean_object* v_00_u03b1_4165_, lean_object* v_name_4166_, lean_object* v_bi_4167_, lean_object* v_type_4168_, lean_object* v_k_4169_, lean_object* v_kind_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_){
_start:
{
uint8_t v_bi_boxed_4178_; uint8_t v_kind_boxed_4179_; lean_object* v_res_4180_; 
v_bi_boxed_4178_ = lean_unbox(v_bi_4167_);
v_kind_boxed_4179_ = lean_unbox(v_kind_4170_);
v_res_4180_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15_spec__18(v_00_u03b1_4165_, v_name_4166_, v_bi_boxed_4178_, v_type_4168_, v_k_4169_, v_kind_boxed_4179_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_);
lean_dec(v___y_4176_);
lean_dec_ref(v___y_4175_);
lean_dec(v___y_4174_);
lean_dec_ref(v___y_4173_);
lean_dec(v___y_4172_);
lean_dec_ref(v___y_4171_);
return v_res_4180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15(lean_object* v_00_u03b1_4181_, lean_object* v_name_4182_, lean_object* v_type_4183_, lean_object* v_k_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_){
_start:
{
lean_object* v___x_4192_; 
v___x_4192_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15___redArg(v_name_4182_, v_type_4183_, v_k_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_);
return v___x_4192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15___boxed(lean_object* v_00_u03b1_4193_, lean_object* v_name_4194_, lean_object* v_type_4195_, lean_object* v_k_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_){
_start:
{
lean_object* v_res_4204_; 
v_res_4204_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_partialFixpoint_spec__15(v_00_u03b1_4193_, v_name_4194_, v_type_4195_, v_k_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_);
lean_dec(v___y_4202_);
lean_dec_ref(v___y_4201_);
lean_dec(v___y_4200_);
lean_dec_ref(v___y_4199_);
lean_dec(v___y_4198_);
lean_dec_ref(v___y_4197_);
return v_res_4204_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21(lean_object* v_00_u03b1_4205_, lean_object* v_x_4206_, uint8_t v_isExporting_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_){
_start:
{
lean_object* v___x_4215_; 
v___x_4215_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___redArg(v_x_4206_, v_isExporting_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_);
return v___x_4215_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21___boxed(lean_object* v_00_u03b1_4216_, lean_object* v_x_4217_, lean_object* v_isExporting_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_){
_start:
{
uint8_t v_isExporting_boxed_4226_; lean_object* v_res_4227_; 
v_isExporting_boxed_4226_ = lean_unbox(v_isExporting_4218_);
v_res_4227_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17_spec__21(v_00_u03b1_4216_, v_x_4217_, v_isExporting_boxed_4226_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
lean_dec(v___y_4224_);
lean_dec_ref(v___y_4223_);
lean_dec(v___y_4222_);
lean_dec_ref(v___y_4221_);
lean_dec(v___y_4220_);
lean_dec_ref(v___y_4219_);
return v_res_4227_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17(lean_object* v_00_u03b1_4228_, lean_object* v_x_4229_, uint8_t v_when_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_){
_start:
{
lean_object* v___x_4238_; 
v___x_4238_ = l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17___redArg(v_x_4229_, v_when_4230_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_);
return v___x_4238_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17___boxed(lean_object* v_00_u03b1_4239_, lean_object* v_x_4240_, lean_object* v_when_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_){
_start:
{
uint8_t v_when_boxed_4249_; lean_object* v_res_4250_; 
v_when_boxed_4249_ = lean_unbox(v_when_4241_);
v_res_4250_ = l_Lean_withoutExporting___at___00Lean_Elab_partialFixpoint_spec__17(v_00_u03b1_4239_, v_x_4240_, v_when_boxed_4249_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_);
lean_dec(v___y_4247_);
lean_dec_ref(v___y_4246_);
lean_dec(v___y_4245_);
lean_dec_ref(v___y_4244_);
lean_dec(v___y_4243_);
lean_dec_ref(v___y_4242_);
return v_res_4250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__21(lean_object* v___x_4251_, lean_object* v___x_4252_, lean_object* v___y_4253_, lean_object* v___x_4254_, lean_object* v_a_4255_, lean_object* v_as_4256_, size_t v_sz_4257_, size_t v_i_4258_, lean_object* v_bs_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_){
_start:
{
lean_object* v___x_4267_; 
v___x_4267_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__21___redArg(v___x_4251_, v___x_4252_, v___y_4253_, v___x_4254_, v_a_4255_, v_sz_4257_, v_i_4258_, v_bs_4259_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_);
return v___x_4267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__21___boxed(lean_object* v___x_4268_, lean_object* v___x_4269_, lean_object* v___y_4270_, lean_object* v___x_4271_, lean_object* v_a_4272_, lean_object* v_as_4273_, lean_object* v_sz_4274_, lean_object* v_i_4275_, lean_object* v_bs_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_){
_start:
{
size_t v_sz_boxed_4284_; size_t v_i_boxed_4285_; lean_object* v_res_4286_; 
v_sz_boxed_4284_ = lean_unbox_usize(v_sz_4274_);
lean_dec(v_sz_4274_);
v_i_boxed_4285_ = lean_unbox_usize(v_i_4275_);
lean_dec(v_i_4275_);
v_res_4286_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__21(v___x_4268_, v___x_4269_, v___y_4270_, v___x_4271_, v_a_4272_, v_as_4273_, v_sz_boxed_4284_, v_i_boxed_4285_, v_bs_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_);
lean_dec(v___y_4282_);
lean_dec_ref(v___y_4281_);
lean_dec(v___y_4280_);
lean_dec_ref(v___y_4279_);
lean_dec(v___y_4278_);
lean_dec_ref(v___y_4277_);
lean_dec_ref(v_as_4273_);
lean_dec_ref(v___x_4268_);
return v_res_4286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__22(size_t v_sz_4287_, size_t v_i_4288_, lean_object* v_bs_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_){
_start:
{
lean_object* v___x_4297_; 
v___x_4297_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__22___redArg(v_sz_4287_, v_i_4288_, v_bs_4289_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_);
return v___x_4297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__22___boxed(lean_object* v_sz_4298_, lean_object* v_i_4299_, lean_object* v_bs_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_){
_start:
{
size_t v_sz_boxed_4308_; size_t v_i_boxed_4309_; lean_object* v_res_4310_; 
v_sz_boxed_4308_ = lean_unbox_usize(v_sz_4298_);
lean_dec(v_sz_4298_);
v_i_boxed_4309_ = lean_unbox_usize(v_i_4299_);
lean_dec(v_i_4299_);
v_res_4310_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__22(v_sz_boxed_4308_, v_i_boxed_4309_, v_bs_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_);
lean_dec(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec(v___y_4304_);
lean_dec_ref(v___y_4303_);
lean_dec(v___y_4302_);
lean_dec_ref(v___y_4301_);
return v_res_4310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2(lean_object* v_msgData_4311_, lean_object* v_macroStack_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_){
_start:
{
lean_object* v___x_4320_; 
v___x_4320_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___redArg(v_msgData_4311_, v_macroStack_4312_, v___y_4317_);
return v___x_4320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2___boxed(lean_object* v_msgData_4321_, lean_object* v_macroStack_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_){
_start:
{
lean_object* v_res_4330_; 
v_res_4330_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_partialFixpoint_spec__1_spec__2(v_msgData_4321_, v_macroStack_4322_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
lean_dec(v___y_4328_);
lean_dec_ref(v___y_4327_);
lean_dec(v___y_4326_);
lean_dec_ref(v___y_4325_);
lean_dec(v___y_4324_);
lean_dec_ref(v___y_4323_);
return v_res_4330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4394_; uint8_t v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; 
v___x_4394_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_partialFixpoint_spec__19___redArg___closed__7));
v___x_4395_ = 0;
v___x_4396_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn___closed__25_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_));
v___x_4397_ = l_Lean_registerTraceClass(v___x_4394_, v___x_4395_, v___x_4396_);
return v___x_4397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2____boxed(lean_object* v_a_4398_){
_start:
{
lean_object* v_res_4399_; 
v_res_4399_ = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__initFn_00___x40_Lean_Elab_PreDefinition_PartialFixpoint_Main_1869300320____hygCtx___hyg_2_();
return v_res_4399_;
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
