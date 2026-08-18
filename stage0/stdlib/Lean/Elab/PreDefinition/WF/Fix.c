// Lean compiler output
// Module: Lean.Elab.PreDefinition.WF.Fix
// Imports: public import Lean.Data.Array public import Lean.Elab.PreDefinition.Basic public import Lean.Elab.PreDefinition.WF.Basic public import Lean.Meta.ArgsPacker public import Lean.Meta.Match.MatcherApp.Transform public import Lean.Meta.Tactic.Cleanup public import Lean.Util.HasConstCache
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
lean_object* l_Lean_stringToMessageData(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_ArgsPacker_unpack(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarsNoDelayed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalContext_isSubPrefixOf(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getRecAppSyntax_x3f(lean_object*);
lean_object* l_Lean_Expr_mdataExpr_x21(lean_object*);
lean_object* l_Lean_MVarId_setType___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_applyCleanWfTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Elab_Tactic_setGoals___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Elab_Term_withDeclName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* l_Lean_mkRecAppWithSyntax(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_HasConstCache_containsUnsafe(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedLocalDecl_default;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_size(lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_local_ctx_is_empty(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addPPExplicitToExposeDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalContext_contains(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMData(lean_object*, lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_getMotivePos(lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_addArg_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_altNumParams(lean_object*);
lean_object* l_Lean_Meta_MatcherApp_toExpr(lean_object*);
lean_object* l_Lean_Elab_ensureNoRecFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM(lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_LocalContext_setUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "wf"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "replaceRecApps"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(40, 215, 222, 176, 152, 52, 0, 225)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(222, 200, 98, 106, 253, 180, 239, 155)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(54, 49, 183, 192, 189, 122, 168, 8)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(68, 153, 95, 135, 30, 171, 176, 236)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "Type check every step of the well-founded definition translation"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "WF"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(24, 25, 43, 203, 194, 237, 195, 214)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(7, 7, 223, 43, 113, 218, 153, 204)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(253, 66, 61, 195, 239, 57, 103, 30)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value_aux_4),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(65, 40, 109, 48, 223, 99, 87, 96)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value_aux_5),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(255, 91, 253, 16, 215, 73, 25, 62)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_debug_definition_wf_replaceRecApps;
static const lean_array_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__0_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__1_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__3;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "unexpected empty local context"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Type not preserved transforming"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__1;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "\nto"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\nType was"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__5;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "\nand now is"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__7;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Type error introduced when transforming"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__30___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__30___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19___closed__0;
static const lean_closure_object l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19___closed__1 = (const lean_object*)&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19___closed__2 = (const lean_object*)&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19___closed__3 = (const lean_object*)&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19___closed__4 = (const lean_object*)&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19___closed__4_value;
static const lean_closure_object l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19___closed__5 = (const lean_object*)&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19___closed__5_value;
static const lean_closure_object l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19___closed__6 = (const lean_object*)&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Meta.Match.MatcherApp.Basic"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Meta.matchMatcherApp\?"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "expected constructor"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0;
static lean_once_cell_t l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__1;
static lean_once_cell_t l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__2;
static lean_once_cell_t l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__3;
static const lean_ctor_object l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__4 = (const lean_object*)&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__9_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__9_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(235, 76, 232, 241, 91, 21, 77, 227)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__2_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "replaceRecApp: eta-expanding"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "unexpected matcher application alternative"};
static const lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__0 = (const lean_object*)&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__0_value;
static lean_once_cell_t l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__1;
static const lean_string_object l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "\nat application"};
static const lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__2 = (const lean_object*)&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__2_value;
static lean_once_cell_t l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__9_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__9_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__2;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "type of functorial "};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__4;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " is"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__6;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "replaceRecApps:"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inl"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__1_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "PSum"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 224, 206, 173, 168, 27, 198, 53)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(14, 217, 178, 28, 107, 212, 157, 131)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__2_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inr"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 224, 206, 173, 168, 27, 198, 53)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__3_value),LEAN_SCALAR_PTR_LITERAL(201, 156, 94, 164, 220, 114, 107, 70)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__4_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "casesOn"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 224, 206, 173, 168, 27, 198, 53)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__5_value),LEAN_SCALAR_PTR_LITERAL(166, 115, 173, 38, 27, 113, 160, 8)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__2_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 76, .m_capacity = 76, .m_length = 75, .m_data = "_private.Lean.Elab.PreDefinition.WF.Fix.0.Lean.Elab.WF.processPSigmaCasesOn"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__1_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lean.Elab.PreDefinition.WF.Fix"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "PSigma"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 171, 149, 177, 120, 131, 37, 223)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(248, 249, 30, 71, 49, 108, 60, 175)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___boxed(lean_object**);
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 171, 149, 177, 120, 131, 37, 223)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__5_value),LEAN_SCALAR_PTR_LITERAL(225, 129, 3, 119, 45, 252, 168, 83)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "tacticDecreasing_tactic"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 100, 186, 108, 185, 30, 251, 120)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "decreasing_tactic"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_WF_assignSubsumed___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Elab_WF_assignSubsumed___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_WF_assignSubsumed___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_WF_assignSubsumed___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_WF_assignSubsumed___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_WF_assignSubsumed___closed__0 = (const lean_object*)&l_Lean_Elab_WF_assignSubsumed___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "MVar does not look like a recursive call:"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Cannot unpack param, unexpected expression:"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_groupGoalsByFunction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_groupGoalsByFunction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "MVar not annotated as a recursive call:"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__0_value;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_WF_isNatLtWF___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "invImage"};
static const lean_object* l_Lean_Elab_WF_isNatLtWF___closed__0 = (const lean_object*)&l_Lean_Elab_WF_isNatLtWF___closed__0_value;
static const lean_ctor_object l_Lean_Elab_WF_isNatLtWF___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_isNatLtWF___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 194, 127, 152, 147, 1, 182, 44)}};
static const lean_object* l_Lean_Elab_WF_isNatLtWF___closed__1 = (const lean_object*)&l_Lean_Elab_WF_isNatLtWF___closed__1_value;
static const lean_string_object l_Lean_Elab_WF_isNatLtWF___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Elab_WF_isNatLtWF___closed__2 = (const lean_object*)&l_Lean_Elab_WF_isNatLtWF___closed__2_value;
static const lean_ctor_object l_Lean_Elab_WF_isNatLtWF___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_isNatLtWF___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Elab_WF_isNatLtWF___closed__3 = (const lean_object*)&l_Lean_Elab_WF_isNatLtWF___closed__3_value;
static lean_once_cell_t l_Lean_Elab_WF_isNatLtWF___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_isNatLtWF___closed__4;
static const lean_string_object l_Lean_Elab_WF_isNatLtWF___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lt_wfRel"};
static const lean_object* l_Lean_Elab_WF_isNatLtWF___closed__5 = (const lean_object*)&l_Lean_Elab_WF_isNatLtWF___closed__5_value;
static const lean_ctor_object l_Lean_Elab_WF_isNatLtWF___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_isNatLtWF___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Elab_WF_isNatLtWF___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_WF_isNatLtWF___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_WF_isNatLtWF___closed__5_value),LEAN_SCALAR_PTR_LITERAL(154, 103, 103, 42, 122, 250, 41, 80)}};
static const lean_object* l_Lean_Elab_WF_isNatLtWF___closed__6 = (const lean_object*)&l_Lean_Elab_WF_isNatLtWF___closed__6_value;
static lean_once_cell_t l_Lean_Elab_WF_isNatLtWF___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_isNatLtWF___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isNatLtWF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isNatLtWF___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_WF_mkFix___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "WellFounded"};
static const lean_object* l_Lean_Elab_WF_mkFix___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_WF_mkFix___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_WF_mkFix___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fix"};
static const lean_object* l_Lean_Elab_WF_mkFix___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_WF_mkFix___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Elab_WF_mkFix___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_mkFix___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(153, 177, 70, 214, 156, 62, 227, 219)}};
static const lean_ctor_object l_Lean_Elab_WF_mkFix___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_WF_mkFix___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_WF_isNatLtWF___closed__2_value),LEAN_SCALAR_PTR_LITERAL(209, 126, 194, 128, 117, 36, 224, 78)}};
static const lean_ctor_object l_Lean_Elab_WF_mkFix___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_WF_mkFix___lam__0___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_WF_mkFix___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(196, 0, 160, 225, 119, 146, 123, 62)}};
static const lean_object* l_Lean_Elab_WF_mkFix___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_WF_mkFix___lam__0___closed__2_value;
static const lean_string_object l_Lean_Elab_WF_mkFix___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "WellFoundedRelation"};
static const lean_object* l_Lean_Elab_WF_mkFix___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_WF_mkFix___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Elab_WF_mkFix___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_mkFix___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(247, 146, 95, 132, 177, 137, 153, 47)}};
static const lean_object* l_Lean_Elab_WF_mkFix___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_WF_mkFix___lam__0___closed__4_value;
static const lean_string_object l_Lean_Elab_WF_mkFix___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "opaqueId"};
static const lean_object* l_Lean_Elab_WF_mkFix___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_WF_mkFix___lam__0___closed__5_value;
static const lean_ctor_object l_Lean_Elab_WF_mkFix___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_WF_mkFix___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_WF_mkFix___lam__0___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_WF_mkFix___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(194, 89, 34, 148, 92, 203, 118, 146)}};
static const lean_object* l_Lean_Elab_WF_mkFix___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_WF_mkFix___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_Elab_WF_mkFix___lam__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_mkFix___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(153, 177, 70, 214, 156, 62, 227, 219)}};
static const lean_ctor_object l_Lean_Elab_WF_mkFix___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_WF_mkFix___lam__0___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_WF_mkFix___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(172, 133, 211, 204, 28, 206, 53, 233)}};
static const lean_object* l_Lean_Elab_WF_mkFix___lam__0___closed__7 = (const lean_object*)&l_Lean_Elab_WF_mkFix___lam__0___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__3___boxed(lean_object**);
static const lean_ctor_object l_Lean_Elab_WF_mkFix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Elab_WF_mkFix___closed__0 = (const lean_object*)&l_Lean_Elab_WF_mkFix___closed__0_value;
static const lean_ctor_object l_Lean_Elab_WF_mkFix___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lean_Elab_WF_mkFix___closed__1 = (const lean_object*)&l_Lean_Elab_WF_mkFix___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_61_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4_));
v___x_62_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4_));
v___x_63_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4_));
v___x_64_ = l_Lean_Option_register___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__spec__0(v___x_61_, v___x_62_, v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4____boxed(lean_object* v_a_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4_();
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg(lean_object* v_decreasingProp_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_){
_start:
{
lean_object* v_ref_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v_ref_75_ = lean_ctor_get(v_a_72_, 5);
lean_inc(v_ref_75_);
v___x_76_ = l_Lean_mkRecAppWithSyntax(v_decreasingProp_69_, v_ref_75_);
v___x_77_ = lean_box(0);
v___x_78_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_76_, v___x_77_, v_a_70_, v_a_71_, v_a_72_, v_a_73_);
if (lean_obj_tag(v___x_78_) == 0)
{
lean_object* v_a_79_; lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; lean_object* v___x_83_; 
v_a_79_ = lean_ctor_get(v___x_78_, 0);
lean_inc(v_a_79_);
lean_dec_ref_known(v___x_78_, 1);
v___x_80_ = l_Lean_Expr_mvarId_x21(v_a_79_);
v___x_81_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg___closed__0));
v___x_82_ = 1;
v___x_83_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(v___x_80_, v___x_81_, v___x_82_, v_a_70_, v_a_71_, v_a_72_, v_a_73_);
if (lean_obj_tag(v___x_83_) == 0)
{
lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_90_; 
v_isSharedCheck_90_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_90_ == 0)
{
lean_object* v_unused_91_; 
v_unused_91_ = lean_ctor_get(v___x_83_, 0);
lean_dec(v_unused_91_);
v___x_85_ = v___x_83_;
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
else
{
lean_dec(v___x_83_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_88_; 
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 0, v_a_79_);
v___x_88_ = v___x_85_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_a_79_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
}
else
{
lean_object* v_a_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_99_; 
lean_dec(v_a_79_);
v_a_92_ = lean_ctor_get(v___x_83_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_99_ == 0)
{
v___x_94_ = v___x_83_;
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_a_92_);
lean_dec(v___x_83_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_97_; 
if (v_isShared_95_ == 0)
{
v___x_97_ = v___x_94_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_a_92_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
}
else
{
return v___x_78_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg___boxed(lean_object* v_decreasingProp_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg(v_decreasingProp_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_);
lean_dec(v_a_104_);
lean_dec_ref(v_a_103_);
lean_dec(v_a_102_);
lean_dec_ref(v_a_101_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof(lean_object* v_decreasingProp_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg(v_decreasingProp_107_, v_a_110_, v_a_111_, v_a_112_, v_a_113_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___boxed(lean_object* v_decreasingProp_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof(v_decreasingProp_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__0(lean_object* v_msg_125_){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = l_Lean_instInhabitedLocalDecl_default;
v___x_127_ = lean_panic_fn_borrowed(v___x_126_, v_msg_125_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(lean_object* v_msgData_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
lean_object* v___x_134_; lean_object* v_env_135_; lean_object* v___x_136_; lean_object* v_mctx_137_; lean_object* v_lctx_138_; lean_object* v_options_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_134_ = lean_st_ref_get(v___y_132_);
v_env_135_ = lean_ctor_get(v___x_134_, 0);
lean_inc_ref(v_env_135_);
lean_dec(v___x_134_);
v___x_136_ = lean_st_ref_get(v___y_130_);
v_mctx_137_ = lean_ctor_get(v___x_136_, 0);
lean_inc_ref(v_mctx_137_);
lean_dec(v___x_136_);
v_lctx_138_ = lean_ctor_get(v___y_129_, 2);
v_options_139_ = lean_ctor_get(v___y_131_, 2);
lean_inc_ref(v_options_139_);
lean_inc_ref(v_lctx_138_);
v___x_140_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_140_, 0, v_env_135_);
lean_ctor_set(v___x_140_, 1, v_mctx_137_);
lean_ctor_set(v___x_140_, 2, v_lctx_138_);
lean_ctor_set(v___x_140_, 3, v_options_139_);
v___x_141_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
lean_ctor_set(v___x_141_, 1, v_msgData_128_);
v___x_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1___boxed(lean_object* v_msgData_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msgData_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(lean_object* v_msg_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v_ref_156_; lean_object* v___x_157_; lean_object* v_a_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_166_; 
v_ref_156_ = lean_ctor_get(v___y_153_, 5);
v___x_157_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_);
v_a_158_ = lean_ctor_get(v___x_157_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_157_);
if (v_isSharedCheck_166_ == 0)
{
v___x_160_ = v___x_157_;
v_isShared_161_ = v_isSharedCheck_166_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_a_158_);
lean_dec(v___x_157_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_166_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_162_; lean_object* v___x_164_; 
lean_inc(v_ref_156_);
v___x_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_162_, 0, v_ref_156_);
lean_ctor_set(v___x_162_, 1, v_a_158_);
if (v_isShared_161_ == 0)
{
lean_ctor_set_tag(v___x_160_, 1);
lean_ctor_set(v___x_160_, 0, v___x_162_);
v___x_164_ = v___x_160_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg___boxed(lean_object* v_msg_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v_msg_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
return v_res_173_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__3(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_177_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__2));
v___x_178_ = lean_unsigned_to_nat(14u);
v___x_179_ = lean_unsigned_to_nat(22u);
v___x_180_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__1));
v___x_181_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__0));
v___x_182_ = l_mkPanicMessageWithDecl(v___x_181_, v___x_180_, v___x_179_, v___x_178_, v___x_177_);
return v___x_182_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__5(void){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__4));
v___x_185_ = l_Lean_stringToMessageData(v___x_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId(lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_){
_start:
{
lean_object* v___y_192_; lean_object* v___y_196_; lean_object* v_lctx_200_; lean_object* v___x_201_; uint8_t v___x_211_; 
v_lctx_200_ = lean_ctor_get(v_a_186_, 2);
v___x_201_ = lean_box(0);
lean_inc_ref(v_lctx_200_);
v___x_211_ = lean_local_ctx_is_empty(v_lctx_200_);
if (v___x_211_ == 0)
{
goto v___jp_202_;
}
else
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_221_; 
v___x_212_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__5);
v___x_213_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v___x_212_, v_a_186_, v_a_187_, v_a_188_, v_a_189_);
v_a_214_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_221_ == 0)
{
v___x_216_ = v___x_213_;
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_dec(v___x_213_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_219_; 
if (v_isShared_217_ == 0)
{
v___x_219_ = v___x_216_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_a_214_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
v___jp_191_:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = l_Lean_LocalDecl_fvarId(v___y_192_);
lean_dec_ref(v___y_192_);
v___x_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
return v___x_194_;
}
v___jp_195_:
{
if (lean_obj_tag(v___y_196_) == 0)
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__3);
v___x_198_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__0(v___x_197_);
v___y_192_ = v___x_198_;
goto v___jp_191_;
}
else
{
lean_object* v_val_199_; 
v_val_199_ = lean_ctor_get(v___y_196_, 0);
lean_inc(v_val_199_);
lean_dec_ref_known(v___y_196_, 1);
v___y_192_ = v_val_199_;
goto v___jp_191_;
}
}
v___jp_202_:
{
lean_object* v_decls_203_; lean_object* v_size_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v_decls_203_ = lean_ctor_get(v_lctx_200_, 1);
v_size_204_ = lean_ctor_get(v_decls_203_, 2);
v___x_205_ = l_Lean_LocalContext_size(v_lctx_200_);
v___x_206_ = lean_unsigned_to_nat(1u);
v___x_207_ = lean_nat_sub(v___x_205_, v___x_206_);
lean_dec(v___x_205_);
v___x_208_ = lean_nat_dec_lt(v___x_207_, v_size_204_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; 
lean_dec(v___x_207_);
v___x_209_ = l_outOfBounds___redArg(v___x_201_);
v___y_196_ = v___x_209_;
goto v___jp_195_;
}
else
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_PersistentArray_get_x21___redArg(v___x_201_, v_decls_203_, v___x_207_);
lean_dec(v___x_207_);
v___y_196_ = v___x_210_;
goto v___jp_195_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___boxed(lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId(v_a_222_, v_a_223_, v_a_224_, v_a_225_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_224_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1(lean_object* v_00_u03b1_228_, lean_object* v_msg_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v_msg_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___boxed(lean_object* v_00_u03b1_236_, lean_object* v_msg_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1(v_00_u03b1_236_, v_msg_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___redArg(lean_object* v_lctxid_244_, lean_object* v_a_245_){
_start:
{
lean_object* v_lctx_247_; uint8_t v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v_lctx_247_ = lean_ctor_get(v_a_245_, 2);
v___x_248_ = l_Lean_LocalContext_contains(v_lctx_247_, v_lctxid_244_);
v___x_249_ = lean_box(v___x_248_);
v___x_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___redArg___boxed(lean_object* v_lctxid_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___redArg(v_lctxid_251_, v_a_252_);
lean_dec_ref(v_a_252_);
lean_dec(v_lctxid_251_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid(lean_object* v_lctxid_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___redArg(v_lctxid_255_, v_a_256_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___boxed(lean_object* v_lctxid_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid(v_lctxid_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_);
lean_dec(v_a_266_);
lean_dec_ref(v_a_265_);
lean_dec(v_a_264_);
lean_dec_ref(v_a_263_);
lean_dec(v_lctxid_262_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___redArg(lean_object* v_recFnName_269_, lean_object* v_e_270_, lean_object* v_a_271_){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v_fst_278_; lean_object* v_snd_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_273_ = lean_st_ref_take(v_a_271_);
v___x_274_ = lean_unsigned_to_nat(1u);
v___x_275_ = lean_mk_empty_array_with_capacity(v___x_274_);
v___x_276_ = lean_array_push(v___x_275_, v_recFnName_269_);
v___x_277_ = l_Lean_HasConstCache_containsUnsafe(v___x_276_, v_e_270_, v___x_273_);
lean_dec_ref(v___x_276_);
v_fst_278_ = lean_ctor_get(v___x_277_, 0);
lean_inc(v_fst_278_);
v_snd_279_ = lean_ctor_get(v___x_277_, 1);
lean_inc(v_snd_279_);
lean_dec_ref(v___x_277_);
v___x_280_ = lean_st_ref_put(v_a_271_, v_snd_279_);
v___x_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_281_, 0, v_fst_278_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___redArg___boxed(lean_object* v_recFnName_282_, lean_object* v_e_283_, lean_object* v_a_284_, lean_object* v_a_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___redArg(v_recFnName_282_, v_e_283_, v_a_284_);
lean_dec(v_a_284_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn(lean_object* v_recFnName_287_, lean_object* v_e_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___redArg(v_recFnName_287_, v_e_288_, v_a_289_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___boxed(lean_object* v_recFnName_299_, lean_object* v_e_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn(v_recFnName_299_, v_e_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_);
lean_dec(v_a_308_);
lean_dec_ref(v_a_307_);
lean_dec(v_a_306_);
lean_dec_ref(v_a_305_);
lean_dec(v_a_304_);
lean_dec_ref(v_a_303_);
lean_dec(v_a_302_);
lean_dec(v_a_301_);
return v_res_310_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_311_; double v___x_312_; 
v___x_311_ = lean_unsigned_to_nat(0u);
v___x_312_ = lean_float_of_nat(v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(lean_object* v_cls_316_, lean_object* v_msg_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v_ref_323_; lean_object* v___x_324_; lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_369_; 
v_ref_323_ = lean_ctor_get(v___y_320_, 5);
v___x_324_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
v_a_325_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_369_ == 0)
{
v___x_327_ = v___x_324_;
v_isShared_328_ = v_isSharedCheck_369_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_324_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_369_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_329_; lean_object* v_traceState_330_; lean_object* v_env_331_; lean_object* v_nextMacroScope_332_; lean_object* v_ngen_333_; lean_object* v_auxDeclNGen_334_; lean_object* v_cache_335_; lean_object* v_messages_336_; lean_object* v_infoState_337_; lean_object* v_snapshotTasks_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_368_; 
v___x_329_ = lean_st_ref_take(v___y_321_);
v_traceState_330_ = lean_ctor_get(v___x_329_, 4);
v_env_331_ = lean_ctor_get(v___x_329_, 0);
v_nextMacroScope_332_ = lean_ctor_get(v___x_329_, 1);
v_ngen_333_ = lean_ctor_get(v___x_329_, 2);
v_auxDeclNGen_334_ = lean_ctor_get(v___x_329_, 3);
v_cache_335_ = lean_ctor_get(v___x_329_, 5);
v_messages_336_ = lean_ctor_get(v___x_329_, 6);
v_infoState_337_ = lean_ctor_get(v___x_329_, 7);
v_snapshotTasks_338_ = lean_ctor_get(v___x_329_, 8);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_368_ == 0)
{
v___x_340_ = v___x_329_;
v_isShared_341_ = v_isSharedCheck_368_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_snapshotTasks_338_);
lean_inc(v_infoState_337_);
lean_inc(v_messages_336_);
lean_inc(v_cache_335_);
lean_inc(v_traceState_330_);
lean_inc(v_auxDeclNGen_334_);
lean_inc(v_ngen_333_);
lean_inc(v_nextMacroScope_332_);
lean_inc(v_env_331_);
lean_dec(v___x_329_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_368_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
uint64_t v_tid_342_; lean_object* v_traces_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_367_; 
v_tid_342_ = lean_ctor_get_uint64(v_traceState_330_, sizeof(void*)*1);
v_traces_343_ = lean_ctor_get(v_traceState_330_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v_traceState_330_);
if (v_isSharedCheck_367_ == 0)
{
v___x_345_ = v_traceState_330_;
v_isShared_346_ = v_isSharedCheck_367_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_traces_343_);
lean_dec(v_traceState_330_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_367_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_347_; double v___x_348_; uint8_t v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_357_; 
v___x_347_ = lean_box(0);
v___x_348_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0);
v___x_349_ = 0;
v___x_350_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__1));
v___x_351_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_351_, 0, v_cls_316_);
lean_ctor_set(v___x_351_, 1, v___x_347_);
lean_ctor_set(v___x_351_, 2, v___x_350_);
lean_ctor_set_float(v___x_351_, sizeof(void*)*3, v___x_348_);
lean_ctor_set_float(v___x_351_, sizeof(void*)*3 + 8, v___x_348_);
lean_ctor_set_uint8(v___x_351_, sizeof(void*)*3 + 16, v___x_349_);
v___x_352_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__2));
v___x_353_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_353_, 0, v___x_351_);
lean_ctor_set(v___x_353_, 1, v_a_325_);
lean_ctor_set(v___x_353_, 2, v___x_352_);
lean_inc(v_ref_323_);
v___x_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_354_, 0, v_ref_323_);
lean_ctor_set(v___x_354_, 1, v___x_353_);
v___x_355_ = l_Lean_PersistentArray_push___redArg(v_traces_343_, v___x_354_);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 0, v___x_355_);
v___x_357_ = v___x_345_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_355_);
lean_ctor_set_uint64(v_reuseFailAlloc_366_, sizeof(void*)*1, v_tid_342_);
v___x_357_ = v_reuseFailAlloc_366_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
lean_object* v___x_359_; 
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 4, v___x_357_);
v___x_359_ = v___x_340_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_env_331_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_nextMacroScope_332_);
lean_ctor_set(v_reuseFailAlloc_365_, 2, v_ngen_333_);
lean_ctor_set(v_reuseFailAlloc_365_, 3, v_auxDeclNGen_334_);
lean_ctor_set(v_reuseFailAlloc_365_, 4, v___x_357_);
lean_ctor_set(v_reuseFailAlloc_365_, 5, v_cache_335_);
lean_ctor_set(v_reuseFailAlloc_365_, 6, v_messages_336_);
lean_ctor_set(v_reuseFailAlloc_365_, 7, v_infoState_337_);
lean_ctor_set(v_reuseFailAlloc_365_, 8, v_snapshotTasks_338_);
v___x_359_ = v_reuseFailAlloc_365_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_363_; 
v___x_360_ = lean_st_ref_put(v___y_321_, v___x_359_);
v___x_361_ = lean_box(0);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 0, v___x_361_);
v___x_363_ = v___x_327_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_361_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___boxed(lean_object* v_cls_370_, lean_object* v_msg_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(v_cls_370_, v_msg_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7_spec__7___redArg(lean_object* v_m_378_, lean_object* v_query_379_, lean_object* v_x_380_, lean_object* v_x_381_, lean_object* v_x_382_){
_start:
{
lean_object* v_zero_383_; uint8_t v_isZero_384_; 
v_zero_383_ = lean_unsigned_to_nat(0u);
v_isZero_384_ = lean_nat_dec_eq(v_x_381_, v_zero_383_);
if (v_isZero_384_ == 1)
{
lean_dec(v_x_382_);
lean_dec(v_x_381_);
if (lean_obj_tag(v_x_380_) == 0)
{
lean_object* v___x_385_; 
v___x_385_ = lean_box(2);
return v___x_385_;
}
else
{
lean_object* v_val_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
v_val_386_ = lean_ctor_get(v_x_380_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v_x_380_);
if (v_isSharedCheck_393_ == 0)
{
v___x_388_ = v_x_380_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_val_386_);
lean_dec(v_x_380_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_val_386_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
else
{
lean_object* v_keyArray_394_; lean_object* v_valueArray_395_; lean_object* v___x_396_; uint8_t v_isSome_397_; 
v_keyArray_394_ = lean_ctor_get(v_m_378_, 1);
v_valueArray_395_ = lean_ctor_get(v_m_378_, 2);
v___x_396_ = lean_array_fget_borrowed(v_keyArray_394_, v_x_382_);
v_isSome_397_ = lean_noption_is_some(v___x_396_);
if (v_isSome_397_ == 0)
{
lean_dec(v_x_381_);
if (lean_obj_tag(v_x_380_) == 0)
{
lean_object* v___x_398_; 
v___x_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_398_, 0, v_x_382_);
return v___x_398_;
}
else
{
lean_object* v_val_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
lean_dec(v_x_382_);
v_val_399_ = lean_ctor_get(v_x_380_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v_x_380_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v_x_380_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_val_399_);
lean_dec(v_x_380_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_val_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
else
{
lean_object* v_one_407_; lean_object* v_n_408_; lean_object* v___y_410_; 
v_one_407_ = lean_unsigned_to_nat(1u);
v_n_408_ = lean_nat_sub(v_x_381_, v_one_407_);
lean_dec(v_x_381_);
if (v_isSome_397_ == 0)
{
goto v___jp_416_;
}
else
{
lean_object* v___x_418_; uint8_t v_isSome_419_; 
v___x_418_ = lean_array_fget_borrowed(v_valueArray_395_, v_x_382_);
v_isSome_419_ = lean_noption_is_some(v___x_418_);
if (v_isSome_419_ == 0)
{
goto v___jp_416_;
}
else
{
lean_object* v_val_420_; uint8_t v___x_421_; 
lean_inc(v___x_396_);
v_val_420_ = lean_noption_get(v___x_396_);
v___x_421_ = lean_expr_eqv(v_val_420_, v_query_379_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; 
lean_dec(v_val_420_);
v___x_422_ = lean_array_get_size(v_keyArray_394_);
v___x_423_ = lean_nat_add(v_x_382_, v_one_407_);
lean_dec(v_x_382_);
v___x_424_ = lean_nat_dec_lt(v___x_423_, v___x_422_);
if (v___x_424_ == 0)
{
lean_dec(v___x_423_);
v_x_381_ = v_n_408_;
v_x_382_ = v_zero_383_;
goto _start;
}
else
{
v_x_381_ = v_n_408_;
v_x_382_ = v___x_423_;
goto _start;
}
}
else
{
lean_object* v_val_427_; lean_object* v___x_428_; 
lean_dec(v_n_408_);
lean_dec(v_x_380_);
lean_inc(v___x_418_);
v_val_427_ = lean_noption_get(v___x_418_);
v___x_428_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_428_, 0, v_x_382_);
lean_ctor_set(v___x_428_, 1, v_val_420_);
lean_ctor_set(v___x_428_, 2, v_val_427_);
return v___x_428_;
}
}
}
v___jp_409_:
{
lean_object* v___x_411_; lean_object* v___x_412_; uint8_t v___x_413_; 
v___x_411_ = lean_array_get_size(v_keyArray_394_);
v___x_412_ = lean_nat_add(v_x_382_, v_one_407_);
lean_dec(v_x_382_);
v___x_413_ = lean_nat_dec_lt(v___x_412_, v___x_411_);
if (v___x_413_ == 0)
{
lean_dec(v___x_412_);
v_x_380_ = v___y_410_;
v_x_381_ = v_n_408_;
v_x_382_ = v_zero_383_;
goto _start;
}
else
{
v_x_380_ = v___y_410_;
v_x_381_ = v_n_408_;
v_x_382_ = v___x_412_;
goto _start;
}
}
v___jp_416_:
{
if (lean_obj_tag(v_x_380_) == 0)
{
lean_object* v___x_417_; 
lean_inc(v_x_382_);
v___x_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_417_, 0, v_x_382_);
v___y_410_ = v___x_417_;
goto v___jp_409_;
}
else
{
v___y_410_ = v_x_380_;
goto v___jp_409_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7_spec__7___redArg___boxed(lean_object* v_m_429_, lean_object* v_query_430_, lean_object* v_x_431_, lean_object* v_x_432_, lean_object* v_x_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7_spec__7___redArg(v_m_429_, v_query_430_, v_x_431_, v_x_432_, v_x_433_);
lean_dec_ref(v_query_430_);
lean_dec_ref(v_m_429_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(lean_object* v_m_435_, lean_object* v_query_436_){
_start:
{
lean_object* v_keyArray_437_; lean_object* v___x_438_; uint64_t v___x_439_; uint64_t v___x_440_; uint64_t v___x_441_; uint64_t v_fold_442_; uint64_t v___x_443_; uint64_t v___x_444_; uint64_t v___x_445_; size_t v___x_446_; size_t v___x_447_; size_t v___x_448_; size_t v___x_449_; size_t v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v_keyArray_437_ = lean_ctor_get(v_m_435_, 1);
v___x_438_ = lean_array_get_size(v_keyArray_437_);
v___x_439_ = l_Lean_Expr_hash(v_query_436_);
v___x_440_ = 32ULL;
v___x_441_ = lean_uint64_shift_right(v___x_439_, v___x_440_);
v_fold_442_ = lean_uint64_xor(v___x_439_, v___x_441_);
v___x_443_ = 16ULL;
v___x_444_ = lean_uint64_shift_right(v_fold_442_, v___x_443_);
v___x_445_ = lean_uint64_xor(v_fold_442_, v___x_444_);
v___x_446_ = lean_uint64_to_usize(v___x_445_);
v___x_447_ = lean_usize_of_nat(v___x_438_);
v___x_448_ = ((size_t)1ULL);
v___x_449_ = lean_usize_sub(v___x_447_, v___x_448_);
v___x_450_ = lean_usize_land(v___x_446_, v___x_449_);
v___x_451_ = lean_usize_to_nat(v___x_450_);
v___x_452_ = lean_box(0);
v___x_453_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7_spec__7___redArg(v_m_435_, v_query_436_, v___x_452_, v___x_438_, v___x_451_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___boxed(lean_object* v_m_454_, lean_object* v_query_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v_m_454_, v_query_455_);
lean_dec_ref(v_query_455_);
lean_dec_ref(v_m_454_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9_spec__11___redArg(lean_object* v_m_457_, lean_object* v_query_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v_m_457_, v_query_458_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v_index_460_; lean_object* v_key_461_; lean_object* v_value_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_469_; 
v_index_460_ = lean_ctor_get(v___x_459_, 0);
v_key_461_ = lean_ctor_get(v___x_459_, 1);
v_value_462_ = lean_ctor_get(v___x_459_, 2);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_469_ == 0)
{
v___x_464_ = v___x_459_;
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_value_462_);
lean_inc(v_key_461_);
lean_inc(v_index_460_);
lean_dec(v___x_459_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_index_460_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_key_461_);
lean_ctor_set(v_reuseFailAlloc_468_, 2, v_value_462_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
else
{
lean_object* v___x_470_; 
lean_dec(v___x_459_);
v___x_470_ = lean_box(1);
return v___x_470_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9_spec__11___redArg___boxed(lean_object* v_m_471_, lean_object* v_query_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9_spec__11___redArg(v_m_471_, v_query_472_);
lean_dec_ref(v_query_472_);
lean_dec_ref(v_m_471_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9___redArg(lean_object* v_m_474_, lean_object* v_a_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9_spec__11___redArg(v_m_474_, v_a_475_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v_value_477_; lean_object* v___x_478_; 
v_value_477_ = lean_ctor_get(v___x_476_, 2);
lean_inc(v_value_477_);
lean_dec_ref_known(v___x_476_, 3);
v___x_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_478_, 0, v_value_477_);
return v___x_478_;
}
else
{
lean_object* v___x_479_; 
v___x_479_ = lean_box(0);
return v___x_479_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9___redArg___boxed(lean_object* v_m_480_, lean_object* v_a_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9___redArg(v_m_480_, v_a_481_);
lean_dec_ref(v_a_481_);
lean_dec_ref(v_m_480_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5___redArg(lean_object* v_msg_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v_ref_489_; lean_object* v___x_490_; lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_499_; 
v_ref_489_ = lean_ctor_get(v___y_486_, 5);
v___x_490_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
v_a_491_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_499_ == 0)
{
v___x_493_ = v___x_490_;
v_isShared_494_ = v_isSharedCheck_499_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_490_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_499_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; lean_object* v___x_497_; 
lean_inc(v_ref_489_);
v___x_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_495_, 0, v_ref_489_);
lean_ctor_set(v___x_495_, 1, v_a_491_);
if (v_isShared_494_ == 0)
{
lean_ctor_set_tag(v___x_493_, 1);
lean_ctor_set(v___x_493_, 0, v___x_495_);
v___x_497_ = v___x_493_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_495_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5___redArg___boxed(lean_object* v_msg_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5___redArg(v_msg_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
return v_res_506_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__1(void){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__0));
v___x_509_ = l_Lean_stringToMessageData(v___x_508_);
return v___x_509_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3(void){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__2));
v___x_512_ = l_Lean_stringToMessageData(v___x_511_);
return v___x_512_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__5(void){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__4));
v___x_515_ = l_Lean_stringToMessageData(v___x_514_);
return v___x_515_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__7(void){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__6));
v___x_518_ = l_Lean_stringToMessageData(v___x_517_);
return v___x_518_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__9(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__8));
v___x_521_ = l_Lean_stringToMessageData(v___x_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0(lean_object* v_a_522_, lean_object* v_e_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v___x_615_; 
lean_inc_ref(v_a_522_);
v___x_615_ = l_Lean_Meta_isTypeCorrect(v_a_522_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; uint8_t v___x_617_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_a_616_);
lean_dec_ref_known(v___x_615_, 1);
v___x_617_ = lean_unbox(v_a_616_);
lean_dec(v_a_616_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_618_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__9, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__9);
lean_inc_ref(v_e_523_);
v___x_619_ = l_Lean_indentExpr(v_e_523_);
v___x_620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_618_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3);
v___x_622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_620_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
lean_inc_ref(v_a_522_);
v___x_623_ = l_Lean_indentExpr(v_a_522_);
v___x_624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_622_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
v___x_625_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5___redArg(v___x_624_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_dec_ref_known(v___x_625_, 1);
v___y_534_ = v___y_524_;
v___y_535_ = v___y_525_;
v___y_536_ = v___y_526_;
v___y_537_ = v___y_527_;
v___y_538_ = v___y_528_;
v___y_539_ = v___y_529_;
v___y_540_ = v___y_530_;
v___y_541_ = v___y_531_;
goto v___jp_533_;
}
else
{
lean_dec_ref(v_e_523_);
lean_dec_ref(v_a_522_);
return v___x_625_;
}
}
else
{
v___y_534_ = v___y_524_;
v___y_535_ = v___y_525_;
v___y_536_ = v___y_526_;
v___y_537_ = v___y_527_;
v___y_538_ = v___y_528_;
v___y_539_ = v___y_529_;
v___y_540_ = v___y_530_;
v___y_541_ = v___y_531_;
goto v___jp_533_;
}
}
else
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
lean_dec_ref(v_e_523_);
lean_dec_ref(v_a_522_);
v_a_626_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_633_ == 0)
{
v___x_628_ = v___x_615_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_615_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_a_626_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
v___jp_533_:
{
lean_object* v___x_542_; 
lean_inc(v___y_541_);
lean_inc_ref(v___y_540_);
lean_inc(v___y_539_);
lean_inc_ref(v___y_538_);
lean_inc_ref(v_e_523_);
v___x_542_ = lean_infer_type(v_e_523_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v_a_543_; lean_object* v___x_544_; 
v_a_543_ = lean_ctor_get(v___x_542_, 0);
lean_inc(v_a_543_);
lean_dec_ref_known(v___x_542_, 1);
lean_inc(v___y_541_);
lean_inc_ref(v___y_540_);
lean_inc(v___y_539_);
lean_inc_ref(v___y_538_);
lean_inc_ref(v_a_522_);
v___x_544_ = lean_infer_type(v_a_522_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; lean_object* v___x_546_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc_n(v_a_545_, 2);
lean_dec_ref_known(v___x_544_, 1);
lean_inc(v_a_543_);
v___x_546_ = l_Lean_Meta_isExprDefEq(v_a_543_, v_a_545_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_590_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_590_ == 0)
{
v___x_549_ = v___x_546_;
v_isShared_550_ = v_isSharedCheck_590_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_546_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_590_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
uint8_t v___x_551_; 
v___x_551_ = lean_unbox(v_a_547_);
lean_dec(v_a_547_);
if (v___x_551_ == 0)
{
lean_object* v___x_552_; 
lean_del_object(v___x_549_);
v___x_552_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_a_543_, v_a_545_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; lean_object* v_fst_554_; lean_object* v_snd_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_577_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_a_553_);
lean_dec_ref_known(v___x_552_, 1);
v_fst_554_ = lean_ctor_get(v_a_553_, 0);
v_snd_555_ = lean_ctor_get(v_a_553_, 1);
v_isSharedCheck_577_ = !lean_is_exclusive(v_a_553_);
if (v_isSharedCheck_577_ == 0)
{
v___x_557_ = v_a_553_;
v_isShared_558_ = v_isSharedCheck_577_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_snd_555_);
lean_inc(v_fst_554_);
lean_dec(v_a_553_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_577_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_562_; 
v___x_559_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__1);
v___x_560_ = l_Lean_indentExpr(v_e_523_);
if (v_isShared_558_ == 0)
{
lean_ctor_set_tag(v___x_557_, 7);
lean_ctor_set(v___x_557_, 1, v___x_560_);
lean_ctor_set(v___x_557_, 0, v___x_559_);
v___x_562_ = v___x_557_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_559_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v___x_560_);
v___x_562_ = v_reuseFailAlloc_576_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_563_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3);
v___x_564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_562_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
v___x_565_ = l_Lean_indentExpr(v_a_522_);
v___x_566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_566_, 0, v___x_564_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
v___x_567_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__5);
v___x_568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_566_);
lean_ctor_set(v___x_568_, 1, v___x_567_);
v___x_569_ = l_Lean_indentExpr(v_fst_554_);
v___x_570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_568_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
v___x_571_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__7, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__7);
v___x_572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_570_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
v___x_573_ = l_Lean_indentExpr(v_snd_555_);
v___x_574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_572_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
v___x_575_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5___redArg(v___x_574_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
return v___x_575_;
}
}
}
else
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_585_; 
lean_dec_ref(v_e_523_);
lean_dec_ref(v_a_522_);
v_a_578_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_585_ == 0)
{
v___x_580_ = v___x_552_;
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_552_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_578_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
else
{
lean_object* v___x_586_; lean_object* v___x_588_; 
lean_dec(v_a_545_);
lean_dec(v_a_543_);
lean_dec_ref(v_e_523_);
lean_dec_ref(v_a_522_);
v___x_586_ = lean_box(0);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 0, v___x_586_);
v___x_588_ = v___x_549_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
else
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_598_; 
lean_dec(v_a_545_);
lean_dec(v_a_543_);
lean_dec_ref(v_e_523_);
lean_dec_ref(v_a_522_);
v_a_591_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_598_ == 0)
{
v___x_593_ = v___x_546_;
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_546_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_594_ == 0)
{
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_591_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
else
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_606_; 
lean_dec(v_a_543_);
lean_dec_ref(v_e_523_);
lean_dec_ref(v_a_522_);
v_a_599_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_606_ == 0)
{
v___x_601_ = v___x_544_;
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_544_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_a_599_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
else
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
lean_dec_ref(v_e_523_);
lean_dec_ref(v_a_522_);
v_a_607_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_614_ == 0)
{
v___x_609_ = v___x_542_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_542_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_a_607_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___boxed(lean_object* v_a_634_, lean_object* v_e_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0(v_a_634_, v_e_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
lean_dec(v___y_636_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___redArg___lam__0(lean_object* v_k_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v_b_651_, lean_object* v_c_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v___x_658_; 
lean_inc(v___y_656_);
lean_inc_ref(v___y_655_);
lean_inc(v___y_654_);
lean_inc_ref(v___y_653_);
lean_inc(v___y_650_);
lean_inc_ref(v___y_649_);
lean_inc(v___y_648_);
lean_inc(v___y_647_);
v___x_658_ = lean_apply_11(v_k_646_, v_b_651_, v_c_652_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, lean_box(0));
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___redArg___lam__0___boxed(lean_object* v_k_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v_b_664_, lean_object* v_c_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___redArg___lam__0(v_k_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v_b_664_, v_c_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec(v___y_660_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___redArg(lean_object* v_e_672_, lean_object* v_maxFVars_673_, lean_object* v_k_674_, uint8_t v_cleanupAnnotations_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v___f_685_; uint8_t v___x_686_; uint8_t v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
lean_inc(v___y_679_);
lean_inc_ref(v___y_678_);
lean_inc(v___y_677_);
lean_inc(v___y_676_);
v___f_685_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___redArg___lam__0___boxed), 12, 5);
lean_closure_set(v___f_685_, 0, v_k_674_);
lean_closure_set(v___f_685_, 1, v___y_676_);
lean_closure_set(v___f_685_, 2, v___y_677_);
lean_closure_set(v___f_685_, 3, v___y_678_);
lean_closure_set(v___f_685_, 4, v___y_679_);
v___x_686_ = 1;
v___x_687_ = 0;
v___x_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_688_, 0, v_maxFVars_673_);
v___x_689_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_672_, v___x_686_, v___x_687_, v___x_686_, v___x_687_, v___x_688_, v___f_685_, v_cleanupAnnotations_675_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
lean_dec_ref_known(v___x_688_, 1);
if (lean_obj_tag(v___x_689_) == 0)
{
return v___x_689_;
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_689_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_689_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___redArg___boxed(lean_object* v_e_698_, lean_object* v_maxFVars_699_, lean_object* v_k_700_, lean_object* v_cleanupAnnotations_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_711_; lean_object* v_res_712_; 
v_cleanupAnnotations_boxed_711_ = lean_unbox(v_cleanupAnnotations_701_);
v_res_712_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___redArg(v_e_698_, v_maxFVars_699_, v_k_700_, v_cleanupAnnotations_boxed_711_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec(v___y_702_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___redArg___lam__0(lean_object* v_k_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v_b_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v___x_724_; 
lean_inc(v___y_722_);
lean_inc_ref(v___y_721_);
lean_inc(v___y_720_);
lean_inc_ref(v___y_719_);
lean_inc(v___y_717_);
lean_inc_ref(v___y_716_);
lean_inc(v___y_715_);
lean_inc(v___y_714_);
v___x_724_ = lean_apply_10(v_k_713_, v_b_718_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, lean_box(0));
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___redArg___lam__0___boxed(lean_object* v_k_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v_b_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___redArg___lam__0(v_k_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v_b_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v___y_727_);
lean_dec(v___y_726_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___redArg(lean_object* v_name_737_, uint8_t v_bi_738_, lean_object* v_type_739_, lean_object* v_k_740_, uint8_t v_kind_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v___f_751_; lean_object* v___x_752_; 
lean_inc(v___y_745_);
lean_inc_ref(v___y_744_);
lean_inc(v___y_743_);
lean_inc(v___y_742_);
v___f_751_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_751_, 0, v_k_740_);
lean_closure_set(v___f_751_, 1, v___y_742_);
lean_closure_set(v___f_751_, 2, v___y_743_);
lean_closure_set(v___f_751_, 3, v___y_744_);
lean_closure_set(v___f_751_, 4, v___y_745_);
v___x_752_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_737_, v_bi_738_, v_type_739_, v___f_751_, v_kind_741_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
if (lean_obj_tag(v___x_752_) == 0)
{
return v___x_752_;
}
else
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
v_a_753_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_760_ == 0)
{
v___x_755_ = v___x_752_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_752_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_753_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___redArg___boxed(lean_object* v_name_761_, lean_object* v_bi_762_, lean_object* v_type_763_, lean_object* v_k_764_, lean_object* v_kind_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
uint8_t v_bi_boxed_775_; uint8_t v_kind_boxed_776_; lean_object* v_res_777_; 
v_bi_boxed_775_ = lean_unbox(v_bi_762_);
v_kind_boxed_776_ = lean_unbox(v_kind_765_);
v_res_777_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___redArg(v_name_761_, v_bi_boxed_775_, v_type_763_, v_k_764_, v_kind_boxed_776_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec(v___y_766_);
return v_res_777_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__0(void){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_778_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__1(void){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__0);
v___x_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
return v___x_780_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__2(void){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_781_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__1);
v___x_782_ = lean_unsigned_to_nat(0u);
v___x_783_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
lean_ctor_set(v___x_783_, 2, v___x_782_);
lean_ctor_set(v___x_783_, 3, v___x_782_);
lean_ctor_set(v___x_783_, 4, v___x_781_);
lean_ctor_set(v___x_783_, 5, v___x_781_);
lean_ctor_set(v___x_783_, 6, v___x_781_);
lean_ctor_set(v___x_783_, 7, v___x_781_);
lean_ctor_set(v___x_783_, 8, v___x_781_);
lean_ctor_set(v___x_783_, 9, v___x_781_);
lean_ctor_set(v___x_783_, 10, v___x_781_);
return v___x_783_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__3(void){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_784_ = lean_unsigned_to_nat(32u);
v___x_785_ = lean_mk_empty_array_with_capacity(v___x_784_);
v___x_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
return v___x_786_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__4(void){
_start:
{
size_t v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_787_ = ((size_t)5ULL);
v___x_788_ = lean_unsigned_to_nat(0u);
v___x_789_ = lean_unsigned_to_nat(32u);
v___x_790_ = lean_mk_empty_array_with_capacity(v___x_789_);
v___x_791_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__3);
v___x_792_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_792_, 0, v___x_791_);
lean_ctor_set(v___x_792_, 1, v___x_790_);
lean_ctor_set(v___x_792_, 2, v___x_788_);
lean_ctor_set(v___x_792_, 3, v___x_788_);
lean_ctor_set_usize(v___x_792_, 4, v___x_787_);
return v___x_792_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__5(void){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_793_ = lean_box(1);
v___x_794_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__4);
v___x_795_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__1);
v___x_796_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_796_, 0, v___x_795_);
lean_ctor_set(v___x_796_, 1, v___x_794_);
lean_ctor_set(v___x_796_, 2, v___x_793_);
return v___x_796_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__7(void){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__6));
v___x_799_ = l_Lean_stringToMessageData(v___x_798_);
return v___x_799_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__9(void){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__8));
v___x_802_ = l_Lean_stringToMessageData(v___x_801_);
return v___x_802_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__11(void){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__10));
v___x_805_ = l_Lean_stringToMessageData(v___x_804_);
return v___x_805_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__13(void){
_start:
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__12));
v___x_808_ = l_Lean_stringToMessageData(v___x_807_);
return v___x_808_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__15(void){
_start:
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__14));
v___x_811_ = l_Lean_stringToMessageData(v___x_810_);
return v___x_811_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__17(void){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__16));
v___x_814_ = l_Lean_stringToMessageData(v___x_813_);
return v___x_814_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__19(void){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_816_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__18));
v___x_817_ = l_Lean_stringToMessageData(v___x_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg(lean_object* v_msg_818_, lean_object* v_declHint_819_, lean_object* v___y_820_){
_start:
{
lean_object* v___x_822_; lean_object* v_env_823_; uint8_t v___x_824_; 
v___x_822_ = lean_st_ref_get(v___y_820_);
v_env_823_ = lean_ctor_get(v___x_822_, 0);
lean_inc_ref(v_env_823_);
lean_dec(v___x_822_);
v___x_824_ = l_Lean_Name_isAnonymous(v_declHint_819_);
if (v___x_824_ == 0)
{
uint8_t v_isExporting_825_; 
v_isExporting_825_ = lean_ctor_get_uint8(v_env_823_, sizeof(void*)*8);
if (v_isExporting_825_ == 0)
{
lean_object* v___x_826_; 
lean_dec_ref(v_env_823_);
lean_dec(v_declHint_819_);
v___x_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_826_, 0, v_msg_818_);
return v___x_826_;
}
else
{
lean_object* v___x_827_; uint8_t v___x_828_; 
lean_inc_ref(v_env_823_);
v___x_827_ = l_Lean_Environment_setExporting(v_env_823_, v___x_824_);
lean_inc(v_declHint_819_);
lean_inc_ref(v___x_827_);
v___x_828_ = l_Lean_Environment_contains(v___x_827_, v_declHint_819_, v_isExporting_825_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; 
lean_dec_ref(v___x_827_);
lean_dec_ref(v_env_823_);
lean_dec(v_declHint_819_);
v___x_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_829_, 0, v_msg_818_);
return v___x_829_;
}
else
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v_c_835_; lean_object* v___x_836_; 
v___x_830_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__2);
v___x_831_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__5);
v___x_832_ = l_Lean_Options_empty;
v___x_833_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_833_, 0, v___x_827_);
lean_ctor_set(v___x_833_, 1, v___x_830_);
lean_ctor_set(v___x_833_, 2, v___x_831_);
lean_ctor_set(v___x_833_, 3, v___x_832_);
lean_inc(v_declHint_819_);
v___x_834_ = l_Lean_MessageData_ofConstName(v_declHint_819_, v___x_824_);
v_c_835_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_835_, 0, v___x_833_);
lean_ctor_set(v_c_835_, 1, v___x_834_);
v___x_836_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_823_, v_declHint_819_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
lean_dec_ref(v_env_823_);
lean_dec(v_declHint_819_);
v___x_837_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__7);
v___x_838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
lean_ctor_set(v___x_838_, 1, v_c_835_);
v___x_839_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__9);
v___x_840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_838_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
v___x_841_ = l_Lean_MessageData_note(v___x_840_);
v___x_842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_842_, 0, v_msg_818_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
v___x_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_843_, 0, v___x_842_);
return v___x_843_;
}
else
{
lean_object* v_val_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_879_; 
v_val_844_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_879_ == 0)
{
v___x_846_ = v___x_836_;
v_isShared_847_ = v_isSharedCheck_879_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_val_844_);
lean_dec(v___x_836_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_879_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v_mod_851_; uint8_t v___x_852_; 
v___x_848_ = lean_box(0);
v___x_849_ = l_Lean_Environment_header(v_env_823_);
lean_dec_ref(v_env_823_);
v___x_850_ = l_Lean_EnvironmentHeader_moduleNames(v___x_849_);
v_mod_851_ = lean_array_get(v___x_848_, v___x_850_, v_val_844_);
lean_dec(v_val_844_);
lean_dec_ref(v___x_850_);
v___x_852_ = l_Lean_isPrivateName(v_declHint_819_);
lean_dec(v_declHint_819_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_864_; 
v___x_853_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__11);
v___x_854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
lean_ctor_set(v___x_854_, 1, v_c_835_);
v___x_855_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__13);
v___x_856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_854_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
v___x_857_ = l_Lean_MessageData_ofName(v_mod_851_);
v___x_858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_856_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
v___x_859_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__15);
v___x_860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_858_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
v___x_861_ = l_Lean_MessageData_note(v___x_860_);
v___x_862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_862_, 0, v_msg_818_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
if (v_isShared_847_ == 0)
{
lean_ctor_set_tag(v___x_846_, 0);
lean_ctor_set(v___x_846_, 0, v___x_862_);
v___x_864_ = v___x_846_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_862_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
else
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_877_; 
v___x_866_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__7);
v___x_867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
lean_ctor_set(v___x_867_, 1, v_c_835_);
v___x_868_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__17);
v___x_869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_867_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
v___x_870_ = l_Lean_MessageData_ofName(v_mod_851_);
v___x_871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_869_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
v___x_872_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___closed__19);
v___x_873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_871_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v___x_874_ = l_Lean_MessageData_note(v___x_873_);
v___x_875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_875_, 0, v_msg_818_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
if (v_isShared_847_ == 0)
{
lean_ctor_set_tag(v___x_846_, 0);
lean_ctor_set(v___x_846_, 0, v___x_875_);
v___x_877_ = v___x_846_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_880_; 
lean_dec_ref(v_env_823_);
lean_dec(v_declHint_819_);
v___x_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_880_, 0, v_msg_818_);
return v___x_880_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg___boxed(lean_object* v_msg_881_, lean_object* v_declHint_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg(v_msg_881_, v_declHint_882_, v___y_883_);
lean_dec(v___y_883_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29(lean_object* v_msg_886_, lean_object* v_declHint_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
lean_object* v___x_897_; lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_907_; 
v___x_897_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg(v_msg_886_, v_declHint_887_, v___y_895_);
v_a_898_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_907_ == 0)
{
v___x_900_ = v___x_897_;
v_isShared_901_ = v_isSharedCheck_907_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_897_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_907_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_905_; 
v___x_902_ = l_Lean_unknownIdentifierMessageTag;
v___x_903_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_902_);
lean_ctor_set(v___x_903_, 1, v_a_898_);
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 0, v___x_903_);
v___x_905_ = v___x_900_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_903_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29___boxed(lean_object* v_msg_908_, lean_object* v_declHint_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29(v_msg_908_, v_declHint_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v___y_911_);
lean_dec(v___y_910_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__30___redArg(lean_object* v_ref_920_, lean_object* v_msg_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v_fileName_931_; lean_object* v_fileMap_932_; lean_object* v_options_933_; lean_object* v_currRecDepth_934_; lean_object* v_maxRecDepth_935_; lean_object* v_ref_936_; lean_object* v_currNamespace_937_; lean_object* v_openDecls_938_; lean_object* v_initHeartbeats_939_; lean_object* v_maxHeartbeats_940_; lean_object* v_quotContext_941_; lean_object* v_currMacroScope_942_; uint8_t v_diag_943_; lean_object* v_cancelTk_x3f_944_; uint8_t v_suppressElabErrors_945_; lean_object* v_inheritedTraceOptions_946_; lean_object* v_ref_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v_fileName_931_ = lean_ctor_get(v___y_928_, 0);
v_fileMap_932_ = lean_ctor_get(v___y_928_, 1);
v_options_933_ = lean_ctor_get(v___y_928_, 2);
v_currRecDepth_934_ = lean_ctor_get(v___y_928_, 3);
v_maxRecDepth_935_ = lean_ctor_get(v___y_928_, 4);
v_ref_936_ = lean_ctor_get(v___y_928_, 5);
v_currNamespace_937_ = lean_ctor_get(v___y_928_, 6);
v_openDecls_938_ = lean_ctor_get(v___y_928_, 7);
v_initHeartbeats_939_ = lean_ctor_get(v___y_928_, 8);
v_maxHeartbeats_940_ = lean_ctor_get(v___y_928_, 9);
v_quotContext_941_ = lean_ctor_get(v___y_928_, 10);
v_currMacroScope_942_ = lean_ctor_get(v___y_928_, 11);
v_diag_943_ = lean_ctor_get_uint8(v___y_928_, sizeof(void*)*14);
v_cancelTk_x3f_944_ = lean_ctor_get(v___y_928_, 12);
v_suppressElabErrors_945_ = lean_ctor_get_uint8(v___y_928_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_946_ = lean_ctor_get(v___y_928_, 13);
v_ref_947_ = l_Lean_replaceRef(v_ref_920_, v_ref_936_);
lean_inc_ref(v_inheritedTraceOptions_946_);
lean_inc(v_cancelTk_x3f_944_);
lean_inc(v_currMacroScope_942_);
lean_inc(v_quotContext_941_);
lean_inc(v_maxHeartbeats_940_);
lean_inc(v_initHeartbeats_939_);
lean_inc(v_openDecls_938_);
lean_inc(v_currNamespace_937_);
lean_inc(v_maxRecDepth_935_);
lean_inc(v_currRecDepth_934_);
lean_inc_ref(v_options_933_);
lean_inc_ref(v_fileMap_932_);
lean_inc_ref(v_fileName_931_);
v___x_948_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_948_, 0, v_fileName_931_);
lean_ctor_set(v___x_948_, 1, v_fileMap_932_);
lean_ctor_set(v___x_948_, 2, v_options_933_);
lean_ctor_set(v___x_948_, 3, v_currRecDepth_934_);
lean_ctor_set(v___x_948_, 4, v_maxRecDepth_935_);
lean_ctor_set(v___x_948_, 5, v_ref_947_);
lean_ctor_set(v___x_948_, 6, v_currNamespace_937_);
lean_ctor_set(v___x_948_, 7, v_openDecls_938_);
lean_ctor_set(v___x_948_, 8, v_initHeartbeats_939_);
lean_ctor_set(v___x_948_, 9, v_maxHeartbeats_940_);
lean_ctor_set(v___x_948_, 10, v_quotContext_941_);
lean_ctor_set(v___x_948_, 11, v_currMacroScope_942_);
lean_ctor_set(v___x_948_, 12, v_cancelTk_x3f_944_);
lean_ctor_set(v___x_948_, 13, v_inheritedTraceOptions_946_);
lean_ctor_set_uint8(v___x_948_, sizeof(void*)*14, v_diag_943_);
lean_ctor_set_uint8(v___x_948_, sizeof(void*)*14 + 1, v_suppressElabErrors_945_);
v___x_949_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5___redArg(v_msg_921_, v___y_926_, v___y_927_, v___x_948_, v___y_929_);
lean_dec_ref_known(v___x_948_, 14);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__30___redArg___boxed(lean_object* v_ref_950_, lean_object* v_msg_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__30___redArg(v_ref_950_, v_msg_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec(v___y_952_);
lean_dec(v_ref_950_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28___redArg(lean_object* v_ref_962_, lean_object* v_msg_963_, lean_object* v_declHint_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v___x_974_; lean_object* v_a_975_; lean_object* v___x_976_; 
v___x_974_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29(v_msg_963_, v_declHint_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
v_a_975_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_a_975_);
lean_dec_ref(v___x_974_);
v___x_976_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__30___redArg(v_ref_962_, v_a_975_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28___redArg___boxed(lean_object* v_ref_977_, lean_object* v_msg_978_, lean_object* v_declHint_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28___redArg(v_ref_977_, v_msg_978_, v_declHint_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec(v___y_980_);
lean_dec(v_ref_977_);
return v_res_989_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26___redArg___closed__1(void){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26___redArg___closed__0));
v___x_992_ = l_Lean_stringToMessageData(v___x_991_);
return v___x_992_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26___redArg___closed__3(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26___redArg___closed__2));
v___x_995_ = l_Lean_stringToMessageData(v___x_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26___redArg(lean_object* v_ref_996_, lean_object* v_constName_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v___x_1007_; uint8_t v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1007_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26___redArg___closed__1);
v___x_1008_ = 0;
lean_inc(v_constName_997_);
v___x_1009_ = l_Lean_MessageData_ofConstName(v_constName_997_, v___x_1008_);
v___x_1010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1007_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26___redArg___closed__3);
v___x_1012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1010_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
v___x_1013_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28___redArg(v_ref_996_, v___x_1012_, v_constName_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26___redArg___boxed(lean_object* v_ref_1014_, lean_object* v_constName_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26___redArg(v_ref_1014_, v_constName_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec(v_ref_1014_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21___redArg(lean_object* v_constName_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v_ref_1036_; lean_object* v___x_1037_; 
v_ref_1036_ = lean_ctor_get(v___y_1033_, 5);
v___x_1037_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26___redArg(v_ref_1036_, v_constName_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21___redArg___boxed(lean_object* v_constName_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21___redArg(v_constName_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec(v___y_1039_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18(lean_object* v_constName_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v___x_1059_; lean_object* v_env_1060_; uint8_t v___x_1061_; lean_object* v___x_1062_; 
v___x_1059_ = lean_st_ref_get(v___y_1057_);
v_env_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc_ref(v_env_1060_);
lean_dec(v___x_1059_);
v___x_1061_ = 0;
lean_inc(v_constName_1049_);
v___x_1062_ = l_Lean_Environment_find_x3f(v_env_1060_, v_constName_1049_, v___x_1061_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21___redArg(v_constName_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
return v___x_1063_;
}
else
{
lean_object* v_val_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
lean_dec(v_constName_1049_);
v_val_1064_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1062_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_val_1064_);
lean_dec(v___x_1062_);
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
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_val_1064_);
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
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18___boxed(lean_object* v_constName_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18(v_constName_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec(v___y_1073_);
return v_res_1082_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19___closed__0(void){
_start:
{
lean_object* v___x_1083_; 
v___x_1083_ = l_instMonadEIO(lean_box(0));
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19(lean_object* v_msg_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v_toApplicative_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1195_; 
v___x_1100_ = lean_obj_once(&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19___closed__0, &l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19___closed__0_once, _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19___closed__0);
v___x_1101_ = l_StateRefT_x27_instMonad___redArg(v___x_1100_);
v_toApplicative_1102_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1195_ == 0)
{
lean_object* v_unused_1196_; 
v_unused_1196_ = lean_ctor_get(v___x_1101_, 1);
lean_dec(v_unused_1196_);
v___x_1104_ = v___x_1101_;
v_isShared_1105_ = v_isSharedCheck_1195_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_toApplicative_1102_);
lean_dec(v___x_1101_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1195_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v_toFunctor_1106_; lean_object* v_toSeq_1107_; lean_object* v_toSeqLeft_1108_; lean_object* v_toSeqRight_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1193_; 
v_toFunctor_1106_ = lean_ctor_get(v_toApplicative_1102_, 0);
v_toSeq_1107_ = lean_ctor_get(v_toApplicative_1102_, 2);
v_toSeqLeft_1108_ = lean_ctor_get(v_toApplicative_1102_, 3);
v_toSeqRight_1109_ = lean_ctor_get(v_toApplicative_1102_, 4);
v_isSharedCheck_1193_ = !lean_is_exclusive(v_toApplicative_1102_);
if (v_isSharedCheck_1193_ == 0)
{
lean_object* v_unused_1194_; 
v_unused_1194_ = lean_ctor_get(v_toApplicative_1102_, 1);
lean_dec(v_unused_1194_);
v___x_1111_ = v_toApplicative_1102_;
v_isShared_1112_ = v_isSharedCheck_1193_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_toSeqRight_1109_);
lean_inc(v_toSeqLeft_1108_);
lean_inc(v_toSeq_1107_);
lean_inc(v_toFunctor_1106_);
lean_dec(v_toApplicative_1102_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1193_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___f_1113_; lean_object* v___f_1114_; lean_object* v___f_1115_; lean_object* v___f_1116_; lean_object* v___x_1117_; lean_object* v___f_1118_; lean_object* v___f_1119_; lean_object* v___f_1120_; lean_object* v___x_1122_; 
v___f_1113_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19___closed__1));
v___f_1114_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19___closed__2));
lean_inc_ref(v_toFunctor_1106_);
v___f_1115_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1115_, 0, v_toFunctor_1106_);
v___f_1116_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1116_, 0, v_toFunctor_1106_);
v___x_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___f_1115_);
lean_ctor_set(v___x_1117_, 1, v___f_1116_);
v___f_1118_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1118_, 0, v_toSeqRight_1109_);
v___f_1119_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1119_, 0, v_toSeqLeft_1108_);
v___f_1120_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1120_, 0, v_toSeq_1107_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 4, v___f_1118_);
lean_ctor_set(v___x_1111_, 3, v___f_1119_);
lean_ctor_set(v___x_1111_, 2, v___f_1120_);
lean_ctor_set(v___x_1111_, 1, v___f_1113_);
lean_ctor_set(v___x_1111_, 0, v___x_1117_);
v___x_1122_ = v___x_1111_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1117_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v___f_1113_);
lean_ctor_set(v_reuseFailAlloc_1192_, 2, v___f_1120_);
lean_ctor_set(v_reuseFailAlloc_1192_, 3, v___f_1119_);
lean_ctor_set(v_reuseFailAlloc_1192_, 4, v___f_1118_);
v___x_1122_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
lean_object* v___x_1124_; 
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 1, v___f_1114_);
lean_ctor_set(v___x_1104_, 0, v___x_1122_);
v___x_1124_ = v___x_1104_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1122_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v___f_1114_);
v___x_1124_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
lean_object* v___x_1125_; lean_object* v_toApplicative_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1189_; 
v___x_1125_ = l_StateRefT_x27_instMonad___redArg(v___x_1124_);
v_toApplicative_1126_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1189_ == 0)
{
lean_object* v_unused_1190_; 
v_unused_1190_ = lean_ctor_get(v___x_1125_, 1);
lean_dec(v_unused_1190_);
v___x_1128_ = v___x_1125_;
v_isShared_1129_ = v_isSharedCheck_1189_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_toApplicative_1126_);
lean_dec(v___x_1125_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1189_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v_toFunctor_1130_; lean_object* v_toSeq_1131_; lean_object* v_toSeqLeft_1132_; lean_object* v_toSeqRight_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1187_; 
v_toFunctor_1130_ = lean_ctor_get(v_toApplicative_1126_, 0);
v_toSeq_1131_ = lean_ctor_get(v_toApplicative_1126_, 2);
v_toSeqLeft_1132_ = lean_ctor_get(v_toApplicative_1126_, 3);
v_toSeqRight_1133_ = lean_ctor_get(v_toApplicative_1126_, 4);
v_isSharedCheck_1187_ = !lean_is_exclusive(v_toApplicative_1126_);
if (v_isSharedCheck_1187_ == 0)
{
lean_object* v_unused_1188_; 
v_unused_1188_ = lean_ctor_get(v_toApplicative_1126_, 1);
lean_dec(v_unused_1188_);
v___x_1135_ = v_toApplicative_1126_;
v_isShared_1136_ = v_isSharedCheck_1187_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_toSeqRight_1133_);
lean_inc(v_toSeqLeft_1132_);
lean_inc(v_toSeq_1131_);
lean_inc(v_toFunctor_1130_);
lean_dec(v_toApplicative_1126_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1187_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___f_1137_; lean_object* v___f_1138_; lean_object* v___f_1139_; lean_object* v___f_1140_; lean_object* v___x_1141_; lean_object* v___f_1142_; lean_object* v___f_1143_; lean_object* v___f_1144_; lean_object* v___x_1146_; 
v___f_1137_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19___closed__3));
v___f_1138_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19___closed__4));
lean_inc_ref(v_toFunctor_1130_);
v___f_1139_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1139_, 0, v_toFunctor_1130_);
v___f_1140_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1140_, 0, v_toFunctor_1130_);
v___x_1141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___f_1139_);
lean_ctor_set(v___x_1141_, 1, v___f_1140_);
v___f_1142_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1142_, 0, v_toSeqRight_1133_);
v___f_1143_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1143_, 0, v_toSeqLeft_1132_);
v___f_1144_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1144_, 0, v_toSeq_1131_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 4, v___f_1142_);
lean_ctor_set(v___x_1135_, 3, v___f_1143_);
lean_ctor_set(v___x_1135_, 2, v___f_1144_);
lean_ctor_set(v___x_1135_, 1, v___f_1137_);
lean_ctor_set(v___x_1135_, 0, v___x_1141_);
v___x_1146_ = v___x_1135_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1141_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v___f_1137_);
lean_ctor_set(v_reuseFailAlloc_1186_, 2, v___f_1144_);
lean_ctor_set(v_reuseFailAlloc_1186_, 3, v___f_1143_);
lean_ctor_set(v_reuseFailAlloc_1186_, 4, v___f_1142_);
v___x_1146_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
lean_object* v___x_1148_; 
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 1, v___f_1138_);
lean_ctor_set(v___x_1128_, 0, v___x_1146_);
v___x_1148_ = v___x_1128_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1146_);
lean_ctor_set(v_reuseFailAlloc_1185_, 1, v___f_1138_);
v___x_1148_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
lean_object* v___x_1149_; lean_object* v_toApplicative_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1183_; 
v___x_1149_ = l_StateRefT_x27_instMonad___redArg(v___x_1148_);
v_toApplicative_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1183_ == 0)
{
lean_object* v_unused_1184_; 
v_unused_1184_ = lean_ctor_get(v___x_1149_, 1);
lean_dec(v_unused_1184_);
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1183_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_toApplicative_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1183_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v_toFunctor_1154_; lean_object* v_toSeq_1155_; lean_object* v_toSeqLeft_1156_; lean_object* v_toSeqRight_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1181_; 
v_toFunctor_1154_ = lean_ctor_get(v_toApplicative_1150_, 0);
v_toSeq_1155_ = lean_ctor_get(v_toApplicative_1150_, 2);
v_toSeqLeft_1156_ = lean_ctor_get(v_toApplicative_1150_, 3);
v_toSeqRight_1157_ = lean_ctor_get(v_toApplicative_1150_, 4);
v_isSharedCheck_1181_ = !lean_is_exclusive(v_toApplicative_1150_);
if (v_isSharedCheck_1181_ == 0)
{
lean_object* v_unused_1182_; 
v_unused_1182_ = lean_ctor_get(v_toApplicative_1150_, 1);
lean_dec(v_unused_1182_);
v___x_1159_ = v_toApplicative_1150_;
v_isShared_1160_ = v_isSharedCheck_1181_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_toSeqRight_1157_);
lean_inc(v_toSeqLeft_1156_);
lean_inc(v_toSeq_1155_);
lean_inc(v_toFunctor_1154_);
lean_dec(v_toApplicative_1150_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1181_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___f_1161_; lean_object* v___f_1162_; lean_object* v___f_1163_; lean_object* v___f_1164_; lean_object* v___x_1165_; lean_object* v___f_1166_; lean_object* v___f_1167_; lean_object* v___f_1168_; lean_object* v___x_1170_; 
v___f_1161_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19___closed__5));
v___f_1162_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19___closed__6));
lean_inc_ref(v_toFunctor_1154_);
v___f_1163_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1163_, 0, v_toFunctor_1154_);
v___f_1164_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1164_, 0, v_toFunctor_1154_);
v___x_1165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___f_1163_);
lean_ctor_set(v___x_1165_, 1, v___f_1164_);
v___f_1166_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1166_, 0, v_toSeqRight_1157_);
v___f_1167_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1167_, 0, v_toSeqLeft_1156_);
v___f_1168_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1168_, 0, v_toSeq_1155_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 4, v___f_1166_);
lean_ctor_set(v___x_1159_, 3, v___f_1167_);
lean_ctor_set(v___x_1159_, 2, v___f_1168_);
lean_ctor_set(v___x_1159_, 1, v___f_1161_);
lean_ctor_set(v___x_1159_, 0, v___x_1165_);
v___x_1170_ = v___x_1159_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1165_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v___f_1161_);
lean_ctor_set(v_reuseFailAlloc_1180_, 2, v___f_1168_);
lean_ctor_set(v_reuseFailAlloc_1180_, 3, v___f_1167_);
lean_ctor_set(v_reuseFailAlloc_1180_, 4, v___f_1166_);
v___x_1170_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
lean_object* v___x_1172_; 
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 1, v___f_1162_);
lean_ctor_set(v___x_1152_, 0, v___x_1170_);
v___x_1172_ = v___x_1152_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1170_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v___f_1162_);
v___x_1172_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_60930__overap_1177_; lean_object* v___x_1178_; 
v___x_1173_ = l_StateRefT_x27_instMonad___redArg(v___x_1172_);
v___x_1174_ = l_StateRefT_x27_instMonad___redArg(v___x_1173_);
v___x_1175_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_1176_ = l_instInhabitedOfMonad___redArg(v___x_1174_, v___x_1175_);
v___x_60930__overap_1177_ = lean_panic_fn_borrowed(v___x_1176_, v_msg_1090_);
lean_dec(v___x_1176_);
lean_inc(v___y_1098_);
lean_inc_ref(v___y_1097_);
lean_inc(v___y_1096_);
lean_inc_ref(v___y_1095_);
lean_inc(v___y_1094_);
lean_inc_ref(v___y_1093_);
lean_inc(v___y_1092_);
lean_inc(v___y_1091_);
v___x_1178_ = lean_apply_9(v___x_60930__overap_1177_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, lean_box(0));
return v___x_1178_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19___boxed(lean_object* v_msg_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19(v_msg_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec(v___y_1198_);
return v_res_1207_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21___closed__3(void){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1211_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21___closed__2));
v___x_1212_ = lean_unsigned_to_nat(53u);
v___x_1213_ = lean_unsigned_to_nat(62u);
v___x_1214_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21___closed__1));
v___x_1215_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21___closed__0));
v___x_1216_ = l_mkPanicMessageWithDecl(v___x_1215_, v___x_1214_, v___x_1213_, v___x_1212_, v___x_1211_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21(size_t v_sz_1217_, size_t v_i_1218_, lean_object* v_bs_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
uint8_t v___x_1229_; 
v___x_1229_ = lean_usize_dec_lt(v_i_1218_, v_sz_1217_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1230_; 
v___x_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1230_, 0, v_bs_1219_);
return v___x_1230_;
}
else
{
lean_object* v_v_1231_; lean_object* v___x_1232_; 
v_v_1231_ = lean_array_uget_borrowed(v_bs_1219_, v_i_1218_);
lean_inc(v_v_1231_);
v___x_1232_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18(v_v_1231_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; lean_object* v___x_1234_; lean_object* v_bs_x27_1235_; lean_object* v_a_1237_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1233_);
lean_dec_ref_known(v___x_1232_, 1);
v___x_1234_ = lean_unsigned_to_nat(0u);
v_bs_x27_1235_ = lean_array_uset(v_bs_1219_, v_i_1218_, v___x_1234_);
if (lean_obj_tag(v_a_1233_) == 6)
{
lean_object* v_val_1242_; lean_object* v_numFields_1243_; uint8_t v___x_1244_; lean_object* v___x_1245_; 
v_val_1242_ = lean_ctor_get(v_a_1233_, 0);
lean_inc_ref(v_val_1242_);
lean_dec_ref_known(v_a_1233_, 1);
v_numFields_1243_ = lean_ctor_get(v_val_1242_, 4);
lean_inc(v_numFields_1243_);
lean_dec_ref(v_val_1242_);
v___x_1244_ = 0;
v___x_1245_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1245_, 0, v_numFields_1243_);
lean_ctor_set(v___x_1245_, 1, v___x_1234_);
lean_ctor_set_uint8(v___x_1245_, sizeof(void*)*2, v___x_1244_);
v_a_1237_ = v___x_1245_;
goto v___jp_1236_;
}
else
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
lean_dec(v_a_1233_);
v___x_1246_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21___closed__3);
v___x_1247_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__19(v___x_1246_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1248_; 
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
lean_inc(v_a_1248_);
lean_dec_ref_known(v___x_1247_, 1);
v_a_1237_ = v_a_1248_;
goto v___jp_1236_;
}
else
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
lean_dec_ref(v_bs_x27_1235_);
v_a_1249_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1251_ = v___x_1247_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1247_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_a_1249_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
v___jp_1236_:
{
size_t v___x_1238_; size_t v___x_1239_; lean_object* v___x_1240_; 
v___x_1238_ = ((size_t)1ULL);
v___x_1239_ = lean_usize_add(v_i_1218_, v___x_1238_);
v___x_1240_ = lean_array_uset(v_bs_x27_1235_, v_i_1218_, v_a_1237_);
v_i_1218_ = v___x_1239_;
v_bs_1219_ = v___x_1240_;
goto _start;
}
}
else
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
lean_dec_ref(v_bs_1219_);
v_a_1257_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1259_ = v___x_1232_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1232_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1257_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21___boxed(lean_object* v_sz_1265_, lean_object* v_i_1266_, lean_object* v_bs_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
size_t v_sz_boxed_1277_; size_t v_i_boxed_1278_; lean_object* v_res_1279_; 
v_sz_boxed_1277_ = lean_unbox_usize(v_sz_1265_);
lean_dec(v_sz_1265_);
v_i_boxed_1278_ = lean_unbox_usize(v_i_1266_);
lean_dec(v_i_1266_);
v_res_1279_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21(v_sz_boxed_1277_, v_i_boxed_1278_, v_bs_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec(v___y_1268_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___redArg(lean_object* v_declName_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v___x_1283_; lean_object* v_env_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1283_ = lean_st_ref_get(v___y_1281_);
v_env_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc_ref(v_env_1284_);
lean_dec(v___x_1283_);
v___x_1285_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_1284_, v_declName_1280_);
v___x_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___redArg___boxed(lean_object* v_declName_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___redArg(v_declName_1287_, v___y_1288_);
lean_dec(v___y_1288_);
return v_res_1290_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0(void){
_start:
{
lean_object* v___x_1291_; lean_object* v_dummy_1292_; 
v___x_1291_ = lean_box(0);
v_dummy_1292_ = l_Lean_Expr_sort___override(v___x_1291_);
return v_dummy_1292_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__1(void){
_start:
{
lean_object* v_cellCount_1293_; lean_object* v___x_1294_; 
v_cellCount_1293_ = lean_unsigned_to_nat(16u);
v___x_1294_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1293_);
return v___x_1294_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__2(void){
_start:
{
lean_object* v_cellCount_1295_; lean_object* v___x_1296_; 
v_cellCount_1295_ = lean_unsigned_to_nat(16u);
v___x_1296_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1295_);
return v___x_1296_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__3(void){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1297_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__2, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__2_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__2);
v___x_1298_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__1);
v___x_1299_ = lean_unsigned_to_nat(0u);
v___x_1300_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1299_);
lean_ctor_set(v___x_1300_, 1, v___x_1298_);
lean_ctor_set(v___x_1300_, 2, v___x_1297_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(lean_object* v_e_1303_, uint8_t v_alsoCasesOn_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
uint8_t v___x_1317_; 
v___x_1317_ = l_Lean_Expr_isApp(v_e_1303_);
if (v___x_1317_ == 0)
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
lean_dec_ref(v_e_1303_);
v___x_1318_ = lean_box(0);
v___x_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
return v___x_1319_;
}
else
{
lean_object* v___x_1320_; 
v___x_1320_ = l_Lean_Expr_getAppFn(v_e_1303_);
if (lean_obj_tag(v___x_1320_) == 4)
{
lean_object* v_declName_1321_; lean_object* v_us_1322_; lean_object* v___x_1323_; lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1478_; 
v_declName_1321_ = lean_ctor_get(v___x_1320_, 0);
lean_inc_n(v_declName_1321_, 2);
v_us_1322_ = lean_ctor_get(v___x_1320_, 1);
lean_inc(v_us_1322_);
lean_dec_ref_known(v___x_1320_, 2);
v___x_1323_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___redArg(v_declName_1321_, v___y_1312_);
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1326_ = v___x_1323_;
v_isShared_1327_ = v_isSharedCheck_1478_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1323_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1478_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
if (lean_obj_tag(v_a_1324_) == 1)
{
lean_object* v_val_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1370_; 
v_val_1328_ = lean_ctor_get(v_a_1324_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v_a_1324_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1330_ = v_a_1324_;
v_isShared_1331_ = v_isSharedCheck_1370_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_val_1328_);
lean_dec(v_a_1324_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1370_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v_dummy_1332_; lean_object* v_nargs_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v_args_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; uint8_t v___x_1340_; 
v_dummy_1332_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0);
v_nargs_1333_ = l_Lean_Expr_getAppNumArgs(v_e_1303_);
lean_inc(v_nargs_1333_);
v___x_1334_ = lean_mk_array(v_nargs_1333_, v_dummy_1332_);
v___x_1335_ = lean_unsigned_to_nat(1u);
v___x_1336_ = lean_nat_sub(v_nargs_1333_, v___x_1335_);
lean_dec(v_nargs_1333_);
v_args_1337_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1303_, v___x_1334_, v___x_1336_);
v___x_1338_ = lean_array_get_size(v_args_1337_);
v___x_1339_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_1328_);
v___x_1340_ = lean_nat_dec_lt(v___x_1338_, v___x_1339_);
lean_dec(v___x_1339_);
if (v___x_1340_ == 0)
{
lean_object* v_numParams_1341_; lean_object* v_numDiscrs_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1361_; 
v_numParams_1341_ = lean_ctor_get(v_val_1328_, 0);
v_numDiscrs_1342_ = lean_ctor_get(v_val_1328_, 1);
v___x_1343_ = lean_array_mk(v_us_1322_);
v___x_1344_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1341_);
v___x_1345_ = l_Array_extract___redArg(v_args_1337_, v___x_1344_, v_numParams_1341_);
v___x_1346_ = l_Lean_instInhabitedExpr;
v___x_1347_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_1328_);
v___x_1348_ = lean_array_get(v___x_1346_, v_args_1337_, v___x_1347_);
lean_dec(v___x_1347_);
v___x_1349_ = lean_nat_add(v_numParams_1341_, v___x_1335_);
v___x_1350_ = lean_nat_add(v___x_1349_, v_numDiscrs_1342_);
lean_inc(v___x_1350_);
lean_inc_ref_n(v_args_1337_, 2);
v___x_1351_ = l_Array_toSubarray___redArg(v_args_1337_, v___x_1349_, v___x_1350_);
v___x_1352_ = l_Subarray_copy___redArg(v___x_1351_);
v___x_1353_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1328_);
v___x_1354_ = lean_nat_add(v___x_1350_, v___x_1353_);
lean_dec(v___x_1353_);
lean_inc(v___x_1354_);
v___x_1355_ = l_Array_toSubarray___redArg(v_args_1337_, v___x_1350_, v___x_1354_);
v___x_1356_ = l_Subarray_copy___redArg(v___x_1355_);
v___x_1357_ = l_Array_toSubarray___redArg(v_args_1337_, v___x_1354_, v___x_1338_);
v___x_1358_ = l_Subarray_copy___redArg(v___x_1357_);
v___x_1359_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1359_, 0, v_val_1328_);
lean_ctor_set(v___x_1359_, 1, v_declName_1321_);
lean_ctor_set(v___x_1359_, 2, v___x_1343_);
lean_ctor_set(v___x_1359_, 3, v___x_1345_);
lean_ctor_set(v___x_1359_, 4, v___x_1348_);
lean_ctor_set(v___x_1359_, 5, v___x_1352_);
lean_ctor_set(v___x_1359_, 6, v___x_1356_);
lean_ctor_set(v___x_1359_, 7, v___x_1358_);
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 0, v___x_1359_);
v___x_1361_ = v___x_1330_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1359_);
v___x_1361_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
lean_object* v___x_1363_; 
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 0, v___x_1361_);
v___x_1363_ = v___x_1326_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1361_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
else
{
lean_object* v___x_1366_; lean_object* v___x_1368_; 
lean_dec_ref(v_args_1337_);
lean_del_object(v___x_1330_);
lean_dec(v_val_1328_);
lean_dec(v_us_1322_);
lean_dec(v_declName_1321_);
v___x_1366_ = lean_box(0);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 0, v___x_1366_);
v___x_1368_ = v___x_1326_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1366_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
else
{
lean_object* v___x_1371_; 
lean_del_object(v___x_1326_);
lean_dec(v_a_1324_);
v___x_1371_ = lean_st_ref_get(v___y_1312_);
if (v_alsoCasesOn_1304_ == 0)
{
lean_dec(v___x_1371_);
lean_dec(v_us_1322_);
lean_dec(v_declName_1321_);
lean_dec_ref(v_e_1303_);
goto v___jp_1314_;
}
else
{
lean_object* v_env_1372_; uint8_t v___x_1373_; 
v_env_1372_ = lean_ctor_get(v___x_1371_, 0);
lean_inc_ref(v_env_1372_);
lean_dec(v___x_1371_);
lean_inc(v_declName_1321_);
v___x_1373_ = l_Lean_isCasesOnRecursor(v_env_1372_, v_declName_1321_);
if (v___x_1373_ == 0)
{
lean_dec(v_us_1322_);
lean_dec(v_declName_1321_);
lean_dec_ref(v_e_1303_);
goto v___jp_1314_;
}
else
{
lean_object* v_indName_1374_; lean_object* v___x_1375_; 
v_indName_1374_ = l_Lean_Name_getPrefix(v_declName_1321_);
v___x_1375_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18(v_indName_1374_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1469_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1378_ = v___x_1375_;
v_isShared_1379_ = v_isSharedCheck_1469_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1375_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1469_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
if (lean_obj_tag(v_a_1376_) == 5)
{
lean_object* v_val_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1464_; 
v_val_1380_ = lean_ctor_get(v_a_1376_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v_a_1376_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1382_ = v_a_1376_;
v_isShared_1383_ = v_isSharedCheck_1464_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_val_1380_);
lean_dec(v_a_1376_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1464_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v_toConstantVal_1384_; lean_object* v_numParams_1385_; lean_object* v_numIndices_1386_; lean_object* v_ctors_1387_; lean_object* v_nargs_1388_; lean_object* v_dummy_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v_args_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; uint8_t v___x_1400_; 
v_toConstantVal_1384_ = lean_ctor_get(v_val_1380_, 0);
lean_inc_ref(v_toConstantVal_1384_);
v_numParams_1385_ = lean_ctor_get(v_val_1380_, 1);
lean_inc(v_numParams_1385_);
v_numIndices_1386_ = lean_ctor_get(v_val_1380_, 2);
lean_inc(v_numIndices_1386_);
v_ctors_1387_ = lean_ctor_get(v_val_1380_, 4);
lean_inc(v_ctors_1387_);
v_nargs_1388_ = l_Lean_Expr_getAppNumArgs(v_e_1303_);
v_dummy_1389_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0);
lean_inc(v_nargs_1388_);
v___x_1390_ = lean_mk_array(v_nargs_1388_, v_dummy_1389_);
v___x_1391_ = lean_unsigned_to_nat(1u);
v___x_1392_ = lean_nat_sub(v_nargs_1388_, v___x_1391_);
lean_dec(v_nargs_1388_);
v_args_1393_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1303_, v___x_1390_, v___x_1392_);
v___x_1394_ = lean_nat_add(v_numParams_1385_, v___x_1391_);
v___x_1395_ = lean_nat_add(v___x_1394_, v_numIndices_1386_);
v___x_1396_ = lean_nat_add(v___x_1395_, v___x_1391_);
lean_dec(v___x_1395_);
v___x_1397_ = l_Lean_InductiveVal_numCtors(v_val_1380_);
lean_dec_ref(v_val_1380_);
v___x_1398_ = lean_nat_add(v___x_1396_, v___x_1397_);
lean_dec(v___x_1397_);
v___x_1399_ = lean_array_get_size(v_args_1393_);
v___x_1400_ = lean_nat_dec_le(v___x_1398_, v___x_1399_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1401_; lean_object* v___x_1403_; 
lean_dec(v___x_1398_);
lean_dec(v___x_1396_);
lean_dec(v___x_1394_);
lean_dec_ref(v_args_1393_);
lean_dec(v_ctors_1387_);
lean_dec(v_numIndices_1386_);
lean_dec(v_numParams_1385_);
lean_dec_ref(v_toConstantVal_1384_);
lean_del_object(v___x_1382_);
lean_dec(v_us_1322_);
lean_dec(v_declName_1321_);
v___x_1401_ = lean_box(0);
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 0, v___x_1401_);
v___x_1403_ = v___x_1378_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1401_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
else
{
lean_object* v___x_1405_; lean_object* v_params_1406_; lean_object* v___x_1407_; lean_object* v_motive_1408_; lean_object* v_discrs_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v_discrInfos_1412_; lean_object* v_alts_1413_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v_lower_1455_; lean_object* v_upper_1456_; uint8_t v___x_1463_; 
lean_del_object(v___x_1378_);
v___x_1405_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1385_);
lean_inc_ref_n(v_args_1393_, 3);
v_params_1406_ = l_Array_toSubarray___redArg(v_args_1393_, v___x_1405_, v_numParams_1385_);
v___x_1407_ = l_Lean_instInhabitedExpr;
v_motive_1408_ = lean_array_get(v___x_1407_, v_args_1393_, v_numParams_1385_);
lean_dec(v_numParams_1385_);
lean_inc(v___x_1396_);
v_discrs_1409_ = l_Array_toSubarray___redArg(v_args_1393_, v___x_1394_, v___x_1396_);
v___x_1410_ = lean_nat_add(v_numIndices_1386_, v___x_1391_);
lean_dec(v_numIndices_1386_);
v___x_1411_ = lean_box(0);
v_discrInfos_1412_ = lean_mk_array(v___x_1410_, v___x_1411_);
lean_inc(v___x_1398_);
v_alts_1413_ = l_Array_toSubarray___redArg(v_args_1393_, v___x_1396_, v___x_1398_);
v___x_1463_ = lean_nat_dec_le(v___x_1398_, v___x_1405_);
if (v___x_1463_ == 0)
{
v_lower_1455_ = v___x_1398_;
v_upper_1456_ = v___x_1399_;
goto v___jp_1454_;
}
else
{
lean_dec(v___x_1398_);
v_lower_1455_ = v___x_1405_;
v_upper_1456_ = v___x_1399_;
goto v___jp_1454_;
}
v___jp_1414_:
{
lean_object* v___x_1417_; size_t v_sz_1418_; size_t v___x_1419_; lean_object* v___x_1420_; 
v___x_1417_ = lean_array_mk(v_ctors_1387_);
v_sz_1418_ = lean_array_size(v___x_1417_);
v___x_1419_ = ((size_t)0ULL);
v___x_1420_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__21(v_sz_1418_, v___x_1419_, v___x_1417_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1445_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1423_ = v___x_1420_;
v_isShared_1424_ = v_isSharedCheck_1445_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1420_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1445_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v_start_1425_; lean_object* v_stop_1426_; lean_object* v_start_1427_; lean_object* v_stop_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1440_; 
v_start_1425_ = lean_ctor_get(v_params_1406_, 1);
lean_inc(v_start_1425_);
v_stop_1426_ = lean_ctor_get(v_params_1406_, 2);
lean_inc(v_stop_1426_);
v_start_1427_ = lean_ctor_get(v_discrs_1409_, 1);
lean_inc(v_start_1427_);
v_stop_1428_ = lean_ctor_get(v_discrs_1409_, 2);
lean_inc(v_stop_1428_);
v___x_1429_ = lean_nat_sub(v_stop_1426_, v_start_1425_);
lean_dec(v_start_1425_);
lean_dec(v_stop_1426_);
v___x_1430_ = lean_nat_sub(v_stop_1428_, v_start_1427_);
lean_dec(v_start_1427_);
lean_dec(v_stop_1428_);
v___x_1431_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__3, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__3_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__3);
v___x_1432_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1429_);
lean_ctor_set(v___x_1432_, 1, v___x_1430_);
lean_ctor_set(v___x_1432_, 2, v_a_1421_);
lean_ctor_set(v___x_1432_, 3, v___y_1416_);
lean_ctor_set(v___x_1432_, 4, v_discrInfos_1412_);
lean_ctor_set(v___x_1432_, 5, v___x_1431_);
v___x_1433_ = lean_array_mk(v_us_1322_);
v___x_1434_ = l_Subarray_copy___redArg(v_params_1406_);
v___x_1435_ = l_Subarray_copy___redArg(v_discrs_1409_);
v___x_1436_ = l_Subarray_copy___redArg(v_alts_1413_);
v___x_1437_ = l_Subarray_copy___redArg(v___y_1415_);
v___x_1438_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1432_);
lean_ctor_set(v___x_1438_, 1, v_declName_1321_);
lean_ctor_set(v___x_1438_, 2, v___x_1433_);
lean_ctor_set(v___x_1438_, 3, v___x_1434_);
lean_ctor_set(v___x_1438_, 4, v_motive_1408_);
lean_ctor_set(v___x_1438_, 5, v___x_1435_);
lean_ctor_set(v___x_1438_, 6, v___x_1436_);
lean_ctor_set(v___x_1438_, 7, v___x_1437_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set_tag(v___x_1382_, 1);
lean_ctor_set(v___x_1382_, 0, v___x_1438_);
v___x_1440_ = v___x_1382_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1442_; 
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v___x_1440_);
v___x_1442_ = v___x_1423_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1440_);
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
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec_ref(v_alts_1413_);
lean_dec_ref(v_discrInfos_1412_);
lean_dec_ref(v_discrs_1409_);
lean_dec(v_motive_1408_);
lean_dec_ref(v_params_1406_);
lean_del_object(v___x_1382_);
lean_dec(v_us_1322_);
lean_dec(v_declName_1321_);
v_a_1446_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1420_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1420_);
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
v___jp_1454_:
{
lean_object* v_levelParams_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; uint8_t v___x_1461_; 
v_levelParams_1457_ = lean_ctor_get(v_toConstantVal_1384_, 1);
lean_inc(v_levelParams_1457_);
lean_dec_ref(v_toConstantVal_1384_);
v___x_1458_ = l_Array_toSubarray___redArg(v_args_1393_, v_lower_1455_, v_upper_1456_);
v___x_1459_ = l_List_lengthTR___redArg(v_levelParams_1457_);
lean_dec(v_levelParams_1457_);
v___x_1460_ = l_List_lengthTR___redArg(v_us_1322_);
v___x_1461_ = lean_nat_dec_eq(v___x_1459_, v___x_1460_);
lean_dec(v___x_1460_);
lean_dec(v___x_1459_);
if (v___x_1461_ == 0)
{
lean_object* v___x_1462_; 
v___x_1462_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__4));
v___y_1415_ = v___x_1458_;
v___y_1416_ = v___x_1462_;
goto v___jp_1414_;
}
else
{
v___y_1415_ = v___x_1458_;
v___y_1416_ = v___x_1411_;
goto v___jp_1414_;
}
}
}
}
}
else
{
lean_object* v___x_1465_; lean_object* v___x_1467_; 
lean_dec(v_a_1376_);
lean_dec(v_us_1322_);
lean_dec(v_declName_1321_);
lean_dec_ref(v_e_1303_);
v___x_1465_ = lean_box(0);
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 0, v___x_1465_);
v___x_1467_ = v___x_1378_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1465_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
else
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
lean_dec(v_us_1322_);
lean_dec(v_declName_1321_);
lean_dec_ref(v_e_1303_);
v_a_1470_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1375_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1375_);
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
}
}
}
}
else
{
lean_dec_ref(v___x_1320_);
lean_dec_ref(v_e_1303_);
goto v___jp_1314_;
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___boxed(lean_object* v_e_1479_, lean_object* v_alsoCasesOn_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
uint8_t v_alsoCasesOn_boxed_1490_; lean_object* v_res_1491_; 
v_alsoCasesOn_boxed_1490_ = lean_unbox(v_alsoCasesOn_1480_);
v_res_1491_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(v_e_1479_, v_alsoCasesOn_boxed_1490_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v___y_1482_);
lean_dec(v___y_1481_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12_spec__15___redArg(lean_object* v_name_1492_, lean_object* v_type_1493_, lean_object* v_val_1494_, lean_object* v_k_1495_, uint8_t v_nondep_1496_, uint8_t v_kind_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v___f_1507_; lean_object* v___x_1508_; 
lean_inc(v___y_1501_);
lean_inc_ref(v___y_1500_);
lean_inc(v___y_1499_);
lean_inc(v___y_1498_);
v___f_1507_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1507_, 0, v_k_1495_);
lean_closure_set(v___f_1507_, 1, v___y_1498_);
lean_closure_set(v___f_1507_, 2, v___y_1499_);
lean_closure_set(v___f_1507_, 3, v___y_1500_);
lean_closure_set(v___f_1507_, 4, v___y_1501_);
v___x_1508_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1492_, v_type_1493_, v_val_1494_, v___f_1507_, v_nondep_1496_, v_kind_1497_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12_spec__15___redArg___boxed(lean_object* v_name_1517_, lean_object* v_type_1518_, lean_object* v_val_1519_, lean_object* v_k_1520_, lean_object* v_nondep_1521_, lean_object* v_kind_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
uint8_t v_nondep_boxed_1532_; uint8_t v_kind_boxed_1533_; lean_object* v_res_1534_; 
v_nondep_boxed_1532_ = lean_unbox(v_nondep_1521_);
v_kind_boxed_1533_ = lean_unbox(v_kind_1522_);
v_res_1534_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12_spec__15___redArg(v_name_1517_, v_type_1518_, v_val_1519_, v_k_1520_, v_nondep_boxed_1532_, v_kind_boxed_1533_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec(v___y_1523_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___lam__0(lean_object* v_k_1535_, uint8_t v_usedLetOnly_1536_, lean_object* v_x_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v___x_1547_; 
lean_inc(v___y_1545_);
lean_inc_ref(v___y_1544_);
lean_inc(v___y_1543_);
lean_inc_ref(v___y_1542_);
lean_inc(v___y_1541_);
lean_inc_ref(v___y_1540_);
lean_inc(v___y_1539_);
lean_inc(v___y_1538_);
lean_inc_ref(v_x_1537_);
v___x_1547_ = lean_apply_10(v_k_1535_, v_x_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, lean_box(0));
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; uint8_t v___x_1553_; lean_object* v___x_1554_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_a_1548_);
lean_dec_ref_known(v___x_1547_, 1);
v___x_1549_ = lean_unsigned_to_nat(1u);
v___x_1550_ = lean_mk_empty_array_with_capacity(v___x_1549_);
v___x_1551_ = lean_array_push(v___x_1550_, v_x_1537_);
v___x_1552_ = 0;
v___x_1553_ = 1;
v___x_1554_ = l_Lean_Meta_mkLetFVars(v___x_1551_, v_a_1548_, v_usedLetOnly_1536_, v___x_1552_, v___x_1553_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
lean_dec_ref(v___x_1551_);
return v___x_1554_;
}
else
{
lean_dec_ref(v_x_1537_);
return v___x_1547_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___lam__0___boxed(lean_object* v_k_1555_, lean_object* v_usedLetOnly_1556_, lean_object* v_x_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
uint8_t v_usedLetOnly_boxed_1567_; lean_object* v_res_1568_; 
v_usedLetOnly_boxed_1567_ = lean_unbox(v_usedLetOnly_1556_);
v_res_1568_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___lam__0(v_k_1555_, v_usedLetOnly_boxed_1567_, v_x_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec(v___y_1558_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(lean_object* v_name_1569_, lean_object* v_type_1570_, lean_object* v_val_1571_, lean_object* v_k_1572_, uint8_t v_nondep_1573_, uint8_t v_kind_1574_, uint8_t v_usedLetOnly_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v___x_1585_; lean_object* v___f_1586_; lean_object* v___x_1587_; 
v___x_1585_ = lean_box(v_usedLetOnly_1575_);
v___f_1586_ = lean_alloc_closure((void*)(l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___lam__0___boxed), 12, 2);
lean_closure_set(v___f_1586_, 0, v_k_1572_);
lean_closure_set(v___f_1586_, 1, v___x_1585_);
v___x_1587_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12_spec__15___redArg(v_name_1569_, v_type_1570_, v_val_1571_, v___f_1586_, v_nondep_1573_, v_kind_1574_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___boxed(lean_object* v_name_1588_, lean_object* v_type_1589_, lean_object* v_val_1590_, lean_object* v_k_1591_, lean_object* v_nondep_1592_, lean_object* v_kind_1593_, lean_object* v_usedLetOnly_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
uint8_t v_nondep_boxed_1604_; uint8_t v_kind_boxed_1605_; uint8_t v_usedLetOnly_boxed_1606_; lean_object* v_res_1607_; 
v_nondep_boxed_1604_ = lean_unbox(v_nondep_1592_);
v_kind_boxed_1605_ = lean_unbox(v_kind_1593_);
v_usedLetOnly_boxed_1606_ = lean_unbox(v_usedLetOnly_1594_);
v_res_1607_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(v_name_1588_, v_type_1589_, v_val_1590_, v_k_1591_, v_nondep_boxed_1604_, v_kind_boxed_1605_, v_usedLetOnly_boxed_1606_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec(v___y_1595_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg___lam__0(lean_object* v_k_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
lean_object* v___x_1618_; 
lean_inc(v___y_1612_);
lean_inc_ref(v___y_1611_);
lean_inc(v___y_1610_);
lean_inc(v___y_1609_);
v___x_1618_ = lean_apply_9(v_k_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, lean_box(0));
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg___lam__0___boxed(lean_object* v_k_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg___lam__0(v_k_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_dec(v___y_1620_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(lean_object* v_k_1630_, uint8_t v_allowLevelAssignments_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
lean_object* v___f_1641_; lean_object* v___x_1642_; 
lean_inc(v___y_1635_);
lean_inc_ref(v___y_1634_);
lean_inc(v___y_1633_);
lean_inc(v___y_1632_);
v___f_1641_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1641_, 0, v_k_1630_);
lean_closure_set(v___f_1641_, 1, v___y_1632_);
lean_closure_set(v___f_1641_, 2, v___y_1633_);
lean_closure_set(v___f_1641_, 3, v___y_1634_);
lean_closure_set(v___f_1641_, 4, v___y_1635_);
v___x_1642_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1631_, v___f_1641_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
if (lean_obj_tag(v___x_1642_) == 0)
{
return v___x_1642_;
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1642_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg___boxed(lean_object* v_k_1651_, lean_object* v_allowLevelAssignments_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1662_; lean_object* v_res_1663_; 
v_allowLevelAssignments_boxed_1662_ = lean_unbox(v_allowLevelAssignments_1652_);
v_res_1663_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v_k_1651_, v_allowLevelAssignments_boxed_1662_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec(v___y_1654_);
lean_dec(v___y_1653_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__9_spec__14___redArg(lean_object* v_b_1664_, lean_object* v_acc_1665_, lean_object* v_i_1666_){
_start:
{
lean_object* v___y_1668_; lean_object* v_keyArray_1676_; lean_object* v_valueArray_1677_; lean_object* v___x_1678_; uint8_t v___x_1679_; 
v_keyArray_1676_ = lean_ctor_get(v_b_1664_, 1);
v_valueArray_1677_ = lean_ctor_get(v_b_1664_, 2);
v___x_1678_ = lean_array_get_size(v_keyArray_1676_);
v___x_1679_ = lean_nat_dec_lt(v_i_1666_, v___x_1678_);
if (v___x_1679_ == 0)
{
lean_dec(v_i_1666_);
return v_acc_1665_;
}
else
{
lean_object* v___x_1680_; uint8_t v_isSome_1681_; 
v___x_1680_ = lean_array_fget_borrowed(v_keyArray_1676_, v_i_1666_);
v_isSome_1681_ = lean_noption_is_some(v___x_1680_);
if (v_isSome_1681_ == 0)
{
goto v___jp_1672_;
}
else
{
lean_object* v___x_1682_; uint8_t v_isSome_1683_; 
v___x_1682_ = lean_array_fget_borrowed(v_valueArray_1677_, v_i_1666_);
v_isSome_1683_ = lean_noption_is_some(v___x_1682_);
if (v_isSome_1683_ == 0)
{
goto v___jp_1672_;
}
else
{
lean_object* v_val_1684_; lean_object* v_val_1685_; lean_object* v_i_1687_; lean_object* v___x_1692_; 
lean_inc(v___x_1680_);
v_val_1684_ = lean_noption_get(v___x_1680_);
lean_inc(v___x_1682_);
v_val_1685_ = lean_noption_get(v___x_1682_);
v___x_1692_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v_acc_1665_, v_val_1684_);
switch(lean_obj_tag(v___x_1692_))
{
case 0:
{
lean_object* v_index_1693_; lean_object* v_size_1694_; lean_object* v___x_1695_; 
v_index_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_index_1693_);
lean_dec_ref_known(v___x_1692_, 3);
v_size_1694_ = lean_ctor_get(v_acc_1665_, 0);
lean_inc(v_size_1694_);
v___x_1695_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1665_, v_size_1694_, v_index_1693_, v_val_1684_, v_val_1685_);
lean_dec(v_index_1693_);
v___y_1668_ = v___x_1695_;
goto v___jp_1667_;
}
case 1:
{
lean_object* v_index_1696_; 
v_index_1696_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_index_1696_);
lean_dec_ref_known(v___x_1692_, 1);
v_i_1687_ = v_index_1696_;
goto v___jp_1686_;
}
default: 
{
lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1697_ = lean_unsigned_to_nat(0u);
v___x_1698_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_1665_, v___x_1697_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_index_1699_; 
v_index_1699_ = lean_ctor_get(v___x_1698_, 0);
lean_inc(v_index_1699_);
lean_dec_ref_known(v___x_1698_, 1);
v_i_1687_ = v_index_1699_;
goto v___jp_1686_;
}
else
{
lean_dec(v_val_1685_);
lean_dec(v_val_1684_);
v___y_1668_ = v_acc_1665_;
goto v___jp_1667_;
}
}
}
v___jp_1686_:
{
lean_object* v_size_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v_size_1688_ = lean_ctor_get(v_acc_1665_, 0);
v___x_1689_ = lean_unsigned_to_nat(1u);
v___x_1690_ = lean_nat_add(v_size_1688_, v___x_1689_);
v___x_1691_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1665_, v___x_1690_, v_i_1687_, v_val_1684_, v_val_1685_);
lean_dec(v_i_1687_);
v___y_1668_ = v___x_1691_;
goto v___jp_1667_;
}
}
}
}
v___jp_1667_:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1669_ = lean_unsigned_to_nat(1u);
v___x_1670_ = lean_nat_add(v_i_1666_, v___x_1669_);
lean_dec(v_i_1666_);
v_acc_1665_ = v___y_1668_;
v_i_1666_ = v___x_1670_;
goto _start;
}
v___jp_1672_:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1673_ = lean_unsigned_to_nat(1u);
v___x_1674_ = lean_nat_add(v_i_1666_, v___x_1673_);
lean_dec(v_i_1666_);
v_i_1666_ = v___x_1674_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__9_spec__14___redArg___boxed(lean_object* v_b_1700_, lean_object* v_acc_1701_, lean_object* v_i_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__9_spec__14___redArg(v_b_1700_, v_acc_1701_, v_i_1702_);
lean_dec_ref(v_b_1700_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__9___redArg(lean_object* v_init_1704_, lean_object* v_b_1705_){
_start:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1706_ = lean_unsigned_to_nat(0u);
v___x_1707_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__9_spec__14___redArg(v_b_1705_, v_init_1704_, v___x_1706_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__9___redArg___boxed(lean_object* v_init_1708_, lean_object* v_b_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__9___redArg(v_init_1708_, v_b_1709_);
lean_dec_ref(v_b_1709_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(lean_object* v_m_1711_){
_start:
{
lean_object* v_keyArray_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v_cellCount_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v_target_1719_; lean_object* v___x_1720_; 
v_keyArray_1712_ = lean_ctor_get(v_m_1711_, 1);
v___x_1713_ = lean_array_get_size(v_keyArray_1712_);
v___x_1714_ = lean_unsigned_to_nat(2u);
v_cellCount_1715_ = lean_nat_mul(v___x_1713_, v___x_1714_);
v___x_1716_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_1715_);
v___x_1717_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1715_);
v___x_1718_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1715_);
v_target_1719_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_1719_, 0, v___x_1716_);
lean_ctor_set(v_target_1719_, 1, v___x_1717_);
lean_ctor_set(v_target_1719_, 2, v___x_1718_);
v___x_1720_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__9___redArg(v_target_1719_, v_m_1711_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg___boxed(lean_object* v_m_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v_m_1721_);
lean_dec_ref(v_m_1721_);
return v_res_1722_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4(lean_object* v_opts_1723_, lean_object* v_opt_1724_){
_start:
{
lean_object* v_name_1725_; lean_object* v_defValue_1726_; lean_object* v_map_1727_; lean_object* v___x_1728_; 
v_name_1725_ = lean_ctor_get(v_opt_1724_, 0);
v_defValue_1726_ = lean_ctor_get(v_opt_1724_, 1);
v_map_1727_ = lean_ctor_get(v_opts_1723_, 0);
v___x_1728_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1727_, v_name_1725_);
if (lean_obj_tag(v___x_1728_) == 0)
{
uint8_t v___x_1729_; 
v___x_1729_ = lean_unbox(v_defValue_1726_);
return v___x_1729_;
}
else
{
lean_object* v_val_1730_; 
v_val_1730_ = lean_ctor_get(v___x_1728_, 0);
lean_inc(v_val_1730_);
lean_dec_ref_known(v___x_1728_, 1);
if (lean_obj_tag(v_val_1730_) == 1)
{
uint8_t v_v_1731_; 
v_v_1731_ = lean_ctor_get_uint8(v_val_1730_, 0);
lean_dec_ref_known(v_val_1730_, 0);
return v_v_1731_;
}
else
{
uint8_t v___x_1732_; 
lean_dec(v_val_1730_);
v___x_1732_ = lean_unbox(v_defValue_1726_);
return v___x_1732_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4___boxed(lean_object* v_opts_1733_, lean_object* v_opt_1734_){
_start:
{
uint8_t v_res_1735_; lean_object* v_r_1736_; 
v_res_1735_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4(v_opts_1733_, v_opt_1734_);
lean_dec_ref(v_opt_1734_);
lean_dec_ref(v_opts_1733_);
v_r_1736_ = lean_box(v_res_1735_);
return v_r_1736_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(lean_object* v_a_1737_, lean_object* v_b_1738_){
_start:
{
lean_object* v_array_1739_; lean_object* v_start_1740_; lean_object* v_stop_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1754_; 
v_array_1739_ = lean_ctor_get(v_a_1737_, 0);
v_start_1740_ = lean_ctor_get(v_a_1737_, 1);
v_stop_1741_ = lean_ctor_get(v_a_1737_, 2);
v_isSharedCheck_1754_ = !lean_is_exclusive(v_a_1737_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1743_ = v_a_1737_;
v_isShared_1744_ = v_isSharedCheck_1754_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_stop_1741_);
lean_inc(v_start_1740_);
lean_inc(v_array_1739_);
lean_dec(v_a_1737_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1754_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
uint8_t v___x_1745_; 
v___x_1745_ = lean_nat_dec_lt(v_start_1740_, v_stop_1741_);
if (v___x_1745_ == 0)
{
lean_del_object(v___x_1743_);
lean_dec(v_stop_1741_);
lean_dec(v_start_1740_);
lean_dec_ref(v_array_1739_);
return v_b_1738_;
}
else
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1749_; 
v___x_1746_ = lean_unsigned_to_nat(1u);
v___x_1747_ = lean_nat_add(v_start_1740_, v___x_1746_);
lean_inc_ref(v_array_1739_);
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 1, v___x_1747_);
v___x_1749_ = v___x_1743_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_array_1739_);
lean_ctor_set(v_reuseFailAlloc_1753_, 1, v___x_1747_);
lean_ctor_set(v_reuseFailAlloc_1753_, 2, v_stop_1741_);
v___x_1749_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1750_ = lean_array_fget(v_array_1739_, v_start_1740_);
lean_dec(v_start_1740_);
lean_dec_ref(v_array_1739_);
v___x_1751_ = lean_array_push(v_b_1738_, v___x_1750_);
v_a_1737_ = v___x_1749_;
v_b_1738_ = v___x_1751_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0(lean_object* v_body_1755_, lean_object* v_recFnName_1756_, lean_object* v_fixedPrefixSize_1757_, lean_object* v_F_1758_, lean_object* v_x_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1769_ = lean_expr_instantiate1(v_body_1755_, v_x_1759_);
v___x_1770_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1756_, v_fixedPrefixSize_1757_, v_F_1758_, v___x_1769_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; uint8_t v___x_1775_; uint8_t v___x_1776_; uint8_t v___x_1777_; lean_object* v___x_1778_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref_known(v___x_1770_, 1);
v___x_1772_ = lean_unsigned_to_nat(1u);
v___x_1773_ = lean_mk_empty_array_with_capacity(v___x_1772_);
v___x_1774_ = lean_array_push(v___x_1773_, v_x_1759_);
v___x_1775_ = 0;
v___x_1776_ = 1;
v___x_1777_ = 1;
v___x_1778_ = l_Lean_Meta_mkLambdaFVars(v___x_1774_, v_a_1771_, v___x_1775_, v___x_1776_, v___x_1775_, v___x_1776_, v___x_1777_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
lean_dec_ref(v___x_1774_);
return v___x_1778_;
}
else
{
lean_dec_ref(v_x_1759_);
return v___x_1770_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0___boxed(lean_object* v_body_1779_, lean_object* v_recFnName_1780_, lean_object* v_fixedPrefixSize_1781_, lean_object* v_F_1782_, lean_object* v_x_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0(v_body_1779_, v_recFnName_1780_, v_fixedPrefixSize_1781_, v_F_1782_, v_x_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec_ref(v_body_1779_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1(lean_object* v_body_1794_, lean_object* v_recFnName_1795_, lean_object* v_fixedPrefixSize_1796_, lean_object* v_F_1797_, lean_object* v_x_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1808_ = lean_expr_instantiate1(v_body_1794_, v_x_1798_);
v___x_1809_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1795_, v_fixedPrefixSize_1796_, v_F_1797_, v___x_1808_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_a_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; uint8_t v___x_1814_; uint8_t v___x_1815_; uint8_t v___x_1816_; lean_object* v___x_1817_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
lean_inc(v_a_1810_);
lean_dec_ref_known(v___x_1809_, 1);
v___x_1811_ = lean_unsigned_to_nat(1u);
v___x_1812_ = lean_mk_empty_array_with_capacity(v___x_1811_);
v___x_1813_ = lean_array_push(v___x_1812_, v_x_1798_);
v___x_1814_ = 0;
v___x_1815_ = 1;
v___x_1816_ = 1;
v___x_1817_ = l_Lean_Meta_mkForallFVars(v___x_1813_, v_a_1810_, v___x_1814_, v___x_1815_, v___x_1815_, v___x_1816_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
lean_dec_ref(v___x_1813_);
return v___x_1817_;
}
else
{
lean_dec_ref(v_x_1798_);
return v___x_1809_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1___boxed(lean_object* v_body_1818_, lean_object* v_recFnName_1819_, lean_object* v_fixedPrefixSize_1820_, lean_object* v_F_1821_, lean_object* v_x_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1(v_body_1818_, v_recFnName_1819_, v_fixedPrefixSize_1820_, v_F_1821_, v_x_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v_body_1818_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2___boxed(lean_object* v_body_1833_, lean_object* v_recFnName_1834_, lean_object* v_fixedPrefixSize_1835_, lean_object* v_F_1836_, lean_object* v_x_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2(v_body_1833_, v_recFnName_1834_, v_fixedPrefixSize_1835_, v_F_1836_, v_x_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec(v___y_1838_);
lean_dec_ref(v_x_1837_);
lean_dec_ref(v_body_1833_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(lean_object* v_recFnName_1850_, lean_object* v_fixedPrefixSize_1851_, lean_object* v_F_1852_, size_t v_sz_1853_, size_t v_i_1854_, lean_object* v_bs_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
uint8_t v___x_1865_; 
v___x_1865_ = lean_usize_dec_lt(v_i_1854_, v_sz_1853_);
if (v___x_1865_ == 0)
{
lean_object* v___x_1866_; 
lean_dec_ref(v_F_1852_);
lean_dec(v_fixedPrefixSize_1851_);
lean_dec(v_recFnName_1850_);
v___x_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1866_, 0, v_bs_1855_);
return v___x_1866_;
}
else
{
lean_object* v_v_1867_; lean_object* v___x_1868_; 
v_v_1867_ = lean_array_uget_borrowed(v_bs_1855_, v_i_1854_);
lean_inc(v_v_1867_);
lean_inc_ref(v_F_1852_);
lean_inc(v_fixedPrefixSize_1851_);
lean_inc(v_recFnName_1850_);
v___x_1868_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1850_, v_fixedPrefixSize_1851_, v_F_1852_, v_v_1867_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v_a_1869_; lean_object* v___x_1870_; lean_object* v_bs_x27_1871_; size_t v___x_1872_; size_t v___x_1873_; lean_object* v___x_1874_; 
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
lean_inc(v_a_1869_);
lean_dec_ref_known(v___x_1868_, 1);
v___x_1870_ = lean_unsigned_to_nat(0u);
v_bs_x27_1871_ = lean_array_uset(v_bs_1855_, v_i_1854_, v___x_1870_);
v___x_1872_ = ((size_t)1ULL);
v___x_1873_ = lean_usize_add(v_i_1854_, v___x_1872_);
v___x_1874_ = lean_array_uset(v_bs_x27_1871_, v_i_1854_, v_a_1869_);
v_i_1854_ = v___x_1873_;
v_bs_1855_ = v___x_1874_;
goto _start;
}
else
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1883_; 
lean_dec_ref(v_bs_1855_);
lean_dec_ref(v_F_1852_);
lean_dec(v_fixedPrefixSize_1851_);
lean_dec(v_recFnName_1850_);
v_a_1876_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1878_ = v___x_1868_;
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1868_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1879_ == 0)
{
v___x_1881_ = v___x_1878_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_a_1876_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4(void){
_start:
{
lean_object* v_cls_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v_cls_1891_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_1892_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__3));
v___x_1893_ = l_Lean_Name_append(v___x_1892_, v_cls_1891_);
return v___x_1893_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6(void){
_start:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1895_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5));
v___x_1896_ = l_Lean_stringToMessageData(v___x_1895_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(lean_object* v_recFnName_1897_, lean_object* v_fixedPrefixSize_1898_, lean_object* v_F_1899_, lean_object* v_e_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_){
_start:
{
lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; lean_object* v___y_1918_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; uint8_t v___x_1925_; 
v___x_1922_ = l_Lean_Expr_getAppNumArgs(v_e_1900_);
v___x_1923_ = lean_unsigned_to_nat(1u);
v___x_1924_ = lean_nat_add(v_fixedPrefixSize_1898_, v___x_1923_);
v___x_1925_ = lean_nat_dec_lt(v___x_1922_, v___x_1924_);
if (v___x_1925_ == 0)
{
lean_object* v_dummy_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v_args_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v_dummy_1926_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0);
lean_inc(v___x_1922_);
v___x_1927_ = lean_mk_array(v___x_1922_, v_dummy_1926_);
v___x_1928_ = lean_nat_sub(v___x_1922_, v___x_1923_);
lean_dec(v___x_1922_);
v_args_1929_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1900_, v___x_1927_, v___x_1928_);
v___x_1930_ = l_Lean_instInhabitedExpr;
v___x_1931_ = lean_array_get(v___x_1930_, v_args_1929_, v_fixedPrefixSize_1898_);
lean_inc_ref(v_F_1899_);
lean_inc(v_fixedPrefixSize_1898_);
lean_inc(v_recFnName_1897_);
v___x_1932_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1897_, v_fixedPrefixSize_1898_, v_F_1899_, v___x_1931_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
lean_dec_ref_known(v___x_1932_, 1);
lean_inc_ref(v_F_1899_);
v___x_1934_ = l_Lean_Expr_app___override(v_F_1899_, v_a_1933_);
lean_inc(v_a_1908_);
lean_inc_ref(v_a_1907_);
lean_inc(v_a_1906_);
lean_inc_ref(v_a_1905_);
lean_inc_ref(v___x_1934_);
v___x_1935_ = lean_infer_type(v___x_1934_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; lean_object* v___x_1937_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_a_1936_);
lean_dec_ref_known(v___x_1935_, 1);
lean_inc(v_a_1908_);
lean_inc_ref(v_a_1907_);
lean_inc(v_a_1906_);
lean_inc_ref(v_a_1905_);
v___x_1937_ = lean_whnf(v_a_1936_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v_a_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_a_1938_);
lean_dec_ref_known(v___x_1937_, 1);
v___x_1939_ = l_Lean_Expr_bindingDomain_x21(v_a_1938_);
lean_dec(v_a_1938_);
v___x_1940_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg(v___x_1939_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
if (lean_obj_tag(v___x_1940_) == 0)
{
lean_object* v_a_1941_; lean_object* v___x_1942_; lean_object* v_lower_1944_; lean_object* v_upper_1945_; lean_object* v___x_1969_; lean_object* v___x_1970_; uint8_t v___x_1971_; 
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
lean_inc(v_a_1941_);
lean_dec_ref_known(v___x_1940_, 1);
v___x_1942_ = l_Lean_Expr_app___override(v___x_1934_, v_a_1941_);
v___x_1969_ = lean_unsigned_to_nat(0u);
v___x_1970_ = lean_array_get_size(v_args_1929_);
v___x_1971_ = lean_nat_dec_le(v___x_1924_, v___x_1969_);
if (v___x_1971_ == 0)
{
v_lower_1944_ = v___x_1924_;
v_upper_1945_ = v___x_1970_;
goto v___jp_1943_;
}
else
{
lean_dec(v___x_1924_);
v_lower_1944_ = v___x_1969_;
v_upper_1945_ = v___x_1970_;
goto v___jp_1943_;
}
v___jp_1943_:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; size_t v_sz_1949_; size_t v___x_1950_; lean_object* v___x_1951_; 
v___x_1946_ = l_Array_toSubarray___redArg(v_args_1929_, v_lower_1944_, v_upper_1945_);
v___x_1947_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
v___x_1948_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(v___x_1946_, v___x_1947_);
v_sz_1949_ = lean_array_size(v___x_1948_);
v___x_1950_ = ((size_t)0ULL);
v___x_1951_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_1897_, v_fixedPrefixSize_1898_, v_F_1899_, v_sz_1949_, v___x_1950_, v___x_1948_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1960_; 
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1954_ = v___x_1951_;
v_isShared_1955_ = v_isSharedCheck_1960_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1951_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1960_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1956_; lean_object* v___x_1958_; 
v___x_1956_ = l_Lean_mkAppN(v___x_1942_, v_a_1952_);
lean_dec(v_a_1952_);
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 0, v___x_1956_);
v___x_1958_ = v___x_1954_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1956_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
else
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
lean_dec_ref(v___x_1942_);
v_a_1961_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v___x_1951_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1951_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1961_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1934_);
lean_dec_ref(v_args_1929_);
lean_dec(v___x_1924_);
lean_dec_ref(v_F_1899_);
lean_dec(v_fixedPrefixSize_1898_);
lean_dec(v_recFnName_1897_);
return v___x_1940_;
}
}
else
{
lean_dec_ref(v___x_1934_);
lean_dec_ref(v_args_1929_);
lean_dec(v___x_1924_);
lean_dec_ref(v_F_1899_);
lean_dec(v_fixedPrefixSize_1898_);
lean_dec(v_recFnName_1897_);
return v___x_1937_;
}
}
else
{
lean_dec_ref(v___x_1934_);
lean_dec_ref(v_args_1929_);
lean_dec(v___x_1924_);
lean_dec_ref(v_F_1899_);
lean_dec(v_fixedPrefixSize_1898_);
lean_dec(v_recFnName_1897_);
return v___x_1935_;
}
}
else
{
lean_dec_ref(v_args_1929_);
lean_dec(v___x_1924_);
lean_dec_ref(v_F_1899_);
lean_dec(v_fixedPrefixSize_1898_);
lean_dec(v_recFnName_1897_);
return v___x_1932_;
}
}
else
{
lean_object* v_options_1972_; uint8_t v_hasTrace_1973_; 
lean_dec(v___x_1924_);
lean_dec(v___x_1922_);
v_options_1972_ = lean_ctor_get(v_a_1907_, 2);
v_hasTrace_1973_ = lean_ctor_get_uint8(v_options_1972_, sizeof(void*)*1);
if (v_hasTrace_1973_ == 0)
{
v___y_1911_ = v_a_1901_;
v___y_1912_ = v_a_1902_;
v___y_1913_ = v_a_1903_;
v___y_1914_ = v_a_1904_;
v___y_1915_ = v_a_1905_;
v___y_1916_ = v_a_1906_;
v___y_1917_ = v_a_1907_;
v___y_1918_ = v_a_1908_;
goto v___jp_1910_;
}
else
{
lean_object* v_inheritedTraceOptions_1974_; lean_object* v_cls_1975_; lean_object* v___x_1976_; uint8_t v___x_1977_; 
v_inheritedTraceOptions_1974_ = lean_ctor_get(v_a_1907_, 13);
v_cls_1975_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_1976_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_1977_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1974_, v_options_1972_, v___x_1976_);
if (v___x_1977_ == 0)
{
v___y_1911_ = v_a_1901_;
v___y_1912_ = v_a_1902_;
v___y_1913_ = v_a_1903_;
v___y_1914_ = v_a_1904_;
v___y_1915_ = v_a_1905_;
v___y_1916_ = v_a_1906_;
v___y_1917_ = v_a_1907_;
v___y_1918_ = v_a_1908_;
goto v___jp_1910_;
}
else
{
lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1978_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6);
lean_inc_ref(v_e_1900_);
v___x_1979_ = l_Lean_indentExpr(v_e_1900_);
v___x_1980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1978_);
lean_ctor_set(v___x_1980_, 1, v___x_1979_);
v___x_1981_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(v_cls_1975_, v___x_1980_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_dec_ref_known(v___x_1981_, 1);
v___y_1911_ = v_a_1901_;
v___y_1912_ = v_a_1902_;
v___y_1913_ = v_a_1903_;
v___y_1914_ = v_a_1904_;
v___y_1915_ = v_a_1905_;
v___y_1916_ = v_a_1906_;
v___y_1917_ = v_a_1907_;
v___y_1918_ = v_a_1908_;
goto v___jp_1910_;
}
else
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1989_; 
lean_dec_ref(v_e_1900_);
lean_dec_ref(v_F_1899_);
lean_dec(v_fixedPrefixSize_1898_);
lean_dec(v_recFnName_1897_);
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1984_ = v___x_1981_;
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1981_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1987_; 
if (v_isShared_1985_ == 0)
{
v___x_1987_ = v___x_1984_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_a_1982_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
}
}
}
v___jp_1910_:
{
lean_object* v___x_1919_; 
v___x_1919_ = l_Lean_Meta_etaExpand(v_e_1900_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v___x_1921_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_a_1920_);
lean_dec_ref_known(v___x_1919_, 1);
v___x_1921_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1897_, v_fixedPrefixSize_1898_, v_F_1899_, v_a_1920_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_);
return v___x_1921_;
}
else
{
lean_dec_ref(v_F_1899_);
lean_dec(v_fixedPrefixSize_1898_);
lean_dec(v_recFnName_1897_);
return v___x_1919_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__17(lean_object* v_recFnName_1990_, lean_object* v_fixedPrefixSize_1991_, lean_object* v_F_1992_, lean_object* v_x_1993_, lean_object* v_x_1994_, lean_object* v_x_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
if (lean_obj_tag(v_x_1993_) == 5)
{
lean_object* v_fn_2005_; lean_object* v_arg_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v_fn_2005_ = lean_ctor_get(v_x_1993_, 0);
lean_inc_ref(v_fn_2005_);
v_arg_2006_ = lean_ctor_get(v_x_1993_, 1);
lean_inc_ref(v_arg_2006_);
lean_dec_ref_known(v_x_1993_, 2);
v___x_2007_ = lean_array_set(v_x_1994_, v_x_1995_, v_arg_2006_);
v___x_2008_ = lean_unsigned_to_nat(1u);
v___x_2009_ = lean_nat_sub(v_x_1995_, v___x_2008_);
lean_dec(v_x_1995_);
v_x_1993_ = v_fn_2005_;
v_x_1994_ = v___x_2007_;
v_x_1995_ = v___x_2009_;
goto _start;
}
else
{
lean_object* v___x_2011_; 
lean_dec(v_x_1995_);
lean_inc_ref(v_F_1992_);
lean_inc(v_fixedPrefixSize_1991_);
lean_inc(v_recFnName_1990_);
v___x_2011_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1990_, v_fixedPrefixSize_1991_, v_F_1992_, v_x_1993_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v_a_2012_; size_t v_sz_2013_; size_t v___x_2014_; lean_object* v___x_2015_; 
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_a_2012_);
lean_dec_ref_known(v___x_2011_, 1);
v_sz_2013_ = lean_array_size(v_x_1994_);
v___x_2014_ = ((size_t)0ULL);
v___x_2015_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_1990_, v_fixedPrefixSize_1991_, v_F_1992_, v_sz_2013_, v___x_2014_, v_x_1994_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2024_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2018_ = v___x_2015_;
v_isShared_2019_ = v_isSharedCheck_2024_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_2015_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2024_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2020_; lean_object* v___x_2022_; 
v___x_2020_ = l_Lean_mkAppN(v_a_2012_, v_a_2016_);
lean_dec(v_a_2016_);
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 0, v___x_2020_);
v___x_2022_ = v___x_2018_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2020_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
else
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
lean_dec(v_a_2012_);
v_a_2025_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2027_ = v___x_2015_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_2015_);
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
else
{
lean_dec_ref(v_x_1994_);
lean_dec_ref(v_F_1992_);
lean_dec(v_fixedPrefixSize_1991_);
lean_dec(v_recFnName_1990_);
return v___x_2011_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(lean_object* v_recFnName_2033_, lean_object* v_fixedPrefixSize_2034_, lean_object* v_F_2035_, lean_object* v_e_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_){
_start:
{
uint8_t v___x_2046_; 
v___x_2046_ = l_Lean_Expr_isAppOf(v_e_2036_, v_recFnName_2033_);
if (v___x_2046_ == 0)
{
lean_object* v_dummy_2047_; lean_object* v_nargs_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v_dummy_2047_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0);
v_nargs_2048_ = l_Lean_Expr_getAppNumArgs(v_e_2036_);
lean_inc(v_nargs_2048_);
v___x_2049_ = lean_mk_array(v_nargs_2048_, v_dummy_2047_);
v___x_2050_ = lean_unsigned_to_nat(1u);
v___x_2051_ = lean_nat_sub(v_nargs_2048_, v___x_2050_);
lean_dec(v_nargs_2048_);
v___x_2052_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__17(v_recFnName_2033_, v_fixedPrefixSize_2034_, v_F_2035_, v_e_2036_, v___x_2049_, v___x_2051_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_);
return v___x_2052_;
}
else
{
lean_object* v___x_2053_; 
v___x_2053_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2033_, v_fixedPrefixSize_2034_, v_F_2035_, v_e_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_);
return v___x_2053_;
}
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2055_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__0));
v___x_2056_ = l_Lean_stringToMessageData(v___x_2055_);
return v___x_2056_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2058_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__2));
v___x_2059_ = l_Lean_stringToMessageData(v___x_2058_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0(lean_object* v___x_2060_, lean_object* v_b_2061_, lean_object* v_recFnName_2062_, lean_object* v_fixedPrefixSize_2063_, uint8_t v___x_2064_, lean_object* v___x_2065_, lean_object* v_a_2066_, lean_object* v_e_2067_, lean_object* v_xs_2068_, lean_object* v_altBody_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
lean_object* v___x_2086_; uint8_t v___x_2087_; 
v___x_2086_ = lean_array_get_size(v_xs_2068_);
v___x_2087_ = lean_nat_dec_eq(v___x_2086_, v___x_2065_);
if (v___x_2087_ == 0)
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
lean_dec_ref(v_altBody_2069_);
lean_dec(v_fixedPrefixSize_2063_);
lean_dec(v_recFnName_2062_);
v___x_2088_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__1, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__1_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__1);
v___x_2089_ = l_Lean_indentExpr(v_a_2066_);
v___x_2090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2088_);
lean_ctor_set(v___x_2090_, 1, v___x_2089_);
v___x_2091_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__3, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__3_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___closed__3);
v___x_2092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2090_);
lean_ctor_set(v___x_2092_, 1, v___x_2091_);
v___x_2093_ = l_Lean_indentExpr(v_e_2067_);
v___x_2094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2092_);
lean_ctor_set(v___x_2094_, 1, v___x_2093_);
v___x_2095_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5___redArg(v___x_2094_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_2095_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2095_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
else
{
lean_dec_ref(v_e_2067_);
lean_dec_ref(v_a_2066_);
goto v___jp_2079_;
}
v___jp_2079_:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2080_ = lean_array_get_borrowed(v___x_2060_, v_xs_2068_, v_b_2061_);
lean_inc(v___x_2080_);
v___x_2081_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2062_, v_fixedPrefixSize_2063_, v___x_2080_, v_altBody_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v_a_2082_; uint8_t v___x_2083_; uint8_t v___x_2084_; lean_object* v___x_2085_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_a_2082_);
lean_dec_ref_known(v___x_2081_, 1);
v___x_2083_ = 0;
v___x_2084_ = 1;
v___x_2085_ = l_Lean_Meta_mkLambdaFVars(v_xs_2068_, v_a_2082_, v___x_2083_, v___x_2064_, v___x_2083_, v___x_2064_, v___x_2084_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
return v___x_2085_;
}
else
{
return v___x_2081_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___boxed(lean_object** _args){
lean_object* v___x_2104_ = _args[0];
lean_object* v_b_2105_ = _args[1];
lean_object* v_recFnName_2106_ = _args[2];
lean_object* v_fixedPrefixSize_2107_ = _args[3];
lean_object* v___x_2108_ = _args[4];
lean_object* v___x_2109_ = _args[5];
lean_object* v_a_2110_ = _args[6];
lean_object* v_e_2111_ = _args[7];
lean_object* v_xs_2112_ = _args[8];
lean_object* v_altBody_2113_ = _args[9];
lean_object* v___y_2114_ = _args[10];
lean_object* v___y_2115_ = _args[11];
lean_object* v___y_2116_ = _args[12];
lean_object* v___y_2117_ = _args[13];
lean_object* v___y_2118_ = _args[14];
lean_object* v___y_2119_ = _args[15];
lean_object* v___y_2120_ = _args[16];
lean_object* v___y_2121_ = _args[17];
lean_object* v___y_2122_ = _args[18];
_start:
{
uint8_t v___x_69363__boxed_2123_; lean_object* v_res_2124_; 
v___x_69363__boxed_2123_ = lean_unbox(v___x_2108_);
v_res_2124_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0(v___x_2104_, v_b_2105_, v_recFnName_2106_, v_fixedPrefixSize_2107_, v___x_69363__boxed_2123_, v___x_2109_, v_a_2110_, v_e_2111_, v_xs_2112_, v_altBody_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
lean_dec(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec_ref(v_xs_2112_);
lean_dec(v___x_2109_);
lean_dec(v_b_2105_);
lean_dec_ref(v___x_2104_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15(lean_object* v_recFnName_2125_, lean_object* v_fixedPrefixSize_2126_, lean_object* v_e_2127_, lean_object* v_as_2128_, lean_object* v_bs_2129_, lean_object* v_i_2130_, lean_object* v_cs_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_){
_start:
{
lean_object* v___x_2141_; uint8_t v___x_2142_; 
v___x_2141_ = lean_array_get_size(v_as_2128_);
v___x_2142_ = lean_nat_dec_lt(v_i_2130_, v___x_2141_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2143_; 
lean_dec(v_i_2130_);
lean_dec_ref(v_e_2127_);
lean_dec(v_fixedPrefixSize_2126_);
lean_dec(v_recFnName_2125_);
v___x_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2143_, 0, v_cs_2131_);
return v___x_2143_;
}
else
{
lean_object* v___x_2144_; uint8_t v___x_2145_; 
v___x_2144_ = lean_array_get_size(v_bs_2129_);
v___x_2145_ = lean_nat_dec_lt(v_i_2130_, v___x_2144_);
if (v___x_2145_ == 0)
{
lean_object* v___x_2146_; 
lean_dec(v_i_2130_);
lean_dec_ref(v_e_2127_);
lean_dec(v_fixedPrefixSize_2126_);
lean_dec(v_recFnName_2125_);
v___x_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2146_, 0, v_cs_2131_);
return v___x_2146_;
}
else
{
lean_object* v___x_2147_; lean_object* v_a_2148_; lean_object* v_b_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___f_2153_; uint8_t v___x_2154_; lean_object* v___x_2155_; 
v___x_2147_ = l_Lean_instInhabitedExpr;
v_a_2148_ = lean_array_fget_borrowed(v_as_2128_, v_i_2130_);
v_b_2149_ = lean_array_fget_borrowed(v_bs_2129_, v_i_2130_);
v___x_2150_ = lean_unsigned_to_nat(1u);
v___x_2151_ = lean_nat_add(v_b_2149_, v___x_2150_);
v___x_2152_ = lean_box(v___x_2145_);
lean_inc_ref(v_e_2127_);
lean_inc_n(v_a_2148_, 2);
lean_inc(v___x_2151_);
lean_inc(v_fixedPrefixSize_2126_);
lean_inc(v_recFnName_2125_);
lean_inc(v_b_2149_);
v___f_2153_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___lam__0___boxed), 19, 8);
lean_closure_set(v___f_2153_, 0, v___x_2147_);
lean_closure_set(v___f_2153_, 1, v_b_2149_);
lean_closure_set(v___f_2153_, 2, v_recFnName_2125_);
lean_closure_set(v___f_2153_, 3, v_fixedPrefixSize_2126_);
lean_closure_set(v___f_2153_, 4, v___x_2152_);
lean_closure_set(v___f_2153_, 5, v___x_2151_);
lean_closure_set(v___f_2153_, 6, v_a_2148_);
lean_closure_set(v___f_2153_, 7, v_e_2127_);
v___x_2154_ = 0;
v___x_2155_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___redArg(v_a_2148_, v___x_2151_, v___f_2153_, v___x_2154_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v_a_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
lean_inc(v_a_2156_);
lean_dec_ref_known(v___x_2155_, 1);
v___x_2157_ = lean_nat_add(v_i_2130_, v___x_2150_);
lean_dec(v_i_2130_);
v___x_2158_ = lean_array_push(v_cs_2131_, v_a_2156_);
v_i_2130_ = v___x_2157_;
v_cs_2131_ = v___x_2158_;
goto _start;
}
else
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2167_; 
lean_dec_ref(v_cs_2131_);
lean_dec(v_i_2130_);
lean_dec_ref(v_e_2127_);
lean_dec(v_fixedPrefixSize_2126_);
lean_dec(v_recFnName_2125_);
v_a_2160_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2162_ = v___x_2155_;
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2155_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2165_; 
if (v_isShared_2163_ == 0)
{
v___x_2165_ = v___x_2162_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2160_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(lean_object* v_recFnName_2168_, lean_object* v_fixedPrefixSize_2169_, lean_object* v_F_2170_, lean_object* v_e_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_){
_start:
{
switch(lean_obj_tag(v_e_2171_))
{
case 6:
{
lean_object* v_binderName_2181_; lean_object* v_binderType_2182_; lean_object* v_body_2183_; uint8_t v_binderInfo_2184_; lean_object* v___x_2185_; 
v_binderName_2181_ = lean_ctor_get(v_e_2171_, 0);
lean_inc(v_binderName_2181_);
v_binderType_2182_ = lean_ctor_get(v_e_2171_, 1);
lean_inc_ref(v_binderType_2182_);
v_body_2183_ = lean_ctor_get(v_e_2171_, 2);
lean_inc_ref(v_body_2183_);
v_binderInfo_2184_ = lean_ctor_get_uint8(v_e_2171_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2171_, 3);
lean_inc_ref(v_F_2170_);
lean_inc(v_fixedPrefixSize_2169_);
lean_inc(v_recFnName_2168_);
v___x_2185_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2168_, v_fixedPrefixSize_2169_, v_F_2170_, v_binderType_2182_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v_a_2186_; lean_object* v___f_2187_; uint8_t v___x_2188_; lean_object* v___x_2189_; 
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
lean_inc(v_a_2186_);
lean_dec_ref_known(v___x_2185_, 1);
v___f_2187_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0___boxed), 14, 4);
lean_closure_set(v___f_2187_, 0, v_body_2183_);
lean_closure_set(v___f_2187_, 1, v_recFnName_2168_);
lean_closure_set(v___f_2187_, 2, v_fixedPrefixSize_2169_);
lean_closure_set(v___f_2187_, 3, v_F_2170_);
v___x_2188_ = 0;
v___x_2189_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___redArg(v_binderName_2181_, v_binderInfo_2184_, v_a_2186_, v___f_2187_, v___x_2188_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_);
return v___x_2189_;
}
else
{
lean_dec_ref(v_body_2183_);
lean_dec(v_binderName_2181_);
lean_dec_ref(v_F_2170_);
lean_dec(v_fixedPrefixSize_2169_);
lean_dec(v_recFnName_2168_);
return v___x_2185_;
}
}
case 7:
{
lean_object* v_binderName_2190_; lean_object* v_binderType_2191_; lean_object* v_body_2192_; uint8_t v_binderInfo_2193_; lean_object* v___x_2194_; 
v_binderName_2190_ = lean_ctor_get(v_e_2171_, 0);
lean_inc(v_binderName_2190_);
v_binderType_2191_ = lean_ctor_get(v_e_2171_, 1);
lean_inc_ref(v_binderType_2191_);
v_body_2192_ = lean_ctor_get(v_e_2171_, 2);
lean_inc_ref(v_body_2192_);
v_binderInfo_2193_ = lean_ctor_get_uint8(v_e_2171_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2171_, 3);
lean_inc_ref(v_F_2170_);
lean_inc(v_fixedPrefixSize_2169_);
lean_inc(v_recFnName_2168_);
v___x_2194_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2168_, v_fixedPrefixSize_2169_, v_F_2170_, v_binderType_2191_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; lean_object* v___f_2196_; uint8_t v___x_2197_; lean_object* v___x_2198_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_a_2195_);
lean_dec_ref_known(v___x_2194_, 1);
v___f_2196_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1___boxed), 14, 4);
lean_closure_set(v___f_2196_, 0, v_body_2192_);
lean_closure_set(v___f_2196_, 1, v_recFnName_2168_);
lean_closure_set(v___f_2196_, 2, v_fixedPrefixSize_2169_);
lean_closure_set(v___f_2196_, 3, v_F_2170_);
v___x_2197_ = 0;
v___x_2198_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___redArg(v_binderName_2190_, v_binderInfo_2193_, v_a_2195_, v___f_2196_, v___x_2197_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_);
return v___x_2198_;
}
else
{
lean_dec_ref(v_body_2192_);
lean_dec(v_binderName_2190_);
lean_dec_ref(v_F_2170_);
lean_dec(v_fixedPrefixSize_2169_);
lean_dec(v_recFnName_2168_);
return v___x_2194_;
}
}
case 8:
{
lean_object* v_declName_2199_; lean_object* v_type_2200_; lean_object* v_value_2201_; lean_object* v_body_2202_; uint8_t v_nondep_2203_; lean_object* v___x_2204_; 
v_declName_2199_ = lean_ctor_get(v_e_2171_, 0);
lean_inc(v_declName_2199_);
v_type_2200_ = lean_ctor_get(v_e_2171_, 1);
lean_inc_ref(v_type_2200_);
v_value_2201_ = lean_ctor_get(v_e_2171_, 2);
lean_inc_ref(v_value_2201_);
v_body_2202_ = lean_ctor_get(v_e_2171_, 3);
lean_inc_ref(v_body_2202_);
v_nondep_2203_ = lean_ctor_get_uint8(v_e_2171_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2171_, 4);
lean_inc_ref(v_F_2170_);
lean_inc(v_fixedPrefixSize_2169_);
lean_inc(v_recFnName_2168_);
v___x_2204_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2168_, v_fixedPrefixSize_2169_, v_F_2170_, v_type_2200_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2205_; lean_object* v___x_2206_; 
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
lean_inc(v_a_2205_);
lean_dec_ref_known(v___x_2204_, 1);
lean_inc_ref(v_F_2170_);
lean_inc(v_fixedPrefixSize_2169_);
lean_inc(v_recFnName_2168_);
v___x_2206_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2168_, v_fixedPrefixSize_2169_, v_F_2170_, v_value_2201_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_object* v_a_2207_; lean_object* v___f_2208_; uint8_t v___x_2209_; uint8_t v___x_2210_; lean_object* v___x_2211_; 
v_a_2207_ = lean_ctor_get(v___x_2206_, 0);
lean_inc(v_a_2207_);
lean_dec_ref_known(v___x_2206_, 1);
v___f_2208_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2___boxed), 14, 4);
lean_closure_set(v___f_2208_, 0, v_body_2202_);
lean_closure_set(v___f_2208_, 1, v_recFnName_2168_);
lean_closure_set(v___f_2208_, 2, v_fixedPrefixSize_2169_);
lean_closure_set(v___f_2208_, 3, v_F_2170_);
v___x_2209_ = 0;
v___x_2210_ = 0;
v___x_2211_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(v_declName_2199_, v_a_2205_, v_a_2207_, v___f_2208_, v_nondep_2203_, v___x_2209_, v___x_2210_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_);
return v___x_2211_;
}
else
{
lean_dec(v_a_2205_);
lean_dec_ref(v_body_2202_);
lean_dec(v_declName_2199_);
lean_dec_ref(v_F_2170_);
lean_dec(v_fixedPrefixSize_2169_);
lean_dec(v_recFnName_2168_);
return v___x_2206_;
}
}
else
{
lean_dec_ref(v_body_2202_);
lean_dec_ref(v_value_2201_);
lean_dec(v_declName_2199_);
lean_dec_ref(v_F_2170_);
lean_dec(v_fixedPrefixSize_2169_);
lean_dec(v_recFnName_2168_);
return v___x_2204_;
}
}
case 10:
{
lean_object* v_data_2212_; lean_object* v_expr_2213_; lean_object* v___x_2214_; 
v_data_2212_ = lean_ctor_get(v_e_2171_, 0);
lean_inc(v_data_2212_);
v_expr_2213_ = lean_ctor_get(v_e_2171_, 1);
lean_inc_ref(v_expr_2213_);
v___x_2214_ = l_Lean_getRecAppSyntax_x3f(v_e_2171_);
lean_dec_ref_known(v_e_2171_, 2);
if (lean_obj_tag(v___x_2214_) == 1)
{
lean_object* v_val_2215_; lean_object* v_fileName_2216_; lean_object* v_fileMap_2217_; lean_object* v_options_2218_; lean_object* v_currRecDepth_2219_; lean_object* v_maxRecDepth_2220_; lean_object* v_ref_2221_; lean_object* v_currNamespace_2222_; lean_object* v_openDecls_2223_; lean_object* v_initHeartbeats_2224_; lean_object* v_maxHeartbeats_2225_; lean_object* v_quotContext_2226_; lean_object* v_currMacroScope_2227_; uint8_t v_diag_2228_; lean_object* v_cancelTk_x3f_2229_; uint8_t v_suppressElabErrors_2230_; lean_object* v_inheritedTraceOptions_2231_; lean_object* v_ref_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
lean_dec(v_data_2212_);
v_val_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_val_2215_);
lean_dec_ref_known(v___x_2214_, 1);
v_fileName_2216_ = lean_ctor_get(v_a_2178_, 0);
v_fileMap_2217_ = lean_ctor_get(v_a_2178_, 1);
v_options_2218_ = lean_ctor_get(v_a_2178_, 2);
v_currRecDepth_2219_ = lean_ctor_get(v_a_2178_, 3);
v_maxRecDepth_2220_ = lean_ctor_get(v_a_2178_, 4);
v_ref_2221_ = lean_ctor_get(v_a_2178_, 5);
v_currNamespace_2222_ = lean_ctor_get(v_a_2178_, 6);
v_openDecls_2223_ = lean_ctor_get(v_a_2178_, 7);
v_initHeartbeats_2224_ = lean_ctor_get(v_a_2178_, 8);
v_maxHeartbeats_2225_ = lean_ctor_get(v_a_2178_, 9);
v_quotContext_2226_ = lean_ctor_get(v_a_2178_, 10);
v_currMacroScope_2227_ = lean_ctor_get(v_a_2178_, 11);
v_diag_2228_ = lean_ctor_get_uint8(v_a_2178_, sizeof(void*)*14);
v_cancelTk_x3f_2229_ = lean_ctor_get(v_a_2178_, 12);
v_suppressElabErrors_2230_ = lean_ctor_get_uint8(v_a_2178_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2231_ = lean_ctor_get(v_a_2178_, 13);
v_ref_2232_ = l_Lean_replaceRef(v_val_2215_, v_ref_2221_);
lean_dec(v_val_2215_);
lean_inc_ref(v_inheritedTraceOptions_2231_);
lean_inc(v_cancelTk_x3f_2229_);
lean_inc(v_currMacroScope_2227_);
lean_inc(v_quotContext_2226_);
lean_inc(v_maxHeartbeats_2225_);
lean_inc(v_initHeartbeats_2224_);
lean_inc(v_openDecls_2223_);
lean_inc(v_currNamespace_2222_);
lean_inc(v_maxRecDepth_2220_);
lean_inc(v_currRecDepth_2219_);
lean_inc_ref(v_options_2218_);
lean_inc_ref(v_fileMap_2217_);
lean_inc_ref(v_fileName_2216_);
v___x_2233_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2233_, 0, v_fileName_2216_);
lean_ctor_set(v___x_2233_, 1, v_fileMap_2217_);
lean_ctor_set(v___x_2233_, 2, v_options_2218_);
lean_ctor_set(v___x_2233_, 3, v_currRecDepth_2219_);
lean_ctor_set(v___x_2233_, 4, v_maxRecDepth_2220_);
lean_ctor_set(v___x_2233_, 5, v_ref_2232_);
lean_ctor_set(v___x_2233_, 6, v_currNamespace_2222_);
lean_ctor_set(v___x_2233_, 7, v_openDecls_2223_);
lean_ctor_set(v___x_2233_, 8, v_initHeartbeats_2224_);
lean_ctor_set(v___x_2233_, 9, v_maxHeartbeats_2225_);
lean_ctor_set(v___x_2233_, 10, v_quotContext_2226_);
lean_ctor_set(v___x_2233_, 11, v_currMacroScope_2227_);
lean_ctor_set(v___x_2233_, 12, v_cancelTk_x3f_2229_);
lean_ctor_set(v___x_2233_, 13, v_inheritedTraceOptions_2231_);
lean_ctor_set_uint8(v___x_2233_, sizeof(void*)*14, v_diag_2228_);
lean_ctor_set_uint8(v___x_2233_, sizeof(void*)*14 + 1, v_suppressElabErrors_2230_);
v___x_2234_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2168_, v_fixedPrefixSize_2169_, v_F_2170_, v_expr_2213_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v___x_2233_, v_a_2179_);
lean_dec_ref_known(v___x_2233_, 14);
return v___x_2234_;
}
else
{
lean_object* v___x_2235_; 
lean_dec(v___x_2214_);
v___x_2235_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2168_, v_fixedPrefixSize_2169_, v_F_2170_, v_expr_2213_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2244_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2238_ = v___x_2235_;
v_isShared_2239_ = v_isSharedCheck_2244_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2235_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2244_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2240_; lean_object* v___x_2242_; 
v___x_2240_ = l_Lean_mkMData(v_data_2212_, v_a_2236_);
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 0, v___x_2240_);
v___x_2242_ = v___x_2238_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2240_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
else
{
lean_dec(v_data_2212_);
return v___x_2235_;
}
}
}
case 11:
{
lean_object* v_typeName_2245_; lean_object* v_idx_2246_; lean_object* v_struct_2247_; lean_object* v___x_2248_; 
v_typeName_2245_ = lean_ctor_get(v_e_2171_, 0);
lean_inc(v_typeName_2245_);
v_idx_2246_ = lean_ctor_get(v_e_2171_, 1);
lean_inc(v_idx_2246_);
v_struct_2247_ = lean_ctor_get(v_e_2171_, 2);
lean_inc_ref(v_struct_2247_);
lean_dec_ref_known(v_e_2171_, 3);
v___x_2248_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2168_, v_fixedPrefixSize_2169_, v_F_2170_, v_struct_2247_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_);
if (lean_obj_tag(v___x_2248_) == 0)
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2257_; 
v_a_2249_ = lean_ctor_get(v___x_2248_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2251_ = v___x_2248_;
v_isShared_2252_ = v_isSharedCheck_2257_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2248_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2257_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2253_; lean_object* v___x_2255_; 
v___x_2253_ = l_Lean_mkProj(v_typeName_2245_, v_idx_2246_, v_a_2249_);
if (v_isShared_2252_ == 0)
{
lean_ctor_set(v___x_2251_, 0, v___x_2253_);
v___x_2255_ = v___x_2251_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v___x_2253_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
else
{
lean_dec(v_idx_2246_);
lean_dec(v_typeName_2245_);
return v___x_2248_;
}
}
case 4:
{
uint8_t v___x_2258_; 
v___x_2258_ = l_Lean_Expr_isConstOf(v_e_2171_, v_recFnName_2168_);
if (v___x_2258_ == 0)
{
lean_object* v___x_2259_; 
lean_dec_ref(v_F_2170_);
lean_dec(v_fixedPrefixSize_2169_);
lean_dec(v_recFnName_2168_);
v___x_2259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2259_, 0, v_e_2171_);
return v___x_2259_;
}
else
{
lean_object* v___x_2260_; 
v___x_2260_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2168_, v_fixedPrefixSize_2169_, v_F_2170_, v_e_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_);
return v___x_2260_;
}
}
case 5:
{
uint8_t v___x_2261_; lean_object* v___x_2262_; 
v___x_2261_ = 1;
lean_inc_ref(v_e_2171_);
v___x_2262_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(v_e_2171_, v___x_2261_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_);
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v_a_2263_; 
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
lean_inc(v_a_2263_);
lean_dec_ref_known(v___x_2262_, 1);
if (lean_obj_tag(v_a_2263_) == 0)
{
lean_object* v___x_2264_; 
v___x_2264_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2168_, v_fixedPrefixSize_2169_, v_F_2170_, v_e_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_);
return v___x_2264_;
}
else
{
lean_object* v_val_2265_; lean_object* v___x_2266_; 
v_val_2265_ = lean_ctor_get(v_a_2263_, 0);
lean_inc(v_val_2265_);
lean_dec_ref_known(v_a_2263_, 1);
lean_inc_ref(v_F_2170_);
v___x_2266_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_val_2265_, v_F_2170_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v_a_2267_; 
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
lean_inc(v_a_2267_);
lean_dec_ref_known(v___x_2266_, 1);
if (lean_obj_tag(v_a_2267_) == 1)
{
lean_object* v_val_2268_; lean_object* v_toMatcherInfo_2269_; lean_object* v_matcherName_2270_; lean_object* v_matcherLevels_2271_; lean_object* v_params_2272_; lean_object* v_motive_2273_; lean_object* v_discrs_2274_; lean_object* v_alts_2275_; lean_object* v_remaining_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v_val_2268_ = lean_ctor_get(v_a_2267_, 0);
lean_inc(v_val_2268_);
lean_dec_ref_known(v_a_2267_, 1);
v_toMatcherInfo_2269_ = lean_ctor_get(v_val_2268_, 0);
lean_inc_ref(v_toMatcherInfo_2269_);
v_matcherName_2270_ = lean_ctor_get(v_val_2268_, 1);
lean_inc(v_matcherName_2270_);
v_matcherLevels_2271_ = lean_ctor_get(v_val_2268_, 2);
lean_inc_ref(v_matcherLevels_2271_);
v_params_2272_ = lean_ctor_get(v_val_2268_, 3);
lean_inc_ref(v_params_2272_);
v_motive_2273_ = lean_ctor_get(v_val_2268_, 4);
lean_inc_ref(v_motive_2273_);
v_discrs_2274_ = lean_ctor_get(v_val_2268_, 5);
lean_inc_ref(v_discrs_2274_);
v_alts_2275_ = lean_ctor_get(v_val_2268_, 6);
lean_inc_ref(v_alts_2275_);
v_remaining_2276_ = lean_ctor_get(v_val_2268_, 7);
lean_inc_ref(v_remaining_2276_);
v___x_2277_ = l_Lean_Meta_MatcherApp_altNumParams(v_val_2268_);
v___x_2278_ = lean_unsigned_to_nat(0u);
v___x_2279_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
lean_inc(v_fixedPrefixSize_2169_);
lean_inc(v_recFnName_2168_);
v___x_2280_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15(v_recFnName_2168_, v_fixedPrefixSize_2169_, v_e_2171_, v_alts_2275_, v___x_2277_, v___x_2278_, v___x_2279_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_);
lean_dec_ref(v___x_2277_);
lean_dec_ref(v_alts_2275_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_object* v_a_2281_; size_t v_sz_2282_; size_t v___x_2283_; lean_object* v___x_2284_; 
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
lean_inc(v_a_2281_);
lean_dec_ref_known(v___x_2280_, 1);
v_sz_2282_ = lean_array_size(v_discrs_2274_);
v___x_2283_ = ((size_t)0ULL);
v___x_2284_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_2168_, v_fixedPrefixSize_2169_, v_F_2170_, v_sz_2282_, v___x_2283_, v_discrs_2274_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2294_; 
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2287_ = v___x_2284_;
v_isShared_2288_ = v_isSharedCheck_2294_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2284_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2294_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2292_; 
v___x_2289_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2289_, 0, v_toMatcherInfo_2269_);
lean_ctor_set(v___x_2289_, 1, v_matcherName_2270_);
lean_ctor_set(v___x_2289_, 2, v_matcherLevels_2271_);
lean_ctor_set(v___x_2289_, 3, v_params_2272_);
lean_ctor_set(v___x_2289_, 4, v_motive_2273_);
lean_ctor_set(v___x_2289_, 5, v_a_2285_);
lean_ctor_set(v___x_2289_, 6, v_a_2281_);
lean_ctor_set(v___x_2289_, 7, v_remaining_2276_);
v___x_2290_ = l_Lean_Meta_MatcherApp_toExpr(v___x_2289_);
if (v_isShared_2288_ == 0)
{
lean_ctor_set(v___x_2287_, 0, v___x_2290_);
v___x_2292_ = v___x_2287_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v___x_2290_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
else
{
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2302_; 
lean_dec(v_a_2281_);
lean_dec_ref(v_remaining_2276_);
lean_dec_ref(v_motive_2273_);
lean_dec_ref(v_params_2272_);
lean_dec_ref(v_matcherLevels_2271_);
lean_dec(v_matcherName_2270_);
lean_dec_ref(v_toMatcherInfo_2269_);
v_a_2295_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2297_ = v___x_2284_;
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___x_2284_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2300_; 
if (v_isShared_2298_ == 0)
{
v___x_2300_ = v___x_2297_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_a_2295_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
else
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2310_; 
lean_dec_ref(v_remaining_2276_);
lean_dec_ref(v_discrs_2274_);
lean_dec_ref(v_motive_2273_);
lean_dec_ref(v_params_2272_);
lean_dec_ref(v_matcherLevels_2271_);
lean_dec(v_matcherName_2270_);
lean_dec_ref(v_toMatcherInfo_2269_);
lean_dec_ref(v_F_2170_);
lean_dec(v_fixedPrefixSize_2169_);
lean_dec(v_recFnName_2168_);
v_a_2303_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2305_ = v___x_2280_;
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2280_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2308_; 
if (v_isShared_2306_ == 0)
{
v___x_2308_ = v___x_2305_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2303_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
}
else
{
lean_object* v___x_2311_; 
lean_dec(v_a_2267_);
v___x_2311_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2168_, v_fixedPrefixSize_2169_, v_F_2170_, v_e_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_);
return v___x_2311_;
}
}
else
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2319_; 
lean_dec_ref_known(v_e_2171_, 2);
lean_dec_ref(v_F_2170_);
lean_dec(v_fixedPrefixSize_2169_);
lean_dec(v_recFnName_2168_);
v_a_2312_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2314_ = v___x_2266_;
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___x_2266_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2317_; 
if (v_isShared_2315_ == 0)
{
v___x_2317_ = v___x_2314_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_a_2312_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
}
}
else
{
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2327_; 
lean_dec_ref_known(v_e_2171_, 2);
lean_dec_ref(v_F_2170_);
lean_dec(v_fixedPrefixSize_2169_);
lean_dec(v_recFnName_2168_);
v_a_2320_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2322_ = v___x_2262_;
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v___x_2262_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2325_; 
if (v_isShared_2323_ == 0)
{
v___x_2325_ = v___x_2322_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_a_2320_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
}
default: 
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
lean_dec_ref(v_F_2170_);
lean_dec(v_fixedPrefixSize_2169_);
v___x_2328_ = lean_unsigned_to_nat(1u);
v___x_2329_ = lean_mk_empty_array_with_capacity(v___x_2328_);
v___x_2330_ = lean_array_push(v___x_2329_, v_recFnName_2168_);
lean_inc_ref(v_e_2171_);
v___x_2331_ = l_Lean_Elab_ensureNoRecFn(v___x_2330_, v_e_2171_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2338_; 
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2338_ == 0)
{
lean_object* v_unused_2339_; 
v_unused_2339_ = lean_ctor_get(v___x_2331_, 0);
lean_dec(v_unused_2339_);
v___x_2333_ = v___x_2331_;
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
else
{
lean_dec(v___x_2331_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2336_; 
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 0, v_e_2171_);
v___x_2336_ = v___x_2333_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_e_2171_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
}
}
}
else
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
lean_dec_ref(v_e_2171_);
v_a_2340_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2331_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2331_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(lean_object* v_recFnName_2348_, lean_object* v_fixedPrefixSize_2349_, lean_object* v_F_2350_, lean_object* v_e_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_){
_start:
{
lean_object* v___x_2361_; 
lean_inc_ref(v_e_2351_);
lean_inc(v_recFnName_2348_);
v___x_2361_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___redArg(v_recFnName_2348_, v_e_2351_, v_a_2352_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2585_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2364_ = v___x_2361_;
v_isShared_2365_ = v_isSharedCheck_2585_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2361_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2585_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
uint8_t v___x_2366_; 
v___x_2366_ = lean_unbox(v_a_2362_);
lean_dec(v_a_2362_);
if (v___x_2366_ == 0)
{
lean_object* v___x_2368_; 
lean_dec_ref(v_F_2350_);
lean_dec(v_fixedPrefixSize_2349_);
lean_dec(v_recFnName_2348_);
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 0, v_e_2351_);
v___x_2368_ = v___x_2364_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_e_2351_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
else
{
lean_object* v___x_2370_; uint8_t v___x_2371_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2431_; lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v___y_2434_; lean_object* v___y_2435_; lean_object* v___y_2436_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v_i_2443_; lean_object* v___y_2449_; lean_object* v___y_2450_; lean_object* v___y_2451_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v___y_2475_; lean_object* v___y_2476_; lean_object* v___y_2477_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2481_; lean_object* v___y_2482_; lean_object* v_i_2483_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2517_; lean_object* v___x_2563_; 
v___x_2370_ = lean_st_ref_get(v_a_2353_);
v___x_2371_ = 0;
v___x_2563_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9___redArg(v___x_2370_, v_e_2351_);
lean_dec(v___x_2370_);
if (lean_obj_tag(v___x_2563_) == 1)
{
lean_object* v_val_2564_; lean_object* v_fst_2565_; lean_object* v_snd_2566_; lean_object* v___x_2567_; 
v_val_2564_ = lean_ctor_get(v___x_2563_, 0);
lean_inc(v_val_2564_);
lean_dec_ref_known(v___x_2563_, 1);
v_fst_2565_ = lean_ctor_get(v_val_2564_, 0);
lean_inc(v_fst_2565_);
v_snd_2566_ = lean_ctor_get(v_val_2564_, 1);
lean_inc(v_snd_2566_);
lean_dec(v_val_2564_);
v___x_2567_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___redArg(v_snd_2566_, v_a_2356_);
lean_dec(v_snd_2566_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2576_; 
v_a_2568_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2570_ = v___x_2567_;
v_isShared_2571_ = v_isSharedCheck_2576_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2567_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2576_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
uint8_t v___x_2572_; 
v___x_2572_ = lean_unbox(v_a_2568_);
lean_dec(v_a_2568_);
if (v___x_2572_ == 0)
{
lean_del_object(v___x_2570_);
lean_dec(v_fst_2565_);
v___y_2510_ = v_a_2352_;
v___y_2511_ = v_a_2353_;
v___y_2512_ = v_a_2354_;
v___y_2513_ = v_a_2355_;
v___y_2514_ = v_a_2356_;
v___y_2515_ = v_a_2357_;
v___y_2516_ = v_a_2358_;
v___y_2517_ = v_a_2359_;
goto v___jp_2509_;
}
else
{
lean_object* v___x_2574_; 
lean_del_object(v___x_2364_);
lean_dec_ref(v_e_2351_);
lean_dec_ref(v_F_2350_);
lean_dec(v_fixedPrefixSize_2349_);
lean_dec(v_recFnName_2348_);
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 0, v_fst_2565_);
v___x_2574_ = v___x_2570_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_fst_2565_);
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
else
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2584_; 
lean_dec(v_fst_2565_);
lean_del_object(v___x_2364_);
lean_dec_ref(v_e_2351_);
lean_dec_ref(v_F_2350_);
lean_dec(v_fixedPrefixSize_2349_);
lean_dec(v_recFnName_2348_);
v_a_2577_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2579_ = v___x_2567_;
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2567_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2582_; 
if (v_isShared_2580_ == 0)
{
v___x_2582_ = v___x_2579_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_a_2577_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
else
{
lean_dec(v___x_2563_);
v___y_2510_ = v_a_2352_;
v___y_2511_ = v_a_2353_;
v___y_2512_ = v_a_2354_;
v___y_2513_ = v_a_2355_;
v___y_2514_ = v_a_2356_;
v___y_2515_ = v_a_2357_;
v___y_2516_ = v_a_2358_;
v___y_2517_ = v_a_2359_;
goto v___jp_2509_;
}
v___jp_2372_:
{
lean_object* v___x_2384_; lean_object* v_options_2385_; lean_object* v___x_2386_; uint8_t v___x_2387_; 
v___x_2384_ = lean_st_ref_put(v___y_2374_, v___y_2383_);
v_options_2385_ = lean_ctor_get(v___y_2377_, 2);
v___x_2386_ = l_Lean_Elab_WF_debug_definition_wf_replaceRecApps;
v___x_2387_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4(v_options_2385_, v___x_2386_);
if (v___x_2387_ == 0)
{
lean_object* v___x_2389_; 
lean_dec_ref(v___y_2373_);
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 0, v___y_2375_);
v___x_2389_ = v___x_2364_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v___y_2375_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
else
{
lean_object* v_keyedConfig_2391_; uint8_t v_trackZetaDelta_2392_; lean_object* v_zetaDeltaSet_2393_; lean_object* v_lctx_2394_; lean_object* v_localInstances_2395_; lean_object* v_defEqCtx_x3f_2396_; lean_object* v_synthPendingDepth_2397_; lean_object* v_customCanUnfoldPredicate_x3f_2398_; uint8_t v_univApprox_2399_; uint8_t v_inTypeClassResolution_2400_; uint8_t v_cacheInferType_2401_; uint8_t v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
lean_del_object(v___x_2364_);
v_keyedConfig_2391_ = lean_ctor_get(v___y_2378_, 0);
v_trackZetaDelta_2392_ = lean_ctor_get_uint8(v___y_2378_, sizeof(void*)*7);
v_zetaDeltaSet_2393_ = lean_ctor_get(v___y_2378_, 1);
v_lctx_2394_ = lean_ctor_get(v___y_2378_, 2);
v_localInstances_2395_ = lean_ctor_get(v___y_2378_, 3);
v_defEqCtx_x3f_2396_ = lean_ctor_get(v___y_2378_, 4);
v_synthPendingDepth_2397_ = lean_ctor_get(v___y_2378_, 5);
v_customCanUnfoldPredicate_x3f_2398_ = lean_ctor_get(v___y_2378_, 6);
v_univApprox_2399_ = lean_ctor_get_uint8(v___y_2378_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2400_ = lean_ctor_get_uint8(v___y_2378_, sizeof(void*)*7 + 2);
v_cacheInferType_2401_ = lean_ctor_get_uint8(v___y_2378_, sizeof(void*)*7 + 3);
v___x_2402_ = 0;
lean_inc_ref(v_keyedConfig_2391_);
v___x_2403_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2402_, v_keyedConfig_2391_);
lean_inc(v_customCanUnfoldPredicate_x3f_2398_);
lean_inc(v_synthPendingDepth_2397_);
lean_inc(v_defEqCtx_x3f_2396_);
lean_inc_ref(v_localInstances_2395_);
lean_inc_ref(v_lctx_2394_);
lean_inc(v_zetaDeltaSet_2393_);
v___x_2404_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2404_, 0, v___x_2403_);
lean_ctor_set(v___x_2404_, 1, v_zetaDeltaSet_2393_);
lean_ctor_set(v___x_2404_, 2, v_lctx_2394_);
lean_ctor_set(v___x_2404_, 3, v_localInstances_2395_);
lean_ctor_set(v___x_2404_, 4, v_defEqCtx_x3f_2396_);
lean_ctor_set(v___x_2404_, 5, v_synthPendingDepth_2397_);
lean_ctor_set(v___x_2404_, 6, v_customCanUnfoldPredicate_x3f_2398_);
lean_ctor_set_uint8(v___x_2404_, sizeof(void*)*7, v_trackZetaDelta_2392_);
lean_ctor_set_uint8(v___x_2404_, sizeof(void*)*7 + 1, v_univApprox_2399_);
lean_ctor_set_uint8(v___x_2404_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2400_);
lean_ctor_set_uint8(v___x_2404_, sizeof(void*)*7 + 3, v_cacheInferType_2401_);
v___x_2405_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v___y_2373_, v___x_2371_, v___y_2381_, v___y_2374_, v___y_2380_, v___y_2379_, v___x_2404_, v___y_2382_, v___y_2377_, v___y_2376_);
lean_dec_ref_known(v___x_2404_, 7);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2412_; 
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2412_ == 0)
{
lean_object* v_unused_2413_; 
v_unused_2413_ = lean_ctor_get(v___x_2405_, 0);
lean_dec(v_unused_2413_);
v___x_2407_ = v___x_2405_;
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
else
{
lean_dec(v___x_2405_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v___x_2410_; 
if (v_isShared_2408_ == 0)
{
lean_ctor_set(v___x_2407_, 0, v___y_2375_);
v___x_2410_ = v___x_2407_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v___y_2375_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
else
{
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2420_; 
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2420_ == 0)
{
lean_object* v_unused_2421_; 
v_unused_2421_ = lean_ctor_get(v___x_2405_, 0);
lean_dec(v_unused_2421_);
v___x_2415_ = v___x_2405_;
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
else
{
lean_dec(v___x_2405_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2418_; 
if (v_isShared_2416_ == 0)
{
lean_ctor_set_tag(v___x_2415_, 0);
lean_ctor_set(v___x_2415_, 0, v___y_2375_);
v___x_2418_ = v___x_2415_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v___y_2375_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
else
{
lean_object* v_a_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2429_; 
lean_dec_ref(v___y_2375_);
v_a_2422_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2424_ = v___x_2405_;
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_a_2422_);
lean_dec(v___x_2405_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2427_; 
if (v_isShared_2425_ == 0)
{
v___x_2427_ = v___x_2424_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_a_2422_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
}
}
}
v___jp_2430_:
{
lean_object* v_size_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
v_size_2444_ = lean_ctor_get(v___y_2440_, 0);
v___x_2445_ = lean_unsigned_to_nat(1u);
v___x_2446_ = lean_nat_add(v_size_2444_, v___x_2445_);
v___x_2447_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2440_, v___x_2446_, v_i_2443_, v_e_2351_, v___y_2439_);
lean_dec(v_i_2443_);
v___y_2373_ = v___y_2431_;
v___y_2374_ = v___y_2432_;
v___y_2375_ = v___y_2433_;
v___y_2376_ = v___y_2434_;
v___y_2377_ = v___y_2435_;
v___y_2378_ = v___y_2436_;
v___y_2379_ = v___y_2437_;
v___y_2380_ = v___y_2438_;
v___y_2381_ = v___y_2441_;
v___y_2382_ = v___y_2442_;
v___y_2383_ = v___x_2447_;
goto v___jp_2372_;
}
v___jp_2448_:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2461_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v___y_2459_);
lean_dec_ref(v___y_2459_);
v___x_2462_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v___x_2461_, v_e_2351_);
switch(lean_obj_tag(v___x_2462_))
{
case 0:
{
lean_object* v_index_2463_; lean_object* v_size_2464_; lean_object* v___x_2465_; 
v_index_2463_ = lean_ctor_get(v___x_2462_, 0);
lean_inc(v_index_2463_);
lean_dec_ref_known(v___x_2462_, 3);
v_size_2464_ = lean_ctor_get(v___x_2461_, 0);
lean_inc(v_size_2464_);
v___x_2465_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2461_, v_size_2464_, v_index_2463_, v_e_2351_, v___y_2457_);
lean_dec(v_index_2463_);
v___y_2373_ = v___y_2449_;
v___y_2374_ = v___y_2450_;
v___y_2375_ = v___y_2451_;
v___y_2376_ = v___y_2452_;
v___y_2377_ = v___y_2453_;
v___y_2378_ = v___y_2454_;
v___y_2379_ = v___y_2455_;
v___y_2380_ = v___y_2456_;
v___y_2381_ = v___y_2458_;
v___y_2382_ = v___y_2460_;
v___y_2383_ = v___x_2465_;
goto v___jp_2372_;
}
case 1:
{
lean_object* v_index_2466_; 
v_index_2466_ = lean_ctor_get(v___x_2462_, 0);
lean_inc(v_index_2466_);
lean_dec_ref_known(v___x_2462_, 1);
v___y_2431_ = v___y_2449_;
v___y_2432_ = v___y_2450_;
v___y_2433_ = v___y_2451_;
v___y_2434_ = v___y_2452_;
v___y_2435_ = v___y_2453_;
v___y_2436_ = v___y_2454_;
v___y_2437_ = v___y_2455_;
v___y_2438_ = v___y_2456_;
v___y_2439_ = v___y_2457_;
v___y_2440_ = v___x_2461_;
v___y_2441_ = v___y_2458_;
v___y_2442_ = v___y_2460_;
v_i_2443_ = v_index_2466_;
goto v___jp_2430_;
}
default: 
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2467_ = lean_unsigned_to_nat(0u);
v___x_2468_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2461_, v___x_2467_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_object* v_index_2469_; 
v_index_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc(v_index_2469_);
lean_dec_ref_known(v___x_2468_, 1);
v___y_2431_ = v___y_2449_;
v___y_2432_ = v___y_2450_;
v___y_2433_ = v___y_2451_;
v___y_2434_ = v___y_2452_;
v___y_2435_ = v___y_2453_;
v___y_2436_ = v___y_2454_;
v___y_2437_ = v___y_2455_;
v___y_2438_ = v___y_2456_;
v___y_2439_ = v___y_2457_;
v___y_2440_ = v___x_2461_;
v___y_2441_ = v___y_2458_;
v___y_2442_ = v___y_2460_;
v_i_2443_ = v_index_2469_;
goto v___jp_2430_;
}
else
{
lean_dec_ref(v___y_2457_);
lean_dec_ref(v_e_2351_);
v___y_2373_ = v___y_2449_;
v___y_2374_ = v___y_2450_;
v___y_2375_ = v___y_2451_;
v___y_2376_ = v___y_2452_;
v___y_2377_ = v___y_2453_;
v___y_2378_ = v___y_2454_;
v___y_2379_ = v___y_2455_;
v___y_2380_ = v___y_2456_;
v___y_2381_ = v___y_2458_;
v___y_2382_ = v___y_2460_;
v___y_2383_ = v___x_2461_;
goto v___jp_2372_;
}
}
}
}
v___jp_2470_:
{
lean_object* v_size_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; 
v_size_2484_ = lean_ctor_get(v___y_2479_, 0);
v___x_2485_ = lean_unsigned_to_nat(1u);
v___x_2486_ = lean_nat_add(v_size_2484_, v___x_2485_);
v___x_2487_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2479_, v___x_2486_, v_i_2483_, v_e_2351_, v___y_2480_);
lean_dec(v_i_2483_);
v___y_2373_ = v___y_2471_;
v___y_2374_ = v___y_2472_;
v___y_2375_ = v___y_2473_;
v___y_2376_ = v___y_2474_;
v___y_2377_ = v___y_2475_;
v___y_2378_ = v___y_2476_;
v___y_2379_ = v___y_2477_;
v___y_2380_ = v___y_2478_;
v___y_2381_ = v___y_2481_;
v___y_2382_ = v___y_2482_;
v___y_2383_ = v___x_2487_;
goto v___jp_2372_;
}
v___jp_2488_:
{
lean_object* v___x_2501_; 
v___x_2501_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v___y_2500_, v_e_2351_);
switch(lean_obj_tag(v___x_2501_))
{
case 0:
{
lean_object* v_index_2502_; lean_object* v_size_2503_; lean_object* v___x_2504_; 
v_index_2502_ = lean_ctor_get(v___x_2501_, 0);
lean_inc(v_index_2502_);
lean_dec_ref_known(v___x_2501_, 3);
v_size_2503_ = lean_ctor_get(v___y_2500_, 0);
lean_inc(v_size_2503_);
v___x_2504_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2500_, v_size_2503_, v_index_2502_, v_e_2351_, v___y_2497_);
lean_dec(v_index_2502_);
v___y_2373_ = v___y_2489_;
v___y_2374_ = v___y_2490_;
v___y_2375_ = v___y_2491_;
v___y_2376_ = v___y_2492_;
v___y_2377_ = v___y_2493_;
v___y_2378_ = v___y_2494_;
v___y_2379_ = v___y_2495_;
v___y_2380_ = v___y_2496_;
v___y_2381_ = v___y_2498_;
v___y_2382_ = v___y_2499_;
v___y_2383_ = v___x_2504_;
goto v___jp_2372_;
}
case 1:
{
lean_object* v_index_2505_; 
v_index_2505_ = lean_ctor_get(v___x_2501_, 0);
lean_inc(v_index_2505_);
lean_dec_ref_known(v___x_2501_, 1);
v___y_2471_ = v___y_2489_;
v___y_2472_ = v___y_2490_;
v___y_2473_ = v___y_2491_;
v___y_2474_ = v___y_2492_;
v___y_2475_ = v___y_2493_;
v___y_2476_ = v___y_2494_;
v___y_2477_ = v___y_2495_;
v___y_2478_ = v___y_2496_;
v___y_2479_ = v___y_2500_;
v___y_2480_ = v___y_2497_;
v___y_2481_ = v___y_2498_;
v___y_2482_ = v___y_2499_;
v_i_2483_ = v_index_2505_;
goto v___jp_2470_;
}
default: 
{
lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2506_ = lean_unsigned_to_nat(0u);
v___x_2507_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2500_, v___x_2506_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v_index_2508_; 
v_index_2508_ = lean_ctor_get(v___x_2507_, 0);
lean_inc(v_index_2508_);
lean_dec_ref_known(v___x_2507_, 1);
v___y_2471_ = v___y_2489_;
v___y_2472_ = v___y_2490_;
v___y_2473_ = v___y_2491_;
v___y_2474_ = v___y_2492_;
v___y_2475_ = v___y_2493_;
v___y_2476_ = v___y_2494_;
v___y_2477_ = v___y_2495_;
v___y_2478_ = v___y_2496_;
v___y_2479_ = v___y_2500_;
v___y_2480_ = v___y_2497_;
v___y_2481_ = v___y_2498_;
v___y_2482_ = v___y_2499_;
v_i_2483_ = v_index_2508_;
goto v___jp_2470_;
}
else
{
lean_dec_ref(v___y_2497_);
lean_dec_ref(v_e_2351_);
v___y_2373_ = v___y_2489_;
v___y_2374_ = v___y_2490_;
v___y_2375_ = v___y_2491_;
v___y_2376_ = v___y_2492_;
v___y_2377_ = v___y_2493_;
v___y_2378_ = v___y_2494_;
v___y_2379_ = v___y_2495_;
v___y_2380_ = v___y_2496_;
v___y_2381_ = v___y_2498_;
v___y_2382_ = v___y_2499_;
v___y_2383_ = v___y_2500_;
goto v___jp_2372_;
}
}
}
}
v___jp_2509_:
{
lean_object* v___x_2518_; 
lean_inc_ref(v_e_2351_);
v___x_2518_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(v_recFnName_2348_, v_fixedPrefixSize_2349_, v_F_2350_, v_e_2351_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_object* v_a_2519_; lean_object* v___x_2520_; 
v_a_2519_ = lean_ctor_get(v___x_2518_, 0);
lean_inc(v_a_2519_);
lean_dec_ref_known(v___x_2518_, 1);
v___x_2520_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId(v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v_a_2521_; lean_object* v___x_2522_; lean_object* v___f_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v_a_2521_ = lean_ctor_get(v___x_2520_, 0);
lean_inc(v_a_2521_);
lean_dec_ref_known(v___x_2520_, 1);
v___x_2522_ = lean_st_ref_take(v___y_2511_);
lean_inc_ref(v_e_2351_);
lean_inc_n(v_a_2519_, 2);
v___f_2523_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___boxed), 11, 2);
lean_closure_set(v___f_2523_, 0, v_a_2519_);
lean_closure_set(v___f_2523_, 1, v_e_2351_);
v___x_2524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2524_, 0, v_a_2519_);
lean_ctor_set(v___x_2524_, 1, v_a_2521_);
v___x_2525_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v___x_2522_, v_e_2351_);
switch(lean_obj_tag(v___x_2525_))
{
case 0:
{
lean_object* v_index_2526_; lean_object* v_size_2527_; lean_object* v___x_2528_; 
v_index_2526_ = lean_ctor_get(v___x_2525_, 0);
lean_inc(v_index_2526_);
lean_dec_ref_known(v___x_2525_, 3);
v_size_2527_ = lean_ctor_get(v___x_2522_, 0);
lean_inc(v_size_2527_);
v___x_2528_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2522_, v_size_2527_, v_index_2526_, v_e_2351_, v___x_2524_);
lean_dec(v_index_2526_);
v___y_2373_ = v___f_2523_;
v___y_2374_ = v___y_2511_;
v___y_2375_ = v_a_2519_;
v___y_2376_ = v___y_2517_;
v___y_2377_ = v___y_2516_;
v___y_2378_ = v___y_2514_;
v___y_2379_ = v___y_2513_;
v___y_2380_ = v___y_2512_;
v___y_2381_ = v___y_2510_;
v___y_2382_ = v___y_2515_;
v___y_2383_ = v___x_2528_;
goto v___jp_2372_;
}
case 1:
{
lean_object* v_index_2529_; lean_object* v_size_2530_; lean_object* v_keyArray_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; uint8_t v___x_2535_; 
v_index_2529_ = lean_ctor_get(v___x_2525_, 0);
lean_inc(v_index_2529_);
lean_dec_ref_known(v___x_2525_, 1);
v_size_2530_ = lean_ctor_get(v___x_2522_, 0);
lean_inc(v_size_2530_);
v_keyArray_2531_ = lean_ctor_get(v___x_2522_, 1);
lean_inc_ref(v_keyArray_2531_);
v___x_2532_ = lean_unsigned_to_nat(1u);
v___x_2533_ = lean_nat_add(v_size_2530_, v___x_2532_);
lean_dec(v_size_2530_);
v___x_2534_ = lean_array_get_size(v_keyArray_2531_);
lean_dec_ref(v_keyArray_2531_);
v___x_2535_ = lean_nat_dec_lt(v___x_2533_, v___x_2534_);
if (v___x_2535_ == 0)
{
lean_dec(v___x_2533_);
lean_dec(v_index_2529_);
v___y_2449_ = v___f_2523_;
v___y_2450_ = v___y_2511_;
v___y_2451_ = v_a_2519_;
v___y_2452_ = v___y_2517_;
v___y_2453_ = v___y_2516_;
v___y_2454_ = v___y_2514_;
v___y_2455_ = v___y_2513_;
v___y_2456_ = v___y_2512_;
v___y_2457_ = v___x_2524_;
v___y_2458_ = v___y_2510_;
v___y_2459_ = v___x_2522_;
v___y_2460_ = v___y_2515_;
goto v___jp_2448_;
}
else
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; uint8_t v___x_2540_; 
v___x_2536_ = lean_unsigned_to_nat(4u);
v___x_2537_ = lean_nat_mul(v___x_2533_, v___x_2536_);
v___x_2538_ = lean_unsigned_to_nat(3u);
v___x_2539_ = lean_nat_mul(v___x_2534_, v___x_2538_);
v___x_2540_ = lean_nat_dec_le(v___x_2537_, v___x_2539_);
lean_dec(v___x_2539_);
lean_dec(v___x_2537_);
if (v___x_2540_ == 0)
{
lean_dec(v___x_2533_);
lean_dec(v_index_2529_);
v___y_2449_ = v___f_2523_;
v___y_2450_ = v___y_2511_;
v___y_2451_ = v_a_2519_;
v___y_2452_ = v___y_2517_;
v___y_2453_ = v___y_2516_;
v___y_2454_ = v___y_2514_;
v___y_2455_ = v___y_2513_;
v___y_2456_ = v___y_2512_;
v___y_2457_ = v___x_2524_;
v___y_2458_ = v___y_2510_;
v___y_2459_ = v___x_2522_;
v___y_2460_ = v___y_2515_;
goto v___jp_2448_;
}
else
{
lean_object* v___x_2541_; 
v___x_2541_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2522_, v___x_2533_, v_index_2529_, v_e_2351_, v___x_2524_);
lean_dec(v_index_2529_);
v___y_2373_ = v___f_2523_;
v___y_2374_ = v___y_2511_;
v___y_2375_ = v_a_2519_;
v___y_2376_ = v___y_2517_;
v___y_2377_ = v___y_2516_;
v___y_2378_ = v___y_2514_;
v___y_2379_ = v___y_2513_;
v___y_2380_ = v___y_2512_;
v___y_2381_ = v___y_2510_;
v___y_2382_ = v___y_2515_;
v___y_2383_ = v___x_2541_;
goto v___jp_2372_;
}
}
}
default: 
{
lean_object* v_size_2542_; lean_object* v_keyArray_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; uint8_t v___x_2547_; 
v_size_2542_ = lean_ctor_get(v___x_2522_, 0);
lean_inc(v_size_2542_);
v_keyArray_2543_ = lean_ctor_get(v___x_2522_, 1);
lean_inc_ref(v_keyArray_2543_);
v___x_2544_ = lean_unsigned_to_nat(1u);
v___x_2545_ = lean_nat_add(v_size_2542_, v___x_2544_);
lean_dec(v_size_2542_);
v___x_2546_ = lean_array_get_size(v_keyArray_2543_);
lean_dec_ref(v_keyArray_2543_);
v___x_2547_ = lean_nat_dec_lt(v___x_2545_, v___x_2546_);
if (v___x_2547_ == 0)
{
lean_object* v___x_2548_; 
lean_dec(v___x_2545_);
v___x_2548_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v___x_2522_);
lean_dec(v___x_2522_);
v___y_2489_ = v___f_2523_;
v___y_2490_ = v___y_2511_;
v___y_2491_ = v_a_2519_;
v___y_2492_ = v___y_2517_;
v___y_2493_ = v___y_2516_;
v___y_2494_ = v___y_2514_;
v___y_2495_ = v___y_2513_;
v___y_2496_ = v___y_2512_;
v___y_2497_ = v___x_2524_;
v___y_2498_ = v___y_2510_;
v___y_2499_ = v___y_2515_;
v___y_2500_ = v___x_2548_;
goto v___jp_2488_;
}
else
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; uint8_t v___x_2553_; 
v___x_2549_ = lean_unsigned_to_nat(4u);
v___x_2550_ = lean_nat_mul(v___x_2545_, v___x_2549_);
lean_dec(v___x_2545_);
v___x_2551_ = lean_unsigned_to_nat(3u);
v___x_2552_ = lean_nat_mul(v___x_2546_, v___x_2551_);
v___x_2553_ = lean_nat_dec_le(v___x_2550_, v___x_2552_);
lean_dec(v___x_2552_);
lean_dec(v___x_2550_);
if (v___x_2553_ == 0)
{
lean_object* v___x_2554_; 
v___x_2554_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v___x_2522_);
lean_dec(v___x_2522_);
v___y_2489_ = v___f_2523_;
v___y_2490_ = v___y_2511_;
v___y_2491_ = v_a_2519_;
v___y_2492_ = v___y_2517_;
v___y_2493_ = v___y_2516_;
v___y_2494_ = v___y_2514_;
v___y_2495_ = v___y_2513_;
v___y_2496_ = v___y_2512_;
v___y_2497_ = v___x_2524_;
v___y_2498_ = v___y_2510_;
v___y_2499_ = v___y_2515_;
v___y_2500_ = v___x_2554_;
goto v___jp_2488_;
}
else
{
v___y_2489_ = v___f_2523_;
v___y_2490_ = v___y_2511_;
v___y_2491_ = v_a_2519_;
v___y_2492_ = v___y_2517_;
v___y_2493_ = v___y_2516_;
v___y_2494_ = v___y_2514_;
v___y_2495_ = v___y_2513_;
v___y_2496_ = v___y_2512_;
v___y_2497_ = v___x_2524_;
v___y_2498_ = v___y_2510_;
v___y_2499_ = v___y_2515_;
v___y_2500_ = v___x_2522_;
goto v___jp_2488_;
}
}
}
}
}
else
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
lean_dec(v_a_2519_);
lean_del_object(v___x_2364_);
lean_dec_ref(v_e_2351_);
v_a_2555_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v___x_2520_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2520_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_a_2555_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
else
{
lean_del_object(v___x_2364_);
lean_dec_ref(v_e_2351_);
return v___x_2518_;
}
}
}
}
}
else
{
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2593_; 
lean_dec_ref(v_e_2351_);
lean_dec_ref(v_F_2350_);
lean_dec(v_fixedPrefixSize_2349_);
lean_dec(v_recFnName_2348_);
v_a_2586_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2588_ = v___x_2361_;
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2361_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2591_; 
if (v_isShared_2589_ == 0)
{
v___x_2591_ = v___x_2588_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_a_2586_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2(lean_object* v_body_2594_, lean_object* v_recFnName_2595_, lean_object* v_fixedPrefixSize_2596_, lean_object* v_F_2597_, lean_object* v_x_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2608_ = lean_expr_instantiate1(v_body_2594_, v_x_2598_);
v___x_2609_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2595_, v_fixedPrefixSize_2596_, v_F_2597_, v___x_2608_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp___boxed(lean_object* v_recFnName_2610_, lean_object* v_fixedPrefixSize_2611_, lean_object* v_F_2612_, lean_object* v_e_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_){
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2610_, v_fixedPrefixSize_2611_, v_F_2612_, v_e_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_);
lean_dec(v_a_2621_);
lean_dec_ref(v_a_2620_);
lean_dec(v_a_2619_);
lean_dec_ref(v_a_2618_);
lean_dec(v_a_2617_);
lean_dec_ref(v_a_2616_);
lean_dec(v_a_2615_);
lean_dec(v_a_2614_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1___boxed(lean_object* v_recFnName_2624_, lean_object* v_fixedPrefixSize_2625_, lean_object* v_F_2626_, lean_object* v_sz_2627_, lean_object* v_i_2628_, lean_object* v_bs_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_){
_start:
{
size_t v_sz_boxed_2639_; size_t v_i_boxed_2640_; lean_object* v_res_2641_; 
v_sz_boxed_2639_ = lean_unbox_usize(v_sz_2627_);
lean_dec(v_sz_2627_);
v_i_boxed_2640_ = lean_unbox_usize(v_i_2628_);
lean_dec(v_i_2628_);
v_res_2641_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_2624_, v_fixedPrefixSize_2625_, v_F_2626_, v_sz_boxed_2639_, v_i_boxed_2640_, v_bs_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec(v___y_2630_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__17___boxed(lean_object* v_recFnName_2642_, lean_object* v_fixedPrefixSize_2643_, lean_object* v_F_2644_, lean_object* v_x_2645_, lean_object* v_x_2646_, lean_object* v_x_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
lean_object* v_res_2657_; 
v_res_2657_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__17(v_recFnName_2642_, v_fixedPrefixSize_2643_, v_F_2644_, v_x_2645_, v_x_2646_, v_x_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec(v___y_2649_);
lean_dec(v___y_2648_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15___boxed(lean_object* v_recFnName_2658_, lean_object* v_fixedPrefixSize_2659_, lean_object* v_e_2660_, lean_object* v_as_2661_, lean_object* v_bs_2662_, lean_object* v_i_2663_, lean_object* v_cs_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__15(v_recFnName_2658_, v_fixedPrefixSize_2659_, v_e_2660_, v_as_2661_, v_bs_2662_, v_i_2663_, v_cs_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v___y_2666_);
lean_dec(v___y_2665_);
lean_dec_ref(v_bs_2662_);
lean_dec_ref(v_as_2661_);
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___boxed(lean_object* v_recFnName_2675_, lean_object* v_fixedPrefixSize_2676_, lean_object* v_F_2677_, lean_object* v_e_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2675_, v_fixedPrefixSize_2676_, v_F_2677_, v_e_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_);
lean_dec(v_a_2686_);
lean_dec_ref(v_a_2685_);
lean_dec(v_a_2684_);
lean_dec_ref(v_a_2683_);
lean_dec(v_a_2682_);
lean_dec_ref(v_a_2681_);
lean_dec(v_a_2680_);
lean_dec(v_a_2679_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___boxed(lean_object* v_recFnName_2689_, lean_object* v_fixedPrefixSize_2690_, lean_object* v_F_2691_, lean_object* v_e_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(v_recFnName_2689_, v_fixedPrefixSize_2690_, v_F_2691_, v_e_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_);
lean_dec(v_a_2700_);
lean_dec_ref(v_a_2699_);
lean_dec(v_a_2698_);
lean_dec_ref(v_a_2697_);
lean_dec(v_a_2696_);
lean_dec_ref(v_a_2695_);
lean_dec(v_a_2694_);
lean_dec(v_a_2693_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___boxed(lean_object* v_recFnName_2703_, lean_object* v_fixedPrefixSize_2704_, lean_object* v_F_2705_, lean_object* v_e_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2703_, v_fixedPrefixSize_2704_, v_F_2705_, v_e_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
lean_dec(v_a_2714_);
lean_dec_ref(v_a_2713_);
lean_dec(v_a_2712_);
lean_dec_ref(v_a_2711_);
lean_dec(v_a_2710_);
lean_dec_ref(v_a_2709_);
lean_dec(v_a_2708_);
lean_dec(v_a_2707_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(lean_object* v_00_u03b1_2717_, lean_object* v_k_2718_, uint8_t v_allowLevelAssignments_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v___x_2729_; 
v___x_2729_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v_k_2718_, v_allowLevelAssignments_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___boxed(lean_object* v_00_u03b1_2730_, lean_object* v_k_2731_, lean_object* v_allowLevelAssignments_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2742_; lean_object* v_res_2743_; 
v_allowLevelAssignments_boxed_2742_ = lean_unbox(v_allowLevelAssignments_2732_);
v_res_2743_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(v_00_u03b1_2730_, v_k_2731_, v_allowLevelAssignments_boxed_2742_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec_ref(v___y_2737_);
lean_dec(v___y_2736_);
lean_dec_ref(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec(v___y_2733_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(lean_object* v_00_u03b1_2744_, lean_object* v_name_2745_, uint8_t v_bi_2746_, lean_object* v_type_2747_, lean_object* v_k_2748_, uint8_t v_kind_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
lean_object* v___x_2759_; 
v___x_2759_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___redArg(v_name_2745_, v_bi_2746_, v_type_2747_, v_k_2748_, v_kind_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_);
return v___x_2759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___boxed(lean_object* v_00_u03b1_2760_, lean_object* v_name_2761_, lean_object* v_bi_2762_, lean_object* v_type_2763_, lean_object* v_k_2764_, lean_object* v_kind_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
uint8_t v_bi_boxed_2775_; uint8_t v_kind_boxed_2776_; lean_object* v_res_2777_; 
v_bi_boxed_2775_ = lean_unbox(v_bi_2762_);
v_kind_boxed_2776_ = lean_unbox(v_kind_2765_);
v_res_2777_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(v_00_u03b1_2760_, v_name_2761_, v_bi_boxed_2775_, v_type_2763_, v_k_2764_, v_kind_boxed_2776_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
lean_dec(v___y_2767_);
lean_dec(v___y_2766_);
return v_res_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(lean_object* v_00_u03b1_2778_, lean_object* v_e_2779_, lean_object* v_maxFVars_2780_, lean_object* v_k_2781_, uint8_t v_cleanupAnnotations_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
lean_object* v___x_2792_; 
v___x_2792_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___redArg(v_e_2779_, v_maxFVars_2780_, v_k_2781_, v_cleanupAnnotations_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___boxed(lean_object* v_00_u03b1_2793_, lean_object* v_e_2794_, lean_object* v_maxFVars_2795_, lean_object* v_k_2796_, lean_object* v_cleanupAnnotations_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2807_; lean_object* v_res_2808_; 
v_cleanupAnnotations_boxed_2807_ = lean_unbox(v_cleanupAnnotations_2797_);
v_res_2808_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(v_00_u03b1_2793_, v_e_2794_, v_maxFVars_2795_, v_k_2796_, v_cleanupAnnotations_boxed_2807_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
lean_dec(v___y_2803_);
lean_dec_ref(v___y_2802_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec(v___y_2798_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0(lean_object* v_inst_2809_, lean_object* v_R_2810_, lean_object* v_a_2811_, lean_object* v_b_2812_){
_start:
{
lean_object* v___x_2813_; 
v___x_2813_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(v_a_2811_, v_b_2812_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2(lean_object* v_cls_2814_, lean_object* v_msg_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_){
_start:
{
lean_object* v___x_2825_; 
v___x_2825_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(v_cls_2814_, v_msg_2815_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
return v___x_2825_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___boxed(lean_object* v_cls_2826_, lean_object* v_msg_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_){
_start:
{
lean_object* v_res_2837_; 
v_res_2837_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2(v_cls_2826_, v_msg_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v___y_2831_);
lean_dec_ref(v___y_2830_);
lean_dec(v___y_2829_);
lean_dec(v___y_2828_);
return v_res_2837_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(lean_object* v_00_u03b1_2838_, lean_object* v_msg_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_){
_start:
{
lean_object* v___x_2849_; 
v___x_2849_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5___redArg(v_msg_2839_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
return v___x_2849_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5___boxed(lean_object* v_00_u03b1_2850_, lean_object* v_msg_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_){
_start:
{
lean_object* v_res_2861_; 
v_res_2861_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v_00_u03b1_2850_, v_msg_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
lean_dec(v___y_2859_);
lean_dec_ref(v___y_2858_);
lean_dec(v___y_2857_);
lean_dec_ref(v___y_2856_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
lean_dec(v___y_2853_);
lean_dec(v___y_2852_);
return v_res_2861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7(lean_object* v_00_u03b2_2862_, lean_object* v_m_2863_, lean_object* v_query_2864_){
_start:
{
lean_object* v___x_2865_; 
v___x_2865_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v_m_2863_, v_query_2864_);
return v___x_2865_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___boxed(lean_object* v_00_u03b2_2866_, lean_object* v_m_2867_, lean_object* v_query_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7(v_00_u03b2_2866_, v_m_2867_, v_query_2868_);
lean_dec_ref(v_query_2868_);
lean_dec_ref(v_m_2867_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8(lean_object* v_00_u03b2_2870_, lean_object* v_m_2871_){
_start:
{
lean_object* v___x_2872_; 
v___x_2872_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v_m_2871_);
return v___x_2872_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___boxed(lean_object* v_00_u03b2_2873_, lean_object* v_m_2874_){
_start:
{
lean_object* v_res_2875_; 
v_res_2875_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8(v_00_u03b2_2873_, v_m_2874_);
lean_dec_ref(v_m_2874_);
return v_res_2875_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9(lean_object* v_00_u03b2_2876_, lean_object* v_m_2877_, lean_object* v_a_2878_){
_start:
{
lean_object* v___x_2879_; 
v___x_2879_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9___redArg(v_m_2877_, v_a_2878_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9___boxed(lean_object* v_00_u03b2_2880_, lean_object* v_m_2881_, lean_object* v_a_2882_){
_start:
{
lean_object* v_res_2883_; 
v_res_2883_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9(v_00_u03b2_2880_, v_m_2881_, v_a_2882_);
lean_dec_ref(v_a_2882_);
lean_dec_ref(v_m_2881_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12_spec__15(lean_object* v_00_u03b1_2884_, lean_object* v_name_2885_, lean_object* v_type_2886_, lean_object* v_val_2887_, lean_object* v_k_2888_, uint8_t v_nondep_2889_, uint8_t v_kind_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_){
_start:
{
lean_object* v___x_2900_; 
v___x_2900_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12_spec__15___redArg(v_name_2885_, v_type_2886_, v_val_2887_, v_k_2888_, v_nondep_2889_, v_kind_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12_spec__15___boxed(lean_object* v_00_u03b1_2901_, lean_object* v_name_2902_, lean_object* v_type_2903_, lean_object* v_val_2904_, lean_object* v_k_2905_, lean_object* v_nondep_2906_, lean_object* v_kind_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_){
_start:
{
uint8_t v_nondep_boxed_2917_; uint8_t v_kind_boxed_2918_; lean_object* v_res_2919_; 
v_nondep_boxed_2917_ = lean_unbox(v_nondep_2906_);
v_kind_boxed_2918_ = lean_unbox(v_kind_2907_);
v_res_2919_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12_spec__15(v_00_u03b1_2901_, v_name_2902_, v_type_2903_, v_val_2904_, v_k_2905_, v_nondep_boxed_2917_, v_kind_boxed_2918_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
lean_dec(v___y_2909_);
lean_dec(v___y_2908_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20(lean_object* v_declName_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_){
_start:
{
lean_object* v___x_2930_; 
v___x_2930_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___redArg(v_declName_2920_, v___y_2928_);
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20___boxed(lean_object* v_declName_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_){
_start:
{
lean_object* v_res_2941_; 
v_res_2941_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__20(v_declName_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec(v___y_2932_);
return v_res_2941_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7_spec__7(lean_object* v_00_u03b2_2942_, lean_object* v_m_2943_, lean_object* v_query_2944_, lean_object* v_x_2945_, lean_object* v_x_2946_, lean_object* v_x_2947_, lean_object* v_x_2948_){
_start:
{
lean_object* v___x_2949_; 
v___x_2949_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7_spec__7___redArg(v_m_2943_, v_query_2944_, v_x_2945_, v_x_2946_, v_x_2947_);
return v___x_2949_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7_spec__7___boxed(lean_object* v_00_u03b2_2950_, lean_object* v_m_2951_, lean_object* v_query_2952_, lean_object* v_x_2953_, lean_object* v_x_2954_, lean_object* v_x_2955_, lean_object* v_x_2956_){
_start:
{
lean_object* v_res_2957_; 
v_res_2957_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7_spec__7(v_00_u03b2_2950_, v_m_2951_, v_query_2952_, v_x_2953_, v_x_2954_, v_x_2955_, v_x_2956_);
lean_dec_ref(v_query_2952_);
lean_dec_ref(v_m_2951_);
return v_res_2957_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__9(lean_object* v_00_u03b2_2958_, lean_object* v_init_2959_, lean_object* v_b_2960_){
_start:
{
lean_object* v___x_2961_; 
v___x_2961_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__9___redArg(v_init_2959_, v_b_2960_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__9___boxed(lean_object* v_00_u03b2_2962_, lean_object* v_init_2963_, lean_object* v_b_2964_){
_start:
{
lean_object* v_res_2965_; 
v_res_2965_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__9(v_00_u03b2_2962_, v_init_2963_, v_b_2964_);
lean_dec_ref(v_b_2964_);
return v_res_2965_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9_spec__11(lean_object* v_00_u03b2_2966_, lean_object* v_m_2967_, lean_object* v_query_2968_){
_start:
{
lean_object* v___x_2969_; 
v___x_2969_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9_spec__11___redArg(v_m_2967_, v_query_2968_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9_spec__11___boxed(lean_object* v_00_u03b2_2970_, lean_object* v_m_2971_, lean_object* v_query_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__9_spec__11(v_00_u03b2_2970_, v_m_2971_, v_query_2972_);
lean_dec_ref(v_query_2972_);
lean_dec_ref(v_m_2971_);
return v_res_2973_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__9_spec__14(lean_object* v_00_u03b2_2974_, lean_object* v_b_2975_, lean_object* v_acc_2976_, lean_object* v_i_2977_){
_start:
{
lean_object* v___x_2978_; 
v___x_2978_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__9_spec__14___redArg(v_b_2975_, v_acc_2976_, v_i_2977_);
return v___x_2978_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__9_spec__14___boxed(lean_object* v_00_u03b2_2979_, lean_object* v_b_2980_, lean_object* v_acc_2981_, lean_object* v_i_2982_){
_start:
{
lean_object* v_res_2983_; 
v_res_2983_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__9_spec__14(v_00_u03b2_2979_, v_b_2980_, v_acc_2981_, v_i_2982_);
lean_dec_ref(v_b_2980_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21(lean_object* v_00_u03b1_2984_, lean_object* v_constName_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_){
_start:
{
lean_object* v___x_2995_; 
v___x_2995_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21___redArg(v_constName_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21___boxed(lean_object* v_00_u03b1_2996_, lean_object* v_constName_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_){
_start:
{
lean_object* v_res_3007_; 
v_res_3007_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21(v_00_u03b1_2996_, v_constName_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec(v___y_2998_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26(lean_object* v_00_u03b1_3008_, lean_object* v_ref_3009_, lean_object* v_constName_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_){
_start:
{
lean_object* v___x_3020_; 
v___x_3020_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26___redArg(v_ref_3009_, v_constName_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26___boxed(lean_object* v_00_u03b1_3021_, lean_object* v_ref_3022_, lean_object* v_constName_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_){
_start:
{
lean_object* v_res_3033_; 
v_res_3033_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26(v_00_u03b1_3021_, v_ref_3022_, v_constName_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
lean_dec(v___y_3031_);
lean_dec_ref(v___y_3030_);
lean_dec(v___y_3029_);
lean_dec_ref(v___y_3028_);
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
lean_dec(v___y_3025_);
lean_dec(v___y_3024_);
lean_dec(v_ref_3022_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28(lean_object* v_00_u03b1_3034_, lean_object* v_ref_3035_, lean_object* v_msg_3036_, lean_object* v_declHint_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_){
_start:
{
lean_object* v___x_3047_; 
v___x_3047_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28___redArg(v_ref_3035_, v_msg_3036_, v_declHint_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28___boxed(lean_object* v_00_u03b1_3048_, lean_object* v_ref_3049_, lean_object* v_msg_3050_, lean_object* v_declHint_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_){
_start:
{
lean_object* v_res_3061_; 
v_res_3061_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28(v_00_u03b1_3048_, v_ref_3049_, v_msg_3050_, v_declHint_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
lean_dec(v___y_3057_);
lean_dec_ref(v___y_3056_);
lean_dec(v___y_3055_);
lean_dec_ref(v___y_3054_);
lean_dec(v___y_3053_);
lean_dec(v___y_3052_);
lean_dec(v_ref_3049_);
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30(lean_object* v_msg_3062_, lean_object* v_declHint_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_){
_start:
{
lean_object* v___x_3073_; 
v___x_3073_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___redArg(v_msg_3062_, v_declHint_3063_, v___y_3071_);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30___boxed(lean_object* v_msg_3074_, lean_object* v_declHint_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__29_spec__30(v_msg_3074_, v_declHint_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
lean_dec(v___y_3081_);
lean_dec_ref(v___y_3080_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec(v___y_3076_);
return v_res_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__30(lean_object* v_00_u03b1_3086_, lean_object* v_ref_3087_, lean_object* v_msg_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_){
_start:
{
lean_object* v___x_3098_; 
v___x_3098_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__30___redArg(v_ref_3087_, v_msg_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
return v___x_3098_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__30___boxed(lean_object* v_00_u03b1_3099_, lean_object* v_ref_3100_, lean_object* v_msg_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_){
_start:
{
lean_object* v_res_3111_; 
v_res_3111_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14_spec__18_spec__21_spec__26_spec__28_spec__30(v_00_u03b1_3099_, v_ref_3100_, v_msg_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec(v___y_3107_);
lean_dec_ref(v___y_3106_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
lean_dec(v___y_3103_);
lean_dec(v___y_3102_);
lean_dec(v_ref_3100_);
return v_res_3111_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(lean_object* v_cls_3112_, lean_object* v_msg_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_){
_start:
{
lean_object* v_ref_3119_; lean_object* v___x_3120_; lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3165_; 
v_ref_3119_ = lean_ctor_get(v___y_3116_, 5);
v___x_3120_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
v_a_3121_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3165_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3123_ = v___x_3120_;
v_isShared_3124_ = v_isSharedCheck_3165_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3120_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3165_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3125_; lean_object* v_traceState_3126_; lean_object* v_env_3127_; lean_object* v_nextMacroScope_3128_; lean_object* v_ngen_3129_; lean_object* v_auxDeclNGen_3130_; lean_object* v_cache_3131_; lean_object* v_messages_3132_; lean_object* v_infoState_3133_; lean_object* v_snapshotTasks_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3164_; 
v___x_3125_ = lean_st_ref_take(v___y_3117_);
v_traceState_3126_ = lean_ctor_get(v___x_3125_, 4);
v_env_3127_ = lean_ctor_get(v___x_3125_, 0);
v_nextMacroScope_3128_ = lean_ctor_get(v___x_3125_, 1);
v_ngen_3129_ = lean_ctor_get(v___x_3125_, 2);
v_auxDeclNGen_3130_ = lean_ctor_get(v___x_3125_, 3);
v_cache_3131_ = lean_ctor_get(v___x_3125_, 5);
v_messages_3132_ = lean_ctor_get(v___x_3125_, 6);
v_infoState_3133_ = lean_ctor_get(v___x_3125_, 7);
v_snapshotTasks_3134_ = lean_ctor_get(v___x_3125_, 8);
v_isSharedCheck_3164_ = !lean_is_exclusive(v___x_3125_);
if (v_isSharedCheck_3164_ == 0)
{
v___x_3136_ = v___x_3125_;
v_isShared_3137_ = v_isSharedCheck_3164_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_snapshotTasks_3134_);
lean_inc(v_infoState_3133_);
lean_inc(v_messages_3132_);
lean_inc(v_cache_3131_);
lean_inc(v_traceState_3126_);
lean_inc(v_auxDeclNGen_3130_);
lean_inc(v_ngen_3129_);
lean_inc(v_nextMacroScope_3128_);
lean_inc(v_env_3127_);
lean_dec(v___x_3125_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3164_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
uint64_t v_tid_3138_; lean_object* v_traces_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3163_; 
v_tid_3138_ = lean_ctor_get_uint64(v_traceState_3126_, sizeof(void*)*1);
v_traces_3139_ = lean_ctor_get(v_traceState_3126_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v_traceState_3126_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3141_ = v_traceState_3126_;
v_isShared_3142_ = v_isSharedCheck_3163_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_traces_3139_);
lean_dec(v_traceState_3126_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3163_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3143_; double v___x_3144_; uint8_t v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3153_; 
v___x_3143_ = lean_box(0);
v___x_3144_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0);
v___x_3145_ = 0;
v___x_3146_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__1));
v___x_3147_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3147_, 0, v_cls_3112_);
lean_ctor_set(v___x_3147_, 1, v___x_3143_);
lean_ctor_set(v___x_3147_, 2, v___x_3146_);
lean_ctor_set_float(v___x_3147_, sizeof(void*)*3, v___x_3144_);
lean_ctor_set_float(v___x_3147_, sizeof(void*)*3 + 8, v___x_3144_);
lean_ctor_set_uint8(v___x_3147_, sizeof(void*)*3 + 16, v___x_3145_);
v___x_3148_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__2));
v___x_3149_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3147_);
lean_ctor_set(v___x_3149_, 1, v_a_3121_);
lean_ctor_set(v___x_3149_, 2, v___x_3148_);
lean_inc(v_ref_3119_);
v___x_3150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3150_, 0, v_ref_3119_);
lean_ctor_set(v___x_3150_, 1, v___x_3149_);
v___x_3151_ = l_Lean_PersistentArray_push___redArg(v_traces_3139_, v___x_3150_);
if (v_isShared_3142_ == 0)
{
lean_ctor_set(v___x_3141_, 0, v___x_3151_);
v___x_3153_ = v___x_3141_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v___x_3151_);
lean_ctor_set_uint64(v_reuseFailAlloc_3162_, sizeof(void*)*1, v_tid_3138_);
v___x_3153_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
lean_object* v___x_3155_; 
if (v_isShared_3137_ == 0)
{
lean_ctor_set(v___x_3136_, 4, v___x_3153_);
v___x_3155_ = v___x_3136_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_env_3127_);
lean_ctor_set(v_reuseFailAlloc_3161_, 1, v_nextMacroScope_3128_);
lean_ctor_set(v_reuseFailAlloc_3161_, 2, v_ngen_3129_);
lean_ctor_set(v_reuseFailAlloc_3161_, 3, v_auxDeclNGen_3130_);
lean_ctor_set(v_reuseFailAlloc_3161_, 4, v___x_3153_);
lean_ctor_set(v_reuseFailAlloc_3161_, 5, v_cache_3131_);
lean_ctor_set(v_reuseFailAlloc_3161_, 6, v_messages_3132_);
lean_ctor_set(v_reuseFailAlloc_3161_, 7, v_infoState_3133_);
lean_ctor_set(v_reuseFailAlloc_3161_, 8, v_snapshotTasks_3134_);
v___x_3155_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3159_; 
v___x_3156_ = lean_st_ref_put(v___y_3117_, v___x_3155_);
v___x_3157_ = lean_box(0);
if (v_isShared_3124_ == 0)
{
lean_ctor_set(v___x_3123_, 0, v___x_3157_);
v___x_3159_ = v___x_3123_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v___x_3157_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg___boxed(lean_object* v_cls_3166_, lean_object* v_msg_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_){
_start:
{
lean_object* v_res_3173_; 
v_res_3173_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3166_, v_msg_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
return v_res_3173_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0(void){
_start:
{
lean_object* v_cellCount_3174_; lean_object* v___x_3175_; 
v_cellCount_3174_ = lean_unsigned_to_nat(16u);
v___x_3175_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_3174_);
return v___x_3175_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1(void){
_start:
{
lean_object* v_cellCount_3176_; lean_object* v___x_3177_; 
v_cellCount_3176_ = lean_unsigned_to_nat(16u);
v___x_3177_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_3176_);
return v___x_3177_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__2(void){
_start:
{
lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3178_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1);
v___x_3179_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0);
v___x_3180_ = lean_unsigned_to_nat(0u);
v___x_3181_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3180_);
lean_ctor_set(v___x_3181_, 1, v___x_3179_);
lean_ctor_set(v___x_3181_, 2, v___x_3178_);
return v___x_3181_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__4(void){
_start:
{
lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3183_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3));
v___x_3184_ = l_Lean_stringToMessageData(v___x_3183_);
return v___x_3184_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__6(void){
_start:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3186_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5));
v___x_3187_ = l_Lean_stringToMessageData(v___x_3186_);
return v___x_3187_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__8(void){
_start:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3189_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7));
v___x_3190_ = l_Lean_stringToMessageData(v___x_3189_);
return v___x_3190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(lean_object* v_recFnName_3191_, lean_object* v_fixedPrefixSize_3192_, lean_object* v_F_3193_, lean_object* v_e_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_){
_start:
{
lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v_options_3223_; uint8_t v_hasTrace_3224_; 
v_options_3223_ = lean_ctor_get(v_a_3199_, 2);
v_hasTrace_3224_ = lean_ctor_get_uint8(v_options_3223_, sizeof(void*)*1);
if (v_hasTrace_3224_ == 0)
{
v___y_3203_ = v_a_3195_;
v___y_3204_ = v_a_3196_;
v___y_3205_ = v_a_3197_;
v___y_3206_ = v_a_3198_;
v___y_3207_ = v_a_3199_;
v___y_3208_ = v_a_3200_;
goto v___jp_3202_;
}
else
{
lean_object* v_inheritedTraceOptions_3225_; lean_object* v_cls_3226_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v_options_3233_; lean_object* v_inheritedTraceOptions_3234_; lean_object* v___y_3235_; lean_object* v___x_3256_; uint8_t v___x_3257_; 
v_inheritedTraceOptions_3225_ = lean_ctor_get(v_a_3199_, 13);
v_cls_3226_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_3256_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_3257_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3225_, v_options_3223_, v___x_3256_);
if (v___x_3257_ == 0)
{
v___y_3228_ = v_a_3195_;
v___y_3229_ = v_a_3196_;
v___y_3230_ = v_a_3197_;
v___y_3231_ = v_a_3198_;
v___y_3232_ = v_a_3199_;
v_options_3233_ = v_options_3223_;
v_inheritedTraceOptions_3234_ = v_inheritedTraceOptions_3225_;
v___y_3235_ = v_a_3200_;
goto v___jp_3227_;
}
else
{
lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; 
v___x_3258_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__8, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__8);
lean_inc_ref(v_e_3194_);
v___x_3259_ = l_Lean_indentExpr(v_e_3194_);
v___x_3260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3260_, 0, v___x_3258_);
lean_ctor_set(v___x_3260_, 1, v___x_3259_);
v___x_3261_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3226_, v___x_3260_, v_a_3197_, v_a_3198_, v_a_3199_, v_a_3200_);
if (lean_obj_tag(v___x_3261_) == 0)
{
lean_dec_ref_known(v___x_3261_, 1);
v___y_3228_ = v_a_3195_;
v___y_3229_ = v_a_3196_;
v___y_3230_ = v_a_3197_;
v___y_3231_ = v_a_3198_;
v___y_3232_ = v_a_3199_;
v_options_3233_ = v_options_3223_;
v_inheritedTraceOptions_3234_ = v_inheritedTraceOptions_3225_;
v___y_3235_ = v_a_3200_;
goto v___jp_3227_;
}
else
{
lean_object* v_a_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3269_; 
lean_dec_ref(v_e_3194_);
lean_dec_ref(v_F_3193_);
lean_dec(v_fixedPrefixSize_3192_);
lean_dec(v_recFnName_3191_);
v_a_3262_ = lean_ctor_get(v___x_3261_, 0);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3261_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3264_ = v___x_3261_;
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_a_3262_);
lean_dec(v___x_3261_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v___x_3267_; 
if (v_isShared_3265_ == 0)
{
v___x_3267_ = v___x_3264_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_a_3262_);
v___x_3267_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
return v___x_3267_;
}
}
}
}
v___jp_3227_:
{
lean_object* v___x_3236_; uint8_t v___x_3237_; 
v___x_3236_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_3237_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3234_, v_options_3233_, v___x_3236_);
if (v___x_3237_ == 0)
{
v___y_3203_ = v___y_3228_;
v___y_3204_ = v___y_3229_;
v___y_3205_ = v___y_3230_;
v___y_3206_ = v___y_3231_;
v___y_3207_ = v___y_3232_;
v___y_3208_ = v___y_3235_;
goto v___jp_3202_;
}
else
{
lean_object* v___x_3238_; 
lean_inc(v___y_3235_);
lean_inc_ref(v___y_3232_);
lean_inc(v___y_3231_);
lean_inc_ref(v___y_3230_);
lean_inc_ref(v_F_3193_);
v___x_3238_ = lean_infer_type(v_F_3193_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3235_);
if (lean_obj_tag(v___x_3238_) == 0)
{
lean_object* v_a_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; 
v_a_3239_ = lean_ctor_get(v___x_3238_, 0);
lean_inc(v_a_3239_);
lean_dec_ref_known(v___x_3238_, 1);
v___x_3240_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__4);
lean_inc_ref(v_F_3193_);
v___x_3241_ = l_Lean_MessageData_ofExpr(v_F_3193_);
v___x_3242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3240_);
lean_ctor_set(v___x_3242_, 1, v___x_3241_);
v___x_3243_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__6, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__6);
v___x_3244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3244_, 0, v___x_3242_);
lean_ctor_set(v___x_3244_, 1, v___x_3243_);
v___x_3245_ = l_Lean_indentExpr(v_a_3239_);
v___x_3246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3244_);
lean_ctor_set(v___x_3246_, 1, v___x_3245_);
v___x_3247_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3226_, v___x_3246_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3235_);
if (lean_obj_tag(v___x_3247_) == 0)
{
lean_dec_ref_known(v___x_3247_, 1);
v___y_3203_ = v___y_3228_;
v___y_3204_ = v___y_3229_;
v___y_3205_ = v___y_3230_;
v___y_3206_ = v___y_3231_;
v___y_3207_ = v___y_3232_;
v___y_3208_ = v___y_3235_;
goto v___jp_3202_;
}
else
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3255_; 
lean_dec_ref(v_e_3194_);
lean_dec_ref(v_F_3193_);
lean_dec(v_fixedPrefixSize_3192_);
lean_dec(v_recFnName_3191_);
v_a_3248_ = lean_ctor_get(v___x_3247_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3247_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3250_ = v___x_3247_;
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_3247_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3253_; 
if (v_isShared_3251_ == 0)
{
v___x_3253_ = v___x_3250_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_a_3248_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
}
else
{
lean_dec_ref(v_e_3194_);
lean_dec_ref(v_F_3193_);
lean_dec(v_fixedPrefixSize_3192_);
lean_dec(v_recFnName_3191_);
return v___x_3238_;
}
}
}
}
v___jp_3202_:
{
lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3209_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__2, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__2);
v___x_3210_ = lean_st_mk_ref(v___x_3209_);
v___x_3211_ = lean_st_mk_ref(v___x_3209_);
v___x_3212_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_3191_, v_fixedPrefixSize_3192_, v_F_3193_, v_e_3194_, v___x_3211_, v___x_3210_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
if (lean_obj_tag(v___x_3212_) == 0)
{
lean_object* v_a_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3222_; 
v_a_3213_ = lean_ctor_get(v___x_3212_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v___x_3212_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3215_ = v___x_3212_;
v_isShared_3216_ = v_isSharedCheck_3222_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_a_3213_);
lean_dec(v___x_3212_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3222_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3220_; 
v___x_3217_ = lean_st_ref_get(v___x_3211_);
lean_dec(v___x_3211_);
lean_dec(v___x_3217_);
v___x_3218_ = lean_st_ref_get(v___x_3210_);
lean_dec(v___x_3210_);
lean_dec(v___x_3218_);
if (v_isShared_3216_ == 0)
{
v___x_3220_ = v___x_3215_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_a_3213_);
v___x_3220_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
return v___x_3220_;
}
}
}
else
{
lean_dec(v___x_3211_);
lean_dec(v___x_3210_);
return v___x_3212_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___boxed(lean_object* v_recFnName_3270_, lean_object* v_fixedPrefixSize_3271_, lean_object* v_F_3272_, lean_object* v_e_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_){
_start:
{
lean_object* v_res_3281_; 
v_res_3281_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(v_recFnName_3270_, v_fixedPrefixSize_3271_, v_F_3272_, v_e_3273_, v_a_3274_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_);
lean_dec(v_a_3279_);
lean_dec_ref(v_a_3278_);
lean_dec(v_a_3277_);
lean_dec_ref(v_a_3276_);
lean_dec(v_a_3275_);
lean_dec_ref(v_a_3274_);
return v_res_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0(lean_object* v_cls_3282_, lean_object* v_msg_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_){
_start:
{
lean_object* v___x_3291_; 
v___x_3291_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3282_, v_msg_3283_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_);
return v___x_3291_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___boxed(lean_object* v_cls_3292_, lean_object* v_msg_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_){
_start:
{
lean_object* v_res_3301_; 
v_res_3301_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0(v_cls_3292_, v_msg_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
return v_res_3301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0(lean_object* v_k_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v_b_3305_, lean_object* v_c_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_){
_start:
{
lean_object* v___x_3312_; 
lean_inc(v___y_3310_);
lean_inc_ref(v___y_3309_);
lean_inc(v___y_3308_);
lean_inc_ref(v___y_3307_);
lean_inc(v___y_3304_);
lean_inc_ref(v___y_3303_);
v___x_3312_ = lean_apply_9(v_k_3302_, v_b_3305_, v_c_3306_, v___y_3303_, v___y_3304_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, lean_box(0));
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed(lean_object* v_k_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v_b_3316_, lean_object* v_c_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
lean_object* v_res_3323_; 
v_res_3323_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0(v_k_3313_, v___y_3314_, v___y_3315_, v_b_3316_, v_c_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3320_);
lean_dec(v___y_3319_);
lean_dec_ref(v___y_3318_);
lean_dec(v___y_3315_);
lean_dec_ref(v___y_3314_);
return v_res_3323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(lean_object* v_e_3324_, lean_object* v_k_3325_, uint8_t v_cleanupAnnotations_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_){
_start:
{
lean_object* v___f_3334_; uint8_t v___x_3335_; uint8_t v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
lean_inc(v___y_3328_);
lean_inc_ref(v___y_3327_);
v___f_3334_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3334_, 0, v_k_3325_);
lean_closure_set(v___f_3334_, 1, v___y_3327_);
lean_closure_set(v___f_3334_, 2, v___y_3328_);
v___x_3335_ = 1;
v___x_3336_ = 0;
v___x_3337_ = lean_box(0);
v___x_3338_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3324_, v___x_3335_, v___x_3336_, v___x_3335_, v___x_3336_, v___x_3337_, v___f_3334_, v_cleanupAnnotations_3326_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
if (lean_obj_tag(v___x_3338_) == 0)
{
return v___x_3338_;
}
else
{
lean_object* v_a_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3346_; 
v_a_3339_ = lean_ctor_get(v___x_3338_, 0);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___x_3338_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3341_ = v___x_3338_;
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_a_3339_);
lean_dec(v___x_3338_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v___x_3344_; 
if (v_isShared_3342_ == 0)
{
v___x_3344_ = v___x_3341_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_a_3339_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___boxed(lean_object* v_e_3347_, lean_object* v_k_3348_, lean_object* v_cleanupAnnotations_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3357_; lean_object* v_res_3358_; 
v_cleanupAnnotations_boxed_3357_ = lean_unbox(v_cleanupAnnotations_3349_);
v_res_3358_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v_e_3347_, v_k_3348_, v_cleanupAnnotations_boxed_3357_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_);
lean_dec(v___y_3355_);
lean_dec_ref(v___y_3354_);
lean_dec(v___y_3353_);
lean_dec_ref(v___y_3352_);
lean_dec(v___y_3351_);
lean_dec_ref(v___y_3350_);
return v_res_3358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0(lean_object* v_00_u03b1_3359_, lean_object* v_e_3360_, lean_object* v_k_3361_, uint8_t v_cleanupAnnotations_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_){
_start:
{
lean_object* v___x_3370_; 
v___x_3370_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v_e_3360_, v_k_3361_, v_cleanupAnnotations_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_);
return v___x_3370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___boxed(lean_object* v_00_u03b1_3371_, lean_object* v_e_3372_, lean_object* v_k_3373_, lean_object* v_cleanupAnnotations_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3382_; lean_object* v_res_3383_; 
v_cleanupAnnotations_boxed_3382_ = lean_unbox(v_cleanupAnnotations_3374_);
v_res_3383_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0(v_00_u03b1_3371_, v_e_3372_, v_k_3373_, v_cleanupAnnotations_boxed_3382_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
lean_dec(v___y_3380_);
lean_dec_ref(v___y_3379_);
lean_dec(v___y_3378_);
lean_dec_ref(v___y_3377_);
lean_dec(v___y_3376_);
lean_dec_ref(v___y_3375_);
return v_res_3383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(lean_object* v_e_3384_, lean_object* v_maxFVars_3385_, lean_object* v_k_3386_, uint8_t v_cleanupAnnotations_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_){
_start:
{
lean_object* v___f_3395_; uint8_t v___x_3396_; uint8_t v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; 
lean_inc(v___y_3389_);
lean_inc_ref(v___y_3388_);
v___f_3395_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3395_, 0, v_k_3386_);
lean_closure_set(v___f_3395_, 1, v___y_3388_);
lean_closure_set(v___f_3395_, 2, v___y_3389_);
v___x_3396_ = 1;
v___x_3397_ = 0;
v___x_3398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3398_, 0, v_maxFVars_3385_);
v___x_3399_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3384_, v___x_3396_, v___x_3397_, v___x_3396_, v___x_3397_, v___x_3398_, v___f_3395_, v_cleanupAnnotations_3387_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_);
lean_dec_ref_known(v___x_3398_, 1);
if (lean_obj_tag(v___x_3399_) == 0)
{
return v___x_3399_;
}
else
{
lean_object* v_a_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3407_; 
v_a_3400_ = lean_ctor_get(v___x_3399_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3402_ = v___x_3399_;
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_a_3400_);
lean_dec(v___x_3399_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3405_; 
if (v_isShared_3403_ == 0)
{
v___x_3405_ = v___x_3402_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_a_3400_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg___boxed(lean_object* v_e_3408_, lean_object* v_maxFVars_3409_, lean_object* v_k_3410_, lean_object* v_cleanupAnnotations_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3419_; lean_object* v_res_3420_; 
v_cleanupAnnotations_boxed_3419_ = lean_unbox(v_cleanupAnnotations_3411_);
v_res_3420_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_e_3408_, v_maxFVars_3409_, v_k_3410_, v_cleanupAnnotations_boxed_3419_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
return v_res_3420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2(lean_object* v_00_u03b1_3421_, lean_object* v_e_3422_, lean_object* v_maxFVars_3423_, lean_object* v_k_3424_, uint8_t v_cleanupAnnotations_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_){
_start:
{
lean_object* v___x_3433_; 
v___x_3433_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_e_3422_, v_maxFVars_3423_, v_k_3424_, v_cleanupAnnotations_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
return v___x_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___boxed(lean_object* v_00_u03b1_3434_, lean_object* v_e_3435_, lean_object* v_maxFVars_3436_, lean_object* v_k_3437_, lean_object* v_cleanupAnnotations_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3446_; lean_object* v_res_3447_; 
v_cleanupAnnotations_boxed_3446_ = lean_unbox(v_cleanupAnnotations_3438_);
v_res_3447_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2(v_00_u03b1_3434_, v_e_3435_, v_maxFVars_3436_, v_k_3437_, v_cleanupAnnotations_boxed_3446_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
lean_dec(v___y_3444_);
lean_dec_ref(v___y_3443_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
return v_res_3447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0(lean_object* v_a_3448_, lean_object* v___x_3449_, lean_object* v___x_3450_, lean_object* v_x_3451_, uint8_t v___x_3452_, lean_object* v_xs_3453_, lean_object* v_type_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_){
_start:
{
lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; 
v___x_3462_ = l_Lean_LocalDecl_type(v_a_3448_);
v___x_3463_ = lean_array_get_borrowed(v___x_3449_, v_xs_3453_, v___x_3450_);
v___x_3464_ = l_Lean_Expr_replaceFVar(v___x_3462_, v_x_3451_, v___x_3463_);
lean_dec_ref(v___x_3462_);
v___x_3465_ = l_Lean_mkArrow(v___x_3464_, v_type_3454_, v___y_3459_, v___y_3460_);
if (lean_obj_tag(v___x_3465_) == 0)
{
lean_object* v_a_3466_; uint8_t v___x_3467_; uint8_t v___x_3468_; lean_object* v___x_3469_; 
v_a_3466_ = lean_ctor_get(v___x_3465_, 0);
lean_inc_n(v_a_3466_, 2);
lean_dec_ref_known(v___x_3465_, 1);
v___x_3467_ = 0;
v___x_3468_ = 1;
v___x_3469_ = l_Lean_Meta_mkLambdaFVars(v_xs_3453_, v_a_3466_, v___x_3467_, v___x_3452_, v___x_3467_, v___x_3452_, v___x_3468_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_);
if (lean_obj_tag(v___x_3469_) == 0)
{
lean_object* v_a_3470_; lean_object* v___x_3471_; 
v_a_3470_ = lean_ctor_get(v___x_3469_, 0);
lean_inc(v_a_3470_);
lean_dec_ref_known(v___x_3469_, 1);
v___x_3471_ = l_Lean_Meta_getLevel(v_a_3466_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_);
if (lean_obj_tag(v___x_3471_) == 0)
{
lean_object* v_a_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3480_; 
v_a_3472_ = lean_ctor_get(v___x_3471_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3471_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3474_ = v___x_3471_;
v_isShared_3475_ = v_isSharedCheck_3480_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_a_3472_);
lean_dec(v___x_3471_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3480_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3476_; lean_object* v___x_3478_; 
v___x_3476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3476_, 0, v_a_3470_);
lean_ctor_set(v___x_3476_, 1, v_a_3472_);
if (v_isShared_3475_ == 0)
{
lean_ctor_set(v___x_3474_, 0, v___x_3476_);
v___x_3478_ = v___x_3474_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v___x_3476_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
else
{
lean_object* v_a_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3488_; 
lean_dec(v_a_3470_);
v_a_3481_ = lean_ctor_get(v___x_3471_, 0);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3471_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3483_ = v___x_3471_;
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_a_3481_);
lean_dec(v___x_3471_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v___x_3486_; 
if (v_isShared_3484_ == 0)
{
v___x_3486_ = v___x_3483_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_a_3481_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
}
}
}
}
else
{
lean_object* v_a_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3496_; 
lean_dec(v_a_3466_);
v_a_3489_ = lean_ctor_get(v___x_3469_, 0);
v_isSharedCheck_3496_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3491_ = v___x_3469_;
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_a_3489_);
lean_dec(v___x_3469_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___x_3494_; 
if (v_isShared_3492_ == 0)
{
v___x_3494_ = v___x_3491_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_a_3489_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
}
}
else
{
lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3504_; 
v_a_3497_ = lean_ctor_get(v___x_3465_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3465_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3499_ = v___x_3465_;
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___x_3465_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3502_; 
if (v_isShared_3500_ == 0)
{
v___x_3502_ = v___x_3499_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_a_3497_);
v___x_3502_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
return v___x_3502_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed(lean_object* v_a_3505_, lean_object* v___x_3506_, lean_object* v___x_3507_, lean_object* v_x_3508_, lean_object* v___x_3509_, lean_object* v_xs_3510_, lean_object* v_type_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_){
_start:
{
uint8_t v___x_6703__boxed_3519_; lean_object* v_res_3520_; 
v___x_6703__boxed_3519_ = lean_unbox(v___x_3509_);
v_res_3520_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0(v_a_3505_, v___x_3506_, v___x_3507_, v_x_3508_, v___x_6703__boxed_3519_, v_xs_3510_, v_type_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_);
lean_dec(v___y_3517_);
lean_dec_ref(v___y_3516_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
lean_dec(v___y_3513_);
lean_dec_ref(v___y_3512_);
lean_dec_ref(v_xs_3510_);
lean_dec(v___x_3507_);
lean_dec_ref(v___x_3506_);
lean_dec_ref(v_a_3505_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0(lean_object* v_k_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v_b_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_){
_start:
{
lean_object* v___x_3530_; 
lean_inc(v___y_3528_);
lean_inc_ref(v___y_3527_);
lean_inc(v___y_3526_);
lean_inc_ref(v___y_3525_);
lean_inc(v___y_3523_);
lean_inc_ref(v___y_3522_);
v___x_3530_ = lean_apply_8(v_k_3521_, v_b_3524_, v___y_3522_, v___y_3523_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_, lean_box(0));
return v___x_3530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_k_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v_b_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_){
_start:
{
lean_object* v_res_3540_; 
v_res_3540_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0(v_k_3531_, v___y_3532_, v___y_3533_, v_b_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_);
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3537_);
lean_dec(v___y_3536_);
lean_dec_ref(v___y_3535_);
lean_dec(v___y_3533_);
lean_dec_ref(v___y_3532_);
return v_res_3540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(lean_object* v_name_3541_, uint8_t v_bi_3542_, lean_object* v_type_3543_, lean_object* v_k_3544_, uint8_t v_kind_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_){
_start:
{
lean_object* v___f_3553_; lean_object* v___x_3554_; 
lean_inc(v___y_3547_);
lean_inc_ref(v___y_3546_);
v___f_3553_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3553_, 0, v_k_3544_);
lean_closure_set(v___f_3553_, 1, v___y_3546_);
lean_closure_set(v___f_3553_, 2, v___y_3547_);
v___x_3554_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3541_, v_bi_3542_, v_type_3543_, v___f_3553_, v_kind_3545_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_);
if (lean_obj_tag(v___x_3554_) == 0)
{
return v___x_3554_;
}
else
{
lean_object* v_a_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3562_; 
v_a_3555_ = lean_ctor_get(v___x_3554_, 0);
v_isSharedCheck_3562_ = !lean_is_exclusive(v___x_3554_);
if (v_isSharedCheck_3562_ == 0)
{
v___x_3557_ = v___x_3554_;
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_a_3555_);
lean_dec(v___x_3554_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v___x_3560_; 
if (v_isShared_3558_ == 0)
{
v___x_3560_ = v___x_3557_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_a_3555_);
v___x_3560_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
return v___x_3560_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___boxed(lean_object* v_name_3563_, lean_object* v_bi_3564_, lean_object* v_type_3565_, lean_object* v_k_3566_, lean_object* v_kind_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_){
_start:
{
uint8_t v_bi_boxed_3575_; uint8_t v_kind_boxed_3576_; lean_object* v_res_3577_; 
v_bi_boxed_3575_ = lean_unbox(v_bi_3564_);
v_kind_boxed_3576_ = lean_unbox(v_kind_3567_);
v_res_3577_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(v_name_3563_, v_bi_boxed_3575_, v_type_3565_, v_k_3566_, v_kind_boxed_3576_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_);
lean_dec(v___y_3573_);
lean_dec_ref(v___y_3572_);
lean_dec(v___y_3571_);
lean_dec_ref(v___y_3570_);
lean_dec(v___y_3569_);
lean_dec_ref(v___y_3568_);
return v_res_3577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(lean_object* v_name_3578_, lean_object* v_type_3579_, lean_object* v_k_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_){
_start:
{
uint8_t v___x_3588_; uint8_t v___x_3589_; lean_object* v___x_3590_; 
v___x_3588_ = 0;
v___x_3589_ = 0;
v___x_3590_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(v_name_3578_, v___x_3588_, v_type_3579_, v_k_3580_, v___x_3589_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_);
return v___x_3590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___boxed(lean_object* v_name_3591_, lean_object* v_type_3592_, lean_object* v_k_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_){
_start:
{
lean_object* v_res_3601_; 
v_res_3601_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_name_3591_, v_type_3592_, v_k_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
return v_res_3601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(lean_object* v_x_3615_, lean_object* v_F_3616_, lean_object* v_val_3617_, lean_object* v_k_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_){
_start:
{
uint8_t v___y_3627_; uint8_t v___x_3742_; 
v___x_3742_ = l_Lean_Expr_isFVar(v_x_3615_);
if (v___x_3742_ == 0)
{
v___y_3627_ = v___x_3742_;
goto v___jp_3626_;
}
else
{
lean_object* v___x_3743_; lean_object* v___x_3744_; uint8_t v___x_3745_; 
v___x_3743_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6));
v___x_3744_ = lean_unsigned_to_nat(6u);
v___x_3745_ = l_Lean_Expr_isAppOfArity(v_val_3617_, v___x_3743_, v___x_3744_);
v___y_3627_ = v___x_3745_;
goto v___jp_3626_;
}
v___jp_3626_:
{
if (v___y_3627_ == 0)
{
lean_object* v___x_3628_; 
lean_inc(v_a_3624_);
lean_inc_ref(v_a_3623_);
lean_inc(v_a_3622_);
lean_inc_ref(v_a_3621_);
lean_inc(v_a_3620_);
lean_inc_ref(v_a_3619_);
v___x_3628_ = lean_apply_10(v_k_3618_, v_x_3615_, v_F_3616_, v_val_3617_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, lean_box(0));
return v___x_3628_;
}
else
{
lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; uint8_t v___x_3635_; 
v___x_3629_ = lean_unsigned_to_nat(3u);
v___x_3630_ = l_Lean_Expr_getAppNumArgs(v_val_3617_);
v___x_3631_ = lean_nat_sub(v___x_3630_, v___x_3629_);
v___x_3632_ = lean_unsigned_to_nat(1u);
v___x_3633_ = lean_nat_sub(v___x_3631_, v___x_3632_);
lean_dec(v___x_3631_);
v___x_3634_ = l_Lean_Expr_getRevArg_x21(v_val_3617_, v___x_3633_);
v___x_3635_ = lean_expr_eqv(v___x_3634_, v_x_3615_);
lean_dec_ref(v___x_3634_);
if (v___x_3635_ == 0)
{
lean_object* v___x_3636_; 
lean_dec(v___x_3630_);
lean_inc(v_a_3624_);
lean_inc_ref(v_a_3623_);
lean_inc(v_a_3622_);
lean_inc_ref(v_a_3621_);
lean_inc(v_a_3620_);
lean_inc_ref(v_a_3619_);
v___x_3636_ = lean_apply_10(v_k_3618_, v_x_3615_, v_F_3616_, v_val_3617_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, lean_box(0));
return v___x_3636_;
}
else
{
lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; uint8_t v___x_3641_; 
v___x_3637_ = lean_unsigned_to_nat(4u);
v___x_3638_ = lean_nat_sub(v___x_3630_, v___x_3637_);
v___x_3639_ = lean_nat_sub(v___x_3638_, v___x_3632_);
lean_dec(v___x_3638_);
v___x_3640_ = l_Lean_Expr_getRevArg_x21(v_val_3617_, v___x_3639_);
v___x_3641_ = l_Lean_Expr_isLambda(v___x_3640_);
lean_dec_ref(v___x_3640_);
if (v___x_3641_ == 0)
{
lean_object* v___x_3642_; 
lean_dec(v___x_3630_);
lean_inc(v_a_3624_);
lean_inc_ref(v_a_3623_);
lean_inc(v_a_3622_);
lean_inc_ref(v_a_3621_);
lean_inc(v_a_3620_);
lean_inc_ref(v_a_3619_);
v___x_3642_ = lean_apply_10(v_k_3618_, v_x_3615_, v_F_3616_, v_val_3617_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, lean_box(0));
return v___x_3642_;
}
else
{
lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; uint8_t v___x_3647_; 
v___x_3643_ = lean_unsigned_to_nat(5u);
v___x_3644_ = lean_nat_sub(v___x_3630_, v___x_3643_);
v___x_3645_ = lean_nat_sub(v___x_3644_, v___x_3632_);
lean_dec(v___x_3644_);
v___x_3646_ = l_Lean_Expr_getRevArg_x21(v_val_3617_, v___x_3645_);
v___x_3647_ = l_Lean_Expr_isLambda(v___x_3646_);
lean_dec_ref(v___x_3646_);
if (v___x_3647_ == 0)
{
lean_object* v___x_3648_; 
lean_dec(v___x_3630_);
lean_inc(v_a_3624_);
lean_inc_ref(v_a_3623_);
lean_inc(v_a_3622_);
lean_inc_ref(v_a_3621_);
lean_inc(v_a_3620_);
lean_inc_ref(v_a_3619_);
v___x_3648_ = lean_apply_10(v_k_3618_, v_x_3615_, v_F_3616_, v_val_3617_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, lean_box(0));
return v___x_3648_;
}
else
{
lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3649_ = l_Lean_Expr_fvarId_x21(v_F_3616_);
v___x_3650_ = l_Lean_FVarId_getDecl___redArg(v___x_3649_, v_a_3621_, v_a_3623_, v_a_3624_);
if (lean_obj_tag(v___x_3650_) == 0)
{
lean_object* v_a_3651_; lean_object* v___x_3652_; lean_object* v_dummy_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v_args_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___f_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; uint8_t v___x_3662_; lean_object* v___x_3663_; 
v_a_3651_ = lean_ctor_get(v___x_3650_, 0);
lean_inc_n(v_a_3651_, 2);
lean_dec_ref_known(v___x_3650_, 1);
v___x_3652_ = l_Lean_instInhabitedExpr;
v_dummy_3653_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0);
lean_inc(v___x_3630_);
v___x_3654_ = lean_mk_array(v___x_3630_, v_dummy_3653_);
v___x_3655_ = lean_nat_sub(v___x_3630_, v___x_3632_);
lean_dec(v___x_3630_);
v_args_3656_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_3617_, v___x_3654_, v___x_3655_);
v___x_3657_ = lean_unsigned_to_nat(0u);
v___x_3658_ = lean_box(v___x_3641_);
lean_inc_ref(v_x_3615_);
v___f_3659_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed), 14, 5);
lean_closure_set(v___f_3659_, 0, v_a_3651_);
lean_closure_set(v___f_3659_, 1, v___x_3652_);
lean_closure_set(v___f_3659_, 2, v___x_3657_);
lean_closure_set(v___f_3659_, 3, v_x_3615_);
lean_closure_set(v___f_3659_, 4, v___x_3658_);
v___x_3660_ = lean_unsigned_to_nat(2u);
v___x_3661_ = lean_array_get(v___x_3652_, v_args_3656_, v___x_3660_);
v___x_3662_ = 0;
v___x_3663_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_3661_, v___f_3659_, v___x_3662_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_);
if (lean_obj_tag(v___x_3663_) == 0)
{
lean_object* v_a_3664_; lean_object* v_fst_3665_; lean_object* v_snd_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3725_; 
v_a_3664_ = lean_ctor_get(v___x_3663_, 0);
lean_inc(v_a_3664_);
lean_dec_ref_known(v___x_3663_, 1);
v_fst_3665_ = lean_ctor_get(v_a_3664_, 0);
v_snd_3666_ = lean_ctor_get(v_a_3664_, 1);
v_isSharedCheck_3725_ = !lean_is_exclusive(v_a_3664_);
if (v_isSharedCheck_3725_ == 0)
{
v___x_3668_ = v_a_3664_;
v_isShared_3669_ = v_isSharedCheck_3725_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_snd_3666_);
lean_inc(v_fst_3665_);
lean_dec(v_a_3664_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3725_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v_00_u03b1_3670_; lean_object* v_00_u03b2_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; 
v_00_u03b1_3670_ = lean_array_get(v___x_3652_, v_args_3656_, v___x_3657_);
v_00_u03b2_3671_ = lean_array_get(v___x_3652_, v_args_3656_, v___x_3632_);
v___x_3672_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__2));
v___x_3673_ = lean_array_get(v___x_3652_, v_args_3656_, v___x_3637_);
lean_inc_ref(v_x_3615_);
lean_inc(v_a_3651_);
lean_inc_ref(v_k_3618_);
lean_inc(v_00_u03b2_3671_);
lean_inc(v_00_u03b1_3670_);
v___x_3674_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3652_, v___x_3657_, v_00_u03b1_3670_, v_00_u03b2_3671_, v___x_3629_, v_k_3618_, v___x_3660_, v___x_3662_, v___x_3641_, v_a_3651_, v_x_3615_, v___x_3632_, v___x_3672_, v___x_3673_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_);
if (lean_obj_tag(v___x_3674_) == 0)
{
lean_object* v_a_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; 
v_a_3675_ = lean_ctor_get(v___x_3674_, 0);
lean_inc(v_a_3675_);
lean_dec_ref_known(v___x_3674_, 1);
v___x_3676_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__4));
v___x_3677_ = lean_array_get(v___x_3652_, v_args_3656_, v___x_3643_);
lean_dec_ref(v_args_3656_);
lean_inc_ref(v_x_3615_);
lean_inc(v_00_u03b2_3671_);
lean_inc(v_00_u03b1_3670_);
v___x_3678_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3652_, v___x_3657_, v_00_u03b1_3670_, v_00_u03b2_3671_, v___x_3629_, v_k_3618_, v___x_3660_, v___x_3662_, v___x_3641_, v_a_3651_, v_x_3615_, v___x_3632_, v___x_3676_, v___x_3677_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_);
if (lean_obj_tag(v___x_3678_) == 0)
{
lean_object* v_a_3679_; lean_object* v___x_3680_; 
v_a_3679_ = lean_ctor_get(v___x_3678_, 0);
lean_inc(v_a_3679_);
lean_dec_ref_known(v___x_3678_, 1);
lean_inc(v_00_u03b1_3670_);
v___x_3680_ = l_Lean_Meta_getLevel(v_00_u03b1_3670_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_);
if (lean_obj_tag(v___x_3680_) == 0)
{
lean_object* v_a_3681_; lean_object* v___x_3682_; 
v_a_3681_ = lean_ctor_get(v___x_3680_, 0);
lean_inc(v_a_3681_);
lean_dec_ref_known(v___x_3680_, 1);
lean_inc(v_00_u03b2_3671_);
v___x_3682_ = l_Lean_Meta_getLevel(v_00_u03b2_3671_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_);
if (lean_obj_tag(v___x_3682_) == 0)
{
lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3708_; 
v_a_3683_ = lean_ctor_get(v___x_3682_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3685_ = v___x_3682_;
v_isShared_3686_ = v_isSharedCheck_3708_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v___x_3682_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3708_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3690_; 
v___x_3687_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6));
v___x_3688_ = lean_box(0);
if (v_isShared_3669_ == 0)
{
lean_ctor_set_tag(v___x_3668_, 1);
lean_ctor_set(v___x_3668_, 1, v___x_3688_);
lean_ctor_set(v___x_3668_, 0, v_a_3683_);
v___x_3690_ = v___x_3668_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_a_3683_);
lean_ctor_set(v_reuseFailAlloc_3707_, 1, v___x_3688_);
v___x_3690_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3705_; 
v___x_3691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3691_, 0, v_a_3681_);
lean_ctor_set(v___x_3691_, 1, v___x_3690_);
v___x_3692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3692_, 0, v_snd_3666_);
lean_ctor_set(v___x_3692_, 1, v___x_3691_);
v___x_3693_ = l_Lean_mkConst(v___x_3687_, v___x_3692_);
v___x_3694_ = lean_unsigned_to_nat(7u);
v___x_3695_ = lean_mk_empty_array_with_capacity(v___x_3694_);
v___x_3696_ = lean_array_push(v___x_3695_, v_00_u03b1_3670_);
v___x_3697_ = lean_array_push(v___x_3696_, v_00_u03b2_3671_);
v___x_3698_ = lean_array_push(v___x_3697_, v_fst_3665_);
v___x_3699_ = lean_array_push(v___x_3698_, v_x_3615_);
v___x_3700_ = lean_array_push(v___x_3699_, v_a_3675_);
v___x_3701_ = lean_array_push(v___x_3700_, v_a_3679_);
v___x_3702_ = lean_array_push(v___x_3701_, v_F_3616_);
v___x_3703_ = l_Lean_mkAppN(v___x_3693_, v___x_3702_);
lean_dec_ref(v___x_3702_);
if (v_isShared_3686_ == 0)
{
lean_ctor_set(v___x_3685_, 0, v___x_3703_);
v___x_3705_ = v___x_3685_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v___x_3703_);
v___x_3705_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
return v___x_3705_;
}
}
}
}
else
{
lean_object* v_a_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3716_; 
lean_dec(v_a_3681_);
lean_dec(v_a_3679_);
lean_dec(v_a_3675_);
lean_dec(v_00_u03b2_3671_);
lean_dec(v_00_u03b1_3670_);
lean_del_object(v___x_3668_);
lean_dec(v_snd_3666_);
lean_dec(v_fst_3665_);
lean_dec_ref(v_F_3616_);
lean_dec_ref(v_x_3615_);
v_a_3709_ = lean_ctor_get(v___x_3682_, 0);
v_isSharedCheck_3716_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3711_ = v___x_3682_;
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_a_3709_);
lean_dec(v___x_3682_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3714_; 
if (v_isShared_3712_ == 0)
{
v___x_3714_ = v___x_3711_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_a_3709_);
v___x_3714_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
return v___x_3714_;
}
}
}
}
else
{
lean_object* v_a_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3724_; 
lean_dec(v_a_3679_);
lean_dec(v_a_3675_);
lean_dec(v_00_u03b2_3671_);
lean_dec(v_00_u03b1_3670_);
lean_del_object(v___x_3668_);
lean_dec(v_snd_3666_);
lean_dec(v_fst_3665_);
lean_dec_ref(v_F_3616_);
lean_dec_ref(v_x_3615_);
v_a_3717_ = lean_ctor_get(v___x_3680_, 0);
v_isSharedCheck_3724_ = !lean_is_exclusive(v___x_3680_);
if (v_isSharedCheck_3724_ == 0)
{
v___x_3719_ = v___x_3680_;
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_a_3717_);
lean_dec(v___x_3680_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3722_; 
if (v_isShared_3720_ == 0)
{
v___x_3722_ = v___x_3719_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_a_3717_);
v___x_3722_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
return v___x_3722_;
}
}
}
}
else
{
lean_dec(v_a_3675_);
lean_dec(v_00_u03b2_3671_);
lean_dec(v_00_u03b1_3670_);
lean_del_object(v___x_3668_);
lean_dec(v_snd_3666_);
lean_dec(v_fst_3665_);
lean_dec_ref(v_F_3616_);
lean_dec_ref(v_x_3615_);
return v___x_3678_;
}
}
else
{
lean_dec(v_00_u03b2_3671_);
lean_dec(v_00_u03b1_3670_);
lean_del_object(v___x_3668_);
lean_dec(v_snd_3666_);
lean_dec(v_fst_3665_);
lean_dec_ref(v_args_3656_);
lean_dec(v_a_3651_);
lean_dec_ref(v_k_3618_);
lean_dec_ref(v_F_3616_);
lean_dec_ref(v_x_3615_);
return v___x_3674_;
}
}
}
else
{
lean_object* v_a_3726_; lean_object* v___x_3728_; uint8_t v_isShared_3729_; uint8_t v_isSharedCheck_3733_; 
lean_dec_ref(v_args_3656_);
lean_dec(v_a_3651_);
lean_dec_ref(v_k_3618_);
lean_dec_ref(v_F_3616_);
lean_dec_ref(v_x_3615_);
v_a_3726_ = lean_ctor_get(v___x_3663_, 0);
v_isSharedCheck_3733_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3733_ == 0)
{
v___x_3728_ = v___x_3663_;
v_isShared_3729_ = v_isSharedCheck_3733_;
goto v_resetjp_3727_;
}
else
{
lean_inc(v_a_3726_);
lean_dec(v___x_3663_);
v___x_3728_ = lean_box(0);
v_isShared_3729_ = v_isSharedCheck_3733_;
goto v_resetjp_3727_;
}
v_resetjp_3727_:
{
lean_object* v___x_3731_; 
if (v_isShared_3729_ == 0)
{
v___x_3731_ = v___x_3728_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v_a_3726_);
v___x_3731_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
return v___x_3731_;
}
}
}
}
else
{
lean_object* v_a_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3741_; 
lean_dec(v___x_3630_);
lean_dec_ref(v_k_3618_);
lean_dec_ref(v_val_3617_);
lean_dec_ref(v_F_3616_);
lean_dec_ref(v_x_3615_);
v_a_3734_ = lean_ctor_get(v___x_3650_, 0);
v_isSharedCheck_3741_ = !lean_is_exclusive(v___x_3650_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3736_ = v___x_3650_;
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_a_3734_);
lean_dec(v___x_3650_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v___x_3739_; 
if (v_isShared_3737_ == 0)
{
v___x_3739_ = v___x_3736_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v_a_3734_);
v___x_3739_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
return v___x_3739_;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1(lean_object* v___x_3746_, lean_object* v_body_3747_, lean_object* v_k_3748_, lean_object* v___x_3749_, uint8_t v___x_3750_, uint8_t v___x_3751_, lean_object* v_FNew_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_){
_start:
{
lean_object* v___x_3760_; 
lean_inc_ref(v_FNew_3752_);
lean_inc_ref(v___x_3746_);
v___x_3760_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v___x_3746_, v_FNew_3752_, v_body_3747_, v_k_3748_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
if (lean_obj_tag(v___x_3760_) == 0)
{
lean_object* v_a_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; uint8_t v___x_3765_; lean_object* v___x_3766_; 
v_a_3761_ = lean_ctor_get(v___x_3760_, 0);
lean_inc(v_a_3761_);
lean_dec_ref_known(v___x_3760_, 1);
v___x_3762_ = lean_mk_empty_array_with_capacity(v___x_3749_);
v___x_3763_ = lean_array_push(v___x_3762_, v___x_3746_);
v___x_3764_ = lean_array_push(v___x_3763_, v_FNew_3752_);
v___x_3765_ = 1;
v___x_3766_ = l_Lean_Meta_mkLambdaFVars(v___x_3764_, v_a_3761_, v___x_3750_, v___x_3751_, v___x_3750_, v___x_3751_, v___x_3765_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
lean_dec_ref(v___x_3764_);
return v___x_3766_;
}
else
{
lean_dec_ref(v_FNew_3752_);
lean_dec_ref(v___x_3746_);
return v___x_3760_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1___boxed(lean_object* v___x_3767_, lean_object* v_body_3768_, lean_object* v_k_3769_, lean_object* v___x_3770_, lean_object* v___x_3771_, lean_object* v___x_3772_, lean_object* v_FNew_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_){
_start:
{
uint8_t v___x_6949__boxed_3781_; uint8_t v___x_6950__boxed_3782_; lean_object* v_res_3783_; 
v___x_6949__boxed_3781_ = lean_unbox(v___x_3771_);
v___x_6950__boxed_3782_ = lean_unbox(v___x_3772_);
v_res_3783_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1(v___x_3767_, v_body_3768_, v_k_3769_, v___x_3770_, v___x_6949__boxed_3781_, v___x_6950__boxed_3782_, v_FNew_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_);
lean_dec(v___y_3779_);
lean_dec_ref(v___y_3778_);
lean_dec(v___y_3777_);
lean_dec_ref(v___y_3776_);
lean_dec(v___y_3775_);
lean_dec_ref(v___y_3774_);
lean_dec(v___x_3770_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2(lean_object* v___x_3784_, lean_object* v___x_3785_, lean_object* v_00_u03b1_3786_, lean_object* v_00_u03b2_3787_, lean_object* v___x_3788_, lean_object* v_ctorName_3789_, lean_object* v_k_3790_, lean_object* v___x_3791_, uint8_t v___x_3792_, uint8_t v___x_3793_, lean_object* v_a_3794_, lean_object* v_x_3795_, lean_object* v_xs_3796_, lean_object* v_body_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_){
_start:
{
lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; 
v___x_3805_ = lean_array_get_borrowed(v___x_3784_, v_xs_3796_, v___x_3785_);
v___x_3806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3806_, 0, v_00_u03b1_3786_);
v___x_3807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3807_, 0, v_00_u03b2_3787_);
lean_inc(v___x_3805_);
v___x_3808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3805_);
v___x_3809_ = lean_mk_empty_array_with_capacity(v___x_3788_);
v___x_3810_ = lean_array_push(v___x_3809_, v___x_3806_);
v___x_3811_ = lean_array_push(v___x_3810_, v___x_3807_);
v___x_3812_ = lean_array_push(v___x_3811_, v___x_3808_);
v___x_3813_ = l_Lean_Meta_mkAppOptM(v_ctorName_3789_, v___x_3812_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_);
if (lean_obj_tag(v___x_3813_) == 0)
{
lean_object* v_a_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___f_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; 
v_a_3814_ = lean_ctor_get(v___x_3813_, 0);
lean_inc(v_a_3814_);
lean_dec_ref_known(v___x_3813_, 1);
v___x_3815_ = lean_box(v___x_3792_);
v___x_3816_ = lean_box(v___x_3793_);
lean_inc(v___x_3805_);
v___f_3817_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1___boxed), 14, 6);
lean_closure_set(v___f_3817_, 0, v___x_3805_);
lean_closure_set(v___f_3817_, 1, v_body_3797_);
lean_closure_set(v___f_3817_, 2, v_k_3790_);
lean_closure_set(v___f_3817_, 3, v___x_3791_);
lean_closure_set(v___f_3817_, 4, v___x_3815_);
lean_closure_set(v___f_3817_, 5, v___x_3816_);
v___x_3818_ = l_Lean_LocalDecl_type(v_a_3794_);
v___x_3819_ = l_Lean_Expr_replaceFVar(v___x_3818_, v_x_3795_, v_a_3814_);
lean_dec(v_a_3814_);
lean_dec_ref(v___x_3818_);
v___x_3820_ = l_Lean_LocalDecl_userName(v_a_3794_);
v___x_3821_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v___x_3820_, v___x_3819_, v___f_3817_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_);
return v___x_3821_;
}
else
{
lean_dec_ref(v_body_3797_);
lean_dec_ref(v_x_3795_);
lean_dec(v___x_3791_);
lean_dec_ref(v_k_3790_);
return v___x_3813_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2___boxed(lean_object** _args){
lean_object* v___x_3822_ = _args[0];
lean_object* v___x_3823_ = _args[1];
lean_object* v_00_u03b1_3824_ = _args[2];
lean_object* v_00_u03b2_3825_ = _args[3];
lean_object* v___x_3826_ = _args[4];
lean_object* v_ctorName_3827_ = _args[5];
lean_object* v_k_3828_ = _args[6];
lean_object* v___x_3829_ = _args[7];
lean_object* v___x_3830_ = _args[8];
lean_object* v___x_3831_ = _args[9];
lean_object* v_a_3832_ = _args[10];
lean_object* v_x_3833_ = _args[11];
lean_object* v_xs_3834_ = _args[12];
lean_object* v_body_3835_ = _args[13];
lean_object* v___y_3836_ = _args[14];
lean_object* v___y_3837_ = _args[15];
lean_object* v___y_3838_ = _args[16];
lean_object* v___y_3839_ = _args[17];
lean_object* v___y_3840_ = _args[18];
lean_object* v___y_3841_ = _args[19];
lean_object* v___y_3842_ = _args[20];
_start:
{
uint8_t v___x_6970__boxed_3843_; uint8_t v___x_6971__boxed_3844_; lean_object* v_res_3845_; 
v___x_6970__boxed_3843_ = lean_unbox(v___x_3830_);
v___x_6971__boxed_3844_ = lean_unbox(v___x_3831_);
v_res_3845_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2(v___x_3822_, v___x_3823_, v_00_u03b1_3824_, v_00_u03b2_3825_, v___x_3826_, v_ctorName_3827_, v_k_3828_, v___x_3829_, v___x_6970__boxed_3843_, v___x_6971__boxed_3844_, v_a_3832_, v_x_3833_, v_xs_3834_, v_body_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_);
lean_dec(v___y_3841_);
lean_dec_ref(v___y_3840_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v___y_3837_);
lean_dec_ref(v___y_3836_);
lean_dec_ref(v_xs_3834_);
lean_dec_ref(v_a_3832_);
lean_dec(v___x_3826_);
lean_dec(v___x_3823_);
lean_dec_ref(v___x_3822_);
return v_res_3845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(lean_object* v___x_3846_, lean_object* v___x_3847_, lean_object* v_00_u03b1_3848_, lean_object* v_00_u03b2_3849_, lean_object* v___x_3850_, lean_object* v_k_3851_, lean_object* v___x_3852_, uint8_t v___x_3853_, uint8_t v___x_3854_, lean_object* v_a_3855_, lean_object* v_x_3856_, lean_object* v___x_3857_, lean_object* v_ctorName_3858_, lean_object* v_minor_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_){
_start:
{
lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___f_3869_; lean_object* v___x_3870_; 
v___x_3867_ = lean_box(v___x_3853_);
v___x_3868_ = lean_box(v___x_3854_);
v___f_3869_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2___boxed), 21, 12);
lean_closure_set(v___f_3869_, 0, v___x_3846_);
lean_closure_set(v___f_3869_, 1, v___x_3847_);
lean_closure_set(v___f_3869_, 2, v_00_u03b1_3848_);
lean_closure_set(v___f_3869_, 3, v_00_u03b2_3849_);
lean_closure_set(v___f_3869_, 4, v___x_3850_);
lean_closure_set(v___f_3869_, 5, v_ctorName_3858_);
lean_closure_set(v___f_3869_, 6, v_k_3851_);
lean_closure_set(v___f_3869_, 7, v___x_3852_);
lean_closure_set(v___f_3869_, 8, v___x_3867_);
lean_closure_set(v___f_3869_, 9, v___x_3868_);
lean_closure_set(v___f_3869_, 10, v_a_3855_);
lean_closure_set(v___f_3869_, 11, v_x_3856_);
v___x_3870_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_minor_3859_, v___x_3857_, v___f_3869_, v___x_3853_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_);
return v___x_3870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3___boxed(lean_object** _args){
lean_object* v___x_3871_ = _args[0];
lean_object* v___x_3872_ = _args[1];
lean_object* v_00_u03b1_3873_ = _args[2];
lean_object* v_00_u03b2_3874_ = _args[3];
lean_object* v___x_3875_ = _args[4];
lean_object* v_k_3876_ = _args[5];
lean_object* v___x_3877_ = _args[6];
lean_object* v___x_3878_ = _args[7];
lean_object* v___x_3879_ = _args[8];
lean_object* v_a_3880_ = _args[9];
lean_object* v_x_3881_ = _args[10];
lean_object* v___x_3882_ = _args[11];
lean_object* v_ctorName_3883_ = _args[12];
lean_object* v_minor_3884_ = _args[13];
lean_object* v___y_3885_ = _args[14];
lean_object* v___y_3886_ = _args[15];
lean_object* v___y_3887_ = _args[16];
lean_object* v___y_3888_ = _args[17];
lean_object* v___y_3889_ = _args[18];
lean_object* v___y_3890_ = _args[19];
lean_object* v___y_3891_ = _args[20];
_start:
{
uint8_t v___x_6934__boxed_3892_; uint8_t v___x_6935__boxed_3893_; lean_object* v_res_3894_; 
v___x_6934__boxed_3892_ = lean_unbox(v___x_3878_);
v___x_6935__boxed_3893_ = lean_unbox(v___x_3879_);
v_res_3894_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3871_, v___x_3872_, v_00_u03b1_3873_, v_00_u03b2_3874_, v___x_3875_, v_k_3876_, v___x_3877_, v___x_6934__boxed_3892_, v___x_6935__boxed_3893_, v_a_3880_, v_x_3881_, v___x_3882_, v_ctorName_3883_, v_minor_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_);
lean_dec(v___y_3890_);
lean_dec_ref(v___y_3889_);
lean_dec(v___y_3888_);
lean_dec_ref(v___y_3887_);
lean_dec(v___y_3886_);
lean_dec_ref(v___y_3885_);
return v_res_3894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___boxed(lean_object* v_x_3895_, lean_object* v_F_3896_, lean_object* v_val_3897_, lean_object* v_k_3898_, lean_object* v_a_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_){
_start:
{
lean_object* v_res_3906_; 
v_res_3906_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v_x_3895_, v_F_3896_, v_val_3897_, v_k_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_, v_a_3903_, v_a_3904_);
lean_dec(v_a_3904_);
lean_dec_ref(v_a_3903_);
lean_dec(v_a_3902_);
lean_dec_ref(v_a_3901_);
lean_dec(v_a_3900_);
lean_dec_ref(v_a_3899_);
return v_res_3906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1(lean_object* v_00_u03b1_3907_, lean_object* v_name_3908_, uint8_t v_bi_3909_, lean_object* v_type_3910_, lean_object* v_k_3911_, uint8_t v_kind_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_){
_start:
{
lean_object* v___x_3920_; 
v___x_3920_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(v_name_3908_, v_bi_3909_, v_type_3910_, v_k_3911_, v_kind_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_);
return v___x_3920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___boxed(lean_object* v_00_u03b1_3921_, lean_object* v_name_3922_, lean_object* v_bi_3923_, lean_object* v_type_3924_, lean_object* v_k_3925_, lean_object* v_kind_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_){
_start:
{
uint8_t v_bi_boxed_3934_; uint8_t v_kind_boxed_3935_; lean_object* v_res_3936_; 
v_bi_boxed_3934_ = lean_unbox(v_bi_3923_);
v_kind_boxed_3935_ = lean_unbox(v_kind_3926_);
v_res_3936_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1(v_00_u03b1_3921_, v_name_3922_, v_bi_boxed_3934_, v_type_3924_, v_k_3925_, v_kind_boxed_3935_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_);
lean_dec(v___y_3932_);
lean_dec_ref(v___y_3931_);
lean_dec(v___y_3930_);
lean_dec_ref(v___y_3929_);
lean_dec(v___y_3928_);
lean_dec_ref(v___y_3927_);
return v_res_3936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1(lean_object* v_00_u03b1_3937_, lean_object* v_name_3938_, lean_object* v_type_3939_, lean_object* v_k_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_){
_start:
{
lean_object* v___x_3948_; 
v___x_3948_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_name_3938_, v_type_3939_, v_k_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_);
return v___x_3948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___boxed(lean_object* v_00_u03b1_3949_, lean_object* v_name_3950_, lean_object* v_type_3951_, lean_object* v_k_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_){
_start:
{
lean_object* v_res_3960_; 
v_res_3960_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1(v_00_u03b1_3949_, v_name_3950_, v_type_3951_, v_k_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_);
lean_dec(v___y_3958_);
lean_dec_ref(v___y_3957_);
lean_dec(v___y_3956_);
lean_dec_ref(v___y_3955_);
lean_dec(v___y_3954_);
lean_dec_ref(v___y_3953_);
return v_res_3960_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3961_; 
v___x_3961_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return v___x_3961_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(lean_object* v_msg_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_){
_start:
{
lean_object* v___x_3970_; lean_object* v___x_3874__overap_3971_; lean_object* v___x_3972_; 
v___x_3970_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0, &l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0);
v___x_3874__overap_3971_ = lean_panic_fn_borrowed(v___x_3970_, v_msg_3962_);
lean_inc(v___y_3968_);
lean_inc_ref(v___y_3967_);
lean_inc(v___y_3966_);
lean_inc_ref(v___y_3965_);
lean_inc(v___y_3964_);
lean_inc_ref(v___y_3963_);
v___x_3972_ = lean_apply_7(v___x_3874__overap_3971_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, lean_box(0));
return v___x_3972_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___boxed(lean_object* v_msg_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_){
_start:
{
lean_object* v_res_3981_; 
v_res_3981_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(v_msg_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_);
lean_dec(v___y_3979_);
lean_dec_ref(v___y_3978_);
lean_dec(v___y_3977_);
lean_dec_ref(v___y_3976_);
lean_dec(v___y_3975_);
lean_dec_ref(v___y_3974_);
return v_res_3981_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3(void){
_start:
{
lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; 
v___x_3985_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__2));
v___x_3986_ = lean_unsigned_to_nat(49u);
v___x_3987_ = lean_unsigned_to_nat(186u);
v___x_3988_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__1));
v___x_3989_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__0));
v___x_3990_ = l_mkPanicMessageWithDecl(v___x_3989_, v___x_3988_, v___x_3987_, v___x_3986_, v___x_3985_);
return v___x_3990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1___boxed(lean_object* v___x_3996_, lean_object* v_a_3997_, lean_object* v_k_3998_, lean_object* v___x_3999_, lean_object* v___x_4000_, lean_object* v___x_4001_, lean_object* v___x_4002_, lean_object* v___x_4003_, lean_object* v_FNew_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_){
_start:
{
uint8_t v___x_4042__boxed_4012_; uint8_t v___x_4043__boxed_4013_; uint8_t v___x_4044__boxed_4014_; lean_object* v_res_4015_; 
v___x_4042__boxed_4012_ = lean_unbox(v___x_4001_);
v___x_4043__boxed_4013_ = lean_unbox(v___x_4002_);
v___x_4044__boxed_4014_ = lean_unbox(v___x_4003_);
v_res_4015_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1(v___x_3996_, v_a_3997_, v_k_3998_, v___x_3999_, v___x_4000_, v___x_4042__boxed_4012_, v___x_4043__boxed_4013_, v___x_4044__boxed_4014_, v_FNew_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_);
lean_dec(v___y_4010_);
lean_dec_ref(v___y_4009_);
lean_dec(v___y_4008_);
lean_dec_ref(v___y_4007_);
lean_dec(v___y_4006_);
lean_dec_ref(v___y_4005_);
lean_dec(v___x_3999_);
return v_res_4015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0(lean_object* v___x_4016_, lean_object* v___x_4017_, lean_object* v___x_4018_, lean_object* v___x_4019_, uint8_t v___x_4020_, uint8_t v___x_4021_, lean_object* v_00_u03b1_4022_, lean_object* v_00_u03b2_4023_, lean_object* v___x_4024_, lean_object* v_k_4025_, lean_object* v___x_4026_, lean_object* v_a_4027_, lean_object* v_x_4028_, lean_object* v_xs_4029_, lean_object* v_body_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_){
_start:
{
lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; uint8_t v___x_4043_; lean_object* v___x_4044_; 
v___x_4038_ = lean_array_get(v___x_4016_, v_xs_4029_, v___x_4017_);
v___x_4039_ = lean_array_get(v___x_4016_, v_xs_4029_, v___x_4018_);
v___x_4040_ = lean_array_get_size(v_xs_4029_);
v___x_4041_ = l_Array_toSubarray___redArg(v_xs_4029_, v___x_4019_, v___x_4040_);
v___x_4042_ = l_Subarray_copy___redArg(v___x_4041_);
v___x_4043_ = 1;
v___x_4044_ = l_Lean_Meta_mkLambdaFVars(v___x_4042_, v_body_4030_, v___x_4020_, v___x_4021_, v___x_4020_, v___x_4021_, v___x_4043_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_);
lean_dec_ref(v___x_4042_);
if (lean_obj_tag(v___x_4044_) == 0)
{
lean_object* v_a_4045_; lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4071_; 
v_a_4045_ = lean_ctor_get(v___x_4044_, 0);
v_isSharedCheck_4071_ = !lean_is_exclusive(v___x_4044_);
if (v_isSharedCheck_4071_ == 0)
{
v___x_4047_ = v___x_4044_;
v_isShared_4048_ = v_isSharedCheck_4071_;
goto v_resetjp_4046_;
}
else
{
lean_inc(v_a_4045_);
lean_dec(v___x_4044_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4071_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v___x_4049_; lean_object* v___x_4051_; 
v___x_4049_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__2));
if (v_isShared_4048_ == 0)
{
lean_ctor_set_tag(v___x_4047_, 1);
lean_ctor_set(v___x_4047_, 0, v_00_u03b1_4022_);
v___x_4051_ = v___x_4047_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_00_u03b1_4022_);
v___x_4051_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; 
v___x_4052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4052_, 0, v_00_u03b2_4023_);
lean_inc(v___x_4038_);
v___x_4053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4053_, 0, v___x_4038_);
lean_inc(v___x_4039_);
v___x_4054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4054_, 0, v___x_4039_);
v___x_4055_ = lean_mk_empty_array_with_capacity(v___x_4024_);
v___x_4056_ = lean_array_push(v___x_4055_, v___x_4051_);
v___x_4057_ = lean_array_push(v___x_4056_, v___x_4052_);
v___x_4058_ = lean_array_push(v___x_4057_, v___x_4053_);
v___x_4059_ = lean_array_push(v___x_4058_, v___x_4054_);
v___x_4060_ = l_Lean_Meta_mkAppOptM(v___x_4049_, v___x_4059_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_);
if (lean_obj_tag(v___x_4060_) == 0)
{
lean_object* v_a_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___f_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; 
v_a_4061_ = lean_ctor_get(v___x_4060_, 0);
lean_inc(v_a_4061_);
lean_dec_ref_known(v___x_4060_, 1);
v___x_4062_ = lean_box(v___x_4020_);
v___x_4063_ = lean_box(v___x_4021_);
v___x_4064_ = lean_box(v___x_4043_);
v___f_4065_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1___boxed), 16, 8);
lean_closure_set(v___f_4065_, 0, v___x_4039_);
lean_closure_set(v___f_4065_, 1, v_a_4045_);
lean_closure_set(v___f_4065_, 2, v_k_4025_);
lean_closure_set(v___f_4065_, 3, v___x_4026_);
lean_closure_set(v___f_4065_, 4, v___x_4038_);
lean_closure_set(v___f_4065_, 5, v___x_4062_);
lean_closure_set(v___f_4065_, 6, v___x_4063_);
lean_closure_set(v___f_4065_, 7, v___x_4064_);
v___x_4066_ = l_Lean_LocalDecl_type(v_a_4027_);
v___x_4067_ = l_Lean_Expr_replaceFVar(v___x_4066_, v_x_4028_, v_a_4061_);
lean_dec(v_a_4061_);
lean_dec_ref(v___x_4066_);
v___x_4068_ = l_Lean_LocalDecl_userName(v_a_4027_);
v___x_4069_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v___x_4068_, v___x_4067_, v___f_4065_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_);
return v___x_4069_;
}
else
{
lean_dec(v_a_4045_);
lean_dec(v___x_4039_);
lean_dec(v___x_4038_);
lean_dec_ref(v_x_4028_);
lean_dec(v___x_4026_);
lean_dec_ref(v_k_4025_);
return v___x_4060_;
}
}
}
}
else
{
lean_dec(v___x_4039_);
lean_dec(v___x_4038_);
lean_dec_ref(v_x_4028_);
lean_dec(v___x_4026_);
lean_dec_ref(v_k_4025_);
lean_dec_ref(v_00_u03b2_4023_);
lean_dec_ref(v_00_u03b1_4022_);
return v___x_4044_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___boxed(lean_object** _args){
lean_object* v___x_4072_ = _args[0];
lean_object* v___x_4073_ = _args[1];
lean_object* v___x_4074_ = _args[2];
lean_object* v___x_4075_ = _args[3];
lean_object* v___x_4076_ = _args[4];
lean_object* v___x_4077_ = _args[5];
lean_object* v_00_u03b1_4078_ = _args[6];
lean_object* v_00_u03b2_4079_ = _args[7];
lean_object* v___x_4080_ = _args[8];
lean_object* v_k_4081_ = _args[9];
lean_object* v___x_4082_ = _args[10];
lean_object* v_a_4083_ = _args[11];
lean_object* v_x_4084_ = _args[12];
lean_object* v_xs_4085_ = _args[13];
lean_object* v_body_4086_ = _args[14];
lean_object* v___y_4087_ = _args[15];
lean_object* v___y_4088_ = _args[16];
lean_object* v___y_4089_ = _args[17];
lean_object* v___y_4090_ = _args[18];
lean_object* v___y_4091_ = _args[19];
lean_object* v___y_4092_ = _args[20];
lean_object* v___y_4093_ = _args[21];
_start:
{
uint8_t v___x_4069__boxed_4094_; uint8_t v___x_4070__boxed_4095_; lean_object* v_res_4096_; 
v___x_4069__boxed_4094_ = lean_unbox(v___x_4076_);
v___x_4070__boxed_4095_ = lean_unbox(v___x_4077_);
v_res_4096_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0(v___x_4072_, v___x_4073_, v___x_4074_, v___x_4075_, v___x_4069__boxed_4094_, v___x_4070__boxed_4095_, v_00_u03b1_4078_, v_00_u03b2_4079_, v___x_4080_, v_k_4081_, v___x_4082_, v_a_4083_, v_x_4084_, v_xs_4085_, v_body_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_);
lean_dec(v___y_4092_);
lean_dec_ref(v___y_4091_);
lean_dec(v___y_4090_);
lean_dec_ref(v___y_4089_);
lean_dec(v___y_4088_);
lean_dec_ref(v___y_4087_);
lean_dec_ref(v_a_4083_);
lean_dec(v___x_4080_);
lean_dec(v___x_4074_);
lean_dec(v___x_4073_);
lean_dec_ref(v___x_4072_);
return v_res_4096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(lean_object* v_x_4100_, lean_object* v_F_4101_, lean_object* v_val_4102_, lean_object* v_k_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_, lean_object* v_a_4108_, lean_object* v_a_4109_){
_start:
{
lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4117_; uint8_t v___y_4121_; uint8_t v___x_4213_; 
v___x_4213_ = l_Lean_Expr_isFVar(v_x_4100_);
if (v___x_4213_ == 0)
{
v___y_4121_ = v___x_4213_;
goto v___jp_4120_;
}
else
{
lean_object* v___x_4214_; lean_object* v___x_4215_; uint8_t v___x_4216_; 
v___x_4214_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4));
v___x_4215_ = lean_unsigned_to_nat(5u);
v___x_4216_ = l_Lean_Expr_isAppOfArity(v_val_4102_, v___x_4214_, v___x_4215_);
v___y_4121_ = v___x_4216_;
goto v___jp_4120_;
}
v___jp_4111_:
{
lean_object* v___x_4118_; lean_object* v___x_4119_; 
v___x_4118_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3);
v___x_4119_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(v___x_4118_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_);
return v___x_4119_;
}
v___jp_4120_:
{
if (v___y_4121_ == 0)
{
lean_object* v___x_4122_; 
lean_dec_ref(v_x_4100_);
lean_inc(v_a_4109_);
lean_inc_ref(v_a_4108_);
lean_inc(v_a_4107_);
lean_inc_ref(v_a_4106_);
lean_inc(v_a_4105_);
lean_inc_ref(v_a_4104_);
v___x_4122_ = lean_apply_9(v_k_4103_, v_F_4101_, v_val_4102_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, lean_box(0));
return v___x_4122_;
}
else
{
lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; uint8_t v___x_4129_; 
v___x_4123_ = lean_unsigned_to_nat(3u);
v___x_4124_ = l_Lean_Expr_getAppNumArgs(v_val_4102_);
v___x_4125_ = lean_nat_sub(v___x_4124_, v___x_4123_);
v___x_4126_ = lean_unsigned_to_nat(1u);
v___x_4127_ = lean_nat_sub(v___x_4125_, v___x_4126_);
lean_dec(v___x_4125_);
v___x_4128_ = l_Lean_Expr_getRevArg_x21(v_val_4102_, v___x_4127_);
v___x_4129_ = lean_expr_eqv(v___x_4128_, v_x_4100_);
lean_dec_ref(v___x_4128_);
if (v___x_4129_ == 0)
{
lean_object* v___x_4130_; 
lean_dec(v___x_4124_);
lean_dec_ref(v_x_4100_);
lean_inc(v_a_4109_);
lean_inc_ref(v_a_4108_);
lean_inc(v_a_4107_);
lean_inc_ref(v_a_4106_);
lean_inc(v_a_4105_);
lean_inc_ref(v_a_4104_);
v___x_4130_ = lean_apply_9(v_k_4103_, v_F_4101_, v_val_4102_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, lean_box(0));
return v___x_4130_;
}
else
{
lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; uint8_t v___x_4135_; 
v___x_4131_ = lean_unsigned_to_nat(4u);
v___x_4132_ = lean_nat_sub(v___x_4124_, v___x_4131_);
v___x_4133_ = lean_nat_sub(v___x_4132_, v___x_4126_);
lean_dec(v___x_4132_);
v___x_4134_ = l_Lean_Expr_getRevArg_x21(v_val_4102_, v___x_4133_);
v___x_4135_ = l_Lean_Expr_isLambda(v___x_4134_);
if (v___x_4135_ == 0)
{
lean_object* v___x_4136_; 
lean_dec_ref(v___x_4134_);
lean_dec(v___x_4124_);
lean_dec_ref(v_x_4100_);
lean_inc(v_a_4109_);
lean_inc_ref(v_a_4108_);
lean_inc(v_a_4107_);
lean_inc_ref(v_a_4106_);
lean_inc(v_a_4105_);
lean_inc_ref(v_a_4104_);
v___x_4136_ = lean_apply_9(v_k_4103_, v_F_4101_, v_val_4102_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, lean_box(0));
return v___x_4136_;
}
else
{
lean_object* v___x_4137_; uint8_t v___x_4138_; 
v___x_4137_ = l_Lean_Expr_bindingBody_x21(v___x_4134_);
lean_dec_ref(v___x_4134_);
v___x_4138_ = l_Lean_Expr_isLambda(v___x_4137_);
lean_dec_ref(v___x_4137_);
if (v___x_4138_ == 0)
{
lean_object* v___x_4139_; 
lean_dec(v___x_4124_);
lean_dec_ref(v_x_4100_);
lean_inc(v_a_4109_);
lean_inc_ref(v_a_4108_);
lean_inc(v_a_4107_);
lean_inc_ref(v_a_4106_);
lean_inc(v_a_4105_);
lean_inc_ref(v_a_4104_);
v___x_4139_ = lean_apply_9(v_k_4103_, v_F_4101_, v_val_4102_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, lean_box(0));
return v___x_4139_;
}
else
{
lean_object* v___x_4140_; lean_object* v___x_4141_; 
v___x_4140_ = l_Lean_Expr_getAppFn(v_val_4102_);
v___x_4141_ = l_Lean_Expr_constLevels_x21(v___x_4140_);
lean_dec_ref(v___x_4140_);
if (lean_obj_tag(v___x_4141_) == 1)
{
lean_object* v_tail_4142_; 
v_tail_4142_ = lean_ctor_get(v___x_4141_, 1);
lean_inc(v_tail_4142_);
lean_dec_ref_known(v___x_4141_, 2);
if (lean_obj_tag(v_tail_4142_) == 1)
{
lean_object* v_tail_4143_; 
v_tail_4143_ = lean_ctor_get(v_tail_4142_, 1);
lean_inc(v_tail_4143_);
if (lean_obj_tag(v_tail_4143_) == 1)
{
lean_object* v_tail_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4211_; 
v_tail_4144_ = lean_ctor_get(v_tail_4143_, 1);
v_isSharedCheck_4211_ = !lean_is_exclusive(v_tail_4143_);
if (v_isSharedCheck_4211_ == 0)
{
lean_object* v_unused_4212_; 
v_unused_4212_ = lean_ctor_get(v_tail_4143_, 0);
lean_dec(v_unused_4212_);
v___x_4146_ = v_tail_4143_;
v_isShared_4147_ = v_isSharedCheck_4211_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_tail_4144_);
lean_dec(v_tail_4143_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4211_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
if (lean_obj_tag(v_tail_4144_) == 0)
{
lean_object* v___x_4148_; lean_object* v___x_4149_; 
v___x_4148_ = l_Lean_Expr_fvarId_x21(v_F_4101_);
v___x_4149_ = l_Lean_FVarId_getDecl___redArg(v___x_4148_, v_a_4106_, v_a_4108_, v_a_4109_);
if (lean_obj_tag(v___x_4149_) == 0)
{
lean_object* v_a_4150_; lean_object* v___x_4151_; lean_object* v_dummy_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v_args_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___f_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; uint8_t v___x_4161_; lean_object* v___x_4162_; 
v_a_4150_ = lean_ctor_get(v___x_4149_, 0);
lean_inc_n(v_a_4150_, 2);
lean_dec_ref_known(v___x_4149_, 1);
v___x_4151_ = l_Lean_instInhabitedExpr;
v_dummy_4152_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___closed__0);
lean_inc(v___x_4124_);
v___x_4153_ = lean_mk_array(v___x_4124_, v_dummy_4152_);
v___x_4154_ = lean_nat_sub(v___x_4124_, v___x_4126_);
lean_dec(v___x_4124_);
v_args_4155_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_4102_, v___x_4153_, v___x_4154_);
v___x_4156_ = lean_unsigned_to_nat(0u);
v___x_4157_ = lean_box(v___x_4135_);
lean_inc_ref(v_x_4100_);
v___f_4158_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed), 14, 5);
lean_closure_set(v___f_4158_, 0, v_a_4150_);
lean_closure_set(v___f_4158_, 1, v___x_4151_);
lean_closure_set(v___f_4158_, 2, v___x_4156_);
lean_closure_set(v___f_4158_, 3, v_x_4100_);
lean_closure_set(v___f_4158_, 4, v___x_4157_);
v___x_4159_ = lean_unsigned_to_nat(2u);
v___x_4160_ = lean_array_get(v___x_4151_, v_args_4155_, v___x_4159_);
v___x_4161_ = 0;
v___x_4162_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_4160_, v___f_4158_, v___x_4161_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_);
if (lean_obj_tag(v___x_4162_) == 0)
{
lean_object* v_a_4163_; lean_object* v_fst_4164_; lean_object* v_snd_4165_; lean_object* v_00_u03b1_4166_; lean_object* v_00_u03b2_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___f_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; 
v_a_4163_ = lean_ctor_get(v___x_4162_, 0);
lean_inc(v_a_4163_);
lean_dec_ref_known(v___x_4162_, 1);
v_fst_4164_ = lean_ctor_get(v_a_4163_, 0);
lean_inc(v_fst_4164_);
v_snd_4165_ = lean_ctor_get(v_a_4163_, 1);
lean_inc(v_snd_4165_);
lean_dec(v_a_4163_);
v_00_u03b1_4166_ = lean_array_get(v___x_4151_, v_args_4155_, v___x_4156_);
v_00_u03b2_4167_ = lean_array_get(v___x_4151_, v_args_4155_, v___x_4126_);
v___x_4168_ = lean_box(v___x_4161_);
v___x_4169_ = lean_box(v___x_4135_);
lean_inc_ref(v_x_4100_);
lean_inc(v_00_u03b2_4167_);
lean_inc(v_00_u03b1_4166_);
v___f_4170_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___boxed), 22, 13);
lean_closure_set(v___f_4170_, 0, v___x_4151_);
lean_closure_set(v___f_4170_, 1, v___x_4156_);
lean_closure_set(v___f_4170_, 2, v___x_4126_);
lean_closure_set(v___f_4170_, 3, v___x_4159_);
lean_closure_set(v___f_4170_, 4, v___x_4168_);
lean_closure_set(v___f_4170_, 5, v___x_4169_);
lean_closure_set(v___f_4170_, 6, v_00_u03b1_4166_);
lean_closure_set(v___f_4170_, 7, v_00_u03b2_4167_);
lean_closure_set(v___f_4170_, 8, v___x_4131_);
lean_closure_set(v___f_4170_, 9, v_k_4103_);
lean_closure_set(v___f_4170_, 10, v___x_4123_);
lean_closure_set(v___f_4170_, 11, v_a_4150_);
lean_closure_set(v___f_4170_, 12, v_x_4100_);
v___x_4171_ = lean_array_get(v___x_4151_, v_args_4155_, v___x_4131_);
lean_dec_ref(v_args_4155_);
v___x_4172_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_4171_, v___f_4170_, v___x_4161_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_);
if (lean_obj_tag(v___x_4172_) == 0)
{
lean_object* v_a_4173_; lean_object* v___x_4175_; uint8_t v_isShared_4176_; uint8_t v_isSharedCheck_4194_; 
v_a_4173_ = lean_ctor_get(v___x_4172_, 0);
v_isSharedCheck_4194_ = !lean_is_exclusive(v___x_4172_);
if (v_isSharedCheck_4194_ == 0)
{
v___x_4175_ = v___x_4172_;
v_isShared_4176_ = v_isSharedCheck_4194_;
goto v_resetjp_4174_;
}
else
{
lean_inc(v_a_4173_);
lean_dec(v___x_4172_);
v___x_4175_ = lean_box(0);
v_isShared_4176_ = v_isSharedCheck_4194_;
goto v_resetjp_4174_;
}
v_resetjp_4174_:
{
lean_object* v___x_4177_; lean_object* v___x_4179_; 
v___x_4177_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4));
if (v_isShared_4147_ == 0)
{
lean_ctor_set(v___x_4146_, 1, v_tail_4142_);
lean_ctor_set(v___x_4146_, 0, v_snd_4165_);
v___x_4179_ = v___x_4146_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4193_; 
v_reuseFailAlloc_4193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4193_, 0, v_snd_4165_);
lean_ctor_set(v_reuseFailAlloc_4193_, 1, v_tail_4142_);
v___x_4179_ = v_reuseFailAlloc_4193_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4191_; 
v___x_4180_ = l_Lean_mkConst(v___x_4177_, v___x_4179_);
v___x_4181_ = lean_unsigned_to_nat(6u);
v___x_4182_ = lean_mk_empty_array_with_capacity(v___x_4181_);
v___x_4183_ = lean_array_push(v___x_4182_, v_00_u03b1_4166_);
v___x_4184_ = lean_array_push(v___x_4183_, v_00_u03b2_4167_);
v___x_4185_ = lean_array_push(v___x_4184_, v_fst_4164_);
v___x_4186_ = lean_array_push(v___x_4185_, v_x_4100_);
v___x_4187_ = lean_array_push(v___x_4186_, v_a_4173_);
v___x_4188_ = lean_array_push(v___x_4187_, v_F_4101_);
v___x_4189_ = l_Lean_mkAppN(v___x_4180_, v___x_4188_);
lean_dec_ref(v___x_4188_);
if (v_isShared_4176_ == 0)
{
lean_ctor_set(v___x_4175_, 0, v___x_4189_);
v___x_4191_ = v___x_4175_;
goto v_reusejp_4190_;
}
else
{
lean_object* v_reuseFailAlloc_4192_; 
v_reuseFailAlloc_4192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4192_, 0, v___x_4189_);
v___x_4191_ = v_reuseFailAlloc_4192_;
goto v_reusejp_4190_;
}
v_reusejp_4190_:
{
return v___x_4191_;
}
}
}
}
else
{
lean_dec(v_00_u03b2_4167_);
lean_dec(v_00_u03b1_4166_);
lean_dec(v_snd_4165_);
lean_dec(v_fst_4164_);
lean_del_object(v___x_4146_);
lean_dec_ref_known(v_tail_4142_, 2);
lean_dec_ref(v_F_4101_);
lean_dec_ref(v_x_4100_);
return v___x_4172_;
}
}
else
{
lean_object* v_a_4195_; lean_object* v___x_4197_; uint8_t v_isShared_4198_; uint8_t v_isSharedCheck_4202_; 
lean_dec_ref(v_args_4155_);
lean_dec(v_a_4150_);
lean_del_object(v___x_4146_);
lean_dec_ref_known(v_tail_4142_, 2);
lean_dec_ref(v_k_4103_);
lean_dec_ref(v_F_4101_);
lean_dec_ref(v_x_4100_);
v_a_4195_ = lean_ctor_get(v___x_4162_, 0);
v_isSharedCheck_4202_ = !lean_is_exclusive(v___x_4162_);
if (v_isSharedCheck_4202_ == 0)
{
v___x_4197_ = v___x_4162_;
v_isShared_4198_ = v_isSharedCheck_4202_;
goto v_resetjp_4196_;
}
else
{
lean_inc(v_a_4195_);
lean_dec(v___x_4162_);
v___x_4197_ = lean_box(0);
v_isShared_4198_ = v_isSharedCheck_4202_;
goto v_resetjp_4196_;
}
v_resetjp_4196_:
{
lean_object* v___x_4200_; 
if (v_isShared_4198_ == 0)
{
v___x_4200_ = v___x_4197_;
goto v_reusejp_4199_;
}
else
{
lean_object* v_reuseFailAlloc_4201_; 
v_reuseFailAlloc_4201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4201_, 0, v_a_4195_);
v___x_4200_ = v_reuseFailAlloc_4201_;
goto v_reusejp_4199_;
}
v_reusejp_4199_:
{
return v___x_4200_;
}
}
}
}
else
{
lean_object* v_a_4203_; lean_object* v___x_4205_; uint8_t v_isShared_4206_; uint8_t v_isSharedCheck_4210_; 
lean_del_object(v___x_4146_);
lean_dec_ref_known(v_tail_4142_, 2);
lean_dec(v___x_4124_);
lean_dec_ref(v_k_4103_);
lean_dec_ref(v_val_4102_);
lean_dec_ref(v_F_4101_);
lean_dec_ref(v_x_4100_);
v_a_4203_ = lean_ctor_get(v___x_4149_, 0);
v_isSharedCheck_4210_ = !lean_is_exclusive(v___x_4149_);
if (v_isSharedCheck_4210_ == 0)
{
v___x_4205_ = v___x_4149_;
v_isShared_4206_ = v_isSharedCheck_4210_;
goto v_resetjp_4204_;
}
else
{
lean_inc(v_a_4203_);
lean_dec(v___x_4149_);
v___x_4205_ = lean_box(0);
v_isShared_4206_ = v_isSharedCheck_4210_;
goto v_resetjp_4204_;
}
v_resetjp_4204_:
{
lean_object* v___x_4208_; 
if (v_isShared_4206_ == 0)
{
v___x_4208_ = v___x_4205_;
goto v_reusejp_4207_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v_a_4203_);
v___x_4208_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4207_;
}
v_reusejp_4207_:
{
return v___x_4208_;
}
}
}
}
else
{
lean_del_object(v___x_4146_);
lean_dec(v_tail_4144_);
lean_dec_ref_known(v_tail_4142_, 2);
lean_dec(v___x_4124_);
lean_dec_ref(v_k_4103_);
lean_dec_ref(v_val_4102_);
lean_dec_ref(v_F_4101_);
lean_dec_ref(v_x_4100_);
v___y_4112_ = v_a_4104_;
v___y_4113_ = v_a_4105_;
v___y_4114_ = v_a_4106_;
v___y_4115_ = v_a_4107_;
v___y_4116_ = v_a_4108_;
v___y_4117_ = v_a_4109_;
goto v___jp_4111_;
}
}
}
else
{
lean_dec(v_tail_4143_);
lean_dec_ref_known(v_tail_4142_, 2);
lean_dec(v___x_4124_);
lean_dec_ref(v_k_4103_);
lean_dec_ref(v_val_4102_);
lean_dec_ref(v_F_4101_);
lean_dec_ref(v_x_4100_);
v___y_4112_ = v_a_4104_;
v___y_4113_ = v_a_4105_;
v___y_4114_ = v_a_4106_;
v___y_4115_ = v_a_4107_;
v___y_4116_ = v_a_4108_;
v___y_4117_ = v_a_4109_;
goto v___jp_4111_;
}
}
else
{
lean_dec(v_tail_4142_);
lean_dec(v___x_4124_);
lean_dec_ref(v_k_4103_);
lean_dec_ref(v_val_4102_);
lean_dec_ref(v_F_4101_);
lean_dec_ref(v_x_4100_);
v___y_4112_ = v_a_4104_;
v___y_4113_ = v_a_4105_;
v___y_4114_ = v_a_4106_;
v___y_4115_ = v_a_4107_;
v___y_4116_ = v_a_4108_;
v___y_4117_ = v_a_4109_;
goto v___jp_4111_;
}
}
else
{
lean_dec(v___x_4141_);
lean_dec(v___x_4124_);
lean_dec_ref(v_k_4103_);
lean_dec_ref(v_val_4102_);
lean_dec_ref(v_F_4101_);
lean_dec_ref(v_x_4100_);
v___y_4112_ = v_a_4104_;
v___y_4113_ = v_a_4105_;
v___y_4114_ = v_a_4106_;
v___y_4115_ = v_a_4107_;
v___y_4116_ = v_a_4108_;
v___y_4117_ = v_a_4109_;
goto v___jp_4111_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1(lean_object* v___x_4217_, lean_object* v_a_4218_, lean_object* v_k_4219_, lean_object* v___x_4220_, lean_object* v___x_4221_, uint8_t v___x_4222_, uint8_t v___x_4223_, uint8_t v___x_4224_, lean_object* v_FNew_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_){
_start:
{
lean_object* v___x_4233_; 
lean_inc_ref(v_FNew_4225_);
lean_inc_ref(v___x_4217_);
v___x_4233_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v___x_4217_, v_FNew_4225_, v_a_4218_, v_k_4219_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_);
if (lean_obj_tag(v___x_4233_) == 0)
{
lean_object* v_a_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; 
v_a_4234_ = lean_ctor_get(v___x_4233_, 0);
lean_inc(v_a_4234_);
lean_dec_ref_known(v___x_4233_, 1);
v___x_4235_ = lean_mk_empty_array_with_capacity(v___x_4220_);
v___x_4236_ = lean_array_push(v___x_4235_, v___x_4221_);
v___x_4237_ = lean_array_push(v___x_4236_, v___x_4217_);
v___x_4238_ = lean_array_push(v___x_4237_, v_FNew_4225_);
v___x_4239_ = l_Lean_Meta_mkLambdaFVars(v___x_4238_, v_a_4234_, v___x_4222_, v___x_4223_, v___x_4222_, v___x_4223_, v___x_4224_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_);
lean_dec_ref(v___x_4238_);
return v___x_4239_;
}
else
{
lean_dec_ref(v_FNew_4225_);
lean_dec_ref(v___x_4221_);
lean_dec_ref(v___x_4217_);
return v___x_4233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___boxed(lean_object* v_x_4240_, lean_object* v_F_4241_, lean_object* v_val_4242_, lean_object* v_k_4243_, lean_object* v_a_4244_, lean_object* v_a_4245_, lean_object* v_a_4246_, lean_object* v_a_4247_, lean_object* v_a_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_){
_start:
{
lean_object* v_res_4251_; 
v_res_4251_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v_x_4240_, v_F_4241_, v_val_4242_, v_k_4243_, v_a_4244_, v_a_4245_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_);
lean_dec(v_a_4249_);
lean_dec_ref(v_a_4248_);
lean_dec(v_a_4247_);
lean_dec_ref(v_a_4246_);
lean_dec(v_a_4245_);
lean_dec_ref(v_a_4244_);
return v_res_4251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0(lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_){
_start:
{
lean_object* v___x_4265_; 
v___x_4265_ = l_Lean_Elab_WF_applyCleanWfTactic(v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_);
if (lean_obj_tag(v___x_4265_) == 0)
{
lean_object* v_ref_4266_; uint8_t v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; 
lean_dec_ref_known(v___x_4265_, 1);
v_ref_4266_ = lean_ctor_get(v___y_4262_, 5);
v___x_4267_ = 0;
v___x_4268_ = l_Lean_SourceInfo_fromRef(v_ref_4266_, v___x_4267_);
v___x_4269_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__1));
v___x_4270_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__2));
lean_inc(v___x_4268_);
v___x_4271_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4271_, 0, v___x_4268_);
lean_ctor_set(v___x_4271_, 1, v___x_4270_);
v___x_4272_ = l_Lean_Syntax_node1(v___x_4268_, v___x_4269_, v___x_4271_);
v___x_4273_ = l_Lean_Elab_Tactic_evalTactic(v___x_4272_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_);
return v___x_4273_;
}
else
{
return v___x_4265_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___boxed(lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_){
_start:
{
lean_object* v_res_4283_; 
v_res_4283_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0(v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_);
lean_dec(v___y_4281_);
lean_dec_ref(v___y_4280_);
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4278_);
lean_dec(v___y_4277_);
lean_dec_ref(v___y_4276_);
lean_dec(v___y_4275_);
lean_dec_ref(v___y_4274_);
return v_res_4283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(lean_object* v_mvarId_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_){
_start:
{
lean_object* v___f_4293_; lean_object* v___x_4294_; 
v___f_4293_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___closed__0));
v___x_4294_ = l_Lean_Elab_Tactic_run(v_mvarId_4285_, v___f_4293_, v_a_4286_, v_a_4287_, v_a_4288_, v_a_4289_, v_a_4290_, v_a_4291_);
if (lean_obj_tag(v___x_4294_) == 0)
{
lean_object* v_a_4295_; lean_object* v___x_4297_; uint8_t v_isShared_4298_; uint8_t v_isSharedCheck_4305_; 
v_a_4295_ = lean_ctor_get(v___x_4294_, 0);
v_isSharedCheck_4305_ = !lean_is_exclusive(v___x_4294_);
if (v_isSharedCheck_4305_ == 0)
{
v___x_4297_ = v___x_4294_;
v_isShared_4298_ = v_isSharedCheck_4305_;
goto v_resetjp_4296_;
}
else
{
lean_inc(v_a_4295_);
lean_dec(v___x_4294_);
v___x_4297_ = lean_box(0);
v_isShared_4298_ = v_isSharedCheck_4305_;
goto v_resetjp_4296_;
}
v_resetjp_4296_:
{
uint8_t v___x_4299_; 
v___x_4299_ = l_List_isEmpty___redArg(v_a_4295_);
if (v___x_4299_ == 0)
{
lean_object* v___x_4300_; 
lean_del_object(v___x_4297_);
v___x_4300_ = l_Lean_Elab_Term_reportUnsolvedGoals(v_a_4295_, v_a_4288_, v_a_4289_, v_a_4290_, v_a_4291_);
return v___x_4300_;
}
else
{
lean_object* v___x_4301_; lean_object* v___x_4303_; 
lean_dec(v_a_4295_);
v___x_4301_ = lean_box(0);
if (v_isShared_4298_ == 0)
{
lean_ctor_set(v___x_4297_, 0, v___x_4301_);
v___x_4303_ = v___x_4297_;
goto v_reusejp_4302_;
}
else
{
lean_object* v_reuseFailAlloc_4304_; 
v_reuseFailAlloc_4304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4304_, 0, v___x_4301_);
v___x_4303_ = v_reuseFailAlloc_4304_;
goto v_reusejp_4302_;
}
v_reusejp_4302_:
{
return v___x_4303_;
}
}
}
}
else
{
lean_object* v_a_4306_; lean_object* v___x_4308_; uint8_t v_isShared_4309_; uint8_t v_isSharedCheck_4313_; 
v_a_4306_ = lean_ctor_get(v___x_4294_, 0);
v_isSharedCheck_4313_ = !lean_is_exclusive(v___x_4294_);
if (v_isSharedCheck_4313_ == 0)
{
v___x_4308_ = v___x_4294_;
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
else
{
lean_inc(v_a_4306_);
lean_dec(v___x_4294_);
v___x_4308_ = lean_box(0);
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
v_resetjp_4307_:
{
lean_object* v___x_4311_; 
if (v_isShared_4309_ == 0)
{
v___x_4311_ = v___x_4308_;
goto v_reusejp_4310_;
}
else
{
lean_object* v_reuseFailAlloc_4312_; 
v_reuseFailAlloc_4312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4312_, 0, v_a_4306_);
v___x_4311_ = v_reuseFailAlloc_4312_;
goto v_reusejp_4310_;
}
v_reusejp_4310_:
{
return v___x_4311_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___boxed(lean_object* v_mvarId_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_){
_start:
{
lean_object* v_res_4322_; 
v_res_4322_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(v_mvarId_4314_, v_a_4315_, v_a_4316_, v_a_4317_, v_a_4318_, v_a_4319_, v_a_4320_);
lean_dec(v_a_4320_);
lean_dec_ref(v_a_4319_);
lean_dec(v_a_4318_);
lean_dec_ref(v_a_4317_);
lean_dec(v_a_4316_);
lean_dec_ref(v_a_4315_);
return v_res_4322_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(lean_object* v_x_4323_, lean_object* v_x_4324_, lean_object* v_x_4325_, lean_object* v_x_4326_){
_start:
{
lean_object* v_ks_4327_; lean_object* v_vs_4328_; lean_object* v___x_4330_; uint8_t v_isShared_4331_; uint8_t v_isSharedCheck_4352_; 
v_ks_4327_ = lean_ctor_get(v_x_4323_, 0);
v_vs_4328_ = lean_ctor_get(v_x_4323_, 1);
v_isSharedCheck_4352_ = !lean_is_exclusive(v_x_4323_);
if (v_isSharedCheck_4352_ == 0)
{
v___x_4330_ = v_x_4323_;
v_isShared_4331_ = v_isSharedCheck_4352_;
goto v_resetjp_4329_;
}
else
{
lean_inc(v_vs_4328_);
lean_inc(v_ks_4327_);
lean_dec(v_x_4323_);
v___x_4330_ = lean_box(0);
v_isShared_4331_ = v_isSharedCheck_4352_;
goto v_resetjp_4329_;
}
v_resetjp_4329_:
{
lean_object* v___x_4332_; uint8_t v___x_4333_; 
v___x_4332_ = lean_array_get_size(v_ks_4327_);
v___x_4333_ = lean_nat_dec_lt(v_x_4324_, v___x_4332_);
if (v___x_4333_ == 0)
{
lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4337_; 
lean_dec(v_x_4324_);
v___x_4334_ = lean_array_push(v_ks_4327_, v_x_4325_);
v___x_4335_ = lean_array_push(v_vs_4328_, v_x_4326_);
if (v_isShared_4331_ == 0)
{
lean_ctor_set(v___x_4330_, 1, v___x_4335_);
lean_ctor_set(v___x_4330_, 0, v___x_4334_);
v___x_4337_ = v___x_4330_;
goto v_reusejp_4336_;
}
else
{
lean_object* v_reuseFailAlloc_4338_; 
v_reuseFailAlloc_4338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4338_, 0, v___x_4334_);
lean_ctor_set(v_reuseFailAlloc_4338_, 1, v___x_4335_);
v___x_4337_ = v_reuseFailAlloc_4338_;
goto v_reusejp_4336_;
}
v_reusejp_4336_:
{
return v___x_4337_;
}
}
else
{
lean_object* v_k_x27_4339_; uint8_t v___x_4340_; 
v_k_x27_4339_ = lean_array_fget_borrowed(v_ks_4327_, v_x_4324_);
v___x_4340_ = l_Lean_instBEqMVarId_beq(v_x_4325_, v_k_x27_4339_);
if (v___x_4340_ == 0)
{
lean_object* v___x_4342_; 
if (v_isShared_4331_ == 0)
{
v___x_4342_ = v___x_4330_;
goto v_reusejp_4341_;
}
else
{
lean_object* v_reuseFailAlloc_4346_; 
v_reuseFailAlloc_4346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4346_, 0, v_ks_4327_);
lean_ctor_set(v_reuseFailAlloc_4346_, 1, v_vs_4328_);
v___x_4342_ = v_reuseFailAlloc_4346_;
goto v_reusejp_4341_;
}
v_reusejp_4341_:
{
lean_object* v___x_4343_; lean_object* v___x_4344_; 
v___x_4343_ = lean_unsigned_to_nat(1u);
v___x_4344_ = lean_nat_add(v_x_4324_, v___x_4343_);
lean_dec(v_x_4324_);
v_x_4323_ = v___x_4342_;
v_x_4324_ = v___x_4344_;
goto _start;
}
}
else
{
lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4350_; 
v___x_4347_ = lean_array_fset(v_ks_4327_, v_x_4324_, v_x_4325_);
v___x_4348_ = lean_array_fset(v_vs_4328_, v_x_4324_, v_x_4326_);
lean_dec(v_x_4324_);
if (v_isShared_4331_ == 0)
{
lean_ctor_set(v___x_4330_, 1, v___x_4348_);
lean_ctor_set(v___x_4330_, 0, v___x_4347_);
v___x_4350_ = v___x_4330_;
goto v_reusejp_4349_;
}
else
{
lean_object* v_reuseFailAlloc_4351_; 
v_reuseFailAlloc_4351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4351_, 0, v___x_4347_);
lean_ctor_set(v_reuseFailAlloc_4351_, 1, v___x_4348_);
v___x_4350_ = v_reuseFailAlloc_4351_;
goto v_reusejp_4349_;
}
v_reusejp_4349_:
{
return v___x_4350_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_4353_, lean_object* v_k_4354_, lean_object* v_v_4355_){
_start:
{
lean_object* v___x_4356_; lean_object* v___x_4357_; 
v___x_4356_ = lean_unsigned_to_nat(0u);
v___x_4357_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_n_4353_, v___x_4356_, v_k_4354_, v_v_4355_);
return v___x_4357_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4358_; 
v___x_4358_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4358_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(lean_object* v_x_4359_, size_t v_x_4360_, size_t v_x_4361_, lean_object* v_x_4362_, lean_object* v_x_4363_){
_start:
{
if (lean_obj_tag(v_x_4359_) == 0)
{
lean_object* v_es_4364_; size_t v___x_4365_; size_t v___x_4366_; lean_object* v_j_4367_; lean_object* v___x_4368_; uint8_t v___x_4369_; 
v_es_4364_ = lean_ctor_get(v_x_4359_, 0);
v___x_4365_ = ((size_t)31ULL);
v___x_4366_ = lean_usize_land(v_x_4360_, v___x_4365_);
v_j_4367_ = lean_usize_to_nat(v___x_4366_);
v___x_4368_ = lean_array_get_size(v_es_4364_);
v___x_4369_ = lean_nat_dec_lt(v_j_4367_, v___x_4368_);
if (v___x_4369_ == 0)
{
lean_dec(v_j_4367_);
lean_dec(v_x_4363_);
lean_dec(v_x_4362_);
return v_x_4359_;
}
else
{
lean_object* v___x_4371_; uint8_t v_isShared_4372_; uint8_t v_isSharedCheck_4408_; 
lean_inc_ref(v_es_4364_);
v_isSharedCheck_4408_ = !lean_is_exclusive(v_x_4359_);
if (v_isSharedCheck_4408_ == 0)
{
lean_object* v_unused_4409_; 
v_unused_4409_ = lean_ctor_get(v_x_4359_, 0);
lean_dec(v_unused_4409_);
v___x_4371_ = v_x_4359_;
v_isShared_4372_ = v_isSharedCheck_4408_;
goto v_resetjp_4370_;
}
else
{
lean_dec(v_x_4359_);
v___x_4371_ = lean_box(0);
v_isShared_4372_ = v_isSharedCheck_4408_;
goto v_resetjp_4370_;
}
v_resetjp_4370_:
{
lean_object* v_v_4373_; lean_object* v___x_4374_; lean_object* v_xs_x27_4375_; lean_object* v___y_4377_; 
v_v_4373_ = lean_array_fget(v_es_4364_, v_j_4367_);
v___x_4374_ = lean_box(0);
v_xs_x27_4375_ = lean_array_fset(v_es_4364_, v_j_4367_, v___x_4374_);
switch(lean_obj_tag(v_v_4373_))
{
case 0:
{
lean_object* v_key_4382_; lean_object* v_val_4383_; lean_object* v___x_4385_; uint8_t v_isShared_4386_; uint8_t v_isSharedCheck_4393_; 
v_key_4382_ = lean_ctor_get(v_v_4373_, 0);
v_val_4383_ = lean_ctor_get(v_v_4373_, 1);
v_isSharedCheck_4393_ = !lean_is_exclusive(v_v_4373_);
if (v_isSharedCheck_4393_ == 0)
{
v___x_4385_ = v_v_4373_;
v_isShared_4386_ = v_isSharedCheck_4393_;
goto v_resetjp_4384_;
}
else
{
lean_inc(v_val_4383_);
lean_inc(v_key_4382_);
lean_dec(v_v_4373_);
v___x_4385_ = lean_box(0);
v_isShared_4386_ = v_isSharedCheck_4393_;
goto v_resetjp_4384_;
}
v_resetjp_4384_:
{
uint8_t v___x_4387_; 
v___x_4387_ = l_Lean_instBEqMVarId_beq(v_x_4362_, v_key_4382_);
if (v___x_4387_ == 0)
{
lean_object* v___x_4388_; lean_object* v___x_4389_; 
lean_del_object(v___x_4385_);
v___x_4388_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4382_, v_val_4383_, v_x_4362_, v_x_4363_);
v___x_4389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4389_, 0, v___x_4388_);
v___y_4377_ = v___x_4389_;
goto v___jp_4376_;
}
else
{
lean_object* v___x_4391_; 
lean_dec(v_val_4383_);
lean_dec(v_key_4382_);
if (v_isShared_4386_ == 0)
{
lean_ctor_set(v___x_4385_, 1, v_x_4363_);
lean_ctor_set(v___x_4385_, 0, v_x_4362_);
v___x_4391_ = v___x_4385_;
goto v_reusejp_4390_;
}
else
{
lean_object* v_reuseFailAlloc_4392_; 
v_reuseFailAlloc_4392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4392_, 0, v_x_4362_);
lean_ctor_set(v_reuseFailAlloc_4392_, 1, v_x_4363_);
v___x_4391_ = v_reuseFailAlloc_4392_;
goto v_reusejp_4390_;
}
v_reusejp_4390_:
{
v___y_4377_ = v___x_4391_;
goto v___jp_4376_;
}
}
}
}
case 1:
{
lean_object* v_node_4394_; lean_object* v___x_4396_; uint8_t v_isShared_4397_; uint8_t v_isSharedCheck_4406_; 
v_node_4394_ = lean_ctor_get(v_v_4373_, 0);
v_isSharedCheck_4406_ = !lean_is_exclusive(v_v_4373_);
if (v_isSharedCheck_4406_ == 0)
{
v___x_4396_ = v_v_4373_;
v_isShared_4397_ = v_isSharedCheck_4406_;
goto v_resetjp_4395_;
}
else
{
lean_inc(v_node_4394_);
lean_dec(v_v_4373_);
v___x_4396_ = lean_box(0);
v_isShared_4397_ = v_isSharedCheck_4406_;
goto v_resetjp_4395_;
}
v_resetjp_4395_:
{
size_t v___x_4398_; size_t v___x_4399_; size_t v___x_4400_; size_t v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4404_; 
v___x_4398_ = ((size_t)5ULL);
v___x_4399_ = lean_usize_shift_right(v_x_4360_, v___x_4398_);
v___x_4400_ = ((size_t)1ULL);
v___x_4401_ = lean_usize_add(v_x_4361_, v___x_4400_);
v___x_4402_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_node_4394_, v___x_4399_, v___x_4401_, v_x_4362_, v_x_4363_);
if (v_isShared_4397_ == 0)
{
lean_ctor_set(v___x_4396_, 0, v___x_4402_);
v___x_4404_ = v___x_4396_;
goto v_reusejp_4403_;
}
else
{
lean_object* v_reuseFailAlloc_4405_; 
v_reuseFailAlloc_4405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4405_, 0, v___x_4402_);
v___x_4404_ = v_reuseFailAlloc_4405_;
goto v_reusejp_4403_;
}
v_reusejp_4403_:
{
v___y_4377_ = v___x_4404_;
goto v___jp_4376_;
}
}
}
default: 
{
lean_object* v___x_4407_; 
v___x_4407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4407_, 0, v_x_4362_);
lean_ctor_set(v___x_4407_, 1, v_x_4363_);
v___y_4377_ = v___x_4407_;
goto v___jp_4376_;
}
}
v___jp_4376_:
{
lean_object* v___x_4378_; lean_object* v___x_4380_; 
v___x_4378_ = lean_array_fset(v_xs_x27_4375_, v_j_4367_, v___y_4377_);
lean_dec(v_j_4367_);
if (v_isShared_4372_ == 0)
{
lean_ctor_set(v___x_4371_, 0, v___x_4378_);
v___x_4380_ = v___x_4371_;
goto v_reusejp_4379_;
}
else
{
lean_object* v_reuseFailAlloc_4381_; 
v_reuseFailAlloc_4381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4381_, 0, v___x_4378_);
v___x_4380_ = v_reuseFailAlloc_4381_;
goto v_reusejp_4379_;
}
v_reusejp_4379_:
{
return v___x_4380_;
}
}
}
}
}
else
{
lean_object* v_ks_4410_; lean_object* v_vs_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4431_; 
v_ks_4410_ = lean_ctor_get(v_x_4359_, 0);
v_vs_4411_ = lean_ctor_get(v_x_4359_, 1);
v_isSharedCheck_4431_ = !lean_is_exclusive(v_x_4359_);
if (v_isSharedCheck_4431_ == 0)
{
v___x_4413_ = v_x_4359_;
v_isShared_4414_ = v_isSharedCheck_4431_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_vs_4411_);
lean_inc(v_ks_4410_);
lean_dec(v_x_4359_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4431_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v___x_4416_; 
if (v_isShared_4414_ == 0)
{
v___x_4416_ = v___x_4413_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4430_; 
v_reuseFailAlloc_4430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4430_, 0, v_ks_4410_);
lean_ctor_set(v_reuseFailAlloc_4430_, 1, v_vs_4411_);
v___x_4416_ = v_reuseFailAlloc_4430_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
lean_object* v_newNode_4417_; uint8_t v___y_4419_; size_t v___x_4425_; uint8_t v___x_4426_; 
v_newNode_4417_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(v___x_4416_, v_x_4362_, v_x_4363_);
v___x_4425_ = ((size_t)7ULL);
v___x_4426_ = lean_usize_dec_le(v___x_4425_, v_x_4361_);
if (v___x_4426_ == 0)
{
lean_object* v___x_4427_; lean_object* v___x_4428_; uint8_t v___x_4429_; 
v___x_4427_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4417_);
v___x_4428_ = lean_unsigned_to_nat(4u);
v___x_4429_ = lean_nat_dec_lt(v___x_4427_, v___x_4428_);
lean_dec(v___x_4427_);
v___y_4419_ = v___x_4429_;
goto v___jp_4418_;
}
else
{
v___y_4419_ = v___x_4426_;
goto v___jp_4418_;
}
v___jp_4418_:
{
if (v___y_4419_ == 0)
{
lean_object* v_ks_4420_; lean_object* v_vs_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; 
v_ks_4420_ = lean_ctor_get(v_newNode_4417_, 0);
lean_inc_ref(v_ks_4420_);
v_vs_4421_ = lean_ctor_get(v_newNode_4417_, 1);
lean_inc_ref(v_vs_4421_);
lean_dec_ref(v_newNode_4417_);
v___x_4422_ = lean_unsigned_to_nat(0u);
v___x_4423_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_4424_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_x_4361_, v_ks_4420_, v_vs_4421_, v___x_4422_, v___x_4423_);
lean_dec_ref(v_vs_4421_);
lean_dec_ref(v_ks_4420_);
return v___x_4424_;
}
else
{
return v_newNode_4417_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_4432_, lean_object* v_keys_4433_, lean_object* v_vals_4434_, lean_object* v_i_4435_, lean_object* v_entries_4436_){
_start:
{
lean_object* v___x_4437_; uint8_t v___x_4438_; 
v___x_4437_ = lean_array_get_size(v_keys_4433_);
v___x_4438_ = lean_nat_dec_lt(v_i_4435_, v___x_4437_);
if (v___x_4438_ == 0)
{
lean_dec(v_i_4435_);
return v_entries_4436_;
}
else
{
lean_object* v_k_4439_; lean_object* v_v_4440_; uint64_t v___x_4441_; size_t v_h_4442_; size_t v___x_4443_; lean_object* v___x_4444_; size_t v___x_4445_; size_t v___x_4446_; size_t v___x_4447_; size_t v_h_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; 
v_k_4439_ = lean_array_fget_borrowed(v_keys_4433_, v_i_4435_);
v_v_4440_ = lean_array_fget_borrowed(v_vals_4434_, v_i_4435_);
v___x_4441_ = l_Lean_instHashableMVarId_hash(v_k_4439_);
v_h_4442_ = lean_uint64_to_usize(v___x_4441_);
v___x_4443_ = ((size_t)5ULL);
v___x_4444_ = lean_unsigned_to_nat(1u);
v___x_4445_ = ((size_t)1ULL);
v___x_4446_ = lean_usize_sub(v_depth_4432_, v___x_4445_);
v___x_4447_ = lean_usize_mul(v___x_4443_, v___x_4446_);
v_h_4448_ = lean_usize_shift_right(v_h_4442_, v___x_4447_);
v___x_4449_ = lean_nat_add(v_i_4435_, v___x_4444_);
lean_dec(v_i_4435_);
lean_inc(v_v_4440_);
lean_inc(v_k_4439_);
v___x_4450_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_entries_4436_, v_h_4448_, v_depth_4432_, v_k_4439_, v_v_4440_);
v_i_4435_ = v___x_4449_;
v_entries_4436_ = v___x_4450_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_4452_, lean_object* v_keys_4453_, lean_object* v_vals_4454_, lean_object* v_i_4455_, lean_object* v_entries_4456_){
_start:
{
size_t v_depth_boxed_4457_; lean_object* v_res_4458_; 
v_depth_boxed_4457_ = lean_unbox_usize(v_depth_4452_);
lean_dec(v_depth_4452_);
v_res_4458_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_4457_, v_keys_4453_, v_vals_4454_, v_i_4455_, v_entries_4456_);
lean_dec_ref(v_vals_4454_);
lean_dec_ref(v_keys_4453_);
return v_res_4458_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_4459_, lean_object* v_x_4460_, lean_object* v_x_4461_, lean_object* v_x_4462_, lean_object* v_x_4463_){
_start:
{
size_t v_x_4253__boxed_4464_; size_t v_x_4254__boxed_4465_; lean_object* v_res_4466_; 
v_x_4253__boxed_4464_ = lean_unbox_usize(v_x_4460_);
lean_dec(v_x_4460_);
v_x_4254__boxed_4465_ = lean_unbox_usize(v_x_4461_);
lean_dec(v_x_4461_);
v_res_4466_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4459_, v_x_4253__boxed_4464_, v_x_4254__boxed_4465_, v_x_4462_, v_x_4463_);
return v_res_4466_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(lean_object* v_x_4467_, lean_object* v_x_4468_, lean_object* v_x_4469_){
_start:
{
uint64_t v___x_4470_; size_t v___x_4471_; size_t v___x_4472_; lean_object* v___x_4473_; 
v___x_4470_ = l_Lean_instHashableMVarId_hash(v_x_4468_);
v___x_4471_ = lean_uint64_to_usize(v___x_4470_);
v___x_4472_ = ((size_t)1ULL);
v___x_4473_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4467_, v___x_4471_, v___x_4472_, v_x_4468_, v_x_4469_);
return v___x_4473_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(lean_object* v_mvarId_4474_, lean_object* v_val_4475_, lean_object* v___y_4476_){
_start:
{
lean_object* v___x_4478_; lean_object* v_mctx_4479_; lean_object* v_cache_4480_; lean_object* v_zetaDeltaFVarIds_4481_; lean_object* v_postponed_4482_; lean_object* v_diag_4483_; lean_object* v___x_4485_; uint8_t v_isShared_4486_; uint8_t v_isSharedCheck_4512_; 
v___x_4478_ = lean_st_ref_take(v___y_4476_);
v_mctx_4479_ = lean_ctor_get(v___x_4478_, 0);
v_cache_4480_ = lean_ctor_get(v___x_4478_, 1);
v_zetaDeltaFVarIds_4481_ = lean_ctor_get(v___x_4478_, 2);
v_postponed_4482_ = lean_ctor_get(v___x_4478_, 3);
v_diag_4483_ = lean_ctor_get(v___x_4478_, 4);
v_isSharedCheck_4512_ = !lean_is_exclusive(v___x_4478_);
if (v_isSharedCheck_4512_ == 0)
{
v___x_4485_ = v___x_4478_;
v_isShared_4486_ = v_isSharedCheck_4512_;
goto v_resetjp_4484_;
}
else
{
lean_inc(v_diag_4483_);
lean_inc(v_postponed_4482_);
lean_inc(v_zetaDeltaFVarIds_4481_);
lean_inc(v_cache_4480_);
lean_inc(v_mctx_4479_);
lean_dec(v___x_4478_);
v___x_4485_ = lean_box(0);
v_isShared_4486_ = v_isSharedCheck_4512_;
goto v_resetjp_4484_;
}
v_resetjp_4484_:
{
lean_object* v_depth_4487_; lean_object* v_levelAssignDepth_4488_; lean_object* v_lmvarCounter_4489_; lean_object* v_mvarCounter_4490_; lean_object* v_lDecls_4491_; lean_object* v_decls_4492_; lean_object* v_userNames_4493_; lean_object* v_lAssignment_4494_; lean_object* v_eAssignment_4495_; lean_object* v_dAssignment_4496_; lean_object* v_instanceTypedMVars_4497_; lean_object* v___x_4499_; uint8_t v_isShared_4500_; uint8_t v_isSharedCheck_4511_; 
v_depth_4487_ = lean_ctor_get(v_mctx_4479_, 0);
v_levelAssignDepth_4488_ = lean_ctor_get(v_mctx_4479_, 1);
v_lmvarCounter_4489_ = lean_ctor_get(v_mctx_4479_, 2);
v_mvarCounter_4490_ = lean_ctor_get(v_mctx_4479_, 3);
v_lDecls_4491_ = lean_ctor_get(v_mctx_4479_, 4);
v_decls_4492_ = lean_ctor_get(v_mctx_4479_, 5);
v_userNames_4493_ = lean_ctor_get(v_mctx_4479_, 6);
v_lAssignment_4494_ = lean_ctor_get(v_mctx_4479_, 7);
v_eAssignment_4495_ = lean_ctor_get(v_mctx_4479_, 8);
v_dAssignment_4496_ = lean_ctor_get(v_mctx_4479_, 9);
v_instanceTypedMVars_4497_ = lean_ctor_get(v_mctx_4479_, 10);
v_isSharedCheck_4511_ = !lean_is_exclusive(v_mctx_4479_);
if (v_isSharedCheck_4511_ == 0)
{
v___x_4499_ = v_mctx_4479_;
v_isShared_4500_ = v_isSharedCheck_4511_;
goto v_resetjp_4498_;
}
else
{
lean_inc(v_instanceTypedMVars_4497_);
lean_inc(v_dAssignment_4496_);
lean_inc(v_eAssignment_4495_);
lean_inc(v_lAssignment_4494_);
lean_inc(v_userNames_4493_);
lean_inc(v_decls_4492_);
lean_inc(v_lDecls_4491_);
lean_inc(v_mvarCounter_4490_);
lean_inc(v_lmvarCounter_4489_);
lean_inc(v_levelAssignDepth_4488_);
lean_inc(v_depth_4487_);
lean_dec(v_mctx_4479_);
v___x_4499_ = lean_box(0);
v_isShared_4500_ = v_isSharedCheck_4511_;
goto v_resetjp_4498_;
}
v_resetjp_4498_:
{
lean_object* v___x_4501_; lean_object* v___x_4503_; 
v___x_4501_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(v_eAssignment_4495_, v_mvarId_4474_, v_val_4475_);
if (v_isShared_4500_ == 0)
{
lean_ctor_set(v___x_4499_, 8, v___x_4501_);
v___x_4503_ = v___x_4499_;
goto v_reusejp_4502_;
}
else
{
lean_object* v_reuseFailAlloc_4510_; 
v_reuseFailAlloc_4510_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_4510_, 0, v_depth_4487_);
lean_ctor_set(v_reuseFailAlloc_4510_, 1, v_levelAssignDepth_4488_);
lean_ctor_set(v_reuseFailAlloc_4510_, 2, v_lmvarCounter_4489_);
lean_ctor_set(v_reuseFailAlloc_4510_, 3, v_mvarCounter_4490_);
lean_ctor_set(v_reuseFailAlloc_4510_, 4, v_lDecls_4491_);
lean_ctor_set(v_reuseFailAlloc_4510_, 5, v_decls_4492_);
lean_ctor_set(v_reuseFailAlloc_4510_, 6, v_userNames_4493_);
lean_ctor_set(v_reuseFailAlloc_4510_, 7, v_lAssignment_4494_);
lean_ctor_set(v_reuseFailAlloc_4510_, 8, v___x_4501_);
lean_ctor_set(v_reuseFailAlloc_4510_, 9, v_dAssignment_4496_);
lean_ctor_set(v_reuseFailAlloc_4510_, 10, v_instanceTypedMVars_4497_);
v___x_4503_ = v_reuseFailAlloc_4510_;
goto v_reusejp_4502_;
}
v_reusejp_4502_:
{
lean_object* v___x_4505_; 
if (v_isShared_4486_ == 0)
{
lean_ctor_set(v___x_4485_, 0, v___x_4503_);
v___x_4505_ = v___x_4485_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4509_; 
v_reuseFailAlloc_4509_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4509_, 0, v___x_4503_);
lean_ctor_set(v_reuseFailAlloc_4509_, 1, v_cache_4480_);
lean_ctor_set(v_reuseFailAlloc_4509_, 2, v_zetaDeltaFVarIds_4481_);
lean_ctor_set(v_reuseFailAlloc_4509_, 3, v_postponed_4482_);
lean_ctor_set(v_reuseFailAlloc_4509_, 4, v_diag_4483_);
v___x_4505_ = v_reuseFailAlloc_4509_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; 
v___x_4506_ = lean_st_ref_put(v___y_4476_, v___x_4505_);
v___x_4507_ = lean_box(0);
v___x_4508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4508_, 0, v___x_4507_);
return v___x_4508_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg___boxed(lean_object* v_mvarId_4513_, lean_object* v_val_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_){
_start:
{
lean_object* v_res_4517_; 
v_res_4517_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mvarId_4513_, v_val_4514_, v___y_4515_);
lean_dec(v___y_4515_);
return v_res_4517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___lam__0(lean_object* v_mv_u2081_4522_, lean_object* v_mv_u2082_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_){
_start:
{
lean_object* v___x_4532_; 
lean_inc(v_mv_u2081_4522_);
v___x_4532_ = l_Lean_MVarId_getDecl(v_mv_u2081_4522_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_);
if (lean_obj_tag(v___x_4532_) == 0)
{
lean_object* v_a_4533_; lean_object* v___x_4534_; 
v_a_4533_ = lean_ctor_get(v___x_4532_, 0);
lean_inc(v_a_4533_);
lean_dec_ref_known(v___x_4532_, 1);
lean_inc(v_mv_u2082_4523_);
v___x_4534_ = l_Lean_MVarId_getDecl(v_mv_u2082_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_);
if (lean_obj_tag(v___x_4534_) == 0)
{
lean_object* v_a_4535_; lean_object* v_lctx_4536_; lean_object* v_type_4537_; lean_object* v_lctx_4538_; lean_object* v_type_4539_; uint8_t v___x_4540_; 
v_a_4535_ = lean_ctor_get(v___x_4534_, 0);
lean_inc(v_a_4535_);
lean_dec_ref_known(v___x_4534_, 1);
v_lctx_4536_ = lean_ctor_get(v_a_4533_, 1);
lean_inc_ref(v_lctx_4536_);
v_type_4537_ = lean_ctor_get(v_a_4533_, 2);
lean_inc_ref(v_type_4537_);
lean_dec(v_a_4533_);
v_lctx_4538_ = lean_ctor_get(v_a_4535_, 1);
lean_inc_ref(v_lctx_4538_);
v_type_4539_ = lean_ctor_get(v_a_4535_, 2);
lean_inc_ref(v_type_4539_);
lean_dec(v_a_4535_);
v___x_4540_ = lean_expr_eqv(v_type_4537_, v_type_4539_);
lean_dec_ref(v_type_4539_);
lean_dec_ref(v_type_4537_);
if (v___x_4540_ == 0)
{
lean_dec_ref(v_lctx_4538_);
lean_dec_ref(v_lctx_4536_);
lean_dec(v_mv_u2082_4523_);
lean_dec(v_mv_u2081_4522_);
goto v___jp_4529_;
}
else
{
lean_object* v___x_4541_; uint8_t v___x_4542_; 
v___x_4541_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
v___x_4542_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_4536_, v_lctx_4538_, v___x_4541_);
if (v___x_4542_ == 0)
{
uint8_t v___x_4543_; 
v___x_4543_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_4538_, v_lctx_4536_, v___x_4541_);
lean_dec_ref(v_lctx_4536_);
lean_dec_ref(v_lctx_4538_);
if (v___x_4543_ == 0)
{
lean_dec(v_mv_u2082_4523_);
lean_dec(v_mv_u2081_4522_);
goto v___jp_4529_;
}
else
{
lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4547_; uint8_t v_isShared_4548_; uint8_t v_isSharedCheck_4555_; 
v___x_4544_ = l_Lean_Expr_mvar___override(v_mv_u2082_4523_);
v___x_4545_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mv_u2081_4522_, v___x_4544_, v___y_4525_);
v_isSharedCheck_4555_ = !lean_is_exclusive(v___x_4545_);
if (v_isSharedCheck_4555_ == 0)
{
lean_object* v_unused_4556_; 
v_unused_4556_ = lean_ctor_get(v___x_4545_, 0);
lean_dec(v_unused_4556_);
v___x_4547_ = v___x_4545_;
v_isShared_4548_ = v_isSharedCheck_4555_;
goto v_resetjp_4546_;
}
else
{
lean_dec(v___x_4545_);
v___x_4547_ = lean_box(0);
v_isShared_4548_ = v_isSharedCheck_4555_;
goto v_resetjp_4546_;
}
v_resetjp_4546_:
{
lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4553_; 
v___x_4549_ = lean_box(v___x_4542_);
v___x_4550_ = lean_box(v___x_4540_);
v___x_4551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4551_, 0, v___x_4549_);
lean_ctor_set(v___x_4551_, 1, v___x_4550_);
if (v_isShared_4548_ == 0)
{
lean_ctor_set(v___x_4547_, 0, v___x_4551_);
v___x_4553_ = v___x_4547_;
goto v_reusejp_4552_;
}
else
{
lean_object* v_reuseFailAlloc_4554_; 
v_reuseFailAlloc_4554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4554_, 0, v___x_4551_);
v___x_4553_ = v_reuseFailAlloc_4554_;
goto v_reusejp_4552_;
}
v_reusejp_4552_:
{
return v___x_4553_;
}
}
}
}
else
{
lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4560_; uint8_t v_isShared_4561_; uint8_t v_isSharedCheck_4569_; 
lean_dec_ref(v_lctx_4538_);
lean_dec_ref(v_lctx_4536_);
v___x_4557_ = l_Lean_Expr_mvar___override(v_mv_u2081_4522_);
v___x_4558_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mv_u2082_4523_, v___x_4557_, v___y_4525_);
v_isSharedCheck_4569_ = !lean_is_exclusive(v___x_4558_);
if (v_isSharedCheck_4569_ == 0)
{
lean_object* v_unused_4570_; 
v_unused_4570_ = lean_ctor_get(v___x_4558_, 0);
lean_dec(v_unused_4570_);
v___x_4560_ = v___x_4558_;
v_isShared_4561_ = v_isSharedCheck_4569_;
goto v_resetjp_4559_;
}
else
{
lean_dec(v___x_4558_);
v___x_4560_ = lean_box(0);
v_isShared_4561_ = v_isSharedCheck_4569_;
goto v_resetjp_4559_;
}
v_resetjp_4559_:
{
uint8_t v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4567_; 
v___x_4562_ = 0;
v___x_4563_ = lean_box(v___x_4540_);
v___x_4564_ = lean_box(v___x_4562_);
v___x_4565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4565_, 0, v___x_4563_);
lean_ctor_set(v___x_4565_, 1, v___x_4564_);
if (v_isShared_4561_ == 0)
{
lean_ctor_set(v___x_4560_, 0, v___x_4565_);
v___x_4567_ = v___x_4560_;
goto v_reusejp_4566_;
}
else
{
lean_object* v_reuseFailAlloc_4568_; 
v_reuseFailAlloc_4568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4568_, 0, v___x_4565_);
v___x_4567_ = v_reuseFailAlloc_4568_;
goto v_reusejp_4566_;
}
v_reusejp_4566_:
{
return v___x_4567_;
}
}
}
}
}
else
{
lean_object* v_a_4571_; lean_object* v___x_4573_; uint8_t v_isShared_4574_; uint8_t v_isSharedCheck_4578_; 
lean_dec(v_a_4533_);
lean_dec(v_mv_u2082_4523_);
lean_dec(v_mv_u2081_4522_);
v_a_4571_ = lean_ctor_get(v___x_4534_, 0);
v_isSharedCheck_4578_ = !lean_is_exclusive(v___x_4534_);
if (v_isSharedCheck_4578_ == 0)
{
v___x_4573_ = v___x_4534_;
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
else
{
lean_inc(v_a_4571_);
lean_dec(v___x_4534_);
v___x_4573_ = lean_box(0);
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
v_resetjp_4572_:
{
lean_object* v___x_4576_; 
if (v_isShared_4574_ == 0)
{
v___x_4576_ = v___x_4573_;
goto v_reusejp_4575_;
}
else
{
lean_object* v_reuseFailAlloc_4577_; 
v_reuseFailAlloc_4577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4577_, 0, v_a_4571_);
v___x_4576_ = v_reuseFailAlloc_4577_;
goto v_reusejp_4575_;
}
v_reusejp_4575_:
{
return v___x_4576_;
}
}
}
}
else
{
lean_object* v_a_4579_; lean_object* v___x_4581_; uint8_t v_isShared_4582_; uint8_t v_isSharedCheck_4586_; 
lean_dec(v_mv_u2082_4523_);
lean_dec(v_mv_u2081_4522_);
v_a_4579_ = lean_ctor_get(v___x_4532_, 0);
v_isSharedCheck_4586_ = !lean_is_exclusive(v___x_4532_);
if (v_isSharedCheck_4586_ == 0)
{
v___x_4581_ = v___x_4532_;
v_isShared_4582_ = v_isSharedCheck_4586_;
goto v_resetjp_4580_;
}
else
{
lean_inc(v_a_4579_);
lean_dec(v___x_4532_);
v___x_4581_ = lean_box(0);
v_isShared_4582_ = v_isSharedCheck_4586_;
goto v_resetjp_4580_;
}
v_resetjp_4580_:
{
lean_object* v___x_4584_; 
if (v_isShared_4582_ == 0)
{
v___x_4584_ = v___x_4581_;
goto v_reusejp_4583_;
}
else
{
lean_object* v_reuseFailAlloc_4585_; 
v_reuseFailAlloc_4585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4585_, 0, v_a_4579_);
v___x_4584_ = v_reuseFailAlloc_4585_;
goto v_reusejp_4583_;
}
v_reusejp_4583_:
{
return v___x_4584_;
}
}
}
v___jp_4529_:
{
lean_object* v___x_4530_; lean_object* v___x_4531_; 
v___x_4530_ = ((lean_object*)(l_Lean_Elab_WF_assignSubsumed___lam__0___closed__0));
v___x_4531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4531_, 0, v___x_4530_);
return v___x_4531_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___lam__0___boxed(lean_object* v_mv_u2081_4587_, lean_object* v_mv_u2082_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_){
_start:
{
lean_object* v_res_4594_; 
v_res_4594_ = l_Lean_Elab_WF_assignSubsumed___lam__0(v_mv_u2081_4587_, v_mv_u2082_4588_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_);
lean_dec(v___y_4592_);
lean_dec_ref(v___y_4591_);
lean_dec(v___y_4590_);
lean_dec_ref(v___y_4589_);
return v_res_4594_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1(lean_object* v___x_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_){
_start:
{
lean_object* v___x_4601_; 
v___x_4601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4601_, 0, v___x_4595_);
return v___x_4601_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1___boxed(lean_object* v___x_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_){
_start:
{
lean_object* v_res_4608_; 
v_res_4608_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1(v___x_4602_, v___y_4603_, v___y_4604_, v___y_4605_, v___y_4606_);
lean_dec(v___y_4606_);
lean_dec_ref(v___y_4605_);
lean_dec(v___y_4604_);
lean_dec_ref(v___y_4603_);
return v_res_4608_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0(lean_object* v_f_4609_, lean_object* v___x_4610_, lean_object* v___x_4611_, lean_object* v___x_4612_, lean_object* v_a_4613_, uint8_t v___x_4614_, lean_object* v_snd_4615_, lean_object* v_fst_4616_, lean_object* v_next_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_){
_start:
{
lean_object* v___x_4623_; 
v___x_4623_ = lean_apply_7(v_f_4609_, v___x_4610_, v___x_4611_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_, lean_box(0));
if (lean_obj_tag(v___x_4623_) == 0)
{
lean_object* v_a_4624_; lean_object* v___x_4626_; uint8_t v_isShared_4627_; uint8_t v_isSharedCheck_4659_; 
v_a_4624_ = lean_ctor_get(v___x_4623_, 0);
v_isSharedCheck_4659_ = !lean_is_exclusive(v___x_4623_);
if (v_isSharedCheck_4659_ == 0)
{
v___x_4626_ = v___x_4623_;
v_isShared_4627_ = v_isSharedCheck_4659_;
goto v_resetjp_4625_;
}
else
{
lean_inc(v_a_4624_);
lean_dec(v___x_4623_);
v___x_4626_ = lean_box(0);
v_isShared_4627_ = v_isSharedCheck_4659_;
goto v_resetjp_4625_;
}
v_resetjp_4625_:
{
lean_object* v_fst_4628_; lean_object* v_snd_4629_; lean_object* v___x_4631_; uint8_t v_isShared_4632_; uint8_t v_isSharedCheck_4658_; 
v_fst_4628_ = lean_ctor_get(v_a_4624_, 0);
v_snd_4629_ = lean_ctor_get(v_a_4624_, 1);
v_isSharedCheck_4658_ = !lean_is_exclusive(v_a_4624_);
if (v_isSharedCheck_4658_ == 0)
{
v___x_4631_ = v_a_4624_;
v_isShared_4632_ = v_isSharedCheck_4658_;
goto v_resetjp_4630_;
}
else
{
lean_inc(v_snd_4629_);
lean_inc(v_fst_4628_);
lean_dec(v_a_4624_);
v___x_4631_ = lean_box(0);
v_isShared_4632_ = v_isSharedCheck_4658_;
goto v_resetjp_4630_;
}
v_resetjp_4630_:
{
lean_object* v_removed_4634_; lean_object* v_numRemoved_4635_; uint8_t v___x_4654_; 
v___x_4654_ = lean_unbox(v_fst_4628_);
lean_dec(v_fst_4628_);
if (v___x_4654_ == 0)
{
lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; 
v___x_4655_ = lean_nat_add(v_snd_4615_, v___x_4612_);
lean_dec(v_snd_4615_);
v___x_4656_ = lean_box(v___x_4614_);
v___x_4657_ = lean_array_set(v_fst_4616_, v_next_4617_, v___x_4656_);
v_removed_4634_ = v___x_4657_;
v_numRemoved_4635_ = v___x_4655_;
goto v___jp_4633_;
}
else
{
v_removed_4634_ = v_fst_4616_;
v_numRemoved_4635_ = v_snd_4615_;
goto v___jp_4633_;
}
v___jp_4633_:
{
uint8_t v___x_4636_; 
v___x_4636_ = lean_unbox(v_snd_4629_);
lean_dec(v_snd_4629_);
if (v___x_4636_ == 0)
{
lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4641_; 
v___x_4637_ = lean_nat_add(v_numRemoved_4635_, v___x_4612_);
lean_dec(v_numRemoved_4635_);
v___x_4638_ = lean_box(v___x_4614_);
v___x_4639_ = lean_array_set(v_removed_4634_, v_a_4613_, v___x_4638_);
if (v_isShared_4632_ == 0)
{
lean_ctor_set(v___x_4631_, 1, v___x_4637_);
lean_ctor_set(v___x_4631_, 0, v___x_4639_);
v___x_4641_ = v___x_4631_;
goto v_reusejp_4640_;
}
else
{
lean_object* v_reuseFailAlloc_4646_; 
v_reuseFailAlloc_4646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4646_, 0, v___x_4639_);
lean_ctor_set(v_reuseFailAlloc_4646_, 1, v___x_4637_);
v___x_4641_ = v_reuseFailAlloc_4646_;
goto v_reusejp_4640_;
}
v_reusejp_4640_:
{
lean_object* v___x_4642_; lean_object* v___x_4644_; 
v___x_4642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4642_, 0, v___x_4641_);
if (v_isShared_4627_ == 0)
{
lean_ctor_set(v___x_4626_, 0, v___x_4642_);
v___x_4644_ = v___x_4626_;
goto v_reusejp_4643_;
}
else
{
lean_object* v_reuseFailAlloc_4645_; 
v_reuseFailAlloc_4645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4645_, 0, v___x_4642_);
v___x_4644_ = v_reuseFailAlloc_4645_;
goto v_reusejp_4643_;
}
v_reusejp_4643_:
{
return v___x_4644_;
}
}
}
else
{
lean_object* v___x_4648_; 
if (v_isShared_4632_ == 0)
{
lean_ctor_set(v___x_4631_, 1, v_numRemoved_4635_);
lean_ctor_set(v___x_4631_, 0, v_removed_4634_);
v___x_4648_ = v___x_4631_;
goto v_reusejp_4647_;
}
else
{
lean_object* v_reuseFailAlloc_4653_; 
v_reuseFailAlloc_4653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4653_, 0, v_removed_4634_);
lean_ctor_set(v_reuseFailAlloc_4653_, 1, v_numRemoved_4635_);
v___x_4648_ = v_reuseFailAlloc_4653_;
goto v_reusejp_4647_;
}
v_reusejp_4647_:
{
lean_object* v___x_4649_; lean_object* v___x_4651_; 
v___x_4649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4649_, 0, v___x_4648_);
if (v_isShared_4627_ == 0)
{
lean_ctor_set(v___x_4626_, 0, v___x_4649_);
v___x_4651_ = v___x_4626_;
goto v_reusejp_4650_;
}
else
{
lean_object* v_reuseFailAlloc_4652_; 
v_reuseFailAlloc_4652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4652_, 0, v___x_4649_);
v___x_4651_ = v_reuseFailAlloc_4652_;
goto v_reusejp_4650_;
}
v_reusejp_4650_:
{
return v___x_4651_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4660_; lean_object* v___x_4662_; uint8_t v_isShared_4663_; uint8_t v_isSharedCheck_4667_; 
lean_dec(v_fst_4616_);
lean_dec(v_snd_4615_);
v_a_4660_ = lean_ctor_get(v___x_4623_, 0);
v_isSharedCheck_4667_ = !lean_is_exclusive(v___x_4623_);
if (v_isSharedCheck_4667_ == 0)
{
v___x_4662_ = v___x_4623_;
v_isShared_4663_ = v_isSharedCheck_4667_;
goto v_resetjp_4661_;
}
else
{
lean_inc(v_a_4660_);
lean_dec(v___x_4623_);
v___x_4662_ = lean_box(0);
v_isShared_4663_ = v_isSharedCheck_4667_;
goto v_resetjp_4661_;
}
v_resetjp_4661_:
{
lean_object* v___x_4665_; 
if (v_isShared_4663_ == 0)
{
v___x_4665_ = v___x_4662_;
goto v_reusejp_4664_;
}
else
{
lean_object* v_reuseFailAlloc_4666_; 
v_reuseFailAlloc_4666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4666_, 0, v_a_4660_);
v___x_4665_ = v_reuseFailAlloc_4666_;
goto v_reusejp_4664_;
}
v_reusejp_4664_:
{
return v___x_4665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_f_4668_, lean_object* v___x_4669_, lean_object* v___x_4670_, lean_object* v___x_4671_, lean_object* v_a_4672_, lean_object* v___x_4673_, lean_object* v_snd_4674_, lean_object* v_fst_4675_, lean_object* v_next_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_){
_start:
{
uint8_t v___x_4630__boxed_4682_; lean_object* v_res_4683_; 
v___x_4630__boxed_4682_ = lean_unbox(v___x_4673_);
v_res_4683_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0(v_f_4668_, v___x_4669_, v___x_4670_, v___x_4671_, v_a_4672_, v___x_4630__boxed_4682_, v_snd_4674_, v_fst_4675_, v_next_4676_, v___y_4677_, v___y_4678_, v___y_4679_, v___y_4680_);
lean_dec(v_next_4676_);
lean_dec(v_a_4672_);
lean_dec(v___x_4671_);
return v_res_4683_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(lean_object* v_upperBound_4684_, lean_object* v_a_4685_, lean_object* v_next_4686_, lean_object* v_f_4687_, lean_object* v_a_4688_, lean_object* v_b_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_){
_start:
{
uint8_t v___x_4695_; 
v___x_4695_ = lean_nat_dec_lt(v_a_4688_, v_upperBound_4684_);
if (v___x_4695_ == 0)
{
lean_object* v___x_4696_; 
lean_dec(v_a_4688_);
lean_dec_ref(v_f_4687_);
lean_dec(v_next_4686_);
v___x_4696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4696_, 0, v_b_4689_);
return v___x_4696_;
}
else
{
lean_object* v_fst_4697_; lean_object* v_snd_4698_; lean_object* v___x_4700_; uint8_t v_isShared_4701_; uint8_t v_isSharedCheck_4745_; 
v_fst_4697_ = lean_ctor_get(v_b_4689_, 0);
v_snd_4698_ = lean_ctor_get(v_b_4689_, 1);
v_isSharedCheck_4745_ = !lean_is_exclusive(v_b_4689_);
if (v_isSharedCheck_4745_ == 0)
{
v___x_4700_ = v_b_4689_;
v_isShared_4701_ = v_isSharedCheck_4745_;
goto v_resetjp_4699_;
}
else
{
lean_inc(v_snd_4698_);
lean_inc(v_fst_4697_);
lean_dec(v_b_4689_);
v___x_4700_ = lean_box(0);
v_isShared_4701_ = v_isSharedCheck_4745_;
goto v_resetjp_4699_;
}
v_resetjp_4699_:
{
lean_object* v___x_4702_; lean_object* v___y_4704_; uint8_t v___y_4727_; uint8_t v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; uint8_t v___x_4740_; 
v___x_4702_ = lean_unsigned_to_nat(1u);
v___x_4737_ = 0;
v___x_4738_ = lean_box(v___x_4737_);
v___x_4739_ = lean_array_get(v___x_4738_, v_fst_4697_, v_next_4686_);
lean_dec(v___x_4738_);
v___x_4740_ = lean_unbox(v___x_4739_);
if (v___x_4740_ == 0)
{
lean_object* v___x_4741_; lean_object* v___x_4742_; uint8_t v___x_4743_; 
lean_dec(v___x_4739_);
v___x_4741_ = lean_box(v___x_4737_);
v___x_4742_ = lean_array_get(v___x_4741_, v_fst_4697_, v_a_4688_);
lean_dec(v___x_4741_);
v___x_4743_ = lean_unbox(v___x_4742_);
lean_dec(v___x_4742_);
v___y_4727_ = v___x_4743_;
goto v___jp_4726_;
}
else
{
uint8_t v___x_4744_; 
v___x_4744_ = lean_unbox(v___x_4739_);
lean_dec(v___x_4739_);
v___y_4727_ = v___x_4744_;
goto v___jp_4726_;
}
v___jp_4703_:
{
lean_object* v___x_4705_; 
lean_inc(v___y_4693_);
lean_inc_ref(v___y_4692_);
lean_inc(v___y_4691_);
lean_inc_ref(v___y_4690_);
v___x_4705_ = lean_apply_5(v___y_4704_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_, lean_box(0));
if (lean_obj_tag(v___x_4705_) == 0)
{
lean_object* v_a_4706_; lean_object* v___x_4708_; uint8_t v_isShared_4709_; uint8_t v_isSharedCheck_4717_; 
v_a_4706_ = lean_ctor_get(v___x_4705_, 0);
v_isSharedCheck_4717_ = !lean_is_exclusive(v___x_4705_);
if (v_isSharedCheck_4717_ == 0)
{
v___x_4708_ = v___x_4705_;
v_isShared_4709_ = v_isSharedCheck_4717_;
goto v_resetjp_4707_;
}
else
{
lean_inc(v_a_4706_);
lean_dec(v___x_4705_);
v___x_4708_ = lean_box(0);
v_isShared_4709_ = v_isSharedCheck_4717_;
goto v_resetjp_4707_;
}
v_resetjp_4707_:
{
if (lean_obj_tag(v_a_4706_) == 0)
{
lean_object* v_a_4710_; lean_object* v___x_4712_; 
lean_dec(v_a_4688_);
lean_dec_ref(v_f_4687_);
lean_dec(v_next_4686_);
v_a_4710_ = lean_ctor_get(v_a_4706_, 0);
lean_inc(v_a_4710_);
lean_dec_ref_known(v_a_4706_, 1);
if (v_isShared_4709_ == 0)
{
lean_ctor_set(v___x_4708_, 0, v_a_4710_);
v___x_4712_ = v___x_4708_;
goto v_reusejp_4711_;
}
else
{
lean_object* v_reuseFailAlloc_4713_; 
v_reuseFailAlloc_4713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4713_, 0, v_a_4710_);
v___x_4712_ = v_reuseFailAlloc_4713_;
goto v_reusejp_4711_;
}
v_reusejp_4711_:
{
return v___x_4712_;
}
}
else
{
lean_object* v_a_4714_; lean_object* v___x_4715_; 
lean_del_object(v___x_4708_);
v_a_4714_ = lean_ctor_get(v_a_4706_, 0);
lean_inc(v_a_4714_);
lean_dec_ref_known(v_a_4706_, 1);
v___x_4715_ = lean_nat_add(v_a_4688_, v___x_4702_);
lean_dec(v_a_4688_);
v_a_4688_ = v___x_4715_;
v_b_4689_ = v_a_4714_;
goto _start;
}
}
}
else
{
lean_object* v_a_4718_; lean_object* v___x_4720_; uint8_t v_isShared_4721_; uint8_t v_isSharedCheck_4725_; 
lean_dec(v_a_4688_);
lean_dec_ref(v_f_4687_);
lean_dec(v_next_4686_);
v_a_4718_ = lean_ctor_get(v___x_4705_, 0);
v_isSharedCheck_4725_ = !lean_is_exclusive(v___x_4705_);
if (v_isSharedCheck_4725_ == 0)
{
v___x_4720_ = v___x_4705_;
v_isShared_4721_ = v_isSharedCheck_4725_;
goto v_resetjp_4719_;
}
else
{
lean_inc(v_a_4718_);
lean_dec(v___x_4705_);
v___x_4720_ = lean_box(0);
v_isShared_4721_ = v_isSharedCheck_4725_;
goto v_resetjp_4719_;
}
v_resetjp_4719_:
{
lean_object* v___x_4723_; 
if (v_isShared_4721_ == 0)
{
v___x_4723_ = v___x_4720_;
goto v_reusejp_4722_;
}
else
{
lean_object* v_reuseFailAlloc_4724_; 
v_reuseFailAlloc_4724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4724_, 0, v_a_4718_);
v___x_4723_ = v_reuseFailAlloc_4724_;
goto v_reusejp_4722_;
}
v_reusejp_4722_:
{
return v___x_4723_;
}
}
}
}
v___jp_4726_:
{
if (v___y_4727_ == 0)
{
lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___f_4731_; 
lean_del_object(v___x_4700_);
v___x_4728_ = lean_array_fget_borrowed(v_a_4685_, v_next_4686_);
v___x_4729_ = lean_array_fget_borrowed(v_a_4685_, v_a_4688_);
v___x_4730_ = lean_box(v___x_4695_);
lean_inc(v_next_4686_);
lean_inc(v_a_4688_);
lean_inc(v___x_4729_);
lean_inc(v___x_4728_);
lean_inc_ref(v_f_4687_);
v___f_4731_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4731_, 0, v_f_4687_);
lean_closure_set(v___f_4731_, 1, v___x_4728_);
lean_closure_set(v___f_4731_, 2, v___x_4729_);
lean_closure_set(v___f_4731_, 3, v___x_4702_);
lean_closure_set(v___f_4731_, 4, v_a_4688_);
lean_closure_set(v___f_4731_, 5, v___x_4730_);
lean_closure_set(v___f_4731_, 6, v_snd_4698_);
lean_closure_set(v___f_4731_, 7, v_fst_4697_);
lean_closure_set(v___f_4731_, 8, v_next_4686_);
v___y_4704_ = v___f_4731_;
goto v___jp_4703_;
}
else
{
lean_object* v___x_4733_; 
if (v_isShared_4701_ == 0)
{
v___x_4733_ = v___x_4700_;
goto v_reusejp_4732_;
}
else
{
lean_object* v_reuseFailAlloc_4736_; 
v_reuseFailAlloc_4736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4736_, 0, v_fst_4697_);
lean_ctor_set(v_reuseFailAlloc_4736_, 1, v_snd_4698_);
v___x_4733_ = v_reuseFailAlloc_4736_;
goto v_reusejp_4732_;
}
v_reusejp_4732_:
{
lean_object* v___x_4734_; lean_object* v___f_4735_; 
v___x_4734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4734_, 0, v___x_4733_);
v___f_4735_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1___boxed), 6, 1);
lean_closure_set(v___f_4735_, 0, v___x_4734_);
v___y_4704_ = v___f_4735_;
goto v___jp_4703_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___boxed(lean_object* v_upperBound_4746_, lean_object* v_a_4747_, lean_object* v_next_4748_, lean_object* v_f_4749_, lean_object* v_a_4750_, lean_object* v_b_4751_, lean_object* v___y_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_, lean_object* v___y_4756_){
_start:
{
lean_object* v_res_4757_; 
v_res_4757_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v_upperBound_4746_, v_a_4747_, v_next_4748_, v_f_4749_, v_a_4750_, v_b_4751_, v___y_4752_, v___y_4753_, v___y_4754_, v___y_4755_);
lean_dec(v___y_4755_);
lean_dec_ref(v___y_4754_);
lean_dec(v___y_4753_);
lean_dec_ref(v___y_4752_);
lean_dec_ref(v_a_4747_);
lean_dec(v_upperBound_4746_);
return v_res_4757_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(lean_object* v_upperBound_4758_, lean_object* v___x_4759_, lean_object* v_a_4760_, lean_object* v_f_4761_, lean_object* v_a_4762_, lean_object* v_b_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_){
_start:
{
uint8_t v___x_4769_; 
v___x_4769_ = lean_nat_dec_lt(v_a_4762_, v_upperBound_4758_);
if (v___x_4769_ == 0)
{
lean_object* v___x_4770_; 
lean_dec(v_a_4762_);
lean_dec_ref(v_f_4761_);
v___x_4770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4770_, 0, v_b_4763_);
return v___x_4770_;
}
else
{
lean_object* v_fst_4771_; lean_object* v_snd_4772_; lean_object* v___x_4774_; uint8_t v_isShared_4775_; uint8_t v_isSharedCheck_4793_; 
v_fst_4771_ = lean_ctor_get(v_b_4763_, 0);
v_snd_4772_ = lean_ctor_get(v_b_4763_, 1);
v_isSharedCheck_4793_ = !lean_is_exclusive(v_b_4763_);
if (v_isSharedCheck_4793_ == 0)
{
v___x_4774_ = v_b_4763_;
v_isShared_4775_ = v_isSharedCheck_4793_;
goto v_resetjp_4773_;
}
else
{
lean_inc(v_snd_4772_);
lean_inc(v_fst_4771_);
lean_dec(v_b_4763_);
v___x_4774_ = lean_box(0);
v_isShared_4775_ = v_isSharedCheck_4793_;
goto v_resetjp_4773_;
}
v_resetjp_4773_:
{
lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4779_; 
v___x_4776_ = lean_unsigned_to_nat(1u);
v___x_4777_ = lean_nat_add(v_a_4762_, v___x_4776_);
if (v_isShared_4775_ == 0)
{
v___x_4779_ = v___x_4774_;
goto v_reusejp_4778_;
}
else
{
lean_object* v_reuseFailAlloc_4792_; 
v_reuseFailAlloc_4792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4792_, 0, v_fst_4771_);
lean_ctor_set(v_reuseFailAlloc_4792_, 1, v_snd_4772_);
v___x_4779_ = v_reuseFailAlloc_4792_;
goto v_reusejp_4778_;
}
v_reusejp_4778_:
{
lean_object* v___x_4780_; 
lean_inc(v___x_4777_);
lean_inc_ref(v_f_4761_);
v___x_4780_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v___x_4759_, v_a_4760_, v_a_4762_, v_f_4761_, v___x_4777_, v___x_4779_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_);
if (lean_obj_tag(v___x_4780_) == 0)
{
lean_object* v_a_4781_; lean_object* v_fst_4782_; lean_object* v_snd_4783_; lean_object* v___x_4785_; uint8_t v_isShared_4786_; uint8_t v_isSharedCheck_4791_; 
v_a_4781_ = lean_ctor_get(v___x_4780_, 0);
lean_inc(v_a_4781_);
lean_dec_ref_known(v___x_4780_, 1);
v_fst_4782_ = lean_ctor_get(v_a_4781_, 0);
v_snd_4783_ = lean_ctor_get(v_a_4781_, 1);
v_isSharedCheck_4791_ = !lean_is_exclusive(v_a_4781_);
if (v_isSharedCheck_4791_ == 0)
{
v___x_4785_ = v_a_4781_;
v_isShared_4786_ = v_isSharedCheck_4791_;
goto v_resetjp_4784_;
}
else
{
lean_inc(v_snd_4783_);
lean_inc(v_fst_4782_);
lean_dec(v_a_4781_);
v___x_4785_ = lean_box(0);
v_isShared_4786_ = v_isSharedCheck_4791_;
goto v_resetjp_4784_;
}
v_resetjp_4784_:
{
lean_object* v___x_4788_; 
if (v_isShared_4786_ == 0)
{
v___x_4788_ = v___x_4785_;
goto v_reusejp_4787_;
}
else
{
lean_object* v_reuseFailAlloc_4790_; 
v_reuseFailAlloc_4790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4790_, 0, v_fst_4782_);
lean_ctor_set(v_reuseFailAlloc_4790_, 1, v_snd_4783_);
v___x_4788_ = v_reuseFailAlloc_4790_;
goto v_reusejp_4787_;
}
v_reusejp_4787_:
{
v_a_4762_ = v___x_4777_;
v_b_4763_ = v___x_4788_;
goto _start;
}
}
}
else
{
lean_dec(v___x_4777_);
lean_dec_ref(v_f_4761_);
return v___x_4780_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_4794_, lean_object* v___x_4795_, lean_object* v_a_4796_, lean_object* v_f_4797_, lean_object* v_a_4798_, lean_object* v_b_4799_, lean_object* v___y_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_){
_start:
{
lean_object* v_res_4805_; 
v_res_4805_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v_upperBound_4794_, v___x_4795_, v_a_4796_, v_f_4797_, v_a_4798_, v_b_4799_, v___y_4800_, v___y_4801_, v___y_4802_, v___y_4803_);
lean_dec(v___y_4803_);
lean_dec_ref(v___y_4802_);
lean_dec(v___y_4801_);
lean_dec_ref(v___y_4800_);
lean_dec_ref(v_a_4796_);
lean_dec(v___x_4795_);
lean_dec(v_upperBound_4794_);
return v_res_4805_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0(lean_object* v___x_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_){
_start:
{
lean_object* v___x_4812_; 
v___x_4812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4812_, 0, v___x_4806_);
return v___x_4812_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed(lean_object* v___x_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_, lean_object* v___y_4816_, lean_object* v___y_4817_, lean_object* v___y_4818_){
_start:
{
lean_object* v_res_4819_; 
v_res_4819_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0(v___x_4813_, v___y_4814_, v___y_4815_, v___y_4816_, v___y_4817_);
lean_dec(v___y_4817_);
lean_dec_ref(v___y_4816_);
lean_dec(v___y_4815_);
lean_dec_ref(v___y_4814_);
return v_res_4819_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(lean_object* v_upperBound_4820_, lean_object* v_removed_4821_, lean_object* v_a_4822_, lean_object* v_a_4823_, lean_object* v_b_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_){
_start:
{
lean_object* v___y_4831_; uint8_t v___x_4854_; 
v___x_4854_ = lean_nat_dec_lt(v_a_4823_, v_upperBound_4820_);
if (v___x_4854_ == 0)
{
lean_object* v___x_4855_; 
lean_dec(v_a_4823_);
v___x_4855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4855_, 0, v_b_4824_);
return v___x_4855_;
}
else
{
uint8_t v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; uint8_t v___x_4859_; 
v___x_4856_ = 0;
v___x_4857_ = lean_box(v___x_4856_);
v___x_4858_ = lean_array_get(v___x_4857_, v_removed_4821_, v_a_4823_);
lean_dec(v___x_4857_);
v___x_4859_ = lean_unbox(v___x_4858_);
lean_dec(v___x_4858_);
if (v___x_4859_ == 0)
{
lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___f_4863_; 
v___x_4860_ = lean_array_fget_borrowed(v_a_4822_, v_a_4823_);
lean_inc(v___x_4860_);
v___x_4861_ = lean_array_push(v_b_4824_, v___x_4860_);
v___x_4862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4862_, 0, v___x_4861_);
v___f_4863_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4863_, 0, v___x_4862_);
v___y_4831_ = v___f_4863_;
goto v___jp_4830_;
}
else
{
lean_object* v___x_4864_; lean_object* v___f_4865_; 
v___x_4864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4864_, 0, v_b_4824_);
v___f_4865_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4865_, 0, v___x_4864_);
v___y_4831_ = v___f_4865_;
goto v___jp_4830_;
}
}
v___jp_4830_:
{
lean_object* v___x_4832_; 
lean_inc(v___y_4828_);
lean_inc_ref(v___y_4827_);
lean_inc(v___y_4826_);
lean_inc_ref(v___y_4825_);
v___x_4832_ = lean_apply_5(v___y_4831_, v___y_4825_, v___y_4826_, v___y_4827_, v___y_4828_, lean_box(0));
if (lean_obj_tag(v___x_4832_) == 0)
{
lean_object* v_a_4833_; lean_object* v___x_4835_; uint8_t v_isShared_4836_; uint8_t v_isSharedCheck_4845_; 
v_a_4833_ = lean_ctor_get(v___x_4832_, 0);
v_isSharedCheck_4845_ = !lean_is_exclusive(v___x_4832_);
if (v_isSharedCheck_4845_ == 0)
{
v___x_4835_ = v___x_4832_;
v_isShared_4836_ = v_isSharedCheck_4845_;
goto v_resetjp_4834_;
}
else
{
lean_inc(v_a_4833_);
lean_dec(v___x_4832_);
v___x_4835_ = lean_box(0);
v_isShared_4836_ = v_isSharedCheck_4845_;
goto v_resetjp_4834_;
}
v_resetjp_4834_:
{
if (lean_obj_tag(v_a_4833_) == 0)
{
lean_object* v_a_4837_; lean_object* v___x_4839_; 
lean_dec(v_a_4823_);
v_a_4837_ = lean_ctor_get(v_a_4833_, 0);
lean_inc(v_a_4837_);
lean_dec_ref_known(v_a_4833_, 1);
if (v_isShared_4836_ == 0)
{
lean_ctor_set(v___x_4835_, 0, v_a_4837_);
v___x_4839_ = v___x_4835_;
goto v_reusejp_4838_;
}
else
{
lean_object* v_reuseFailAlloc_4840_; 
v_reuseFailAlloc_4840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4840_, 0, v_a_4837_);
v___x_4839_ = v_reuseFailAlloc_4840_;
goto v_reusejp_4838_;
}
v_reusejp_4838_:
{
return v___x_4839_;
}
}
else
{
lean_object* v_a_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; 
lean_del_object(v___x_4835_);
v_a_4841_ = lean_ctor_get(v_a_4833_, 0);
lean_inc(v_a_4841_);
lean_dec_ref_known(v_a_4833_, 1);
v___x_4842_ = lean_unsigned_to_nat(1u);
v___x_4843_ = lean_nat_add(v_a_4823_, v___x_4842_);
lean_dec(v_a_4823_);
v_a_4823_ = v___x_4843_;
v_b_4824_ = v_a_4841_;
goto _start;
}
}
}
else
{
lean_object* v_a_4846_; lean_object* v___x_4848_; uint8_t v_isShared_4849_; uint8_t v_isSharedCheck_4853_; 
lean_dec(v_a_4823_);
v_a_4846_ = lean_ctor_get(v___x_4832_, 0);
v_isSharedCheck_4853_ = !lean_is_exclusive(v___x_4832_);
if (v_isSharedCheck_4853_ == 0)
{
v___x_4848_ = v___x_4832_;
v_isShared_4849_ = v_isSharedCheck_4853_;
goto v_resetjp_4847_;
}
else
{
lean_inc(v_a_4846_);
lean_dec(v___x_4832_);
v___x_4848_ = lean_box(0);
v_isShared_4849_ = v_isSharedCheck_4853_;
goto v_resetjp_4847_;
}
v_resetjp_4847_:
{
lean_object* v___x_4851_; 
if (v_isShared_4849_ == 0)
{
v___x_4851_ = v___x_4848_;
goto v_reusejp_4850_;
}
else
{
lean_object* v_reuseFailAlloc_4852_; 
v_reuseFailAlloc_4852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4852_, 0, v_a_4846_);
v___x_4851_ = v_reuseFailAlloc_4852_;
goto v_reusejp_4850_;
}
v_reusejp_4850_:
{
return v___x_4851_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___boxed(lean_object* v_upperBound_4866_, lean_object* v_removed_4867_, lean_object* v_a_4868_, lean_object* v_a_4869_, lean_object* v_b_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_){
_start:
{
lean_object* v_res_4876_; 
v_res_4876_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v_upperBound_4866_, v_removed_4867_, v_a_4868_, v_a_4869_, v_b_4870_, v___y_4871_, v___y_4872_, v___y_4873_, v___y_4874_);
lean_dec(v___y_4874_);
lean_dec_ref(v___y_4873_);
lean_dec(v___y_4872_);
lean_dec_ref(v___y_4871_);
lean_dec_ref(v_a_4868_);
lean_dec_ref(v_removed_4867_);
lean_dec(v_upperBound_4866_);
return v_res_4876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(lean_object* v_a_4877_, lean_object* v_f_4878_, lean_object* v___y_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_, lean_object* v___y_4882_){
_start:
{
lean_object* v___x_4884_; uint8_t v___x_4885_; lean_object* v___x_4886_; lean_object* v_removed_4887_; lean_object* v_numRemoved_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; 
v___x_4884_ = lean_array_get_size(v_a_4877_);
v___x_4885_ = 0;
v___x_4886_ = lean_box(v___x_4885_);
v_removed_4887_ = lean_mk_array(v___x_4884_, v___x_4886_);
v_numRemoved_4888_ = lean_unsigned_to_nat(0u);
v___x_4889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4889_, 0, v_removed_4887_);
lean_ctor_set(v___x_4889_, 1, v_numRemoved_4888_);
v___x_4890_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v___x_4884_, v___x_4884_, v_a_4877_, v_f_4878_, v_numRemoved_4888_, v___x_4889_, v___y_4879_, v___y_4880_, v___y_4881_, v___y_4882_);
if (lean_obj_tag(v___x_4890_) == 0)
{
lean_object* v_a_4891_; lean_object* v_fst_4892_; lean_object* v_snd_4893_; lean_object* v_a_x27_4894_; lean_object* v___x_4895_; 
v_a_4891_ = lean_ctor_get(v___x_4890_, 0);
lean_inc(v_a_4891_);
lean_dec_ref_known(v___x_4890_, 1);
v_fst_4892_ = lean_ctor_get(v_a_4891_, 0);
lean_inc(v_fst_4892_);
v_snd_4893_ = lean_ctor_get(v_a_4891_, 1);
lean_inc(v_snd_4893_);
lean_dec(v_a_4891_);
v_a_x27_4894_ = lean_mk_empty_array_with_capacity(v_snd_4893_);
lean_dec(v_snd_4893_);
v___x_4895_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v___x_4884_, v_fst_4892_, v_a_4877_, v_numRemoved_4888_, v_a_x27_4894_, v___y_4879_, v___y_4880_, v___y_4881_, v___y_4882_);
lean_dec(v_fst_4892_);
return v___x_4895_;
}
else
{
lean_object* v_a_4896_; lean_object* v___x_4898_; uint8_t v_isShared_4899_; uint8_t v_isSharedCheck_4903_; 
v_a_4896_ = lean_ctor_get(v___x_4890_, 0);
v_isSharedCheck_4903_ = !lean_is_exclusive(v___x_4890_);
if (v_isSharedCheck_4903_ == 0)
{
v___x_4898_ = v___x_4890_;
v_isShared_4899_ = v_isSharedCheck_4903_;
goto v_resetjp_4897_;
}
else
{
lean_inc(v_a_4896_);
lean_dec(v___x_4890_);
v___x_4898_ = lean_box(0);
v_isShared_4899_ = v_isSharedCheck_4903_;
goto v_resetjp_4897_;
}
v_resetjp_4897_:
{
lean_object* v___x_4901_; 
if (v_isShared_4899_ == 0)
{
v___x_4901_ = v___x_4898_;
goto v_reusejp_4900_;
}
else
{
lean_object* v_reuseFailAlloc_4902_; 
v_reuseFailAlloc_4902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4902_, 0, v_a_4896_);
v___x_4901_ = v_reuseFailAlloc_4902_;
goto v_reusejp_4900_;
}
v_reusejp_4900_:
{
return v___x_4901_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg___boxed(lean_object* v_a_4904_, lean_object* v_f_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_){
_start:
{
lean_object* v_res_4911_; 
v_res_4911_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_a_4904_, v_f_4905_, v___y_4906_, v___y_4907_, v___y_4908_, v___y_4909_);
lean_dec(v___y_4909_);
lean_dec_ref(v___y_4908_);
lean_dec(v___y_4907_);
lean_dec_ref(v___y_4906_);
lean_dec_ref(v_a_4904_);
return v_res_4911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed(lean_object* v_mvars_4913_, lean_object* v_a_4914_, lean_object* v_a_4915_, lean_object* v_a_4916_, lean_object* v_a_4917_){
_start:
{
lean_object* v___f_4919_; lean_object* v___x_4920_; 
v___f_4919_ = ((lean_object*)(l_Lean_Elab_WF_assignSubsumed___closed__0));
v___x_4920_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_mvars_4913_, v___f_4919_, v_a_4914_, v_a_4915_, v_a_4916_, v_a_4917_);
return v___x_4920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___boxed(lean_object* v_mvars_4921_, lean_object* v_a_4922_, lean_object* v_a_4923_, lean_object* v_a_4924_, lean_object* v_a_4925_, lean_object* v_a_4926_){
_start:
{
lean_object* v_res_4927_; 
v_res_4927_ = l_Lean_Elab_WF_assignSubsumed(v_mvars_4921_, v_a_4922_, v_a_4923_, v_a_4924_, v_a_4925_);
lean_dec(v_a_4925_);
lean_dec_ref(v_a_4924_);
lean_dec(v_a_4923_);
lean_dec_ref(v_a_4922_);
lean_dec_ref(v_mvars_4921_);
return v_res_4927_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0(lean_object* v_mvarId_4928_, lean_object* v_val_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_){
_start:
{
lean_object* v___x_4935_; 
v___x_4935_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mvarId_4928_, v_val_4929_, v___y_4931_);
return v___x_4935_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___boxed(lean_object* v_mvarId_4936_, lean_object* v_val_4937_, lean_object* v___y_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_){
_start:
{
lean_object* v_res_4943_; 
v_res_4943_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0(v_mvarId_4936_, v_val_4937_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_);
lean_dec(v___y_4941_);
lean_dec_ref(v___y_4940_);
lean_dec(v___y_4939_);
lean_dec_ref(v___y_4938_);
return v_res_4943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1(lean_object* v_00_u03b1_4944_, lean_object* v_a_4945_, lean_object* v_f_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_){
_start:
{
lean_object* v___x_4952_; 
v___x_4952_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_a_4945_, v_f_4946_, v___y_4947_, v___y_4948_, v___y_4949_, v___y_4950_);
return v___x_4952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___boxed(lean_object* v_00_u03b1_4953_, lean_object* v_a_4954_, lean_object* v_f_4955_, lean_object* v___y_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_){
_start:
{
lean_object* v_res_4961_; 
v_res_4961_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1(v_00_u03b1_4953_, v_a_4954_, v_f_4955_, v___y_4956_, v___y_4957_, v___y_4958_, v___y_4959_);
lean_dec(v___y_4959_);
lean_dec_ref(v___y_4958_);
lean_dec(v___y_4957_);
lean_dec_ref(v___y_4956_);
lean_dec_ref(v_a_4954_);
return v_res_4961_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0(lean_object* v_00_u03b2_4962_, lean_object* v_x_4963_, lean_object* v_x_4964_, lean_object* v_x_4965_){
_start:
{
lean_object* v___x_4966_; 
v___x_4966_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(v_x_4963_, v_x_4964_, v_x_4965_);
return v___x_4966_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2(lean_object* v_upperBound_4967_, lean_object* v_00_u03b1_4968_, lean_object* v_a_4969_, lean_object* v_next_4970_, lean_object* v_f_4971_, lean_object* v_inst_4972_, lean_object* v_R_4973_, lean_object* v_a_4974_, lean_object* v_b_4975_, lean_object* v_c_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_){
_start:
{
lean_object* v___x_4982_; 
v___x_4982_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v_upperBound_4967_, v_a_4969_, v_next_4970_, v_f_4971_, v_a_4974_, v_b_4975_, v___y_4977_, v___y_4978_, v___y_4979_, v___y_4980_);
return v___x_4982_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___boxed(lean_object* v_upperBound_4983_, lean_object* v_00_u03b1_4984_, lean_object* v_a_4985_, lean_object* v_next_4986_, lean_object* v_f_4987_, lean_object* v_inst_4988_, lean_object* v_R_4989_, lean_object* v_a_4990_, lean_object* v_b_4991_, lean_object* v_c_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_){
_start:
{
lean_object* v_res_4998_; 
v_res_4998_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2(v_upperBound_4983_, v_00_u03b1_4984_, v_a_4985_, v_next_4986_, v_f_4987_, v_inst_4988_, v_R_4989_, v_a_4990_, v_b_4991_, v_c_4992_, v___y_4993_, v___y_4994_, v___y_4995_, v___y_4996_);
lean_dec(v___y_4996_);
lean_dec_ref(v___y_4995_);
lean_dec(v___y_4994_);
lean_dec_ref(v___y_4993_);
lean_dec_ref(v_a_4985_);
lean_dec(v_upperBound_4983_);
return v_res_4998_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3(lean_object* v_00_u03b1_4999_, lean_object* v_upperBound_5000_, lean_object* v_removed_5001_, lean_object* v_a_5002_, lean_object* v_inst_5003_, lean_object* v_R_5004_, lean_object* v_a_5005_, lean_object* v_b_5006_, lean_object* v_c_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_, lean_object* v___y_5011_){
_start:
{
lean_object* v___x_5013_; 
v___x_5013_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v_upperBound_5000_, v_removed_5001_, v_a_5002_, v_a_5005_, v_b_5006_, v___y_5008_, v___y_5009_, v___y_5010_, v___y_5011_);
return v___x_5013_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___boxed(lean_object* v_00_u03b1_5014_, lean_object* v_upperBound_5015_, lean_object* v_removed_5016_, lean_object* v_a_5017_, lean_object* v_inst_5018_, lean_object* v_R_5019_, lean_object* v_a_5020_, lean_object* v_b_5021_, lean_object* v_c_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_){
_start:
{
lean_object* v_res_5028_; 
v_res_5028_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3(v_00_u03b1_5014_, v_upperBound_5015_, v_removed_5016_, v_a_5017_, v_inst_5018_, v_R_5019_, v_a_5020_, v_b_5021_, v_c_5022_, v___y_5023_, v___y_5024_, v___y_5025_, v___y_5026_);
lean_dec(v___y_5026_);
lean_dec_ref(v___y_5025_);
lean_dec(v___y_5024_);
lean_dec_ref(v___y_5023_);
lean_dec_ref(v_a_5017_);
lean_dec_ref(v_removed_5016_);
lean_dec(v_upperBound_5015_);
return v_res_5028_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4(lean_object* v_upperBound_5029_, lean_object* v___x_5030_, lean_object* v_00_u03b1_5031_, lean_object* v_a_5032_, lean_object* v_f_5033_, lean_object* v_inst_5034_, lean_object* v_R_5035_, lean_object* v_a_5036_, lean_object* v_b_5037_, lean_object* v_c_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_){
_start:
{
lean_object* v___x_5044_; 
v___x_5044_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v_upperBound_5029_, v___x_5030_, v_a_5032_, v_f_5033_, v_a_5036_, v_b_5037_, v___y_5039_, v___y_5040_, v___y_5041_, v___y_5042_);
return v___x_5044_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___boxed(lean_object* v_upperBound_5045_, lean_object* v___x_5046_, lean_object* v_00_u03b1_5047_, lean_object* v_a_5048_, lean_object* v_f_5049_, lean_object* v_inst_5050_, lean_object* v_R_5051_, lean_object* v_a_5052_, lean_object* v_b_5053_, lean_object* v_c_5054_, lean_object* v___y_5055_, lean_object* v___y_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_, lean_object* v___y_5059_){
_start:
{
lean_object* v_res_5060_; 
v_res_5060_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4(v_upperBound_5045_, v___x_5046_, v_00_u03b1_5047_, v_a_5048_, v_f_5049_, v_inst_5050_, v_R_5051_, v_a_5052_, v_b_5053_, v_c_5054_, v___y_5055_, v___y_5056_, v___y_5057_, v___y_5058_);
lean_dec(v___y_5058_);
lean_dec_ref(v___y_5057_);
lean_dec(v___y_5056_);
lean_dec_ref(v___y_5055_);
lean_dec_ref(v_a_5048_);
lean_dec(v___x_5046_);
lean_dec(v_upperBound_5045_);
return v_res_5060_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5061_, lean_object* v_x_5062_, size_t v_x_5063_, size_t v_x_5064_, lean_object* v_x_5065_, lean_object* v_x_5066_){
_start:
{
lean_object* v___x_5067_; 
v___x_5067_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_5062_, v_x_5063_, v_x_5064_, v_x_5065_, v_x_5066_);
return v___x_5067_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5068_, lean_object* v_x_5069_, lean_object* v_x_5070_, lean_object* v_x_5071_, lean_object* v_x_5072_, lean_object* v_x_5073_){
_start:
{
size_t v_x_5200__boxed_5074_; size_t v_x_5201__boxed_5075_; lean_object* v_res_5076_; 
v_x_5200__boxed_5074_ = lean_unbox_usize(v_x_5070_);
lean_dec(v_x_5070_);
v_x_5201__boxed_5075_ = lean_unbox_usize(v_x_5071_);
lean_dec(v_x_5071_);
v_res_5076_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1(v_00_u03b2_5068_, v_x_5069_, v_x_5200__boxed_5074_, v_x_5201__boxed_5075_, v_x_5072_, v_x_5073_);
return v_res_5076_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_5077_, lean_object* v_n_5078_, lean_object* v_k_5079_, lean_object* v_v_5080_){
_start:
{
lean_object* v___x_5081_; 
v___x_5081_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(v_n_5078_, v_k_5079_, v_v_5080_);
return v___x_5081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_5082_, size_t v_depth_5083_, lean_object* v_keys_5084_, lean_object* v_vals_5085_, lean_object* v_heq_5086_, lean_object* v_i_5087_, lean_object* v_entries_5088_){
_start:
{
lean_object* v___x_5089_; 
v___x_5089_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_5083_, v_keys_5084_, v_vals_5085_, v_i_5087_, v_entries_5088_);
return v___x_5089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_5090_, lean_object* v_depth_5091_, lean_object* v_keys_5092_, lean_object* v_vals_5093_, lean_object* v_heq_5094_, lean_object* v_i_5095_, lean_object* v_entries_5096_){
_start:
{
size_t v_depth_boxed_5097_; lean_object* v_res_5098_; 
v_depth_boxed_5097_ = lean_unbox_usize(v_depth_5091_);
lean_dec(v_depth_5091_);
v_res_5098_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_5090_, v_depth_boxed_5097_, v_keys_5092_, v_vals_5093_, v_heq_5094_, v_i_5095_, v_entries_5096_);
lean_dec_ref(v_vals_5093_);
lean_dec_ref(v_keys_5092_);
return v_res_5098_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_5099_, lean_object* v_x_5100_, lean_object* v_x_5101_, lean_object* v_x_5102_, lean_object* v_x_5103_){
_start:
{
lean_object* v___x_5104_; 
v___x_5104_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_x_5100_, v_x_5101_, v_x_5102_, v_x_5103_);
return v___x_5104_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1(void){
_start:
{
lean_object* v___x_5106_; lean_object* v___x_5107_; 
v___x_5106_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__0));
v___x_5107_ = l_Lean_stringToMessageData(v___x_5106_);
return v___x_5107_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3(void){
_start:
{
lean_object* v___x_5109_; lean_object* v___x_5110_; 
v___x_5109_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__2));
v___x_5110_ = l_Lean_stringToMessageData(v___x_5109_);
return v___x_5110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(lean_object* v_argsPacker_5111_, lean_object* v_as_5112_, size_t v_sz_5113_, size_t v_i_5114_, lean_object* v_b_5115_, lean_object* v___y_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_){
_start:
{
lean_object* v_a_5122_; uint8_t v___x_5126_; 
v___x_5126_ = lean_usize_dec_lt(v_i_5114_, v_sz_5113_);
if (v___x_5126_ == 0)
{
lean_object* v___x_5127_; 
v___x_5127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5127_, 0, v_b_5115_);
return v___x_5127_;
}
else
{
lean_object* v_a_5128_; lean_object* v___x_5129_; 
v_a_5128_ = lean_array_uget_borrowed(v_as_5112_, v_i_5114_);
lean_inc(v_a_5128_);
v___x_5129_ = l_Lean_MVarId_getType(v_a_5128_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_);
if (lean_obj_tag(v___x_5129_) == 0)
{
lean_object* v_a_5130_; lean_object* v___y_5132_; lean_object* v___y_5133_; lean_object* v___y_5134_; lean_object* v___y_5135_; 
v_a_5130_ = lean_ctor_get(v___x_5129_, 0);
lean_inc(v_a_5130_);
lean_dec_ref_known(v___x_5129_, 1);
if (lean_obj_tag(v_a_5130_) == 10)
{
lean_object* v_expr_5148_; 
v_expr_5148_ = lean_ctor_get(v_a_5130_, 1);
if (lean_obj_tag(v_expr_5148_) == 5)
{
lean_object* v_arg_5149_; lean_object* v___x_5150_; 
lean_inc_ref(v_expr_5148_);
lean_dec_ref_known(v_a_5130_, 2);
v_arg_5149_ = lean_ctor_get(v_expr_5148_, 1);
lean_inc_ref_n(v_arg_5149_, 2);
lean_dec_ref_known(v_expr_5148_, 2);
v___x_5150_ = l_Lean_Meta_ArgsPacker_unpack(v_argsPacker_5111_, v_arg_5149_);
if (lean_obj_tag(v___x_5150_) == 1)
{
lean_object* v_val_5151_; lean_object* v_fst_5152_; lean_object* v___x_5153_; uint8_t v___x_5154_; 
lean_dec_ref(v_arg_5149_);
v_val_5151_ = lean_ctor_get(v___x_5150_, 0);
lean_inc(v_val_5151_);
lean_dec_ref_known(v___x_5150_, 1);
v_fst_5152_ = lean_ctor_get(v_val_5151_, 0);
lean_inc(v_fst_5152_);
lean_dec(v_val_5151_);
v___x_5153_ = lean_array_get_size(v_b_5115_);
v___x_5154_ = lean_nat_dec_lt(v_fst_5152_, v___x_5153_);
if (v___x_5154_ == 0)
{
lean_dec(v_fst_5152_);
v_a_5122_ = v_b_5115_;
goto v___jp_5121_;
}
else
{
lean_object* v_v_5155_; lean_object* v___x_5156_; lean_object* v_xs_x27_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; 
v_v_5155_ = lean_array_fget(v_b_5115_, v_fst_5152_);
v___x_5156_ = lean_box(0);
v_xs_x27_5157_ = lean_array_fset(v_b_5115_, v_fst_5152_, v___x_5156_);
lean_inc(v_a_5128_);
v___x_5158_ = lean_array_push(v_v_5155_, v_a_5128_);
v___x_5159_ = lean_array_fset(v_xs_x27_5157_, v_fst_5152_, v___x_5158_);
lean_dec(v_fst_5152_);
v_a_5122_ = v___x_5159_;
goto v___jp_5121_;
}
}
else
{
lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; lean_object* v___x_5163_; 
lean_dec(v___x_5150_);
v___x_5160_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3);
v___x_5161_ = l_Lean_indentExpr(v_arg_5149_);
v___x_5162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5162_, 0, v___x_5160_);
lean_ctor_set(v___x_5162_, 1, v___x_5161_);
v___x_5163_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v___x_5162_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_);
if (lean_obj_tag(v___x_5163_) == 0)
{
lean_dec_ref_known(v___x_5163_, 1);
v_a_5122_ = v_b_5115_;
goto v___jp_5121_;
}
else
{
lean_object* v_a_5164_; lean_object* v___x_5166_; uint8_t v_isShared_5167_; uint8_t v_isSharedCheck_5171_; 
lean_dec_ref(v_b_5115_);
v_a_5164_ = lean_ctor_get(v___x_5163_, 0);
v_isSharedCheck_5171_ = !lean_is_exclusive(v___x_5163_);
if (v_isSharedCheck_5171_ == 0)
{
v___x_5166_ = v___x_5163_;
v_isShared_5167_ = v_isSharedCheck_5171_;
goto v_resetjp_5165_;
}
else
{
lean_inc(v_a_5164_);
lean_dec(v___x_5163_);
v___x_5166_ = lean_box(0);
v_isShared_5167_ = v_isSharedCheck_5171_;
goto v_resetjp_5165_;
}
v_resetjp_5165_:
{
lean_object* v___x_5169_; 
if (v_isShared_5167_ == 0)
{
v___x_5169_ = v___x_5166_;
goto v_reusejp_5168_;
}
else
{
lean_object* v_reuseFailAlloc_5170_; 
v_reuseFailAlloc_5170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5170_, 0, v_a_5164_);
v___x_5169_ = v_reuseFailAlloc_5170_;
goto v_reusejp_5168_;
}
v_reusejp_5168_:
{
return v___x_5169_;
}
}
}
}
}
else
{
v___y_5132_ = v___y_5116_;
v___y_5133_ = v___y_5117_;
v___y_5134_ = v___y_5118_;
v___y_5135_ = v___y_5119_;
goto v___jp_5131_;
}
}
else
{
v___y_5132_ = v___y_5116_;
v___y_5133_ = v___y_5117_;
v___y_5134_ = v___y_5118_;
v___y_5135_ = v___y_5119_;
goto v___jp_5131_;
}
v___jp_5131_:
{
lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; 
v___x_5136_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1);
v___x_5137_ = l_Lean_indentExpr(v_a_5130_);
v___x_5138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5138_, 0, v___x_5136_);
lean_ctor_set(v___x_5138_, 1, v___x_5137_);
v___x_5139_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v___x_5138_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_);
if (lean_obj_tag(v___x_5139_) == 0)
{
lean_dec_ref_known(v___x_5139_, 1);
v_a_5122_ = v_b_5115_;
goto v___jp_5121_;
}
else
{
lean_object* v_a_5140_; lean_object* v___x_5142_; uint8_t v_isShared_5143_; uint8_t v_isSharedCheck_5147_; 
lean_dec_ref(v_b_5115_);
v_a_5140_ = lean_ctor_get(v___x_5139_, 0);
v_isSharedCheck_5147_ = !lean_is_exclusive(v___x_5139_);
if (v_isSharedCheck_5147_ == 0)
{
v___x_5142_ = v___x_5139_;
v_isShared_5143_ = v_isSharedCheck_5147_;
goto v_resetjp_5141_;
}
else
{
lean_inc(v_a_5140_);
lean_dec(v___x_5139_);
v___x_5142_ = lean_box(0);
v_isShared_5143_ = v_isSharedCheck_5147_;
goto v_resetjp_5141_;
}
v_resetjp_5141_:
{
lean_object* v___x_5145_; 
if (v_isShared_5143_ == 0)
{
v___x_5145_ = v___x_5142_;
goto v_reusejp_5144_;
}
else
{
lean_object* v_reuseFailAlloc_5146_; 
v_reuseFailAlloc_5146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5146_, 0, v_a_5140_);
v___x_5145_ = v_reuseFailAlloc_5146_;
goto v_reusejp_5144_;
}
v_reusejp_5144_:
{
return v___x_5145_;
}
}
}
}
}
else
{
lean_object* v_a_5172_; lean_object* v___x_5174_; uint8_t v_isShared_5175_; uint8_t v_isSharedCheck_5179_; 
lean_dec_ref(v_b_5115_);
v_a_5172_ = lean_ctor_get(v___x_5129_, 0);
v_isSharedCheck_5179_ = !lean_is_exclusive(v___x_5129_);
if (v_isSharedCheck_5179_ == 0)
{
v___x_5174_ = v___x_5129_;
v_isShared_5175_ = v_isSharedCheck_5179_;
goto v_resetjp_5173_;
}
else
{
lean_inc(v_a_5172_);
lean_dec(v___x_5129_);
v___x_5174_ = lean_box(0);
v_isShared_5175_ = v_isSharedCheck_5179_;
goto v_resetjp_5173_;
}
v_resetjp_5173_:
{
lean_object* v___x_5177_; 
if (v_isShared_5175_ == 0)
{
v___x_5177_ = v___x_5174_;
goto v_reusejp_5176_;
}
else
{
lean_object* v_reuseFailAlloc_5178_; 
v_reuseFailAlloc_5178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5178_, 0, v_a_5172_);
v___x_5177_ = v_reuseFailAlloc_5178_;
goto v_reusejp_5176_;
}
v_reusejp_5176_:
{
return v___x_5177_;
}
}
}
}
v___jp_5121_:
{
size_t v___x_5123_; size_t v___x_5124_; 
v___x_5123_ = ((size_t)1ULL);
v___x_5124_ = lean_usize_add(v_i_5114_, v___x_5123_);
v_i_5114_ = v___x_5124_;
v_b_5115_ = v_a_5122_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___boxed(lean_object* v_argsPacker_5180_, lean_object* v_as_5181_, lean_object* v_sz_5182_, lean_object* v_i_5183_, lean_object* v_b_5184_, lean_object* v___y_5185_, lean_object* v___y_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_, lean_object* v___y_5189_){
_start:
{
size_t v_sz_boxed_5190_; size_t v_i_boxed_5191_; lean_object* v_res_5192_; 
v_sz_boxed_5190_ = lean_unbox_usize(v_sz_5182_);
lean_dec(v_sz_5182_);
v_i_boxed_5191_ = lean_unbox_usize(v_i_5183_);
lean_dec(v_i_5183_);
v_res_5192_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(v_argsPacker_5180_, v_as_5181_, v_sz_boxed_5190_, v_i_boxed_5191_, v_b_5184_, v___y_5185_, v___y_5186_, v___y_5187_, v___y_5188_);
lean_dec(v___y_5188_);
lean_dec_ref(v___y_5187_);
lean_dec(v___y_5186_);
lean_dec_ref(v___y_5185_);
lean_dec_ref(v_as_5181_);
lean_dec_ref(v_argsPacker_5180_);
return v_res_5192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_groupGoalsByFunction(lean_object* v_argsPacker_5193_, lean_object* v_numFuncs_5194_, lean_object* v_goals_5195_, lean_object* v_a_5196_, lean_object* v_a_5197_, lean_object* v_a_5198_, lean_object* v_a_5199_){
_start:
{
lean_object* v___x_5201_; lean_object* v_r_5202_; size_t v_sz_5203_; size_t v___x_5204_; lean_object* v___x_5205_; 
v___x_5201_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg___closed__0));
v_r_5202_ = lean_mk_array(v_numFuncs_5194_, v___x_5201_);
v_sz_5203_ = lean_array_size(v_goals_5195_);
v___x_5204_ = ((size_t)0ULL);
v___x_5205_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(v_argsPacker_5193_, v_goals_5195_, v_sz_5203_, v___x_5204_, v_r_5202_, v_a_5196_, v_a_5197_, v_a_5198_, v_a_5199_);
return v___x_5205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_groupGoalsByFunction___boxed(lean_object* v_argsPacker_5206_, lean_object* v_numFuncs_5207_, lean_object* v_goals_5208_, lean_object* v_a_5209_, lean_object* v_a_5210_, lean_object* v_a_5211_, lean_object* v_a_5212_, lean_object* v_a_5213_){
_start:
{
lean_object* v_res_5214_; 
v_res_5214_ = l_Lean_Elab_WF_groupGoalsByFunction(v_argsPacker_5206_, v_numFuncs_5207_, v_goals_5208_, v_a_5209_, v_a_5210_, v_a_5211_, v_a_5212_);
lean_dec(v_a_5212_);
lean_dec_ref(v_a_5211_);
lean_dec(v_a_5210_);
lean_dec_ref(v_a_5209_);
lean_dec_ref(v_goals_5208_);
lean_dec_ref(v_argsPacker_5206_);
return v_res_5214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(lean_object* v_t_5215_, lean_object* v___y_5216_){
_start:
{
lean_object* v___x_5218_; lean_object* v_infoState_5219_; uint8_t v_enabled_5220_; 
v___x_5218_ = lean_st_ref_get(v___y_5216_);
v_infoState_5219_ = lean_ctor_get(v___x_5218_, 7);
lean_inc_ref(v_infoState_5219_);
lean_dec(v___x_5218_);
v_enabled_5220_ = lean_ctor_get_uint8(v_infoState_5219_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5219_);
if (v_enabled_5220_ == 0)
{
lean_object* v___x_5221_; lean_object* v___x_5222_; 
lean_dec_ref(v_t_5215_);
v___x_5221_ = lean_box(0);
v___x_5222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5222_, 0, v___x_5221_);
return v___x_5222_;
}
else
{
lean_object* v___x_5223_; lean_object* v_infoState_5224_; lean_object* v_env_5225_; lean_object* v_nextMacroScope_5226_; lean_object* v_ngen_5227_; lean_object* v_auxDeclNGen_5228_; lean_object* v_traceState_5229_; lean_object* v_cache_5230_; lean_object* v_messages_5231_; lean_object* v_snapshotTasks_5232_; lean_object* v___x_5234_; uint8_t v_isShared_5235_; uint8_t v_isSharedCheck_5254_; 
v___x_5223_ = lean_st_ref_take(v___y_5216_);
v_infoState_5224_ = lean_ctor_get(v___x_5223_, 7);
v_env_5225_ = lean_ctor_get(v___x_5223_, 0);
v_nextMacroScope_5226_ = lean_ctor_get(v___x_5223_, 1);
v_ngen_5227_ = lean_ctor_get(v___x_5223_, 2);
v_auxDeclNGen_5228_ = lean_ctor_get(v___x_5223_, 3);
v_traceState_5229_ = lean_ctor_get(v___x_5223_, 4);
v_cache_5230_ = lean_ctor_get(v___x_5223_, 5);
v_messages_5231_ = lean_ctor_get(v___x_5223_, 6);
v_snapshotTasks_5232_ = lean_ctor_get(v___x_5223_, 8);
v_isSharedCheck_5254_ = !lean_is_exclusive(v___x_5223_);
if (v_isSharedCheck_5254_ == 0)
{
v___x_5234_ = v___x_5223_;
v_isShared_5235_ = v_isSharedCheck_5254_;
goto v_resetjp_5233_;
}
else
{
lean_inc(v_snapshotTasks_5232_);
lean_inc(v_infoState_5224_);
lean_inc(v_messages_5231_);
lean_inc(v_cache_5230_);
lean_inc(v_traceState_5229_);
lean_inc(v_auxDeclNGen_5228_);
lean_inc(v_ngen_5227_);
lean_inc(v_nextMacroScope_5226_);
lean_inc(v_env_5225_);
lean_dec(v___x_5223_);
v___x_5234_ = lean_box(0);
v_isShared_5235_ = v_isSharedCheck_5254_;
goto v_resetjp_5233_;
}
v_resetjp_5233_:
{
uint8_t v_enabled_5236_; lean_object* v_assignment_5237_; lean_object* v_lazyAssignment_5238_; lean_object* v_trees_5239_; lean_object* v___x_5241_; uint8_t v_isShared_5242_; uint8_t v_isSharedCheck_5253_; 
v_enabled_5236_ = lean_ctor_get_uint8(v_infoState_5224_, sizeof(void*)*3);
v_assignment_5237_ = lean_ctor_get(v_infoState_5224_, 0);
v_lazyAssignment_5238_ = lean_ctor_get(v_infoState_5224_, 1);
v_trees_5239_ = lean_ctor_get(v_infoState_5224_, 2);
v_isSharedCheck_5253_ = !lean_is_exclusive(v_infoState_5224_);
if (v_isSharedCheck_5253_ == 0)
{
v___x_5241_ = v_infoState_5224_;
v_isShared_5242_ = v_isSharedCheck_5253_;
goto v_resetjp_5240_;
}
else
{
lean_inc(v_trees_5239_);
lean_inc(v_lazyAssignment_5238_);
lean_inc(v_assignment_5237_);
lean_dec(v_infoState_5224_);
v___x_5241_ = lean_box(0);
v_isShared_5242_ = v_isSharedCheck_5253_;
goto v_resetjp_5240_;
}
v_resetjp_5240_:
{
lean_object* v___x_5243_; lean_object* v___x_5245_; 
v___x_5243_ = l_Lean_PersistentArray_push___redArg(v_trees_5239_, v_t_5215_);
if (v_isShared_5242_ == 0)
{
lean_ctor_set(v___x_5241_, 2, v___x_5243_);
v___x_5245_ = v___x_5241_;
goto v_reusejp_5244_;
}
else
{
lean_object* v_reuseFailAlloc_5252_; 
v_reuseFailAlloc_5252_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5252_, 0, v_assignment_5237_);
lean_ctor_set(v_reuseFailAlloc_5252_, 1, v_lazyAssignment_5238_);
lean_ctor_set(v_reuseFailAlloc_5252_, 2, v___x_5243_);
lean_ctor_set_uint8(v_reuseFailAlloc_5252_, sizeof(void*)*3, v_enabled_5236_);
v___x_5245_ = v_reuseFailAlloc_5252_;
goto v_reusejp_5244_;
}
v_reusejp_5244_:
{
lean_object* v___x_5247_; 
if (v_isShared_5235_ == 0)
{
lean_ctor_set(v___x_5234_, 7, v___x_5245_);
v___x_5247_ = v___x_5234_;
goto v_reusejp_5246_;
}
else
{
lean_object* v_reuseFailAlloc_5251_; 
v_reuseFailAlloc_5251_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5251_, 0, v_env_5225_);
lean_ctor_set(v_reuseFailAlloc_5251_, 1, v_nextMacroScope_5226_);
lean_ctor_set(v_reuseFailAlloc_5251_, 2, v_ngen_5227_);
lean_ctor_set(v_reuseFailAlloc_5251_, 3, v_auxDeclNGen_5228_);
lean_ctor_set(v_reuseFailAlloc_5251_, 4, v_traceState_5229_);
lean_ctor_set(v_reuseFailAlloc_5251_, 5, v_cache_5230_);
lean_ctor_set(v_reuseFailAlloc_5251_, 6, v_messages_5231_);
lean_ctor_set(v_reuseFailAlloc_5251_, 7, v___x_5245_);
lean_ctor_set(v_reuseFailAlloc_5251_, 8, v_snapshotTasks_5232_);
v___x_5247_ = v_reuseFailAlloc_5251_;
goto v_reusejp_5246_;
}
v_reusejp_5246_:
{
lean_object* v___x_5248_; lean_object* v___x_5249_; lean_object* v___x_5250_; 
v___x_5248_ = lean_st_ref_put(v___y_5216_, v___x_5247_);
v___x_5249_ = lean_box(0);
v___x_5250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5250_, 0, v___x_5249_);
return v___x_5250_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg___boxed(lean_object* v_t_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_){
_start:
{
lean_object* v_res_5258_; 
v_res_5258_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v_t_5255_, v___y_5256_);
lean_dec(v___y_5256_);
return v_res_5258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0(lean_object* v_t_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_, lean_object* v___y_5262_, lean_object* v___y_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_){
_start:
{
lean_object* v___x_5267_; 
v___x_5267_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v_t_5259_, v___y_5265_);
return v___x_5267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___boxed(lean_object* v_t_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_){
_start:
{
lean_object* v_res_5276_; 
v_res_5276_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0(v_t_5268_, v___y_5269_, v___y_5270_, v___y_5271_, v___y_5272_, v___y_5273_, v___y_5274_);
lean_dec(v___y_5274_);
lean_dec_ref(v___y_5273_);
lean_dec(v___y_5272_);
lean_dec_ref(v___y_5271_);
lean_dec(v___y_5270_);
lean_dec_ref(v___y_5269_);
return v_res_5276_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(lean_object* v_e_5277_, lean_object* v___y_5278_){
_start:
{
uint8_t v___x_5280_; 
v___x_5280_ = l_Lean_Expr_hasMVar(v_e_5277_);
if (v___x_5280_ == 0)
{
lean_object* v___x_5281_; 
v___x_5281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5281_, 0, v_e_5277_);
return v___x_5281_;
}
else
{
lean_object* v___x_5282_; lean_object* v_mctx_5283_; lean_object* v___x_5284_; lean_object* v_fst_5285_; lean_object* v_snd_5286_; lean_object* v___x_5287_; lean_object* v_cache_5288_; lean_object* v_zetaDeltaFVarIds_5289_; lean_object* v_postponed_5290_; lean_object* v_diag_5291_; lean_object* v___x_5293_; uint8_t v_isShared_5294_; uint8_t v_isSharedCheck_5300_; 
v___x_5282_ = lean_st_ref_get(v___y_5278_);
v_mctx_5283_ = lean_ctor_get(v___x_5282_, 0);
lean_inc_ref(v_mctx_5283_);
lean_dec(v___x_5282_);
v___x_5284_ = l_Lean_instantiateMVarsCore(v_mctx_5283_, v_e_5277_);
v_fst_5285_ = lean_ctor_get(v___x_5284_, 0);
lean_inc(v_fst_5285_);
v_snd_5286_ = lean_ctor_get(v___x_5284_, 1);
lean_inc(v_snd_5286_);
lean_dec_ref(v___x_5284_);
v___x_5287_ = lean_st_ref_take(v___y_5278_);
v_cache_5288_ = lean_ctor_get(v___x_5287_, 1);
v_zetaDeltaFVarIds_5289_ = lean_ctor_get(v___x_5287_, 2);
v_postponed_5290_ = lean_ctor_get(v___x_5287_, 3);
v_diag_5291_ = lean_ctor_get(v___x_5287_, 4);
v_isSharedCheck_5300_ = !lean_is_exclusive(v___x_5287_);
if (v_isSharedCheck_5300_ == 0)
{
lean_object* v_unused_5301_; 
v_unused_5301_ = lean_ctor_get(v___x_5287_, 0);
lean_dec(v_unused_5301_);
v___x_5293_ = v___x_5287_;
v_isShared_5294_ = v_isSharedCheck_5300_;
goto v_resetjp_5292_;
}
else
{
lean_inc(v_diag_5291_);
lean_inc(v_postponed_5290_);
lean_inc(v_zetaDeltaFVarIds_5289_);
lean_inc(v_cache_5288_);
lean_dec(v___x_5287_);
v___x_5293_ = lean_box(0);
v_isShared_5294_ = v_isSharedCheck_5300_;
goto v_resetjp_5292_;
}
v_resetjp_5292_:
{
lean_object* v___x_5296_; 
if (v_isShared_5294_ == 0)
{
lean_ctor_set(v___x_5293_, 0, v_snd_5286_);
v___x_5296_ = v___x_5293_;
goto v_reusejp_5295_;
}
else
{
lean_object* v_reuseFailAlloc_5299_; 
v_reuseFailAlloc_5299_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5299_, 0, v_snd_5286_);
lean_ctor_set(v_reuseFailAlloc_5299_, 1, v_cache_5288_);
lean_ctor_set(v_reuseFailAlloc_5299_, 2, v_zetaDeltaFVarIds_5289_);
lean_ctor_set(v_reuseFailAlloc_5299_, 3, v_postponed_5290_);
lean_ctor_set(v_reuseFailAlloc_5299_, 4, v_diag_5291_);
v___x_5296_ = v_reuseFailAlloc_5299_;
goto v_reusejp_5295_;
}
v_reusejp_5295_:
{
lean_object* v___x_5297_; lean_object* v___x_5298_; 
v___x_5297_ = lean_st_ref_put(v___y_5278_, v___x_5296_);
v___x_5298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5298_, 0, v_fst_5285_);
return v___x_5298_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg___boxed(lean_object* v_e_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_){
_start:
{
lean_object* v_res_5305_; 
v_res_5305_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_e_5302_, v___y_5303_);
lean_dec(v___y_5303_);
return v_res_5305_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7(lean_object* v_e_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_){
_start:
{
lean_object* v___x_5312_; 
v___x_5312_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_e_5306_, v___y_5308_);
return v___x_5312_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___boxed(lean_object* v_e_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_){
_start:
{
lean_object* v_res_5319_; 
v_res_5319_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7(v_e_5313_, v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_);
lean_dec(v___y_5317_);
lean_dec_ref(v___y_5316_);
lean_dec(v___y_5315_);
lean_dec_ref(v___y_5314_);
return v_res_5319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(lean_object* v_as_5320_, size_t v_i_5321_, size_t v_stop_5322_, lean_object* v_b_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_){
_start:
{
uint8_t v___x_5331_; 
v___x_5331_ = lean_usize_dec_eq(v_i_5321_, v_stop_5322_);
if (v___x_5331_ == 0)
{
lean_object* v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; 
v___x_5332_ = lean_array_uget_borrowed(v_as_5320_, v_i_5321_);
lean_inc(v___x_5332_);
v___x_5333_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_5333_, 0, v___x_5332_);
v___x_5334_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v___x_5333_, v___y_5329_);
if (lean_obj_tag(v___x_5334_) == 0)
{
lean_object* v_a_5335_; size_t v___x_5336_; size_t v___x_5337_; 
v_a_5335_ = lean_ctor_get(v___x_5334_, 0);
lean_inc(v_a_5335_);
lean_dec_ref_known(v___x_5334_, 1);
v___x_5336_ = ((size_t)1ULL);
v___x_5337_ = lean_usize_add(v_i_5321_, v___x_5336_);
v_i_5321_ = v___x_5337_;
v_b_5323_ = v_a_5335_;
goto _start;
}
else
{
return v___x_5334_;
}
}
else
{
lean_object* v___x_5339_; 
v___x_5339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5339_, 0, v_b_5323_);
return v___x_5339_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4___boxed(lean_object* v_as_5340_, lean_object* v_i_5341_, lean_object* v_stop_5342_, lean_object* v_b_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_, lean_object* v___y_5350_){
_start:
{
size_t v_i_boxed_5351_; size_t v_stop_boxed_5352_; lean_object* v_res_5353_; 
v_i_boxed_5351_ = lean_unbox_usize(v_i_5341_);
lean_dec(v_i_5341_);
v_stop_boxed_5352_ = lean_unbox_usize(v_stop_5342_);
lean_dec(v_stop_5342_);
v_res_5353_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v_as_5340_, v_i_boxed_5351_, v_stop_boxed_5352_, v_b_5343_, v___y_5344_, v___y_5345_, v___y_5346_, v___y_5347_, v___y_5348_, v___y_5349_);
lean_dec(v___y_5349_);
lean_dec_ref(v___y_5348_);
lean_dec(v___y_5347_);
lean_dec_ref(v___y_5346_);
lean_dec(v___y_5345_);
lean_dec_ref(v___y_5344_);
lean_dec_ref(v_as_5340_);
return v_res_5353_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_5354_; lean_object* v___x_5355_; lean_object* v___x_5356_; 
v___x_5354_ = lean_unsigned_to_nat(32u);
v___x_5355_ = lean_mk_empty_array_with_capacity(v___x_5354_);
v___x_5356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5356_, 0, v___x_5355_);
return v___x_5356_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_5357_; lean_object* v___x_5358_; lean_object* v___x_5359_; lean_object* v___x_5360_; lean_object* v___x_5361_; lean_object* v___x_5362_; 
v___x_5357_ = ((size_t)5ULL);
v___x_5358_ = lean_unsigned_to_nat(0u);
v___x_5359_ = lean_unsigned_to_nat(32u);
v___x_5360_ = lean_mk_empty_array_with_capacity(v___x_5359_);
v___x_5361_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0);
v___x_5362_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5362_, 0, v___x_5361_);
lean_ctor_set(v___x_5362_, 1, v___x_5360_);
lean_ctor_set(v___x_5362_, 2, v___x_5358_);
lean_ctor_set(v___x_5362_, 3, v___x_5358_);
lean_ctor_set_usize(v___x_5362_, 4, v___x_5357_);
return v___x_5362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(lean_object* v___y_5363_){
_start:
{
lean_object* v___x_5365_; lean_object* v_infoState_5366_; lean_object* v_trees_5367_; lean_object* v___x_5368_; lean_object* v_infoState_5369_; lean_object* v_env_5370_; lean_object* v_nextMacroScope_5371_; lean_object* v_ngen_5372_; lean_object* v_auxDeclNGen_5373_; lean_object* v_traceState_5374_; lean_object* v_cache_5375_; lean_object* v_messages_5376_; lean_object* v_snapshotTasks_5377_; lean_object* v___x_5379_; uint8_t v_isShared_5380_; uint8_t v_isSharedCheck_5398_; 
v___x_5365_ = lean_st_ref_get(v___y_5363_);
v_infoState_5366_ = lean_ctor_get(v___x_5365_, 7);
lean_inc_ref(v_infoState_5366_);
lean_dec(v___x_5365_);
v_trees_5367_ = lean_ctor_get(v_infoState_5366_, 2);
lean_inc_ref(v_trees_5367_);
lean_dec_ref(v_infoState_5366_);
v___x_5368_ = lean_st_ref_take(v___y_5363_);
v_infoState_5369_ = lean_ctor_get(v___x_5368_, 7);
v_env_5370_ = lean_ctor_get(v___x_5368_, 0);
v_nextMacroScope_5371_ = lean_ctor_get(v___x_5368_, 1);
v_ngen_5372_ = lean_ctor_get(v___x_5368_, 2);
v_auxDeclNGen_5373_ = lean_ctor_get(v___x_5368_, 3);
v_traceState_5374_ = lean_ctor_get(v___x_5368_, 4);
v_cache_5375_ = lean_ctor_get(v___x_5368_, 5);
v_messages_5376_ = lean_ctor_get(v___x_5368_, 6);
v_snapshotTasks_5377_ = lean_ctor_get(v___x_5368_, 8);
v_isSharedCheck_5398_ = !lean_is_exclusive(v___x_5368_);
if (v_isSharedCheck_5398_ == 0)
{
v___x_5379_ = v___x_5368_;
v_isShared_5380_ = v_isSharedCheck_5398_;
goto v_resetjp_5378_;
}
else
{
lean_inc(v_snapshotTasks_5377_);
lean_inc(v_infoState_5369_);
lean_inc(v_messages_5376_);
lean_inc(v_cache_5375_);
lean_inc(v_traceState_5374_);
lean_inc(v_auxDeclNGen_5373_);
lean_inc(v_ngen_5372_);
lean_inc(v_nextMacroScope_5371_);
lean_inc(v_env_5370_);
lean_dec(v___x_5368_);
v___x_5379_ = lean_box(0);
v_isShared_5380_ = v_isSharedCheck_5398_;
goto v_resetjp_5378_;
}
v_resetjp_5378_:
{
uint8_t v_enabled_5381_; lean_object* v_assignment_5382_; lean_object* v_lazyAssignment_5383_; lean_object* v___x_5385_; uint8_t v_isShared_5386_; uint8_t v_isSharedCheck_5396_; 
v_enabled_5381_ = lean_ctor_get_uint8(v_infoState_5369_, sizeof(void*)*3);
v_assignment_5382_ = lean_ctor_get(v_infoState_5369_, 0);
v_lazyAssignment_5383_ = lean_ctor_get(v_infoState_5369_, 1);
v_isSharedCheck_5396_ = !lean_is_exclusive(v_infoState_5369_);
if (v_isSharedCheck_5396_ == 0)
{
lean_object* v_unused_5397_; 
v_unused_5397_ = lean_ctor_get(v_infoState_5369_, 2);
lean_dec(v_unused_5397_);
v___x_5385_ = v_infoState_5369_;
v_isShared_5386_ = v_isSharedCheck_5396_;
goto v_resetjp_5384_;
}
else
{
lean_inc(v_lazyAssignment_5383_);
lean_inc(v_assignment_5382_);
lean_dec(v_infoState_5369_);
v___x_5385_ = lean_box(0);
v_isShared_5386_ = v_isSharedCheck_5396_;
goto v_resetjp_5384_;
}
v_resetjp_5384_:
{
lean_object* v___x_5387_; lean_object* v___x_5389_; 
v___x_5387_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1);
if (v_isShared_5386_ == 0)
{
lean_ctor_set(v___x_5385_, 2, v___x_5387_);
v___x_5389_ = v___x_5385_;
goto v_reusejp_5388_;
}
else
{
lean_object* v_reuseFailAlloc_5395_; 
v_reuseFailAlloc_5395_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5395_, 0, v_assignment_5382_);
lean_ctor_set(v_reuseFailAlloc_5395_, 1, v_lazyAssignment_5383_);
lean_ctor_set(v_reuseFailAlloc_5395_, 2, v___x_5387_);
lean_ctor_set_uint8(v_reuseFailAlloc_5395_, sizeof(void*)*3, v_enabled_5381_);
v___x_5389_ = v_reuseFailAlloc_5395_;
goto v_reusejp_5388_;
}
v_reusejp_5388_:
{
lean_object* v___x_5391_; 
if (v_isShared_5380_ == 0)
{
lean_ctor_set(v___x_5379_, 7, v___x_5389_);
v___x_5391_ = v___x_5379_;
goto v_reusejp_5390_;
}
else
{
lean_object* v_reuseFailAlloc_5394_; 
v_reuseFailAlloc_5394_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5394_, 0, v_env_5370_);
lean_ctor_set(v_reuseFailAlloc_5394_, 1, v_nextMacroScope_5371_);
lean_ctor_set(v_reuseFailAlloc_5394_, 2, v_ngen_5372_);
lean_ctor_set(v_reuseFailAlloc_5394_, 3, v_auxDeclNGen_5373_);
lean_ctor_set(v_reuseFailAlloc_5394_, 4, v_traceState_5374_);
lean_ctor_set(v_reuseFailAlloc_5394_, 5, v_cache_5375_);
lean_ctor_set(v_reuseFailAlloc_5394_, 6, v_messages_5376_);
lean_ctor_set(v_reuseFailAlloc_5394_, 7, v___x_5389_);
lean_ctor_set(v_reuseFailAlloc_5394_, 8, v_snapshotTasks_5377_);
v___x_5391_ = v_reuseFailAlloc_5394_;
goto v_reusejp_5390_;
}
v_reusejp_5390_:
{
lean_object* v___x_5392_; lean_object* v___x_5393_; 
v___x_5392_ = lean_st_ref_put(v___y_5363_, v___x_5391_);
v___x_5393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5393_, 0, v_trees_5367_);
return v___x_5393_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___boxed(lean_object* v___y_5399_, lean_object* v___y_5400_){
_start:
{
lean_object* v_res_5401_; 
v_res_5401_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_5399_);
lean_dec(v___y_5399_);
return v_res_5401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(lean_object* v___y_5402_, lean_object* v_mkInfoTree_5403_, lean_object* v___y_5404_, lean_object* v___y_5405_, lean_object* v___y_5406_, lean_object* v___y_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_, lean_object* v_a_5411_, lean_object* v_a_x3f_5412_){
_start:
{
lean_object* v___x_5414_; lean_object* v_infoState_5415_; lean_object* v_trees_5416_; lean_object* v___x_5417_; 
v___x_5414_ = lean_st_ref_get(v___y_5402_);
v_infoState_5415_ = lean_ctor_get(v___x_5414_, 7);
lean_inc_ref(v_infoState_5415_);
lean_dec(v___x_5414_);
v_trees_5416_ = lean_ctor_get(v_infoState_5415_, 2);
lean_inc_ref(v_trees_5416_);
lean_dec_ref(v_infoState_5415_);
lean_inc(v___y_5402_);
lean_inc_ref(v___y_5410_);
lean_inc(v___y_5409_);
lean_inc_ref(v___y_5408_);
lean_inc(v___y_5407_);
lean_inc_ref(v___y_5406_);
lean_inc(v___y_5405_);
lean_inc_ref(v___y_5404_);
v___x_5417_ = lean_apply_10(v_mkInfoTree_5403_, v_trees_5416_, v___y_5404_, v___y_5405_, v___y_5406_, v___y_5407_, v___y_5408_, v___y_5409_, v___y_5410_, v___y_5402_, lean_box(0));
if (lean_obj_tag(v___x_5417_) == 0)
{
lean_object* v_a_5418_; lean_object* v___x_5420_; uint8_t v_isShared_5421_; uint8_t v_isSharedCheck_5456_; 
v_a_5418_ = lean_ctor_get(v___x_5417_, 0);
v_isSharedCheck_5456_ = !lean_is_exclusive(v___x_5417_);
if (v_isSharedCheck_5456_ == 0)
{
v___x_5420_ = v___x_5417_;
v_isShared_5421_ = v_isSharedCheck_5456_;
goto v_resetjp_5419_;
}
else
{
lean_inc(v_a_5418_);
lean_dec(v___x_5417_);
v___x_5420_ = lean_box(0);
v_isShared_5421_ = v_isSharedCheck_5456_;
goto v_resetjp_5419_;
}
v_resetjp_5419_:
{
lean_object* v___x_5422_; lean_object* v_infoState_5423_; lean_object* v_env_5424_; lean_object* v_nextMacroScope_5425_; lean_object* v_ngen_5426_; lean_object* v_auxDeclNGen_5427_; lean_object* v_traceState_5428_; lean_object* v_cache_5429_; lean_object* v_messages_5430_; lean_object* v_snapshotTasks_5431_; lean_object* v___x_5433_; uint8_t v_isShared_5434_; uint8_t v_isSharedCheck_5455_; 
v___x_5422_ = lean_st_ref_take(v___y_5402_);
v_infoState_5423_ = lean_ctor_get(v___x_5422_, 7);
v_env_5424_ = lean_ctor_get(v___x_5422_, 0);
v_nextMacroScope_5425_ = lean_ctor_get(v___x_5422_, 1);
v_ngen_5426_ = lean_ctor_get(v___x_5422_, 2);
v_auxDeclNGen_5427_ = lean_ctor_get(v___x_5422_, 3);
v_traceState_5428_ = lean_ctor_get(v___x_5422_, 4);
v_cache_5429_ = lean_ctor_get(v___x_5422_, 5);
v_messages_5430_ = lean_ctor_get(v___x_5422_, 6);
v_snapshotTasks_5431_ = lean_ctor_get(v___x_5422_, 8);
v_isSharedCheck_5455_ = !lean_is_exclusive(v___x_5422_);
if (v_isSharedCheck_5455_ == 0)
{
v___x_5433_ = v___x_5422_;
v_isShared_5434_ = v_isSharedCheck_5455_;
goto v_resetjp_5432_;
}
else
{
lean_inc(v_snapshotTasks_5431_);
lean_inc(v_infoState_5423_);
lean_inc(v_messages_5430_);
lean_inc(v_cache_5429_);
lean_inc(v_traceState_5428_);
lean_inc(v_auxDeclNGen_5427_);
lean_inc(v_ngen_5426_);
lean_inc(v_nextMacroScope_5425_);
lean_inc(v_env_5424_);
lean_dec(v___x_5422_);
v___x_5433_ = lean_box(0);
v_isShared_5434_ = v_isSharedCheck_5455_;
goto v_resetjp_5432_;
}
v_resetjp_5432_:
{
uint8_t v_enabled_5435_; lean_object* v_assignment_5436_; lean_object* v_lazyAssignment_5437_; lean_object* v___x_5439_; uint8_t v_isShared_5440_; uint8_t v_isSharedCheck_5453_; 
v_enabled_5435_ = lean_ctor_get_uint8(v_infoState_5423_, sizeof(void*)*3);
v_assignment_5436_ = lean_ctor_get(v_infoState_5423_, 0);
v_lazyAssignment_5437_ = lean_ctor_get(v_infoState_5423_, 1);
v_isSharedCheck_5453_ = !lean_is_exclusive(v_infoState_5423_);
if (v_isSharedCheck_5453_ == 0)
{
lean_object* v_unused_5454_; 
v_unused_5454_ = lean_ctor_get(v_infoState_5423_, 2);
lean_dec(v_unused_5454_);
v___x_5439_ = v_infoState_5423_;
v_isShared_5440_ = v_isSharedCheck_5453_;
goto v_resetjp_5438_;
}
else
{
lean_inc(v_lazyAssignment_5437_);
lean_inc(v_assignment_5436_);
lean_dec(v_infoState_5423_);
v___x_5439_ = lean_box(0);
v_isShared_5440_ = v_isSharedCheck_5453_;
goto v_resetjp_5438_;
}
v_resetjp_5438_:
{
lean_object* v___x_5441_; lean_object* v___x_5443_; 
v___x_5441_ = l_Lean_PersistentArray_push___redArg(v_a_5411_, v_a_5418_);
if (v_isShared_5440_ == 0)
{
lean_ctor_set(v___x_5439_, 2, v___x_5441_);
v___x_5443_ = v___x_5439_;
goto v_reusejp_5442_;
}
else
{
lean_object* v_reuseFailAlloc_5452_; 
v_reuseFailAlloc_5452_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5452_, 0, v_assignment_5436_);
lean_ctor_set(v_reuseFailAlloc_5452_, 1, v_lazyAssignment_5437_);
lean_ctor_set(v_reuseFailAlloc_5452_, 2, v___x_5441_);
lean_ctor_set_uint8(v_reuseFailAlloc_5452_, sizeof(void*)*3, v_enabled_5435_);
v___x_5443_ = v_reuseFailAlloc_5452_;
goto v_reusejp_5442_;
}
v_reusejp_5442_:
{
lean_object* v___x_5445_; 
if (v_isShared_5434_ == 0)
{
lean_ctor_set(v___x_5433_, 7, v___x_5443_);
v___x_5445_ = v___x_5433_;
goto v_reusejp_5444_;
}
else
{
lean_object* v_reuseFailAlloc_5451_; 
v_reuseFailAlloc_5451_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5451_, 0, v_env_5424_);
lean_ctor_set(v_reuseFailAlloc_5451_, 1, v_nextMacroScope_5425_);
lean_ctor_set(v_reuseFailAlloc_5451_, 2, v_ngen_5426_);
lean_ctor_set(v_reuseFailAlloc_5451_, 3, v_auxDeclNGen_5427_);
lean_ctor_set(v_reuseFailAlloc_5451_, 4, v_traceState_5428_);
lean_ctor_set(v_reuseFailAlloc_5451_, 5, v_cache_5429_);
lean_ctor_set(v_reuseFailAlloc_5451_, 6, v_messages_5430_);
lean_ctor_set(v_reuseFailAlloc_5451_, 7, v___x_5443_);
lean_ctor_set(v_reuseFailAlloc_5451_, 8, v_snapshotTasks_5431_);
v___x_5445_ = v_reuseFailAlloc_5451_;
goto v_reusejp_5444_;
}
v_reusejp_5444_:
{
lean_object* v___x_5446_; lean_object* v___x_5447_; lean_object* v___x_5449_; 
v___x_5446_ = lean_st_ref_put(v___y_5402_, v___x_5445_);
v___x_5447_ = lean_box(0);
if (v_isShared_5421_ == 0)
{
lean_ctor_set(v___x_5420_, 0, v___x_5447_);
v___x_5449_ = v___x_5420_;
goto v_reusejp_5448_;
}
else
{
lean_object* v_reuseFailAlloc_5450_; 
v_reuseFailAlloc_5450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5450_, 0, v___x_5447_);
v___x_5449_ = v_reuseFailAlloc_5450_;
goto v_reusejp_5448_;
}
v_reusejp_5448_:
{
return v___x_5449_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5457_; lean_object* v___x_5459_; uint8_t v_isShared_5460_; uint8_t v_isSharedCheck_5464_; 
lean_dec_ref(v_a_5411_);
v_a_5457_ = lean_ctor_get(v___x_5417_, 0);
v_isSharedCheck_5464_ = !lean_is_exclusive(v___x_5417_);
if (v_isSharedCheck_5464_ == 0)
{
v___x_5459_ = v___x_5417_;
v_isShared_5460_ = v_isSharedCheck_5464_;
goto v_resetjp_5458_;
}
else
{
lean_inc(v_a_5457_);
lean_dec(v___x_5417_);
v___x_5459_ = lean_box(0);
v_isShared_5460_ = v_isSharedCheck_5464_;
goto v_resetjp_5458_;
}
v_resetjp_5458_:
{
lean_object* v___x_5462_; 
if (v_isShared_5460_ == 0)
{
v___x_5462_ = v___x_5459_;
goto v_reusejp_5461_;
}
else
{
lean_object* v_reuseFailAlloc_5463_; 
v_reuseFailAlloc_5463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5463_, 0, v_a_5457_);
v___x_5462_ = v_reuseFailAlloc_5463_;
goto v_reusejp_5461_;
}
v_reusejp_5461_:
{
return v___x_5462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0___boxed(lean_object* v___y_5465_, lean_object* v_mkInfoTree_5466_, lean_object* v___y_5467_, lean_object* v___y_5468_, lean_object* v___y_5469_, lean_object* v___y_5470_, lean_object* v___y_5471_, lean_object* v___y_5472_, lean_object* v___y_5473_, lean_object* v_a_5474_, lean_object* v_a_x3f_5475_, lean_object* v___y_5476_){
_start:
{
lean_object* v_res_5477_; 
v_res_5477_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5465_, v_mkInfoTree_5466_, v___y_5467_, v___y_5468_, v___y_5469_, v___y_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v_a_5474_, v_a_x3f_5475_);
lean_dec(v_a_x3f_5475_);
lean_dec_ref(v___y_5473_);
lean_dec(v___y_5472_);
lean_dec_ref(v___y_5471_);
lean_dec(v___y_5470_);
lean_dec_ref(v___y_5469_);
lean_dec(v___y_5468_);
lean_dec_ref(v___y_5467_);
lean_dec(v___y_5465_);
return v_res_5477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(lean_object* v_x_5478_, lean_object* v_mkInfoTree_5479_, lean_object* v___y_5480_, lean_object* v___y_5481_, lean_object* v___y_5482_, lean_object* v___y_5483_, lean_object* v___y_5484_, lean_object* v___y_5485_, lean_object* v___y_5486_, lean_object* v___y_5487_){
_start:
{
lean_object* v___x_5489_; lean_object* v_infoState_5490_; uint8_t v_enabled_5491_; 
v___x_5489_ = lean_st_ref_get(v___y_5487_);
v_infoState_5490_ = lean_ctor_get(v___x_5489_, 7);
lean_inc_ref(v_infoState_5490_);
lean_dec(v___x_5489_);
v_enabled_5491_ = lean_ctor_get_uint8(v_infoState_5490_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5490_);
if (v_enabled_5491_ == 0)
{
lean_object* v___x_5492_; 
lean_dec_ref(v_mkInfoTree_5479_);
lean_inc(v___y_5487_);
lean_inc_ref(v___y_5486_);
lean_inc(v___y_5485_);
lean_inc_ref(v___y_5484_);
lean_inc(v___y_5483_);
lean_inc_ref(v___y_5482_);
lean_inc(v___y_5481_);
lean_inc_ref(v___y_5480_);
v___x_5492_ = lean_apply_9(v_x_5478_, v___y_5480_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_, v___y_5487_, lean_box(0));
return v___x_5492_;
}
else
{
lean_object* v___x_5493_; lean_object* v_a_5494_; lean_object* v_r_5495_; 
v___x_5493_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_5487_);
v_a_5494_ = lean_ctor_get(v___x_5493_, 0);
lean_inc(v_a_5494_);
lean_dec_ref(v___x_5493_);
lean_inc(v___y_5487_);
lean_inc_ref(v___y_5486_);
lean_inc(v___y_5485_);
lean_inc_ref(v___y_5484_);
lean_inc(v___y_5483_);
lean_inc_ref(v___y_5482_);
lean_inc(v___y_5481_);
lean_inc_ref(v___y_5480_);
v_r_5495_ = lean_apply_9(v_x_5478_, v___y_5480_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_, v___y_5487_, lean_box(0));
if (lean_obj_tag(v_r_5495_) == 0)
{
lean_object* v_a_5496_; lean_object* v___x_5498_; uint8_t v_isShared_5499_; uint8_t v_isSharedCheck_5520_; 
v_a_5496_ = lean_ctor_get(v_r_5495_, 0);
v_isSharedCheck_5520_ = !lean_is_exclusive(v_r_5495_);
if (v_isSharedCheck_5520_ == 0)
{
v___x_5498_ = v_r_5495_;
v_isShared_5499_ = v_isSharedCheck_5520_;
goto v_resetjp_5497_;
}
else
{
lean_inc(v_a_5496_);
lean_dec(v_r_5495_);
v___x_5498_ = lean_box(0);
v_isShared_5499_ = v_isSharedCheck_5520_;
goto v_resetjp_5497_;
}
v_resetjp_5497_:
{
lean_object* v___x_5501_; 
lean_inc(v_a_5496_);
if (v_isShared_5499_ == 0)
{
lean_ctor_set_tag(v___x_5498_, 1);
v___x_5501_ = v___x_5498_;
goto v_reusejp_5500_;
}
else
{
lean_object* v_reuseFailAlloc_5519_; 
v_reuseFailAlloc_5519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5519_, 0, v_a_5496_);
v___x_5501_ = v_reuseFailAlloc_5519_;
goto v_reusejp_5500_;
}
v_reusejp_5500_:
{
lean_object* v___x_5502_; 
v___x_5502_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5487_, v_mkInfoTree_5479_, v___y_5480_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_, v_a_5494_, v___x_5501_);
lean_dec_ref(v___x_5501_);
if (lean_obj_tag(v___x_5502_) == 0)
{
lean_object* v___x_5504_; uint8_t v_isShared_5505_; uint8_t v_isSharedCheck_5509_; 
v_isSharedCheck_5509_ = !lean_is_exclusive(v___x_5502_);
if (v_isSharedCheck_5509_ == 0)
{
lean_object* v_unused_5510_; 
v_unused_5510_ = lean_ctor_get(v___x_5502_, 0);
lean_dec(v_unused_5510_);
v___x_5504_ = v___x_5502_;
v_isShared_5505_ = v_isSharedCheck_5509_;
goto v_resetjp_5503_;
}
else
{
lean_dec(v___x_5502_);
v___x_5504_ = lean_box(0);
v_isShared_5505_ = v_isSharedCheck_5509_;
goto v_resetjp_5503_;
}
v_resetjp_5503_:
{
lean_object* v___x_5507_; 
if (v_isShared_5505_ == 0)
{
lean_ctor_set(v___x_5504_, 0, v_a_5496_);
v___x_5507_ = v___x_5504_;
goto v_reusejp_5506_;
}
else
{
lean_object* v_reuseFailAlloc_5508_; 
v_reuseFailAlloc_5508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5508_, 0, v_a_5496_);
v___x_5507_ = v_reuseFailAlloc_5508_;
goto v_reusejp_5506_;
}
v_reusejp_5506_:
{
return v___x_5507_;
}
}
}
else
{
lean_object* v_a_5511_; lean_object* v___x_5513_; uint8_t v_isShared_5514_; uint8_t v_isSharedCheck_5518_; 
lean_dec(v_a_5496_);
v_a_5511_ = lean_ctor_get(v___x_5502_, 0);
v_isSharedCheck_5518_ = !lean_is_exclusive(v___x_5502_);
if (v_isSharedCheck_5518_ == 0)
{
v___x_5513_ = v___x_5502_;
v_isShared_5514_ = v_isSharedCheck_5518_;
goto v_resetjp_5512_;
}
else
{
lean_inc(v_a_5511_);
lean_dec(v___x_5502_);
v___x_5513_ = lean_box(0);
v_isShared_5514_ = v_isSharedCheck_5518_;
goto v_resetjp_5512_;
}
v_resetjp_5512_:
{
lean_object* v___x_5516_; 
if (v_isShared_5514_ == 0)
{
v___x_5516_ = v___x_5513_;
goto v_reusejp_5515_;
}
else
{
lean_object* v_reuseFailAlloc_5517_; 
v_reuseFailAlloc_5517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5517_, 0, v_a_5511_);
v___x_5516_ = v_reuseFailAlloc_5517_;
goto v_reusejp_5515_;
}
v_reusejp_5515_:
{
return v___x_5516_;
}
}
}
}
}
}
else
{
lean_object* v_a_5521_; lean_object* v___x_5522_; lean_object* v___x_5523_; 
v_a_5521_ = lean_ctor_get(v_r_5495_, 0);
lean_inc(v_a_5521_);
lean_dec_ref_known(v_r_5495_, 1);
v___x_5522_ = lean_box(0);
v___x_5523_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5487_, v_mkInfoTree_5479_, v___y_5480_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_, v_a_5494_, v___x_5522_);
if (lean_obj_tag(v___x_5523_) == 0)
{
lean_object* v___x_5525_; uint8_t v_isShared_5526_; uint8_t v_isSharedCheck_5530_; 
v_isSharedCheck_5530_ = !lean_is_exclusive(v___x_5523_);
if (v_isSharedCheck_5530_ == 0)
{
lean_object* v_unused_5531_; 
v_unused_5531_ = lean_ctor_get(v___x_5523_, 0);
lean_dec(v_unused_5531_);
v___x_5525_ = v___x_5523_;
v_isShared_5526_ = v_isSharedCheck_5530_;
goto v_resetjp_5524_;
}
else
{
lean_dec(v___x_5523_);
v___x_5525_ = lean_box(0);
v_isShared_5526_ = v_isSharedCheck_5530_;
goto v_resetjp_5524_;
}
v_resetjp_5524_:
{
lean_object* v___x_5528_; 
if (v_isShared_5526_ == 0)
{
lean_ctor_set_tag(v___x_5525_, 1);
lean_ctor_set(v___x_5525_, 0, v_a_5521_);
v___x_5528_ = v___x_5525_;
goto v_reusejp_5527_;
}
else
{
lean_object* v_reuseFailAlloc_5529_; 
v_reuseFailAlloc_5529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5529_, 0, v_a_5521_);
v___x_5528_ = v_reuseFailAlloc_5529_;
goto v_reusejp_5527_;
}
v_reusejp_5527_:
{
return v___x_5528_;
}
}
}
else
{
lean_object* v_a_5532_; lean_object* v___x_5534_; uint8_t v_isShared_5535_; uint8_t v_isSharedCheck_5539_; 
lean_dec(v_a_5521_);
v_a_5532_ = lean_ctor_get(v___x_5523_, 0);
v_isSharedCheck_5539_ = !lean_is_exclusive(v___x_5523_);
if (v_isSharedCheck_5539_ == 0)
{
v___x_5534_ = v___x_5523_;
v_isShared_5535_ = v_isSharedCheck_5539_;
goto v_resetjp_5533_;
}
else
{
lean_inc(v_a_5532_);
lean_dec(v___x_5523_);
v___x_5534_ = lean_box(0);
v_isShared_5535_ = v_isSharedCheck_5539_;
goto v_resetjp_5533_;
}
v_resetjp_5533_:
{
lean_object* v___x_5537_; 
if (v_isShared_5535_ == 0)
{
v___x_5537_ = v___x_5534_;
goto v_reusejp_5536_;
}
else
{
lean_object* v_reuseFailAlloc_5538_; 
v_reuseFailAlloc_5538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5538_, 0, v_a_5532_);
v___x_5537_ = v_reuseFailAlloc_5538_;
goto v_reusejp_5536_;
}
v_reusejp_5536_:
{
return v___x_5537_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___boxed(lean_object* v_x_5540_, lean_object* v_mkInfoTree_5541_, lean_object* v___y_5542_, lean_object* v___y_5543_, lean_object* v___y_5544_, lean_object* v___y_5545_, lean_object* v___y_5546_, lean_object* v___y_5547_, lean_object* v___y_5548_, lean_object* v___y_5549_, lean_object* v___y_5550_){
_start:
{
lean_object* v_res_5551_; 
v_res_5551_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v_x_5540_, v_mkInfoTree_5541_, v___y_5542_, v___y_5543_, v___y_5544_, v___y_5545_, v___y_5546_, v___y_5547_, v___y_5548_, v___y_5549_);
lean_dec(v___y_5549_);
lean_dec_ref(v___y_5548_);
lean_dec(v___y_5547_);
lean_dec_ref(v___y_5546_);
lean_dec(v___y_5545_);
lean_dec_ref(v___y_5544_);
lean_dec(v___y_5543_);
lean_dec_ref(v___y_5542_);
return v_res_5551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1(lean_object* v_a_5552_, lean_object* v_trees_5553_, lean_object* v___y_5554_, lean_object* v___y_5555_, lean_object* v___y_5556_, lean_object* v___y_5557_, lean_object* v___y_5558_, lean_object* v___y_5559_, lean_object* v___y_5560_, lean_object* v___y_5561_){
_start:
{
lean_object* v___x_5563_; 
lean_inc(v___y_5561_);
lean_inc_ref(v___y_5560_);
lean_inc(v___y_5559_);
lean_inc_ref(v___y_5558_);
lean_inc(v___y_5557_);
lean_inc_ref(v___y_5556_);
lean_inc(v___y_5555_);
lean_inc_ref(v___y_5554_);
v___x_5563_ = lean_apply_9(v_a_5552_, v___y_5554_, v___y_5555_, v___y_5556_, v___y_5557_, v___y_5558_, v___y_5559_, v___y_5560_, v___y_5561_, lean_box(0));
if (lean_obj_tag(v___x_5563_) == 0)
{
lean_object* v_a_5564_; lean_object* v___x_5566_; uint8_t v_isShared_5567_; uint8_t v_isSharedCheck_5572_; 
v_a_5564_ = lean_ctor_get(v___x_5563_, 0);
v_isSharedCheck_5572_ = !lean_is_exclusive(v___x_5563_);
if (v_isSharedCheck_5572_ == 0)
{
v___x_5566_ = v___x_5563_;
v_isShared_5567_ = v_isSharedCheck_5572_;
goto v_resetjp_5565_;
}
else
{
lean_inc(v_a_5564_);
lean_dec(v___x_5563_);
v___x_5566_ = lean_box(0);
v_isShared_5567_ = v_isSharedCheck_5572_;
goto v_resetjp_5565_;
}
v_resetjp_5565_:
{
lean_object* v___x_5568_; lean_object* v___x_5570_; 
v___x_5568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5568_, 0, v_a_5564_);
lean_ctor_set(v___x_5568_, 1, v_trees_5553_);
if (v_isShared_5567_ == 0)
{
lean_ctor_set(v___x_5566_, 0, v___x_5568_);
v___x_5570_ = v___x_5566_;
goto v_reusejp_5569_;
}
else
{
lean_object* v_reuseFailAlloc_5571_; 
v_reuseFailAlloc_5571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5571_, 0, v___x_5568_);
v___x_5570_ = v_reuseFailAlloc_5571_;
goto v_reusejp_5569_;
}
v_reusejp_5569_:
{
return v___x_5570_;
}
}
}
else
{
lean_object* v_a_5573_; lean_object* v___x_5575_; uint8_t v_isShared_5576_; uint8_t v_isSharedCheck_5580_; 
lean_dec_ref(v_trees_5553_);
v_a_5573_ = lean_ctor_get(v___x_5563_, 0);
v_isSharedCheck_5580_ = !lean_is_exclusive(v___x_5563_);
if (v_isSharedCheck_5580_ == 0)
{
v___x_5575_ = v___x_5563_;
v_isShared_5576_ = v_isSharedCheck_5580_;
goto v_resetjp_5574_;
}
else
{
lean_inc(v_a_5573_);
lean_dec(v___x_5563_);
v___x_5575_ = lean_box(0);
v_isShared_5576_ = v_isSharedCheck_5580_;
goto v_resetjp_5574_;
}
v_resetjp_5574_:
{
lean_object* v___x_5578_; 
if (v_isShared_5576_ == 0)
{
v___x_5578_ = v___x_5575_;
goto v_reusejp_5577_;
}
else
{
lean_object* v_reuseFailAlloc_5579_; 
v_reuseFailAlloc_5579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5579_, 0, v_a_5573_);
v___x_5578_ = v_reuseFailAlloc_5579_;
goto v_reusejp_5577_;
}
v_reusejp_5577_:
{
return v___x_5578_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1___boxed(lean_object* v_a_5581_, lean_object* v_trees_5582_, lean_object* v___y_5583_, lean_object* v___y_5584_, lean_object* v___y_5585_, lean_object* v___y_5586_, lean_object* v___y_5587_, lean_object* v___y_5588_, lean_object* v___y_5589_, lean_object* v___y_5590_, lean_object* v___y_5591_){
_start:
{
lean_object* v_res_5592_; 
v_res_5592_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1(v_a_5581_, v_trees_5582_, v___y_5583_, v___y_5584_, v___y_5585_, v___y_5586_, v___y_5587_, v___y_5588_, v___y_5589_, v___y_5590_);
lean_dec(v___y_5590_);
lean_dec_ref(v___y_5589_);
lean_dec(v___y_5588_);
lean_dec_ref(v___y_5587_);
lean_dec(v___y_5586_);
lean_dec_ref(v___y_5585_);
lean_dec(v___y_5584_);
lean_dec_ref(v___y_5583_);
return v_res_5592_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2(lean_object* v___x_5593_, lean_object* v_ref_5594_, lean_object* v_tactic_5595_, lean_object* v___y_5596_, lean_object* v___y_5597_, lean_object* v___y_5598_, lean_object* v___y_5599_, lean_object* v___y_5600_, lean_object* v___y_5601_, lean_object* v___y_5602_, lean_object* v___y_5603_){
_start:
{
lean_object* v___x_5605_; 
v___x_5605_ = l_Lean_Elab_Tactic_setGoals___redArg(v___x_5593_, v___y_5597_);
if (lean_obj_tag(v___x_5605_) == 0)
{
lean_object* v___x_5606_; 
lean_dec_ref_known(v___x_5605_, 1);
v___x_5606_ = l_Lean_Elab_WF_applyCleanWfTactic(v___y_5596_, v___y_5597_, v___y_5598_, v___y_5599_, v___y_5600_, v___y_5601_, v___y_5602_, v___y_5603_);
if (lean_obj_tag(v___x_5606_) == 0)
{
lean_object* v___x_5607_; 
lean_dec_ref_known(v___x_5606_, 1);
v___x_5607_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v_ref_5594_, v___y_5596_, v___y_5597_, v___y_5598_, v___y_5599_, v___y_5600_, v___y_5601_, v___y_5602_, v___y_5603_);
if (lean_obj_tag(v___x_5607_) == 0)
{
lean_object* v_a_5608_; lean_object* v___f_5609_; lean_object* v___x_5610_; lean_object* v___x_5611_; 
v_a_5608_ = lean_ctor_get(v___x_5607_, 0);
lean_inc(v_a_5608_);
lean_dec_ref_known(v___x_5607_, 1);
v___f_5609_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1___boxed), 11, 1);
lean_closure_set(v___f_5609_, 0, v_a_5608_);
v___x_5610_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_5610_, 0, v_tactic_5595_);
v___x_5611_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v___x_5610_, v___f_5609_, v___y_5596_, v___y_5597_, v___y_5598_, v___y_5599_, v___y_5600_, v___y_5601_, v___y_5602_, v___y_5603_);
return v___x_5611_;
}
else
{
lean_object* v_a_5612_; lean_object* v___x_5614_; uint8_t v_isShared_5615_; uint8_t v_isSharedCheck_5619_; 
lean_dec(v_tactic_5595_);
v_a_5612_ = lean_ctor_get(v___x_5607_, 0);
v_isSharedCheck_5619_ = !lean_is_exclusive(v___x_5607_);
if (v_isSharedCheck_5619_ == 0)
{
v___x_5614_ = v___x_5607_;
v_isShared_5615_ = v_isSharedCheck_5619_;
goto v_resetjp_5613_;
}
else
{
lean_inc(v_a_5612_);
lean_dec(v___x_5607_);
v___x_5614_ = lean_box(0);
v_isShared_5615_ = v_isSharedCheck_5619_;
goto v_resetjp_5613_;
}
v_resetjp_5613_:
{
lean_object* v___x_5617_; 
if (v_isShared_5615_ == 0)
{
v___x_5617_ = v___x_5614_;
goto v_reusejp_5616_;
}
else
{
lean_object* v_reuseFailAlloc_5618_; 
v_reuseFailAlloc_5618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5618_, 0, v_a_5612_);
v___x_5617_ = v_reuseFailAlloc_5618_;
goto v_reusejp_5616_;
}
v_reusejp_5616_:
{
return v___x_5617_;
}
}
}
}
else
{
lean_dec(v_tactic_5595_);
lean_dec(v_ref_5594_);
return v___x_5606_;
}
}
else
{
lean_dec(v_tactic_5595_);
lean_dec(v_ref_5594_);
return v___x_5605_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2___boxed(lean_object* v___x_5620_, lean_object* v_ref_5621_, lean_object* v_tactic_5622_, lean_object* v___y_5623_, lean_object* v___y_5624_, lean_object* v___y_5625_, lean_object* v___y_5626_, lean_object* v___y_5627_, lean_object* v___y_5628_, lean_object* v___y_5629_, lean_object* v___y_5630_, lean_object* v___y_5631_){
_start:
{
lean_object* v_res_5632_; 
v_res_5632_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2(v___x_5620_, v_ref_5621_, v_tactic_5622_, v___y_5623_, v___y_5624_, v___y_5625_, v___y_5626_, v___y_5627_, v___y_5628_, v___y_5629_, v___y_5630_);
lean_dec(v___y_5630_);
lean_dec_ref(v___y_5629_);
lean_dec(v___y_5628_);
lean_dec_ref(v___y_5627_);
lean_dec(v___y_5626_);
lean_dec_ref(v___y_5625_);
lean_dec(v___y_5624_);
lean_dec_ref(v___y_5623_);
return v_res_5632_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5633_; lean_object* v___x_5634_; 
v___x_5633_ = lean_box(1);
v___x_5634_ = l_Lean_MessageData_ofFormat(v___x_5633_);
return v___x_5634_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5638_; lean_object* v___x_5639_; 
v___x_5638_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__2));
v___x_5639_ = l_Lean_MessageData_ofFormat(v___x_5638_);
return v___x_5639_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3(lean_object* v_x_5640_, lean_object* v_x_5641_){
_start:
{
if (lean_obj_tag(v_x_5641_) == 0)
{
return v_x_5640_;
}
else
{
lean_object* v_head_5642_; lean_object* v_tail_5643_; lean_object* v___x_5645_; uint8_t v_isShared_5646_; uint8_t v_isSharedCheck_5665_; 
v_head_5642_ = lean_ctor_get(v_x_5641_, 0);
v_tail_5643_ = lean_ctor_get(v_x_5641_, 1);
v_isSharedCheck_5665_ = !lean_is_exclusive(v_x_5641_);
if (v_isSharedCheck_5665_ == 0)
{
v___x_5645_ = v_x_5641_;
v_isShared_5646_ = v_isSharedCheck_5665_;
goto v_resetjp_5644_;
}
else
{
lean_inc(v_tail_5643_);
lean_inc(v_head_5642_);
lean_dec(v_x_5641_);
v___x_5645_ = lean_box(0);
v_isShared_5646_ = v_isSharedCheck_5665_;
goto v_resetjp_5644_;
}
v_resetjp_5644_:
{
lean_object* v_before_5647_; lean_object* v___x_5649_; uint8_t v_isShared_5650_; uint8_t v_isSharedCheck_5663_; 
v_before_5647_ = lean_ctor_get(v_head_5642_, 0);
v_isSharedCheck_5663_ = !lean_is_exclusive(v_head_5642_);
if (v_isSharedCheck_5663_ == 0)
{
lean_object* v_unused_5664_; 
v_unused_5664_ = lean_ctor_get(v_head_5642_, 1);
lean_dec(v_unused_5664_);
v___x_5649_ = v_head_5642_;
v_isShared_5650_ = v_isSharedCheck_5663_;
goto v_resetjp_5648_;
}
else
{
lean_inc(v_before_5647_);
lean_dec(v_head_5642_);
v___x_5649_ = lean_box(0);
v_isShared_5650_ = v_isSharedCheck_5663_;
goto v_resetjp_5648_;
}
v_resetjp_5648_:
{
lean_object* v___x_5651_; lean_object* v___x_5653_; 
v___x_5651_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_5650_ == 0)
{
lean_ctor_set_tag(v___x_5649_, 7);
lean_ctor_set(v___x_5649_, 1, v___x_5651_);
lean_ctor_set(v___x_5649_, 0, v_x_5640_);
v___x_5653_ = v___x_5649_;
goto v_reusejp_5652_;
}
else
{
lean_object* v_reuseFailAlloc_5662_; 
v_reuseFailAlloc_5662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5662_, 0, v_x_5640_);
lean_ctor_set(v_reuseFailAlloc_5662_, 1, v___x_5651_);
v___x_5653_ = v_reuseFailAlloc_5662_;
goto v_reusejp_5652_;
}
v_reusejp_5652_:
{
lean_object* v___x_5654_; lean_object* v___x_5656_; 
v___x_5654_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3);
if (v_isShared_5646_ == 0)
{
lean_ctor_set_tag(v___x_5645_, 7);
lean_ctor_set(v___x_5645_, 1, v___x_5654_);
lean_ctor_set(v___x_5645_, 0, v___x_5653_);
v___x_5656_ = v___x_5645_;
goto v_reusejp_5655_;
}
else
{
lean_object* v_reuseFailAlloc_5661_; 
v_reuseFailAlloc_5661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5661_, 0, v___x_5653_);
lean_ctor_set(v_reuseFailAlloc_5661_, 1, v___x_5654_);
v___x_5656_ = v_reuseFailAlloc_5661_;
goto v_reusejp_5655_;
}
v_reusejp_5655_:
{
lean_object* v___x_5657_; lean_object* v___x_5658_; lean_object* v___x_5659_; 
v___x_5657_ = l_Lean_MessageData_ofSyntax(v_before_5647_);
v___x_5658_ = l_Lean_indentD(v___x_5657_);
v___x_5659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5659_, 0, v___x_5656_);
lean_ctor_set(v___x_5659_, 1, v___x_5658_);
v_x_5640_ = v___x_5659_;
v_x_5641_ = v_tail_5643_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_5669_; lean_object* v___x_5670_; 
v___x_5669_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__1));
v___x_5670_ = l_Lean_MessageData_ofFormat(v___x_5669_);
return v___x_5670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(lean_object* v_msgData_5671_, lean_object* v_macroStack_5672_, lean_object* v___y_5673_){
_start:
{
lean_object* v_options_5675_; lean_object* v___x_5676_; uint8_t v___x_5677_; 
v_options_5675_ = lean_ctor_get(v___y_5673_, 2);
v___x_5676_ = l_Lean_Elab_pp_macroStack;
v___x_5677_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4(v_options_5675_, v___x_5676_);
if (v___x_5677_ == 0)
{
lean_object* v___x_5678_; 
lean_dec(v_macroStack_5672_);
v___x_5678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5678_, 0, v_msgData_5671_);
return v___x_5678_;
}
else
{
if (lean_obj_tag(v_macroStack_5672_) == 0)
{
lean_object* v___x_5679_; 
v___x_5679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5679_, 0, v_msgData_5671_);
return v___x_5679_;
}
else
{
lean_object* v_head_5680_; lean_object* v_after_5681_; lean_object* v___x_5683_; uint8_t v_isShared_5684_; uint8_t v_isSharedCheck_5696_; 
v_head_5680_ = lean_ctor_get(v_macroStack_5672_, 0);
lean_inc(v_head_5680_);
v_after_5681_ = lean_ctor_get(v_head_5680_, 1);
v_isSharedCheck_5696_ = !lean_is_exclusive(v_head_5680_);
if (v_isSharedCheck_5696_ == 0)
{
lean_object* v_unused_5697_; 
v_unused_5697_ = lean_ctor_get(v_head_5680_, 0);
lean_dec(v_unused_5697_);
v___x_5683_ = v_head_5680_;
v_isShared_5684_ = v_isSharedCheck_5696_;
goto v_resetjp_5682_;
}
else
{
lean_inc(v_after_5681_);
lean_dec(v_head_5680_);
v___x_5683_ = lean_box(0);
v_isShared_5684_ = v_isSharedCheck_5696_;
goto v_resetjp_5682_;
}
v_resetjp_5682_:
{
lean_object* v___x_5685_; lean_object* v___x_5687_; 
v___x_5685_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_5684_ == 0)
{
lean_ctor_set_tag(v___x_5683_, 7);
lean_ctor_set(v___x_5683_, 1, v___x_5685_);
lean_ctor_set(v___x_5683_, 0, v_msgData_5671_);
v___x_5687_ = v___x_5683_;
goto v_reusejp_5686_;
}
else
{
lean_object* v_reuseFailAlloc_5695_; 
v_reuseFailAlloc_5695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5695_, 0, v_msgData_5671_);
lean_ctor_set(v_reuseFailAlloc_5695_, 1, v___x_5685_);
v___x_5687_ = v_reuseFailAlloc_5695_;
goto v_reusejp_5686_;
}
v_reusejp_5686_:
{
lean_object* v___x_5688_; lean_object* v___x_5689_; lean_object* v___x_5690_; lean_object* v___x_5691_; lean_object* v_msgData_5692_; lean_object* v___x_5693_; lean_object* v___x_5694_; 
v___x_5688_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2);
v___x_5689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5689_, 0, v___x_5687_);
lean_ctor_set(v___x_5689_, 1, v___x_5688_);
v___x_5690_ = l_Lean_MessageData_ofSyntax(v_after_5681_);
v___x_5691_ = l_Lean_indentD(v___x_5690_);
v_msgData_5692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_5692_, 0, v___x_5689_);
lean_ctor_set(v_msgData_5692_, 1, v___x_5691_);
v___x_5693_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3(v_msgData_5692_, v_macroStack_5672_);
v___x_5694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5694_, 0, v___x_5693_);
return v___x_5694_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_5698_, lean_object* v_macroStack_5699_, lean_object* v___y_5700_, lean_object* v___y_5701_){
_start:
{
lean_object* v_res_5702_; 
v_res_5702_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_msgData_5698_, v_macroStack_5699_, v___y_5700_);
lean_dec_ref(v___y_5700_);
return v_res_5702_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(lean_object* v_msg_5703_, lean_object* v___y_5704_, lean_object* v___y_5705_, lean_object* v___y_5706_, lean_object* v___y_5707_, lean_object* v___y_5708_, lean_object* v___y_5709_){
_start:
{
lean_object* v_ref_5711_; lean_object* v___x_5712_; lean_object* v_a_5713_; lean_object* v_macroStack_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; lean_object* v_a_5717_; lean_object* v___x_5719_; uint8_t v_isShared_5720_; uint8_t v_isSharedCheck_5725_; 
v_ref_5711_ = lean_ctor_get(v___y_5708_, 5);
v___x_5712_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_5703_, v___y_5706_, v___y_5707_, v___y_5708_, v___y_5709_);
v_a_5713_ = lean_ctor_get(v___x_5712_, 0);
lean_inc(v_a_5713_);
lean_dec_ref(v___x_5712_);
v_macroStack_5714_ = lean_ctor_get(v___y_5704_, 1);
v___x_5715_ = l_Lean_Elab_getBetterRef(v_ref_5711_, v_macroStack_5714_);
lean_inc(v_macroStack_5714_);
v___x_5716_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_a_5713_, v_macroStack_5714_, v___y_5708_);
v_a_5717_ = lean_ctor_get(v___x_5716_, 0);
v_isSharedCheck_5725_ = !lean_is_exclusive(v___x_5716_);
if (v_isSharedCheck_5725_ == 0)
{
v___x_5719_ = v___x_5716_;
v_isShared_5720_ = v_isSharedCheck_5725_;
goto v_resetjp_5718_;
}
else
{
lean_inc(v_a_5717_);
lean_dec(v___x_5716_);
v___x_5719_ = lean_box(0);
v_isShared_5720_ = v_isSharedCheck_5725_;
goto v_resetjp_5718_;
}
v_resetjp_5718_:
{
lean_object* v___x_5721_; lean_object* v___x_5723_; 
v___x_5721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5721_, 0, v___x_5715_);
lean_ctor_set(v___x_5721_, 1, v_a_5717_);
if (v_isShared_5720_ == 0)
{
lean_ctor_set_tag(v___x_5719_, 1);
lean_ctor_set(v___x_5719_, 0, v___x_5721_);
v___x_5723_ = v___x_5719_;
goto v_reusejp_5722_;
}
else
{
lean_object* v_reuseFailAlloc_5724_; 
v_reuseFailAlloc_5724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5724_, 0, v___x_5721_);
v___x_5723_ = v_reuseFailAlloc_5724_;
goto v_reusejp_5722_;
}
v_reusejp_5722_:
{
return v___x_5723_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg___boxed(lean_object* v_msg_5726_, lean_object* v___y_5727_, lean_object* v___y_5728_, lean_object* v___y_5729_, lean_object* v___y_5730_, lean_object* v___y_5731_, lean_object* v___y_5732_, lean_object* v___y_5733_){
_start:
{
lean_object* v_res_5734_; 
v_res_5734_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v_msg_5726_, v___y_5727_, v___y_5728_, v___y_5729_, v___y_5730_, v___y_5731_, v___y_5732_);
lean_dec(v___y_5732_);
lean_dec_ref(v___y_5731_);
lean_dec(v___y_5730_);
lean_dec_ref(v___y_5729_);
lean_dec(v___y_5728_);
lean_dec_ref(v___y_5727_);
return v_res_5734_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1(void){
_start:
{
lean_object* v___x_5736_; lean_object* v___x_5737_; 
v___x_5736_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__0));
v___x_5737_ = l_Lean_stringToMessageData(v___x_5736_);
return v___x_5737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(lean_object* v_as_5738_, size_t v_sz_5739_, size_t v_i_5740_, lean_object* v_b_5741_, lean_object* v___y_5742_, lean_object* v___y_5743_, lean_object* v___y_5744_, lean_object* v___y_5745_, lean_object* v___y_5746_, lean_object* v___y_5747_){
_start:
{
lean_object* v_a_5750_; uint8_t v___x_5754_; 
v___x_5754_ = lean_usize_dec_lt(v_i_5740_, v_sz_5739_);
if (v___x_5754_ == 0)
{
lean_object* v___x_5755_; 
v___x_5755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5755_, 0, v_b_5741_);
return v___x_5755_;
}
else
{
lean_object* v_a_5756_; lean_object* v___x_5757_; 
v_a_5756_ = lean_array_uget_borrowed(v_as_5738_, v_i_5740_);
lean_inc(v_a_5756_);
v___x_5757_ = l_Lean_MVarId_getType(v_a_5756_, v___y_5744_, v___y_5745_, v___y_5746_, v___y_5747_);
if (lean_obj_tag(v___x_5757_) == 0)
{
lean_object* v_a_5758_; lean_object* v___x_5759_; 
v_a_5758_ = lean_ctor_get(v___x_5757_, 0);
lean_inc(v_a_5758_);
lean_dec_ref_known(v___x_5757_, 1);
lean_inc(v_a_5756_);
v___x_5759_ = l_Lean_MVarId_getType(v_a_5756_, v___y_5744_, v___y_5745_, v___y_5746_, v___y_5747_);
if (lean_obj_tag(v___x_5759_) == 0)
{
lean_object* v_a_5760_; lean_object* v___x_5761_; lean_object* v___x_5762_; 
v_a_5760_ = lean_ctor_get(v___x_5759_, 0);
lean_inc(v_a_5760_);
lean_dec_ref_known(v___x_5759_, 1);
v___x_5761_ = lean_box(0);
v___x_5762_ = l_Lean_getRecAppSyntax_x3f(v_a_5760_);
lean_dec(v_a_5760_);
if (lean_obj_tag(v___x_5762_) == 1)
{
lean_object* v_val_5763_; lean_object* v___x_5764_; lean_object* v___x_5765_; 
v_val_5763_ = lean_ctor_get(v___x_5762_, 0);
lean_inc(v_val_5763_);
lean_dec_ref_known(v___x_5762_, 1);
v___x_5764_ = l_Lean_Expr_mdataExpr_x21(v_a_5758_);
lean_dec(v_a_5758_);
lean_inc(v_a_5756_);
v___x_5765_ = l_Lean_MVarId_setType___redArg(v_a_5756_, v___x_5764_, v___y_5745_);
if (lean_obj_tag(v___x_5765_) == 0)
{
lean_object* v_fileName_5766_; lean_object* v_fileMap_5767_; lean_object* v_options_5768_; lean_object* v_currRecDepth_5769_; lean_object* v_maxRecDepth_5770_; lean_object* v_ref_5771_; lean_object* v_currNamespace_5772_; lean_object* v_openDecls_5773_; lean_object* v_initHeartbeats_5774_; lean_object* v_maxHeartbeats_5775_; lean_object* v_quotContext_5776_; lean_object* v_currMacroScope_5777_; uint8_t v_diag_5778_; lean_object* v_cancelTk_x3f_5779_; uint8_t v_suppressElabErrors_5780_; lean_object* v_inheritedTraceOptions_5781_; lean_object* v_ref_5782_; lean_object* v___x_5783_; lean_object* v___x_5784_; 
lean_dec_ref_known(v___x_5765_, 1);
v_fileName_5766_ = lean_ctor_get(v___y_5746_, 0);
v_fileMap_5767_ = lean_ctor_get(v___y_5746_, 1);
v_options_5768_ = lean_ctor_get(v___y_5746_, 2);
v_currRecDepth_5769_ = lean_ctor_get(v___y_5746_, 3);
v_maxRecDepth_5770_ = lean_ctor_get(v___y_5746_, 4);
v_ref_5771_ = lean_ctor_get(v___y_5746_, 5);
v_currNamespace_5772_ = lean_ctor_get(v___y_5746_, 6);
v_openDecls_5773_ = lean_ctor_get(v___y_5746_, 7);
v_initHeartbeats_5774_ = lean_ctor_get(v___y_5746_, 8);
v_maxHeartbeats_5775_ = lean_ctor_get(v___y_5746_, 9);
v_quotContext_5776_ = lean_ctor_get(v___y_5746_, 10);
v_currMacroScope_5777_ = lean_ctor_get(v___y_5746_, 11);
v_diag_5778_ = lean_ctor_get_uint8(v___y_5746_, sizeof(void*)*14);
v_cancelTk_x3f_5779_ = lean_ctor_get(v___y_5746_, 12);
v_suppressElabErrors_5780_ = lean_ctor_get_uint8(v___y_5746_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5781_ = lean_ctor_get(v___y_5746_, 13);
v_ref_5782_ = l_Lean_replaceRef(v_val_5763_, v_ref_5771_);
lean_dec(v_val_5763_);
lean_inc_ref(v_inheritedTraceOptions_5781_);
lean_inc(v_cancelTk_x3f_5779_);
lean_inc(v_currMacroScope_5777_);
lean_inc(v_quotContext_5776_);
lean_inc(v_maxHeartbeats_5775_);
lean_inc(v_initHeartbeats_5774_);
lean_inc(v_openDecls_5773_);
lean_inc(v_currNamespace_5772_);
lean_inc(v_maxRecDepth_5770_);
lean_inc(v_currRecDepth_5769_);
lean_inc_ref(v_options_5768_);
lean_inc_ref(v_fileMap_5767_);
lean_inc_ref(v_fileName_5766_);
v___x_5783_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5783_, 0, v_fileName_5766_);
lean_ctor_set(v___x_5783_, 1, v_fileMap_5767_);
lean_ctor_set(v___x_5783_, 2, v_options_5768_);
lean_ctor_set(v___x_5783_, 3, v_currRecDepth_5769_);
lean_ctor_set(v___x_5783_, 4, v_maxRecDepth_5770_);
lean_ctor_set(v___x_5783_, 5, v_ref_5782_);
lean_ctor_set(v___x_5783_, 6, v_currNamespace_5772_);
lean_ctor_set(v___x_5783_, 7, v_openDecls_5773_);
lean_ctor_set(v___x_5783_, 8, v_initHeartbeats_5774_);
lean_ctor_set(v___x_5783_, 9, v_maxHeartbeats_5775_);
lean_ctor_set(v___x_5783_, 10, v_quotContext_5776_);
lean_ctor_set(v___x_5783_, 11, v_currMacroScope_5777_);
lean_ctor_set(v___x_5783_, 12, v_cancelTk_x3f_5779_);
lean_ctor_set(v___x_5783_, 13, v_inheritedTraceOptions_5781_);
lean_ctor_set_uint8(v___x_5783_, sizeof(void*)*14, v_diag_5778_);
lean_ctor_set_uint8(v___x_5783_, sizeof(void*)*14 + 1, v_suppressElabErrors_5780_);
lean_inc(v_a_5756_);
v___x_5784_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(v_a_5756_, v___y_5742_, v___y_5743_, v___y_5744_, v___y_5745_, v___x_5783_, v___y_5747_);
lean_dec_ref_known(v___x_5783_, 14);
if (lean_obj_tag(v___x_5784_) == 0)
{
lean_dec_ref_known(v___x_5784_, 1);
v_a_5750_ = v___x_5761_;
goto v___jp_5749_;
}
else
{
return v___x_5784_;
}
}
else
{
lean_dec(v_val_5763_);
return v___x_5765_;
}
}
else
{
lean_object* v___x_5785_; lean_object* v___x_5786_; lean_object* v___x_5787_; lean_object* v___x_5788_; 
lean_dec(v___x_5762_);
v___x_5785_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1);
v___x_5786_ = l_Lean_indentExpr(v_a_5758_);
v___x_5787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5787_, 0, v___x_5785_);
lean_ctor_set(v___x_5787_, 1, v___x_5786_);
v___x_5788_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v___x_5787_, v___y_5742_, v___y_5743_, v___y_5744_, v___y_5745_, v___y_5746_, v___y_5747_);
if (lean_obj_tag(v___x_5788_) == 0)
{
lean_dec_ref_known(v___x_5788_, 1);
v_a_5750_ = v___x_5761_;
goto v___jp_5749_;
}
else
{
return v___x_5788_;
}
}
}
else
{
lean_object* v_a_5789_; lean_object* v___x_5791_; uint8_t v_isShared_5792_; uint8_t v_isSharedCheck_5796_; 
lean_dec(v_a_5758_);
v_a_5789_ = lean_ctor_get(v___x_5759_, 0);
v_isSharedCheck_5796_ = !lean_is_exclusive(v___x_5759_);
if (v_isSharedCheck_5796_ == 0)
{
v___x_5791_ = v___x_5759_;
v_isShared_5792_ = v_isSharedCheck_5796_;
goto v_resetjp_5790_;
}
else
{
lean_inc(v_a_5789_);
lean_dec(v___x_5759_);
v___x_5791_ = lean_box(0);
v_isShared_5792_ = v_isSharedCheck_5796_;
goto v_resetjp_5790_;
}
v_resetjp_5790_:
{
lean_object* v___x_5794_; 
if (v_isShared_5792_ == 0)
{
v___x_5794_ = v___x_5791_;
goto v_reusejp_5793_;
}
else
{
lean_object* v_reuseFailAlloc_5795_; 
v_reuseFailAlloc_5795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5795_, 0, v_a_5789_);
v___x_5794_ = v_reuseFailAlloc_5795_;
goto v_reusejp_5793_;
}
v_reusejp_5793_:
{
return v___x_5794_;
}
}
}
}
else
{
lean_object* v_a_5797_; lean_object* v___x_5799_; uint8_t v_isShared_5800_; uint8_t v_isSharedCheck_5804_; 
v_a_5797_ = lean_ctor_get(v___x_5757_, 0);
v_isSharedCheck_5804_ = !lean_is_exclusive(v___x_5757_);
if (v_isSharedCheck_5804_ == 0)
{
v___x_5799_ = v___x_5757_;
v_isShared_5800_ = v_isSharedCheck_5804_;
goto v_resetjp_5798_;
}
else
{
lean_inc(v_a_5797_);
lean_dec(v___x_5757_);
v___x_5799_ = lean_box(0);
v_isShared_5800_ = v_isSharedCheck_5804_;
goto v_resetjp_5798_;
}
v_resetjp_5798_:
{
lean_object* v___x_5802_; 
if (v_isShared_5800_ == 0)
{
v___x_5802_ = v___x_5799_;
goto v_reusejp_5801_;
}
else
{
lean_object* v_reuseFailAlloc_5803_; 
v_reuseFailAlloc_5803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5803_, 0, v_a_5797_);
v___x_5802_ = v_reuseFailAlloc_5803_;
goto v_reusejp_5801_;
}
v_reusejp_5801_:
{
return v___x_5802_;
}
}
}
}
v___jp_5749_:
{
size_t v___x_5751_; size_t v___x_5752_; 
v___x_5751_ = ((size_t)1ULL);
v___x_5752_ = lean_usize_add(v_i_5740_, v___x_5751_);
v_i_5740_ = v___x_5752_;
v_b_5741_ = v_a_5750_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___boxed(lean_object* v_as_5805_, lean_object* v_sz_5806_, lean_object* v_i_5807_, lean_object* v_b_5808_, lean_object* v___y_5809_, lean_object* v___y_5810_, lean_object* v___y_5811_, lean_object* v___y_5812_, lean_object* v___y_5813_, lean_object* v___y_5814_, lean_object* v___y_5815_){
_start:
{
size_t v_sz_boxed_5816_; size_t v_i_boxed_5817_; lean_object* v_res_5818_; 
v_sz_boxed_5816_ = lean_unbox_usize(v_sz_5806_);
lean_dec(v_sz_5806_);
v_i_boxed_5817_ = lean_unbox_usize(v_i_5807_);
lean_dec(v_i_5807_);
v_res_5818_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(v_as_5805_, v_sz_boxed_5816_, v_i_boxed_5817_, v_b_5808_, v___y_5809_, v___y_5810_, v___y_5811_, v___y_5812_, v___y_5813_, v___y_5814_);
lean_dec(v___y_5814_);
lean_dec_ref(v___y_5813_);
lean_dec(v___y_5812_);
lean_dec_ref(v___y_5811_);
lean_dec(v___y_5810_);
lean_dec_ref(v___y_5809_);
lean_dec_ref(v_as_5805_);
return v_res_5818_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(lean_object* v_as_5819_, size_t v_i_5820_, size_t v_stop_5821_, lean_object* v_b_5822_, lean_object* v___y_5823_, lean_object* v___y_5824_, lean_object* v___y_5825_, lean_object* v___y_5826_){
_start:
{
uint8_t v___x_5828_; 
v___x_5828_ = lean_usize_dec_eq(v_i_5820_, v_stop_5821_);
if (v___x_5828_ == 0)
{
lean_object* v___x_5829_; lean_object* v___x_5830_; 
v___x_5829_ = lean_array_uget_borrowed(v_as_5819_, v_i_5820_);
lean_inc(v___x_5829_);
v___x_5830_ = l_Lean_MVarId_getType(v___x_5829_, v___y_5823_, v___y_5824_, v___y_5825_, v___y_5826_);
if (lean_obj_tag(v___x_5830_) == 0)
{
lean_object* v_a_5831_; lean_object* v___x_5832_; lean_object* v___x_5833_; 
v_a_5831_ = lean_ctor_get(v___x_5830_, 0);
lean_inc(v_a_5831_);
lean_dec_ref_known(v___x_5830_, 1);
v___x_5832_ = l_Lean_Expr_mdataExpr_x21(v_a_5831_);
lean_dec(v_a_5831_);
lean_inc(v___x_5829_);
v___x_5833_ = l_Lean_MVarId_setType___redArg(v___x_5829_, v___x_5832_, v___y_5824_);
if (lean_obj_tag(v___x_5833_) == 0)
{
lean_object* v_a_5834_; size_t v___x_5835_; size_t v___x_5836_; 
v_a_5834_ = lean_ctor_get(v___x_5833_, 0);
lean_inc(v_a_5834_);
lean_dec_ref_known(v___x_5833_, 1);
v___x_5835_ = ((size_t)1ULL);
v___x_5836_ = lean_usize_add(v_i_5820_, v___x_5835_);
v_i_5820_ = v___x_5836_;
v_b_5822_ = v_a_5834_;
goto _start;
}
else
{
return v___x_5833_;
}
}
else
{
lean_object* v_a_5838_; lean_object* v___x_5840_; uint8_t v_isShared_5841_; uint8_t v_isSharedCheck_5845_; 
v_a_5838_ = lean_ctor_get(v___x_5830_, 0);
v_isSharedCheck_5845_ = !lean_is_exclusive(v___x_5830_);
if (v_isSharedCheck_5845_ == 0)
{
v___x_5840_ = v___x_5830_;
v_isShared_5841_ = v_isSharedCheck_5845_;
goto v_resetjp_5839_;
}
else
{
lean_inc(v_a_5838_);
lean_dec(v___x_5830_);
v___x_5840_ = lean_box(0);
v_isShared_5841_ = v_isSharedCheck_5845_;
goto v_resetjp_5839_;
}
v_resetjp_5839_:
{
lean_object* v___x_5843_; 
if (v_isShared_5841_ == 0)
{
v___x_5843_ = v___x_5840_;
goto v_reusejp_5842_;
}
else
{
lean_object* v_reuseFailAlloc_5844_; 
v_reuseFailAlloc_5844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5844_, 0, v_a_5838_);
v___x_5843_ = v_reuseFailAlloc_5844_;
goto v_reusejp_5842_;
}
v_reusejp_5842_:
{
return v___x_5843_;
}
}
}
}
else
{
lean_object* v___x_5846_; 
v___x_5846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5846_, 0, v_b_5822_);
return v___x_5846_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg___boxed(lean_object* v_as_5847_, lean_object* v_i_5848_, lean_object* v_stop_5849_, lean_object* v_b_5850_, lean_object* v___y_5851_, lean_object* v___y_5852_, lean_object* v___y_5853_, lean_object* v___y_5854_, lean_object* v___y_5855_){
_start:
{
size_t v_i_boxed_5856_; size_t v_stop_boxed_5857_; lean_object* v_res_5858_; 
v_i_boxed_5856_ = lean_unbox_usize(v_i_5848_);
lean_dec(v_i_5848_);
v_stop_boxed_5857_ = lean_unbox_usize(v_stop_5849_);
lean_dec(v_stop_5849_);
v_res_5858_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v_as_5847_, v_i_boxed_5856_, v_stop_boxed_5857_, v_b_5850_, v___y_5851_, v___y_5852_, v___y_5853_, v___y_5854_);
lean_dec(v___y_5854_);
lean_dec_ref(v___y_5853_);
lean_dec(v___y_5852_);
lean_dec_ref(v___y_5851_);
lean_dec_ref(v_as_5847_);
return v_res_5858_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3(lean_object* v___x_5859_, lean_object* v___x_5860_, lean_object* v___y_5861_, lean_object* v___y_5862_, lean_object* v___y_5863_, lean_object* v___y_5864_, lean_object* v___y_5865_, lean_object* v___y_5866_){
_start:
{
if (lean_obj_tag(v___x_5859_) == 0)
{
lean_object* v___x_5868_; size_t v_sz_5869_; size_t v___x_5870_; lean_object* v___x_5871_; 
v___x_5868_ = lean_box(0);
v_sz_5869_ = lean_array_size(v___x_5860_);
v___x_5870_ = ((size_t)0ULL);
v___x_5871_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(v___x_5860_, v_sz_5869_, v___x_5870_, v___x_5868_, v___y_5861_, v___y_5862_, v___y_5863_, v___y_5864_, v___y_5865_, v___y_5866_);
lean_dec_ref(v___x_5860_);
if (lean_obj_tag(v___x_5871_) == 0)
{
lean_object* v___x_5873_; uint8_t v_isShared_5874_; uint8_t v_isSharedCheck_5878_; 
v_isSharedCheck_5878_ = !lean_is_exclusive(v___x_5871_);
if (v_isSharedCheck_5878_ == 0)
{
lean_object* v_unused_5879_; 
v_unused_5879_ = lean_ctor_get(v___x_5871_, 0);
lean_dec(v_unused_5879_);
v___x_5873_ = v___x_5871_;
v_isShared_5874_ = v_isSharedCheck_5878_;
goto v_resetjp_5872_;
}
else
{
lean_dec(v___x_5871_);
v___x_5873_ = lean_box(0);
v_isShared_5874_ = v_isSharedCheck_5878_;
goto v_resetjp_5872_;
}
v_resetjp_5872_:
{
lean_object* v___x_5876_; 
if (v_isShared_5874_ == 0)
{
lean_ctor_set(v___x_5873_, 0, v___x_5868_);
v___x_5876_ = v___x_5873_;
goto v_reusejp_5875_;
}
else
{
lean_object* v_reuseFailAlloc_5877_; 
v_reuseFailAlloc_5877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5877_, 0, v___x_5868_);
v___x_5876_ = v_reuseFailAlloc_5877_;
goto v_reusejp_5875_;
}
v_reusejp_5875_:
{
return v___x_5876_;
}
}
}
else
{
return v___x_5871_;
}
}
else
{
lean_object* v_val_5880_; lean_object* v___x_5882_; uint8_t v_isShared_5883_; uint8_t v_isSharedCheck_5959_; 
v_val_5880_ = lean_ctor_get(v___x_5859_, 0);
v_isSharedCheck_5959_ = !lean_is_exclusive(v___x_5859_);
if (v_isSharedCheck_5959_ == 0)
{
v___x_5882_ = v___x_5859_;
v_isShared_5883_ = v_isSharedCheck_5959_;
goto v_resetjp_5881_;
}
else
{
lean_inc(v_val_5880_);
lean_dec(v___x_5859_);
v___x_5882_ = lean_box(0);
v_isShared_5883_ = v_isSharedCheck_5959_;
goto v_resetjp_5881_;
}
v_resetjp_5881_:
{
lean_object* v_ref_5884_; lean_object* v_tactic_5885_; lean_object* v_fileName_5886_; lean_object* v_fileMap_5887_; lean_object* v_options_5888_; lean_object* v_currRecDepth_5889_; lean_object* v_maxRecDepth_5890_; lean_object* v_ref_5891_; lean_object* v_currNamespace_5892_; lean_object* v_openDecls_5893_; lean_object* v_initHeartbeats_5894_; lean_object* v_maxHeartbeats_5895_; lean_object* v_quotContext_5896_; lean_object* v_currMacroScope_5897_; uint8_t v_diag_5898_; lean_object* v_cancelTk_x3f_5899_; uint8_t v_suppressElabErrors_5900_; lean_object* v_inheritedTraceOptions_5901_; lean_object* v___x_5902_; lean_object* v___x_5903_; lean_object* v_ref_5904_; lean_object* v___x_5905_; lean_object* v___y_5932_; lean_object* v___y_5949_; uint8_t v___x_5950_; 
v_ref_5884_ = lean_ctor_get(v_val_5880_, 0);
lean_inc(v_ref_5884_);
v_tactic_5885_ = lean_ctor_get(v_val_5880_, 1);
lean_inc(v_tactic_5885_);
lean_dec(v_val_5880_);
v_fileName_5886_ = lean_ctor_get(v___y_5865_, 0);
v_fileMap_5887_ = lean_ctor_get(v___y_5865_, 1);
v_options_5888_ = lean_ctor_get(v___y_5865_, 2);
v_currRecDepth_5889_ = lean_ctor_get(v___y_5865_, 3);
v_maxRecDepth_5890_ = lean_ctor_get(v___y_5865_, 4);
v_ref_5891_ = lean_ctor_get(v___y_5865_, 5);
v_currNamespace_5892_ = lean_ctor_get(v___y_5865_, 6);
v_openDecls_5893_ = lean_ctor_get(v___y_5865_, 7);
v_initHeartbeats_5894_ = lean_ctor_get(v___y_5865_, 8);
v_maxHeartbeats_5895_ = lean_ctor_get(v___y_5865_, 9);
v_quotContext_5896_ = lean_ctor_get(v___y_5865_, 10);
v_currMacroScope_5897_ = lean_ctor_get(v___y_5865_, 11);
v_diag_5898_ = lean_ctor_get_uint8(v___y_5865_, sizeof(void*)*14);
v_cancelTk_x3f_5899_ = lean_ctor_get(v___y_5865_, 12);
v_suppressElabErrors_5900_ = lean_ctor_get_uint8(v___y_5865_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5901_ = lean_ctor_get(v___y_5865_, 13);
v___x_5902_ = lean_unsigned_to_nat(0u);
v___x_5903_ = lean_array_get_size(v___x_5860_);
v_ref_5904_ = l_Lean_replaceRef(v_ref_5884_, v_ref_5891_);
lean_inc_ref(v_inheritedTraceOptions_5901_);
lean_inc(v_cancelTk_x3f_5899_);
lean_inc(v_currMacroScope_5897_);
lean_inc(v_quotContext_5896_);
lean_inc(v_maxHeartbeats_5895_);
lean_inc(v_initHeartbeats_5894_);
lean_inc(v_openDecls_5893_);
lean_inc(v_currNamespace_5892_);
lean_inc(v_maxRecDepth_5890_);
lean_inc(v_currRecDepth_5889_);
lean_inc_ref(v_options_5888_);
lean_inc_ref(v_fileMap_5887_);
lean_inc_ref(v_fileName_5886_);
v___x_5905_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5905_, 0, v_fileName_5886_);
lean_ctor_set(v___x_5905_, 1, v_fileMap_5887_);
lean_ctor_set(v___x_5905_, 2, v_options_5888_);
lean_ctor_set(v___x_5905_, 3, v_currRecDepth_5889_);
lean_ctor_set(v___x_5905_, 4, v_maxRecDepth_5890_);
lean_ctor_set(v___x_5905_, 5, v_ref_5904_);
lean_ctor_set(v___x_5905_, 6, v_currNamespace_5892_);
lean_ctor_set(v___x_5905_, 7, v_openDecls_5893_);
lean_ctor_set(v___x_5905_, 8, v_initHeartbeats_5894_);
lean_ctor_set(v___x_5905_, 9, v_maxHeartbeats_5895_);
lean_ctor_set(v___x_5905_, 10, v_quotContext_5896_);
lean_ctor_set(v___x_5905_, 11, v_currMacroScope_5897_);
lean_ctor_set(v___x_5905_, 12, v_cancelTk_x3f_5899_);
lean_ctor_set(v___x_5905_, 13, v_inheritedTraceOptions_5901_);
lean_ctor_set_uint8(v___x_5905_, sizeof(void*)*14, v_diag_5898_);
lean_ctor_set_uint8(v___x_5905_, sizeof(void*)*14 + 1, v_suppressElabErrors_5900_);
v___x_5950_ = lean_nat_dec_lt(v___x_5902_, v___x_5903_);
if (v___x_5950_ == 0)
{
goto v___jp_5933_;
}
else
{
lean_object* v___x_5951_; uint8_t v___x_5952_; 
v___x_5951_ = lean_box(0);
v___x_5952_ = lean_nat_dec_le(v___x_5903_, v___x_5903_);
if (v___x_5952_ == 0)
{
if (v___x_5950_ == 0)
{
goto v___jp_5933_;
}
else
{
size_t v___x_5953_; size_t v___x_5954_; lean_object* v___x_5955_; 
v___x_5953_ = ((size_t)0ULL);
v___x_5954_ = lean_usize_of_nat(v___x_5903_);
v___x_5955_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v___x_5860_, v___x_5953_, v___x_5954_, v___x_5951_, v___y_5863_, v___y_5864_, v___x_5905_, v___y_5866_);
v___y_5949_ = v___x_5955_;
goto v___jp_5948_;
}
}
else
{
size_t v___x_5956_; size_t v___x_5957_; lean_object* v___x_5958_; 
v___x_5956_ = ((size_t)0ULL);
v___x_5957_ = lean_usize_of_nat(v___x_5903_);
v___x_5958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v___x_5860_, v___x_5956_, v___x_5957_, v___x_5951_, v___y_5863_, v___y_5864_, v___x_5905_, v___y_5866_);
v___y_5949_ = v___x_5958_;
goto v___jp_5948_;
}
}
v___jp_5906_:
{
lean_object* v___x_5907_; lean_object* v___x_5908_; lean_object* v___x_5909_; lean_object* v___f_5910_; lean_object* v___x_5911_; 
v___x_5907_ = lean_box(0);
v___x_5908_ = lean_array_get(v___x_5907_, v___x_5860_, v___x_5902_);
v___x_5909_ = lean_array_to_list(v___x_5860_);
v___f_5910_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2___boxed), 12, 3);
lean_closure_set(v___f_5910_, 0, v___x_5909_);
lean_closure_set(v___f_5910_, 1, v_ref_5884_);
lean_closure_set(v___f_5910_, 2, v_tactic_5885_);
v___x_5911_ = l_Lean_Elab_Tactic_run(v___x_5908_, v___f_5910_, v___y_5861_, v___y_5862_, v___y_5863_, v___y_5864_, v___x_5905_, v___y_5866_);
if (lean_obj_tag(v___x_5911_) == 0)
{
lean_object* v_a_5912_; lean_object* v___x_5914_; uint8_t v_isShared_5915_; uint8_t v_isSharedCheck_5922_; 
v_a_5912_ = lean_ctor_get(v___x_5911_, 0);
v_isSharedCheck_5922_ = !lean_is_exclusive(v___x_5911_);
if (v_isSharedCheck_5922_ == 0)
{
v___x_5914_ = v___x_5911_;
v_isShared_5915_ = v_isSharedCheck_5922_;
goto v_resetjp_5913_;
}
else
{
lean_inc(v_a_5912_);
lean_dec(v___x_5911_);
v___x_5914_ = lean_box(0);
v_isShared_5915_ = v_isSharedCheck_5922_;
goto v_resetjp_5913_;
}
v_resetjp_5913_:
{
uint8_t v___x_5916_; 
v___x_5916_ = l_List_isEmpty___redArg(v_a_5912_);
if (v___x_5916_ == 0)
{
lean_object* v___x_5917_; 
lean_del_object(v___x_5914_);
v___x_5917_ = l_Lean_Elab_Term_reportUnsolvedGoals(v_a_5912_, v___y_5863_, v___y_5864_, v___x_5905_, v___y_5866_);
lean_dec_ref_known(v___x_5905_, 14);
return v___x_5917_;
}
else
{
lean_object* v___x_5918_; lean_object* v___x_5920_; 
lean_dec(v_a_5912_);
lean_dec_ref_known(v___x_5905_, 14);
v___x_5918_ = lean_box(0);
if (v_isShared_5915_ == 0)
{
lean_ctor_set(v___x_5914_, 0, v___x_5918_);
v___x_5920_ = v___x_5914_;
goto v_reusejp_5919_;
}
else
{
lean_object* v_reuseFailAlloc_5921_; 
v_reuseFailAlloc_5921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5921_, 0, v___x_5918_);
v___x_5920_ = v_reuseFailAlloc_5921_;
goto v_reusejp_5919_;
}
v_reusejp_5919_:
{
return v___x_5920_;
}
}
}
}
else
{
lean_object* v_a_5923_; lean_object* v___x_5925_; uint8_t v_isShared_5926_; uint8_t v_isSharedCheck_5930_; 
lean_dec_ref_known(v___x_5905_, 14);
v_a_5923_ = lean_ctor_get(v___x_5911_, 0);
v_isSharedCheck_5930_ = !lean_is_exclusive(v___x_5911_);
if (v_isSharedCheck_5930_ == 0)
{
v___x_5925_ = v___x_5911_;
v_isShared_5926_ = v_isSharedCheck_5930_;
goto v_resetjp_5924_;
}
else
{
lean_inc(v_a_5923_);
lean_dec(v___x_5911_);
v___x_5925_ = lean_box(0);
v_isShared_5926_ = v_isSharedCheck_5930_;
goto v_resetjp_5924_;
}
v_resetjp_5924_:
{
lean_object* v___x_5928_; 
if (v_isShared_5926_ == 0)
{
v___x_5928_ = v___x_5925_;
goto v_reusejp_5927_;
}
else
{
lean_object* v_reuseFailAlloc_5929_; 
v_reuseFailAlloc_5929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5929_, 0, v_a_5923_);
v___x_5928_ = v_reuseFailAlloc_5929_;
goto v_reusejp_5927_;
}
v_reusejp_5927_:
{
return v___x_5928_;
}
}
}
}
v___jp_5931_:
{
if (lean_obj_tag(v___y_5932_) == 0)
{
lean_dec_ref_known(v___y_5932_, 1);
goto v___jp_5906_;
}
else
{
lean_dec_ref_known(v___x_5905_, 14);
lean_dec(v_tactic_5885_);
lean_dec(v_ref_5884_);
lean_dec_ref(v___x_5860_);
return v___y_5932_;
}
}
v___jp_5933_:
{
uint8_t v___x_5934_; 
v___x_5934_ = lean_nat_dec_eq(v___x_5903_, v___x_5902_);
if (v___x_5934_ == 0)
{
uint8_t v___x_5935_; 
lean_del_object(v___x_5882_);
v___x_5935_ = lean_nat_dec_lt(v___x_5902_, v___x_5903_);
if (v___x_5935_ == 0)
{
goto v___jp_5906_;
}
else
{
lean_object* v___x_5936_; uint8_t v___x_5937_; 
v___x_5936_ = lean_box(0);
v___x_5937_ = lean_nat_dec_le(v___x_5903_, v___x_5903_);
if (v___x_5937_ == 0)
{
if (v___x_5935_ == 0)
{
goto v___jp_5906_;
}
else
{
size_t v___x_5938_; size_t v___x_5939_; lean_object* v___x_5940_; 
v___x_5938_ = ((size_t)0ULL);
v___x_5939_ = lean_usize_of_nat(v___x_5903_);
v___x_5940_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v___x_5860_, v___x_5938_, v___x_5939_, v___x_5936_, v___y_5861_, v___y_5862_, v___y_5863_, v___y_5864_, v___x_5905_, v___y_5866_);
v___y_5932_ = v___x_5940_;
goto v___jp_5931_;
}
}
else
{
size_t v___x_5941_; size_t v___x_5942_; lean_object* v___x_5943_; 
v___x_5941_ = ((size_t)0ULL);
v___x_5942_ = lean_usize_of_nat(v___x_5903_);
v___x_5943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v___x_5860_, v___x_5941_, v___x_5942_, v___x_5936_, v___y_5861_, v___y_5862_, v___y_5863_, v___y_5864_, v___x_5905_, v___y_5866_);
v___y_5932_ = v___x_5943_;
goto v___jp_5931_;
}
}
}
else
{
lean_object* v___x_5944_; lean_object* v___x_5946_; 
lean_dec_ref_known(v___x_5905_, 14);
lean_dec(v_tactic_5885_);
lean_dec(v_ref_5884_);
lean_dec_ref(v___x_5860_);
v___x_5944_ = lean_box(0);
if (v_isShared_5883_ == 0)
{
lean_ctor_set_tag(v___x_5882_, 0);
lean_ctor_set(v___x_5882_, 0, v___x_5944_);
v___x_5946_ = v___x_5882_;
goto v_reusejp_5945_;
}
else
{
lean_object* v_reuseFailAlloc_5947_; 
v_reuseFailAlloc_5947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5947_, 0, v___x_5944_);
v___x_5946_ = v_reuseFailAlloc_5947_;
goto v_reusejp_5945_;
}
v_reusejp_5945_:
{
return v___x_5946_;
}
}
}
v___jp_5948_:
{
if (lean_obj_tag(v___y_5949_) == 0)
{
lean_dec_ref_known(v___y_5949_, 1);
goto v___jp_5933_;
}
else
{
lean_dec_ref_known(v___x_5905_, 14);
lean_dec(v_tactic_5885_);
lean_dec(v_ref_5884_);
lean_del_object(v___x_5882_);
lean_dec_ref(v___x_5860_);
return v___y_5949_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3___boxed(lean_object* v___x_5960_, lean_object* v___x_5961_, lean_object* v___y_5962_, lean_object* v___y_5963_, lean_object* v___y_5964_, lean_object* v___y_5965_, lean_object* v___y_5966_, lean_object* v___y_5967_, lean_object* v___y_5968_){
_start:
{
lean_object* v_res_5969_; 
v_res_5969_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3(v___x_5960_, v___x_5961_, v___y_5962_, v___y_5963_, v___y_5964_, v___y_5965_, v___y_5966_, v___y_5967_);
lean_dec(v___y_5967_);
lean_dec_ref(v___y_5966_);
lean_dec(v___y_5965_);
lean_dec_ref(v___y_5964_);
lean_dec(v___y_5963_);
lean_dec_ref(v___y_5962_);
return v_res_5969_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0(lean_object* v_x_5970_){
_start:
{
uint8_t v___x_5971_; 
v___x_5971_ = 0;
return v___x_5971_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0___boxed(lean_object* v_x_5972_){
_start:
{
uint8_t v_res_5973_; lean_object* v_r_5974_; 
v_res_5973_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0(v_x_5972_);
lean_dec(v_x_5972_);
v_r_5974_ = lean_box(v_res_5973_);
return v_r_5974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(lean_object* v_as_5981_, size_t v_sz_5982_, size_t v_i_5983_, lean_object* v_b_5984_, lean_object* v___y_5985_, lean_object* v___y_5986_, lean_object* v___y_5987_, lean_object* v___y_5988_){
_start:
{
uint8_t v___x_5990_; 
v___x_5990_ = lean_usize_dec_lt(v_i_5983_, v_sz_5982_);
if (v___x_5990_ == 0)
{
lean_object* v___x_5991_; 
v___x_5991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5991_, 0, v_b_5984_);
return v___x_5991_;
}
else
{
lean_object* v_snd_5992_; lean_object* v_fst_5993_; lean_object* v___x_5995_; uint8_t v_isShared_5996_; uint8_t v_isSharedCheck_6064_; 
v_snd_5992_ = lean_ctor_get(v_b_5984_, 1);
v_fst_5993_ = lean_ctor_get(v_b_5984_, 0);
v_isSharedCheck_6064_ = !lean_is_exclusive(v_b_5984_);
if (v_isSharedCheck_6064_ == 0)
{
v___x_5995_ = v_b_5984_;
v_isShared_5996_ = v_isSharedCheck_6064_;
goto v_resetjp_5994_;
}
else
{
lean_inc(v_snd_5992_);
lean_inc(v_fst_5993_);
lean_dec(v_b_5984_);
v___x_5995_ = lean_box(0);
v_isShared_5996_ = v_isSharedCheck_6064_;
goto v_resetjp_5994_;
}
v_resetjp_5994_:
{
lean_object* v_array_5997_; lean_object* v_start_5998_; lean_object* v_stop_5999_; uint8_t v___x_6000_; 
v_array_5997_ = lean_ctor_get(v_snd_5992_, 0);
v_start_5998_ = lean_ctor_get(v_snd_5992_, 1);
v_stop_5999_ = lean_ctor_get(v_snd_5992_, 2);
v___x_6000_ = lean_nat_dec_lt(v_start_5998_, v_stop_5999_);
if (v___x_6000_ == 0)
{
lean_object* v___x_6002_; 
if (v_isShared_5996_ == 0)
{
v___x_6002_ = v___x_5995_;
goto v_reusejp_6001_;
}
else
{
lean_object* v_reuseFailAlloc_6004_; 
v_reuseFailAlloc_6004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6004_, 0, v_fst_5993_);
lean_ctor_set(v_reuseFailAlloc_6004_, 1, v_snd_5992_);
v___x_6002_ = v_reuseFailAlloc_6004_;
goto v_reusejp_6001_;
}
v_reusejp_6001_:
{
lean_object* v___x_6003_; 
v___x_6003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6003_, 0, v___x_6002_);
return v___x_6003_;
}
}
else
{
lean_object* v___x_6006_; uint8_t v_isShared_6007_; uint8_t v_isSharedCheck_6060_; 
lean_inc(v_stop_5999_);
lean_inc(v_start_5998_);
lean_inc_ref(v_array_5997_);
v_isSharedCheck_6060_ = !lean_is_exclusive(v_snd_5992_);
if (v_isSharedCheck_6060_ == 0)
{
lean_object* v_unused_6061_; lean_object* v_unused_6062_; lean_object* v_unused_6063_; 
v_unused_6061_ = lean_ctor_get(v_snd_5992_, 2);
lean_dec(v_unused_6061_);
v_unused_6062_ = lean_ctor_get(v_snd_5992_, 1);
lean_dec(v_unused_6062_);
v_unused_6063_ = lean_ctor_get(v_snd_5992_, 0);
lean_dec(v_unused_6063_);
v___x_6006_ = v_snd_5992_;
v_isShared_6007_ = v_isSharedCheck_6060_;
goto v_resetjp_6005_;
}
else
{
lean_dec(v_snd_5992_);
v___x_6006_ = lean_box(0);
v_isShared_6007_ = v_isSharedCheck_6060_;
goto v_resetjp_6005_;
}
v_resetjp_6005_:
{
lean_object* v_array_6008_; lean_object* v_start_6009_; lean_object* v_stop_6010_; lean_object* v___x_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6015_; 
v_array_6008_ = lean_ctor_get(v_fst_5993_, 0);
v_start_6009_ = lean_ctor_get(v_fst_5993_, 1);
v_stop_6010_ = lean_ctor_get(v_fst_5993_, 2);
v___x_6011_ = lean_array_fget(v_array_5997_, v_start_5998_);
v___x_6012_ = lean_unsigned_to_nat(1u);
v___x_6013_ = lean_nat_add(v_start_5998_, v___x_6012_);
lean_dec(v_start_5998_);
if (v_isShared_6007_ == 0)
{
lean_ctor_set(v___x_6006_, 1, v___x_6013_);
v___x_6015_ = v___x_6006_;
goto v_reusejp_6014_;
}
else
{
lean_object* v_reuseFailAlloc_6059_; 
v_reuseFailAlloc_6059_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6059_, 0, v_array_5997_);
lean_ctor_set(v_reuseFailAlloc_6059_, 1, v___x_6013_);
lean_ctor_set(v_reuseFailAlloc_6059_, 2, v_stop_5999_);
v___x_6015_ = v_reuseFailAlloc_6059_;
goto v_reusejp_6014_;
}
v_reusejp_6014_:
{
uint8_t v___x_6016_; 
v___x_6016_ = lean_nat_dec_lt(v_start_6009_, v_stop_6010_);
if (v___x_6016_ == 0)
{
lean_object* v___x_6018_; 
lean_dec(v___x_6011_);
if (v_isShared_5996_ == 0)
{
lean_ctor_set(v___x_5995_, 1, v___x_6015_);
v___x_6018_ = v___x_5995_;
goto v_reusejp_6017_;
}
else
{
lean_object* v_reuseFailAlloc_6020_; 
v_reuseFailAlloc_6020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6020_, 0, v_fst_5993_);
lean_ctor_set(v_reuseFailAlloc_6020_, 1, v___x_6015_);
v___x_6018_ = v_reuseFailAlloc_6020_;
goto v_reusejp_6017_;
}
v_reusejp_6017_:
{
lean_object* v___x_6019_; 
v___x_6019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6019_, 0, v___x_6018_);
return v___x_6019_;
}
}
else
{
lean_object* v___x_6022_; uint8_t v_isShared_6023_; uint8_t v_isSharedCheck_6055_; 
lean_inc(v_stop_6010_);
lean_inc(v_start_6009_);
lean_inc_ref(v_array_6008_);
v_isSharedCheck_6055_ = !lean_is_exclusive(v_fst_5993_);
if (v_isSharedCheck_6055_ == 0)
{
lean_object* v_unused_6056_; lean_object* v_unused_6057_; lean_object* v_unused_6058_; 
v_unused_6056_ = lean_ctor_get(v_fst_5993_, 2);
lean_dec(v_unused_6056_);
v_unused_6057_ = lean_ctor_get(v_fst_5993_, 1);
lean_dec(v_unused_6057_);
v_unused_6058_ = lean_ctor_get(v_fst_5993_, 0);
lean_dec(v_unused_6058_);
v___x_6022_ = v_fst_5993_;
v_isShared_6023_ = v_isSharedCheck_6055_;
goto v_resetjp_6021_;
}
else
{
lean_dec(v_fst_5993_);
v___x_6022_ = lean_box(0);
v_isShared_6023_ = v_isSharedCheck_6055_;
goto v_resetjp_6021_;
}
v_resetjp_6021_:
{
lean_object* v___f_6024_; lean_object* v_a_6025_; lean_object* v___x_6026_; lean_object* v___y_6027_; lean_object* v___x_6028_; lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; uint8_t v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6036_; 
v___f_6024_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__0));
v_a_6025_ = lean_array_uget_borrowed(v_as_5981_, v_i_5983_);
v___x_6026_ = lean_array_fget_borrowed(v_array_6008_, v_start_6009_);
lean_inc(v___x_6026_);
v___y_6027_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3___boxed), 9, 2);
lean_closure_set(v___y_6027_, 0, v___x_6011_);
lean_closure_set(v___y_6027_, 1, v___x_6026_);
lean_inc(v_a_6025_);
v___x_6028_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withDeclName___boxed), 10, 3);
lean_closure_set(v___x_6028_, 0, lean_box(0));
lean_closure_set(v___x_6028_, 1, v_a_6025_);
lean_closure_set(v___x_6028_, 2, v___y_6027_);
v___x_6029_ = lean_box(0);
v___x_6030_ = lean_box(0);
v___x_6031_ = lean_box(1);
v___x_6032_ = 0;
v___x_6033_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__1));
v___x_6034_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_6034_, 0, v___x_6029_);
lean_ctor_set(v___x_6034_, 1, v___x_6030_);
lean_ctor_set(v___x_6034_, 2, v___x_6029_);
lean_ctor_set(v___x_6034_, 3, v___f_6024_);
lean_ctor_set(v___x_6034_, 4, v___x_6031_);
lean_ctor_set(v___x_6034_, 5, v___x_6031_);
lean_ctor_set(v___x_6034_, 6, v___x_6029_);
lean_ctor_set(v___x_6034_, 7, v___x_6033_);
lean_ctor_set_uint8(v___x_6034_, sizeof(void*)*8, v___x_6016_);
lean_ctor_set_uint8(v___x_6034_, sizeof(void*)*8 + 1, v___x_6016_);
lean_ctor_set_uint8(v___x_6034_, sizeof(void*)*8 + 2, v___x_6016_);
lean_ctor_set_uint8(v___x_6034_, sizeof(void*)*8 + 3, v___x_6016_);
lean_ctor_set_uint8(v___x_6034_, sizeof(void*)*8 + 4, v___x_6032_);
lean_ctor_set_uint8(v___x_6034_, sizeof(void*)*8 + 5, v___x_6032_);
lean_ctor_set_uint8(v___x_6034_, sizeof(void*)*8 + 6, v___x_6032_);
lean_ctor_set_uint8(v___x_6034_, sizeof(void*)*8 + 7, v___x_6032_);
lean_ctor_set_uint8(v___x_6034_, sizeof(void*)*8 + 8, v___x_6016_);
lean_ctor_set_uint8(v___x_6034_, sizeof(void*)*8 + 9, v___x_6032_);
lean_ctor_set_uint8(v___x_6034_, sizeof(void*)*8 + 10, v___x_6016_);
v___x_6035_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__2));
v___x_6036_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_6028_, v___x_6034_, v___x_6035_, v___y_5985_, v___y_5986_, v___y_5987_, v___y_5988_);
if (lean_obj_tag(v___x_6036_) == 0)
{
lean_object* v___x_6037_; lean_object* v___x_6039_; 
lean_dec_ref_known(v___x_6036_, 1);
v___x_6037_ = lean_nat_add(v_start_6009_, v___x_6012_);
lean_dec(v_start_6009_);
if (v_isShared_6023_ == 0)
{
lean_ctor_set(v___x_6022_, 1, v___x_6037_);
v___x_6039_ = v___x_6022_;
goto v_reusejp_6038_;
}
else
{
lean_object* v_reuseFailAlloc_6046_; 
v_reuseFailAlloc_6046_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6046_, 0, v_array_6008_);
lean_ctor_set(v_reuseFailAlloc_6046_, 1, v___x_6037_);
lean_ctor_set(v_reuseFailAlloc_6046_, 2, v_stop_6010_);
v___x_6039_ = v_reuseFailAlloc_6046_;
goto v_reusejp_6038_;
}
v_reusejp_6038_:
{
lean_object* v___x_6041_; 
if (v_isShared_5996_ == 0)
{
lean_ctor_set(v___x_5995_, 1, v___x_6015_);
lean_ctor_set(v___x_5995_, 0, v___x_6039_);
v___x_6041_ = v___x_5995_;
goto v_reusejp_6040_;
}
else
{
lean_object* v_reuseFailAlloc_6045_; 
v_reuseFailAlloc_6045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6045_, 0, v___x_6039_);
lean_ctor_set(v_reuseFailAlloc_6045_, 1, v___x_6015_);
v___x_6041_ = v_reuseFailAlloc_6045_;
goto v_reusejp_6040_;
}
v_reusejp_6040_:
{
size_t v___x_6042_; size_t v___x_6043_; 
v___x_6042_ = ((size_t)1ULL);
v___x_6043_ = lean_usize_add(v_i_5983_, v___x_6042_);
v_i_5983_ = v___x_6043_;
v_b_5984_ = v___x_6041_;
goto _start;
}
}
}
else
{
lean_object* v_a_6047_; lean_object* v___x_6049_; uint8_t v_isShared_6050_; uint8_t v_isSharedCheck_6054_; 
lean_del_object(v___x_6022_);
lean_dec_ref(v___x_6015_);
lean_dec(v_stop_6010_);
lean_dec(v_start_6009_);
lean_dec_ref(v_array_6008_);
lean_del_object(v___x_5995_);
v_a_6047_ = lean_ctor_get(v___x_6036_, 0);
v_isSharedCheck_6054_ = !lean_is_exclusive(v___x_6036_);
if (v_isSharedCheck_6054_ == 0)
{
v___x_6049_ = v___x_6036_;
v_isShared_6050_ = v_isSharedCheck_6054_;
goto v_resetjp_6048_;
}
else
{
lean_inc(v_a_6047_);
lean_dec(v___x_6036_);
v___x_6049_ = lean_box(0);
v_isShared_6050_ = v_isSharedCheck_6054_;
goto v_resetjp_6048_;
}
v_resetjp_6048_:
{
lean_object* v___x_6052_; 
if (v_isShared_6050_ == 0)
{
v___x_6052_ = v___x_6049_;
goto v_reusejp_6051_;
}
else
{
lean_object* v_reuseFailAlloc_6053_; 
v_reuseFailAlloc_6053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6053_, 0, v_a_6047_);
v___x_6052_ = v_reuseFailAlloc_6053_;
goto v_reusejp_6051_;
}
v_reusejp_6051_:
{
return v___x_6052_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___boxed(lean_object* v_as_6065_, lean_object* v_sz_6066_, lean_object* v_i_6067_, lean_object* v_b_6068_, lean_object* v___y_6069_, lean_object* v___y_6070_, lean_object* v___y_6071_, lean_object* v___y_6072_, lean_object* v___y_6073_){
_start:
{
size_t v_sz_boxed_6074_; size_t v_i_boxed_6075_; lean_object* v_res_6076_; 
v_sz_boxed_6074_ = lean_unbox_usize(v_sz_6066_);
lean_dec(v_sz_6066_);
v_i_boxed_6075_ = lean_unbox_usize(v_i_6067_);
lean_dec(v_i_6067_);
v_res_6076_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(v_as_6065_, v_sz_boxed_6074_, v_i_boxed_6075_, v_b_6068_, v___y_6069_, v___y_6070_, v___y_6071_, v___y_6072_);
lean_dec(v___y_6072_);
lean_dec_ref(v___y_6071_);
lean_dec(v___y_6070_);
lean_dec_ref(v___y_6069_);
lean_dec_ref(v_as_6065_);
return v_res_6076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___lam__0(lean_object* v_value_6077_, lean_object* v_decrTactics_6078_, lean_object* v_argsPacker_6079_, lean_object* v_funNames_6080_, lean_object* v___y_6081_, lean_object* v___y_6082_, lean_object* v___y_6083_, lean_object* v___y_6084_){
_start:
{
lean_object* v___x_6086_; 
lean_inc_ref(v_value_6077_);
v___x_6086_ = l_Lean_Meta_getMVarsNoDelayed(v_value_6077_, v___y_6081_, v___y_6082_, v___y_6083_, v___y_6084_);
if (lean_obj_tag(v___x_6086_) == 0)
{
lean_object* v_a_6087_; lean_object* v___x_6088_; 
v_a_6087_ = lean_ctor_get(v___x_6086_, 0);
lean_inc(v_a_6087_);
lean_dec_ref_known(v___x_6086_, 1);
v___x_6088_ = l_Lean_Elab_WF_assignSubsumed(v_a_6087_, v___y_6081_, v___y_6082_, v___y_6083_, v___y_6084_);
lean_dec(v_a_6087_);
if (lean_obj_tag(v___x_6088_) == 0)
{
lean_object* v_a_6089_; lean_object* v___x_6090_; lean_object* v___x_6091_; 
v_a_6089_ = lean_ctor_get(v___x_6088_, 0);
lean_inc(v_a_6089_);
lean_dec_ref_known(v___x_6088_, 1);
v___x_6090_ = lean_array_get_size(v_decrTactics_6078_);
v___x_6091_ = l_Lean_Elab_WF_groupGoalsByFunction(v_argsPacker_6079_, v___x_6090_, v_a_6089_, v___y_6081_, v___y_6082_, v___y_6083_, v___y_6084_);
lean_dec(v_a_6089_);
if (lean_obj_tag(v___x_6091_) == 0)
{
lean_object* v_a_6092_; lean_object* v___x_6093_; lean_object* v___x_6094_; lean_object* v___x_6095_; lean_object* v___x_6096_; lean_object* v___x_6097_; size_t v_sz_6098_; size_t v___x_6099_; lean_object* v___x_6100_; 
v_a_6092_ = lean_ctor_get(v___x_6091_, 0);
lean_inc(v_a_6092_);
lean_dec_ref_known(v___x_6091_, 1);
v___x_6093_ = lean_unsigned_to_nat(0u);
v___x_6094_ = lean_array_get_size(v_a_6092_);
v___x_6095_ = l_Array_toSubarray___redArg(v_a_6092_, v___x_6093_, v___x_6094_);
v___x_6096_ = l_Array_toSubarray___redArg(v_decrTactics_6078_, v___x_6093_, v___x_6090_);
v___x_6097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6097_, 0, v___x_6095_);
lean_ctor_set(v___x_6097_, 1, v___x_6096_);
v_sz_6098_ = lean_array_size(v_funNames_6080_);
v___x_6099_ = ((size_t)0ULL);
v___x_6100_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(v_funNames_6080_, v_sz_6098_, v___x_6099_, v___x_6097_, v___y_6081_, v___y_6082_, v___y_6083_, v___y_6084_);
if (lean_obj_tag(v___x_6100_) == 0)
{
lean_object* v___x_6101_; 
lean_dec_ref_known(v___x_6100_, 1);
v___x_6101_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_value_6077_, v___y_6082_);
return v___x_6101_;
}
else
{
lean_object* v_a_6102_; lean_object* v___x_6104_; uint8_t v_isShared_6105_; uint8_t v_isSharedCheck_6109_; 
lean_dec_ref(v_value_6077_);
v_a_6102_ = lean_ctor_get(v___x_6100_, 0);
v_isSharedCheck_6109_ = !lean_is_exclusive(v___x_6100_);
if (v_isSharedCheck_6109_ == 0)
{
v___x_6104_ = v___x_6100_;
v_isShared_6105_ = v_isSharedCheck_6109_;
goto v_resetjp_6103_;
}
else
{
lean_inc(v_a_6102_);
lean_dec(v___x_6100_);
v___x_6104_ = lean_box(0);
v_isShared_6105_ = v_isSharedCheck_6109_;
goto v_resetjp_6103_;
}
v_resetjp_6103_:
{
lean_object* v___x_6107_; 
if (v_isShared_6105_ == 0)
{
v___x_6107_ = v___x_6104_;
goto v_reusejp_6106_;
}
else
{
lean_object* v_reuseFailAlloc_6108_; 
v_reuseFailAlloc_6108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6108_, 0, v_a_6102_);
v___x_6107_ = v_reuseFailAlloc_6108_;
goto v_reusejp_6106_;
}
v_reusejp_6106_:
{
return v___x_6107_;
}
}
}
}
else
{
lean_object* v_a_6110_; lean_object* v___x_6112_; uint8_t v_isShared_6113_; uint8_t v_isSharedCheck_6117_; 
lean_dec_ref(v_decrTactics_6078_);
lean_dec_ref(v_value_6077_);
v_a_6110_ = lean_ctor_get(v___x_6091_, 0);
v_isSharedCheck_6117_ = !lean_is_exclusive(v___x_6091_);
if (v_isSharedCheck_6117_ == 0)
{
v___x_6112_ = v___x_6091_;
v_isShared_6113_ = v_isSharedCheck_6117_;
goto v_resetjp_6111_;
}
else
{
lean_inc(v_a_6110_);
lean_dec(v___x_6091_);
v___x_6112_ = lean_box(0);
v_isShared_6113_ = v_isSharedCheck_6117_;
goto v_resetjp_6111_;
}
v_resetjp_6111_:
{
lean_object* v___x_6115_; 
if (v_isShared_6113_ == 0)
{
v___x_6115_ = v___x_6112_;
goto v_reusejp_6114_;
}
else
{
lean_object* v_reuseFailAlloc_6116_; 
v_reuseFailAlloc_6116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6116_, 0, v_a_6110_);
v___x_6115_ = v_reuseFailAlloc_6116_;
goto v_reusejp_6114_;
}
v_reusejp_6114_:
{
return v___x_6115_;
}
}
}
}
else
{
lean_object* v_a_6118_; lean_object* v___x_6120_; uint8_t v_isShared_6121_; uint8_t v_isSharedCheck_6125_; 
lean_dec_ref(v_decrTactics_6078_);
lean_dec_ref(v_value_6077_);
v_a_6118_ = lean_ctor_get(v___x_6088_, 0);
v_isSharedCheck_6125_ = !lean_is_exclusive(v___x_6088_);
if (v_isSharedCheck_6125_ == 0)
{
v___x_6120_ = v___x_6088_;
v_isShared_6121_ = v_isSharedCheck_6125_;
goto v_resetjp_6119_;
}
else
{
lean_inc(v_a_6118_);
lean_dec(v___x_6088_);
v___x_6120_ = lean_box(0);
v_isShared_6121_ = v_isSharedCheck_6125_;
goto v_resetjp_6119_;
}
v_resetjp_6119_:
{
lean_object* v___x_6123_; 
if (v_isShared_6121_ == 0)
{
v___x_6123_ = v___x_6120_;
goto v_reusejp_6122_;
}
else
{
lean_object* v_reuseFailAlloc_6124_; 
v_reuseFailAlloc_6124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6124_, 0, v_a_6118_);
v___x_6123_ = v_reuseFailAlloc_6124_;
goto v_reusejp_6122_;
}
v_reusejp_6122_:
{
return v___x_6123_;
}
}
}
}
else
{
lean_object* v_a_6126_; lean_object* v___x_6128_; uint8_t v_isShared_6129_; uint8_t v_isSharedCheck_6133_; 
lean_dec_ref(v_decrTactics_6078_);
lean_dec_ref(v_value_6077_);
v_a_6126_ = lean_ctor_get(v___x_6086_, 0);
v_isSharedCheck_6133_ = !lean_is_exclusive(v___x_6086_);
if (v_isSharedCheck_6133_ == 0)
{
v___x_6128_ = v___x_6086_;
v_isShared_6129_ = v_isSharedCheck_6133_;
goto v_resetjp_6127_;
}
else
{
lean_inc(v_a_6126_);
lean_dec(v___x_6086_);
v___x_6128_ = lean_box(0);
v_isShared_6129_ = v_isSharedCheck_6133_;
goto v_resetjp_6127_;
}
v_resetjp_6127_:
{
lean_object* v___x_6131_; 
if (v_isShared_6129_ == 0)
{
v___x_6131_ = v___x_6128_;
goto v_reusejp_6130_;
}
else
{
lean_object* v_reuseFailAlloc_6132_; 
v_reuseFailAlloc_6132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6132_, 0, v_a_6126_);
v___x_6131_ = v_reuseFailAlloc_6132_;
goto v_reusejp_6130_;
}
v_reusejp_6130_:
{
return v___x_6131_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___lam__0___boxed(lean_object* v_value_6134_, lean_object* v_decrTactics_6135_, lean_object* v_argsPacker_6136_, lean_object* v_funNames_6137_, lean_object* v___y_6138_, lean_object* v___y_6139_, lean_object* v___y_6140_, lean_object* v___y_6141_, lean_object* v___y_6142_){
_start:
{
lean_object* v_res_6143_; 
v_res_6143_ = l_Lean_Elab_WF_solveDecreasingGoals___lam__0(v_value_6134_, v_decrTactics_6135_, v_argsPacker_6136_, v_funNames_6137_, v___y_6138_, v___y_6139_, v___y_6140_, v___y_6141_);
lean_dec(v___y_6141_);
lean_dec_ref(v___y_6140_);
lean_dec(v___y_6139_);
lean_dec_ref(v___y_6138_);
lean_dec_ref(v_funNames_6137_);
lean_dec_ref(v_argsPacker_6136_);
return v_res_6143_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(lean_object* v___y_6144_, uint8_t v_isExporting_6145_, lean_object* v___x_6146_, lean_object* v___y_6147_, lean_object* v___x_6148_, lean_object* v_a_x3f_6149_){
_start:
{
lean_object* v___x_6151_; lean_object* v_env_6152_; lean_object* v_nextMacroScope_6153_; lean_object* v_ngen_6154_; lean_object* v_auxDeclNGen_6155_; lean_object* v_traceState_6156_; lean_object* v_messages_6157_; lean_object* v_infoState_6158_; lean_object* v_snapshotTasks_6159_; lean_object* v___x_6161_; uint8_t v_isShared_6162_; uint8_t v_isSharedCheck_6184_; 
v___x_6151_ = lean_st_ref_take(v___y_6144_);
v_env_6152_ = lean_ctor_get(v___x_6151_, 0);
v_nextMacroScope_6153_ = lean_ctor_get(v___x_6151_, 1);
v_ngen_6154_ = lean_ctor_get(v___x_6151_, 2);
v_auxDeclNGen_6155_ = lean_ctor_get(v___x_6151_, 3);
v_traceState_6156_ = lean_ctor_get(v___x_6151_, 4);
v_messages_6157_ = lean_ctor_get(v___x_6151_, 6);
v_infoState_6158_ = lean_ctor_get(v___x_6151_, 7);
v_snapshotTasks_6159_ = lean_ctor_get(v___x_6151_, 8);
v_isSharedCheck_6184_ = !lean_is_exclusive(v___x_6151_);
if (v_isSharedCheck_6184_ == 0)
{
lean_object* v_unused_6185_; 
v_unused_6185_ = lean_ctor_get(v___x_6151_, 5);
lean_dec(v_unused_6185_);
v___x_6161_ = v___x_6151_;
v_isShared_6162_ = v_isSharedCheck_6184_;
goto v_resetjp_6160_;
}
else
{
lean_inc(v_snapshotTasks_6159_);
lean_inc(v_infoState_6158_);
lean_inc(v_messages_6157_);
lean_inc(v_traceState_6156_);
lean_inc(v_auxDeclNGen_6155_);
lean_inc(v_ngen_6154_);
lean_inc(v_nextMacroScope_6153_);
lean_inc(v_env_6152_);
lean_dec(v___x_6151_);
v___x_6161_ = lean_box(0);
v_isShared_6162_ = v_isSharedCheck_6184_;
goto v_resetjp_6160_;
}
v_resetjp_6160_:
{
lean_object* v___x_6163_; lean_object* v___x_6165_; 
v___x_6163_ = l_Lean_Environment_setExporting(v_env_6152_, v_isExporting_6145_);
if (v_isShared_6162_ == 0)
{
lean_ctor_set(v___x_6161_, 5, v___x_6146_);
lean_ctor_set(v___x_6161_, 0, v___x_6163_);
v___x_6165_ = v___x_6161_;
goto v_reusejp_6164_;
}
else
{
lean_object* v_reuseFailAlloc_6183_; 
v_reuseFailAlloc_6183_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6183_, 0, v___x_6163_);
lean_ctor_set(v_reuseFailAlloc_6183_, 1, v_nextMacroScope_6153_);
lean_ctor_set(v_reuseFailAlloc_6183_, 2, v_ngen_6154_);
lean_ctor_set(v_reuseFailAlloc_6183_, 3, v_auxDeclNGen_6155_);
lean_ctor_set(v_reuseFailAlloc_6183_, 4, v_traceState_6156_);
lean_ctor_set(v_reuseFailAlloc_6183_, 5, v___x_6146_);
lean_ctor_set(v_reuseFailAlloc_6183_, 6, v_messages_6157_);
lean_ctor_set(v_reuseFailAlloc_6183_, 7, v_infoState_6158_);
lean_ctor_set(v_reuseFailAlloc_6183_, 8, v_snapshotTasks_6159_);
v___x_6165_ = v_reuseFailAlloc_6183_;
goto v_reusejp_6164_;
}
v_reusejp_6164_:
{
lean_object* v___x_6166_; lean_object* v___x_6167_; lean_object* v_mctx_6168_; lean_object* v_zetaDeltaFVarIds_6169_; lean_object* v_postponed_6170_; lean_object* v_diag_6171_; lean_object* v___x_6173_; uint8_t v_isShared_6174_; uint8_t v_isSharedCheck_6181_; 
v___x_6166_ = lean_st_ref_put(v___y_6144_, v___x_6165_);
v___x_6167_ = lean_st_ref_take(v___y_6147_);
v_mctx_6168_ = lean_ctor_get(v___x_6167_, 0);
v_zetaDeltaFVarIds_6169_ = lean_ctor_get(v___x_6167_, 2);
v_postponed_6170_ = lean_ctor_get(v___x_6167_, 3);
v_diag_6171_ = lean_ctor_get(v___x_6167_, 4);
v_isSharedCheck_6181_ = !lean_is_exclusive(v___x_6167_);
if (v_isSharedCheck_6181_ == 0)
{
lean_object* v_unused_6182_; 
v_unused_6182_ = lean_ctor_get(v___x_6167_, 1);
lean_dec(v_unused_6182_);
v___x_6173_ = v___x_6167_;
v_isShared_6174_ = v_isSharedCheck_6181_;
goto v_resetjp_6172_;
}
else
{
lean_inc(v_diag_6171_);
lean_inc(v_postponed_6170_);
lean_inc(v_zetaDeltaFVarIds_6169_);
lean_inc(v_mctx_6168_);
lean_dec(v___x_6167_);
v___x_6173_ = lean_box(0);
v_isShared_6174_ = v_isSharedCheck_6181_;
goto v_resetjp_6172_;
}
v_resetjp_6172_:
{
lean_object* v___x_6176_; 
if (v_isShared_6174_ == 0)
{
lean_ctor_set(v___x_6173_, 1, v___x_6148_);
v___x_6176_ = v___x_6173_;
goto v_reusejp_6175_;
}
else
{
lean_object* v_reuseFailAlloc_6180_; 
v_reuseFailAlloc_6180_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6180_, 0, v_mctx_6168_);
lean_ctor_set(v_reuseFailAlloc_6180_, 1, v___x_6148_);
lean_ctor_set(v_reuseFailAlloc_6180_, 2, v_zetaDeltaFVarIds_6169_);
lean_ctor_set(v_reuseFailAlloc_6180_, 3, v_postponed_6170_);
lean_ctor_set(v_reuseFailAlloc_6180_, 4, v_diag_6171_);
v___x_6176_ = v_reuseFailAlloc_6180_;
goto v_reusejp_6175_;
}
v_reusejp_6175_:
{
lean_object* v___x_6177_; lean_object* v___x_6178_; lean_object* v___x_6179_; 
v___x_6177_ = lean_st_ref_put(v___y_6147_, v___x_6176_);
v___x_6178_ = lean_box(0);
v___x_6179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6179_, 0, v___x_6178_);
return v___x_6179_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0___boxed(lean_object* v___y_6186_, lean_object* v_isExporting_6187_, lean_object* v___x_6188_, lean_object* v___y_6189_, lean_object* v___x_6190_, lean_object* v_a_x3f_6191_, lean_object* v___y_6192_){
_start:
{
uint8_t v_isExporting_boxed_6193_; lean_object* v_res_6194_; 
v_isExporting_boxed_6193_ = lean_unbox(v_isExporting_6187_);
v_res_6194_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6186_, v_isExporting_boxed_6193_, v___x_6188_, v___y_6189_, v___x_6190_, v_a_x3f_6191_);
lean_dec(v_a_x3f_6191_);
lean_dec(v___y_6189_);
lean_dec(v___y_6186_);
return v_res_6194_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_6195_; 
v___x_6195_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_6195_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_6196_; lean_object* v___x_6197_; 
v___x_6196_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0);
v___x_6197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6197_, 0, v___x_6196_);
return v___x_6197_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_6198_; lean_object* v___x_6199_; 
v___x_6198_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1);
v___x_6199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6199_, 0, v___x_6198_);
lean_ctor_set(v___x_6199_, 1, v___x_6198_);
return v___x_6199_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_6200_; lean_object* v___x_6201_; 
v___x_6200_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1);
v___x_6201_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6201_, 0, v___x_6200_);
lean_ctor_set(v___x_6201_, 1, v___x_6200_);
lean_ctor_set(v___x_6201_, 2, v___x_6200_);
lean_ctor_set(v___x_6201_, 3, v___x_6200_);
lean_ctor_set(v___x_6201_, 4, v___x_6200_);
lean_ctor_set(v___x_6201_, 5, v___x_6200_);
return v___x_6201_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(lean_object* v_x_6202_, uint8_t v_isExporting_6203_, lean_object* v___y_6204_, lean_object* v___y_6205_, lean_object* v___y_6206_, lean_object* v___y_6207_){
_start:
{
lean_object* v___x_6209_; lean_object* v_env_6210_; uint8_t v_isExporting_6211_; lean_object* v___x_6277_; uint8_t v_isModule_6278_; 
v___x_6209_ = lean_st_ref_get(v___y_6207_);
v_env_6210_ = lean_ctor_get(v___x_6209_, 0);
lean_inc_ref(v_env_6210_);
lean_dec(v___x_6209_);
v_isExporting_6211_ = lean_ctor_get_uint8(v_env_6210_, sizeof(void*)*8);
v___x_6277_ = l_Lean_Environment_header(v_env_6210_);
lean_dec_ref(v_env_6210_);
v_isModule_6278_ = lean_ctor_get_uint8(v___x_6277_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_6277_);
if (v_isModule_6278_ == 0)
{
lean_object* v___x_6279_; 
lean_inc(v___y_6207_);
lean_inc_ref(v___y_6206_);
lean_inc(v___y_6205_);
lean_inc_ref(v___y_6204_);
v___x_6279_ = lean_apply_5(v_x_6202_, v___y_6204_, v___y_6205_, v___y_6206_, v___y_6207_, lean_box(0));
return v___x_6279_;
}
else
{
if (v_isExporting_6211_ == 0)
{
if (v_isExporting_6203_ == 0)
{
lean_object* v___x_6280_; 
lean_inc(v___y_6207_);
lean_inc_ref(v___y_6206_);
lean_inc(v___y_6205_);
lean_inc_ref(v___y_6204_);
v___x_6280_ = lean_apply_5(v_x_6202_, v___y_6204_, v___y_6205_, v___y_6206_, v___y_6207_, lean_box(0));
return v___x_6280_;
}
else
{
goto v___jp_6212_;
}
}
else
{
if (v_isExporting_6203_ == 0)
{
goto v___jp_6212_;
}
else
{
lean_object* v___x_6281_; 
lean_inc(v___y_6207_);
lean_inc_ref(v___y_6206_);
lean_inc(v___y_6205_);
lean_inc_ref(v___y_6204_);
v___x_6281_ = lean_apply_5(v_x_6202_, v___y_6204_, v___y_6205_, v___y_6206_, v___y_6207_, lean_box(0));
return v___x_6281_;
}
}
}
v___jp_6212_:
{
lean_object* v___x_6213_; lean_object* v_env_6214_; lean_object* v_nextMacroScope_6215_; lean_object* v_ngen_6216_; lean_object* v_auxDeclNGen_6217_; lean_object* v_traceState_6218_; lean_object* v_messages_6219_; lean_object* v_infoState_6220_; lean_object* v_snapshotTasks_6221_; lean_object* v___x_6223_; uint8_t v_isShared_6224_; uint8_t v_isSharedCheck_6275_; 
v___x_6213_ = lean_st_ref_take(v___y_6207_);
v_env_6214_ = lean_ctor_get(v___x_6213_, 0);
v_nextMacroScope_6215_ = lean_ctor_get(v___x_6213_, 1);
v_ngen_6216_ = lean_ctor_get(v___x_6213_, 2);
v_auxDeclNGen_6217_ = lean_ctor_get(v___x_6213_, 3);
v_traceState_6218_ = lean_ctor_get(v___x_6213_, 4);
v_messages_6219_ = lean_ctor_get(v___x_6213_, 6);
v_infoState_6220_ = lean_ctor_get(v___x_6213_, 7);
v_snapshotTasks_6221_ = lean_ctor_get(v___x_6213_, 8);
v_isSharedCheck_6275_ = !lean_is_exclusive(v___x_6213_);
if (v_isSharedCheck_6275_ == 0)
{
lean_object* v_unused_6276_; 
v_unused_6276_ = lean_ctor_get(v___x_6213_, 5);
lean_dec(v_unused_6276_);
v___x_6223_ = v___x_6213_;
v_isShared_6224_ = v_isSharedCheck_6275_;
goto v_resetjp_6222_;
}
else
{
lean_inc(v_snapshotTasks_6221_);
lean_inc(v_infoState_6220_);
lean_inc(v_messages_6219_);
lean_inc(v_traceState_6218_);
lean_inc(v_auxDeclNGen_6217_);
lean_inc(v_ngen_6216_);
lean_inc(v_nextMacroScope_6215_);
lean_inc(v_env_6214_);
lean_dec(v___x_6213_);
v___x_6223_ = lean_box(0);
v_isShared_6224_ = v_isSharedCheck_6275_;
goto v_resetjp_6222_;
}
v_resetjp_6222_:
{
lean_object* v___x_6225_; lean_object* v___x_6226_; lean_object* v___x_6228_; 
v___x_6225_ = l_Lean_Environment_setExporting(v_env_6214_, v_isExporting_6203_);
v___x_6226_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2);
if (v_isShared_6224_ == 0)
{
lean_ctor_set(v___x_6223_, 5, v___x_6226_);
lean_ctor_set(v___x_6223_, 0, v___x_6225_);
v___x_6228_ = v___x_6223_;
goto v_reusejp_6227_;
}
else
{
lean_object* v_reuseFailAlloc_6274_; 
v_reuseFailAlloc_6274_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6274_, 0, v___x_6225_);
lean_ctor_set(v_reuseFailAlloc_6274_, 1, v_nextMacroScope_6215_);
lean_ctor_set(v_reuseFailAlloc_6274_, 2, v_ngen_6216_);
lean_ctor_set(v_reuseFailAlloc_6274_, 3, v_auxDeclNGen_6217_);
lean_ctor_set(v_reuseFailAlloc_6274_, 4, v_traceState_6218_);
lean_ctor_set(v_reuseFailAlloc_6274_, 5, v___x_6226_);
lean_ctor_set(v_reuseFailAlloc_6274_, 6, v_messages_6219_);
lean_ctor_set(v_reuseFailAlloc_6274_, 7, v_infoState_6220_);
lean_ctor_set(v_reuseFailAlloc_6274_, 8, v_snapshotTasks_6221_);
v___x_6228_ = v_reuseFailAlloc_6274_;
goto v_reusejp_6227_;
}
v_reusejp_6227_:
{
lean_object* v___x_6229_; lean_object* v___x_6230_; lean_object* v_mctx_6231_; lean_object* v_zetaDeltaFVarIds_6232_; lean_object* v_postponed_6233_; lean_object* v_diag_6234_; lean_object* v___x_6236_; uint8_t v_isShared_6237_; uint8_t v_isSharedCheck_6272_; 
v___x_6229_ = lean_st_ref_put(v___y_6207_, v___x_6228_);
v___x_6230_ = lean_st_ref_take(v___y_6205_);
v_mctx_6231_ = lean_ctor_get(v___x_6230_, 0);
v_zetaDeltaFVarIds_6232_ = lean_ctor_get(v___x_6230_, 2);
v_postponed_6233_ = lean_ctor_get(v___x_6230_, 3);
v_diag_6234_ = lean_ctor_get(v___x_6230_, 4);
v_isSharedCheck_6272_ = !lean_is_exclusive(v___x_6230_);
if (v_isSharedCheck_6272_ == 0)
{
lean_object* v_unused_6273_; 
v_unused_6273_ = lean_ctor_get(v___x_6230_, 1);
lean_dec(v_unused_6273_);
v___x_6236_ = v___x_6230_;
v_isShared_6237_ = v_isSharedCheck_6272_;
goto v_resetjp_6235_;
}
else
{
lean_inc(v_diag_6234_);
lean_inc(v_postponed_6233_);
lean_inc(v_zetaDeltaFVarIds_6232_);
lean_inc(v_mctx_6231_);
lean_dec(v___x_6230_);
v___x_6236_ = lean_box(0);
v_isShared_6237_ = v_isSharedCheck_6272_;
goto v_resetjp_6235_;
}
v_resetjp_6235_:
{
lean_object* v___x_6238_; lean_object* v___x_6240_; 
v___x_6238_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3);
if (v_isShared_6237_ == 0)
{
lean_ctor_set(v___x_6236_, 1, v___x_6238_);
v___x_6240_ = v___x_6236_;
goto v_reusejp_6239_;
}
else
{
lean_object* v_reuseFailAlloc_6271_; 
v_reuseFailAlloc_6271_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6271_, 0, v_mctx_6231_);
lean_ctor_set(v_reuseFailAlloc_6271_, 1, v___x_6238_);
lean_ctor_set(v_reuseFailAlloc_6271_, 2, v_zetaDeltaFVarIds_6232_);
lean_ctor_set(v_reuseFailAlloc_6271_, 3, v_postponed_6233_);
lean_ctor_set(v_reuseFailAlloc_6271_, 4, v_diag_6234_);
v___x_6240_ = v_reuseFailAlloc_6271_;
goto v_reusejp_6239_;
}
v_reusejp_6239_:
{
lean_object* v___x_6241_; lean_object* v_r_6242_; 
v___x_6241_ = lean_st_ref_put(v___y_6205_, v___x_6240_);
lean_inc(v___y_6207_);
lean_inc_ref(v___y_6206_);
lean_inc(v___y_6205_);
lean_inc_ref(v___y_6204_);
v_r_6242_ = lean_apply_5(v_x_6202_, v___y_6204_, v___y_6205_, v___y_6206_, v___y_6207_, lean_box(0));
if (lean_obj_tag(v_r_6242_) == 0)
{
lean_object* v_a_6243_; lean_object* v___x_6245_; uint8_t v_isShared_6246_; uint8_t v_isSharedCheck_6259_; 
v_a_6243_ = lean_ctor_get(v_r_6242_, 0);
v_isSharedCheck_6259_ = !lean_is_exclusive(v_r_6242_);
if (v_isSharedCheck_6259_ == 0)
{
v___x_6245_ = v_r_6242_;
v_isShared_6246_ = v_isSharedCheck_6259_;
goto v_resetjp_6244_;
}
else
{
lean_inc(v_a_6243_);
lean_dec(v_r_6242_);
v___x_6245_ = lean_box(0);
v_isShared_6246_ = v_isSharedCheck_6259_;
goto v_resetjp_6244_;
}
v_resetjp_6244_:
{
lean_object* v___x_6248_; 
lean_inc(v_a_6243_);
if (v_isShared_6246_ == 0)
{
lean_ctor_set_tag(v___x_6245_, 1);
v___x_6248_ = v___x_6245_;
goto v_reusejp_6247_;
}
else
{
lean_object* v_reuseFailAlloc_6258_; 
v_reuseFailAlloc_6258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6258_, 0, v_a_6243_);
v___x_6248_ = v_reuseFailAlloc_6258_;
goto v_reusejp_6247_;
}
v_reusejp_6247_:
{
lean_object* v___x_6249_; lean_object* v___x_6251_; uint8_t v_isShared_6252_; uint8_t v_isSharedCheck_6256_; 
v___x_6249_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6207_, v_isExporting_6211_, v___x_6226_, v___y_6205_, v___x_6238_, v___x_6248_);
lean_dec_ref(v___x_6248_);
v_isSharedCheck_6256_ = !lean_is_exclusive(v___x_6249_);
if (v_isSharedCheck_6256_ == 0)
{
lean_object* v_unused_6257_; 
v_unused_6257_ = lean_ctor_get(v___x_6249_, 0);
lean_dec(v_unused_6257_);
v___x_6251_ = v___x_6249_;
v_isShared_6252_ = v_isSharedCheck_6256_;
goto v_resetjp_6250_;
}
else
{
lean_dec(v___x_6249_);
v___x_6251_ = lean_box(0);
v_isShared_6252_ = v_isSharedCheck_6256_;
goto v_resetjp_6250_;
}
v_resetjp_6250_:
{
lean_object* v___x_6254_; 
if (v_isShared_6252_ == 0)
{
lean_ctor_set(v___x_6251_, 0, v_a_6243_);
v___x_6254_ = v___x_6251_;
goto v_reusejp_6253_;
}
else
{
lean_object* v_reuseFailAlloc_6255_; 
v_reuseFailAlloc_6255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6255_, 0, v_a_6243_);
v___x_6254_ = v_reuseFailAlloc_6255_;
goto v_reusejp_6253_;
}
v_reusejp_6253_:
{
return v___x_6254_;
}
}
}
}
}
else
{
lean_object* v_a_6260_; lean_object* v___x_6261_; lean_object* v___x_6262_; lean_object* v___x_6264_; uint8_t v_isShared_6265_; uint8_t v_isSharedCheck_6269_; 
v_a_6260_ = lean_ctor_get(v_r_6242_, 0);
lean_inc(v_a_6260_);
lean_dec_ref_known(v_r_6242_, 1);
v___x_6261_ = lean_box(0);
v___x_6262_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6207_, v_isExporting_6211_, v___x_6226_, v___y_6205_, v___x_6238_, v___x_6261_);
v_isSharedCheck_6269_ = !lean_is_exclusive(v___x_6262_);
if (v_isSharedCheck_6269_ == 0)
{
lean_object* v_unused_6270_; 
v_unused_6270_ = lean_ctor_get(v___x_6262_, 0);
lean_dec(v_unused_6270_);
v___x_6264_ = v___x_6262_;
v_isShared_6265_ = v_isSharedCheck_6269_;
goto v_resetjp_6263_;
}
else
{
lean_dec(v___x_6262_);
v___x_6264_ = lean_box(0);
v_isShared_6265_ = v_isSharedCheck_6269_;
goto v_resetjp_6263_;
}
v_resetjp_6263_:
{
lean_object* v___x_6267_; 
if (v_isShared_6265_ == 0)
{
lean_ctor_set_tag(v___x_6264_, 1);
lean_ctor_set(v___x_6264_, 0, v_a_6260_);
v___x_6267_ = v___x_6264_;
goto v_reusejp_6266_;
}
else
{
lean_object* v_reuseFailAlloc_6268_; 
v_reuseFailAlloc_6268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6268_, 0, v_a_6260_);
v___x_6267_ = v_reuseFailAlloc_6268_;
goto v_reusejp_6266_;
}
v_reusejp_6266_:
{
return v___x_6267_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___boxed(lean_object* v_x_6282_, lean_object* v_isExporting_6283_, lean_object* v___y_6284_, lean_object* v___y_6285_, lean_object* v___y_6286_, lean_object* v___y_6287_, lean_object* v___y_6288_){
_start:
{
uint8_t v_isExporting_boxed_6289_; lean_object* v_res_6290_; 
v_isExporting_boxed_6289_ = lean_unbox(v_isExporting_6283_);
v_res_6290_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6282_, v_isExporting_boxed_6289_, v___y_6284_, v___y_6285_, v___y_6286_, v___y_6287_);
lean_dec(v___y_6287_);
lean_dec_ref(v___y_6286_);
lean_dec(v___y_6285_);
lean_dec_ref(v___y_6284_);
return v_res_6290_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(lean_object* v_x_6291_, uint8_t v_when_6292_, lean_object* v___y_6293_, lean_object* v___y_6294_, lean_object* v___y_6295_, lean_object* v___y_6296_){
_start:
{
if (v_when_6292_ == 0)
{
lean_object* v___x_6298_; 
lean_inc(v___y_6296_);
lean_inc_ref(v___y_6295_);
lean_inc(v___y_6294_);
lean_inc_ref(v___y_6293_);
v___x_6298_ = lean_apply_5(v_x_6291_, v___y_6293_, v___y_6294_, v___y_6295_, v___y_6296_, lean_box(0));
return v___x_6298_;
}
else
{
uint8_t v___x_6299_; lean_object* v___x_6300_; 
v___x_6299_ = 0;
v___x_6300_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6291_, v___x_6299_, v___y_6293_, v___y_6294_, v___y_6295_, v___y_6296_);
return v___x_6300_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg___boxed(lean_object* v_x_6301_, lean_object* v_when_6302_, lean_object* v___y_6303_, lean_object* v___y_6304_, lean_object* v___y_6305_, lean_object* v___y_6306_, lean_object* v___y_6307_){
_start:
{
uint8_t v_when_boxed_6308_; lean_object* v_res_6309_; 
v_when_boxed_6308_ = lean_unbox(v_when_6302_);
v_res_6309_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v_x_6301_, v_when_boxed_6308_, v___y_6303_, v___y_6304_, v___y_6305_, v___y_6306_);
lean_dec(v___y_6306_);
lean_dec_ref(v___y_6305_);
lean_dec(v___y_6304_);
lean_dec_ref(v___y_6303_);
return v_res_6309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals(lean_object* v_funNames_6310_, lean_object* v_argsPacker_6311_, lean_object* v_decrTactics_6312_, lean_object* v_value_6313_, lean_object* v_a_6314_, lean_object* v_a_6315_, lean_object* v_a_6316_, lean_object* v_a_6317_){
_start:
{
lean_object* v___f_6319_; uint8_t v___x_6320_; lean_object* v___x_6321_; 
v___f_6319_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_solveDecreasingGoals___lam__0___boxed), 9, 4);
lean_closure_set(v___f_6319_, 0, v_value_6313_);
lean_closure_set(v___f_6319_, 1, v_decrTactics_6312_);
lean_closure_set(v___f_6319_, 2, v_argsPacker_6311_);
lean_closure_set(v___f_6319_, 3, v_funNames_6310_);
v___x_6320_ = 1;
v___x_6321_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v___f_6319_, v___x_6320_, v_a_6314_, v_a_6315_, v_a_6316_, v_a_6317_);
return v___x_6321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___boxed(lean_object* v_funNames_6322_, lean_object* v_argsPacker_6323_, lean_object* v_decrTactics_6324_, lean_object* v_value_6325_, lean_object* v_a_6326_, lean_object* v_a_6327_, lean_object* v_a_6328_, lean_object* v_a_6329_, lean_object* v_a_6330_){
_start:
{
lean_object* v_res_6331_; 
v_res_6331_ = l_Lean_Elab_WF_solveDecreasingGoals(v_funNames_6322_, v_argsPacker_6323_, v_decrTactics_6324_, v_value_6325_, v_a_6326_, v_a_6327_, v_a_6328_, v_a_6329_);
lean_dec(v_a_6329_);
lean_dec_ref(v_a_6328_);
lean_dec(v_a_6327_);
lean_dec_ref(v_a_6326_);
return v_res_6331_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1(lean_object* v_00_u03b1_6332_, lean_object* v_msg_6333_, lean_object* v___y_6334_, lean_object* v___y_6335_, lean_object* v___y_6336_, lean_object* v___y_6337_, lean_object* v___y_6338_, lean_object* v___y_6339_){
_start:
{
lean_object* v___x_6341_; 
v___x_6341_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v_msg_6333_, v___y_6334_, v___y_6335_, v___y_6336_, v___y_6337_, v___y_6338_, v___y_6339_);
return v___x_6341_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___boxed(lean_object* v_00_u03b1_6342_, lean_object* v_msg_6343_, lean_object* v___y_6344_, lean_object* v___y_6345_, lean_object* v___y_6346_, lean_object* v___y_6347_, lean_object* v___y_6348_, lean_object* v___y_6349_, lean_object* v___y_6350_){
_start:
{
lean_object* v_res_6351_; 
v_res_6351_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1(v_00_u03b1_6342_, v_msg_6343_, v___y_6344_, v___y_6345_, v___y_6346_, v___y_6347_, v___y_6348_, v___y_6349_);
lean_dec(v___y_6349_);
lean_dec_ref(v___y_6348_);
lean_dec(v___y_6347_);
lean_dec_ref(v___y_6346_);
lean_dec(v___y_6345_);
lean_dec_ref(v___y_6344_);
return v_res_6351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4(lean_object* v___y_6352_, lean_object* v___y_6353_, lean_object* v___y_6354_, lean_object* v___y_6355_, lean_object* v___y_6356_, lean_object* v___y_6357_, lean_object* v___y_6358_, lean_object* v___y_6359_){
_start:
{
lean_object* v___x_6361_; 
v___x_6361_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_6359_);
return v___x_6361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___boxed(lean_object* v___y_6362_, lean_object* v___y_6363_, lean_object* v___y_6364_, lean_object* v___y_6365_, lean_object* v___y_6366_, lean_object* v___y_6367_, lean_object* v___y_6368_, lean_object* v___y_6369_, lean_object* v___y_6370_){
_start:
{
lean_object* v_res_6371_; 
v_res_6371_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4(v___y_6362_, v___y_6363_, v___y_6364_, v___y_6365_, v___y_6366_, v___y_6367_, v___y_6368_, v___y_6369_);
lean_dec(v___y_6369_);
lean_dec_ref(v___y_6368_);
lean_dec(v___y_6367_);
lean_dec_ref(v___y_6366_);
lean_dec(v___y_6365_);
lean_dec_ref(v___y_6364_);
lean_dec(v___y_6363_);
lean_dec_ref(v___y_6362_);
return v_res_6371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3(lean_object* v_00_u03b1_6372_, lean_object* v_x_6373_, lean_object* v_mkInfoTree_6374_, lean_object* v___y_6375_, lean_object* v___y_6376_, lean_object* v___y_6377_, lean_object* v___y_6378_, lean_object* v___y_6379_, lean_object* v___y_6380_, lean_object* v___y_6381_, lean_object* v___y_6382_){
_start:
{
lean_object* v___x_6384_; 
v___x_6384_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v_x_6373_, v_mkInfoTree_6374_, v___y_6375_, v___y_6376_, v___y_6377_, v___y_6378_, v___y_6379_, v___y_6380_, v___y_6381_, v___y_6382_);
return v___x_6384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___boxed(lean_object* v_00_u03b1_6385_, lean_object* v_x_6386_, lean_object* v_mkInfoTree_6387_, lean_object* v___y_6388_, lean_object* v___y_6389_, lean_object* v___y_6390_, lean_object* v___y_6391_, lean_object* v___y_6392_, lean_object* v___y_6393_, lean_object* v___y_6394_, lean_object* v___y_6395_, lean_object* v___y_6396_){
_start:
{
lean_object* v_res_6397_; 
v_res_6397_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3(v_00_u03b1_6385_, v_x_6386_, v_mkInfoTree_6387_, v___y_6388_, v___y_6389_, v___y_6390_, v___y_6391_, v___y_6392_, v___y_6393_, v___y_6394_, v___y_6395_);
lean_dec(v___y_6395_);
lean_dec_ref(v___y_6394_);
lean_dec(v___y_6393_);
lean_dec_ref(v___y_6392_);
lean_dec(v___y_6391_);
lean_dec_ref(v___y_6390_);
lean_dec(v___y_6389_);
lean_dec_ref(v___y_6388_);
return v_res_6397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5(lean_object* v_as_6398_, size_t v_i_6399_, size_t v_stop_6400_, lean_object* v_b_6401_, lean_object* v___y_6402_, lean_object* v___y_6403_, lean_object* v___y_6404_, lean_object* v___y_6405_, lean_object* v___y_6406_, lean_object* v___y_6407_){
_start:
{
lean_object* v___x_6409_; 
v___x_6409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v_as_6398_, v_i_6399_, v_stop_6400_, v_b_6401_, v___y_6404_, v___y_6405_, v___y_6406_, v___y_6407_);
return v___x_6409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___boxed(lean_object* v_as_6410_, lean_object* v_i_6411_, lean_object* v_stop_6412_, lean_object* v_b_6413_, lean_object* v___y_6414_, lean_object* v___y_6415_, lean_object* v___y_6416_, lean_object* v___y_6417_, lean_object* v___y_6418_, lean_object* v___y_6419_, lean_object* v___y_6420_){
_start:
{
size_t v_i_boxed_6421_; size_t v_stop_boxed_6422_; lean_object* v_res_6423_; 
v_i_boxed_6421_ = lean_unbox_usize(v_i_6411_);
lean_dec(v_i_6411_);
v_stop_boxed_6422_ = lean_unbox_usize(v_stop_6412_);
lean_dec(v_stop_6412_);
v_res_6423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5(v_as_6410_, v_i_boxed_6421_, v_stop_boxed_6422_, v_b_6413_, v___y_6414_, v___y_6415_, v___y_6416_, v___y_6417_, v___y_6418_, v___y_6419_);
lean_dec(v___y_6419_);
lean_dec_ref(v___y_6418_);
lean_dec(v___y_6417_);
lean_dec_ref(v___y_6416_);
lean_dec(v___y_6415_);
lean_dec_ref(v___y_6414_);
lean_dec_ref(v_as_6410_);
return v_res_6423_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10(lean_object* v_00_u03b1_6424_, lean_object* v_x_6425_, uint8_t v_isExporting_6426_, lean_object* v___y_6427_, lean_object* v___y_6428_, lean_object* v___y_6429_, lean_object* v___y_6430_){
_start:
{
lean_object* v___x_6432_; 
v___x_6432_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6425_, v_isExporting_6426_, v___y_6427_, v___y_6428_, v___y_6429_, v___y_6430_);
return v___x_6432_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___boxed(lean_object* v_00_u03b1_6433_, lean_object* v_x_6434_, lean_object* v_isExporting_6435_, lean_object* v___y_6436_, lean_object* v___y_6437_, lean_object* v___y_6438_, lean_object* v___y_6439_, lean_object* v___y_6440_){
_start:
{
uint8_t v_isExporting_boxed_6441_; lean_object* v_res_6442_; 
v_isExporting_boxed_6441_ = lean_unbox(v_isExporting_6435_);
v_res_6442_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10(v_00_u03b1_6433_, v_x_6434_, v_isExporting_boxed_6441_, v___y_6436_, v___y_6437_, v___y_6438_, v___y_6439_);
lean_dec(v___y_6439_);
lean_dec_ref(v___y_6438_);
lean_dec(v___y_6437_);
lean_dec_ref(v___y_6436_);
return v_res_6442_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8(lean_object* v_00_u03b1_6443_, lean_object* v_x_6444_, uint8_t v_when_6445_, lean_object* v___y_6446_, lean_object* v___y_6447_, lean_object* v___y_6448_, lean_object* v___y_6449_){
_start:
{
lean_object* v___x_6451_; 
v___x_6451_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v_x_6444_, v_when_6445_, v___y_6446_, v___y_6447_, v___y_6448_, v___y_6449_);
return v___x_6451_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___boxed(lean_object* v_00_u03b1_6452_, lean_object* v_x_6453_, lean_object* v_when_6454_, lean_object* v___y_6455_, lean_object* v___y_6456_, lean_object* v___y_6457_, lean_object* v___y_6458_, lean_object* v___y_6459_){
_start:
{
uint8_t v_when_boxed_6460_; lean_object* v_res_6461_; 
v_when_boxed_6460_ = lean_unbox(v_when_6454_);
v_res_6461_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8(v_00_u03b1_6452_, v_x_6453_, v_when_boxed_6460_, v___y_6455_, v___y_6456_, v___y_6457_, v___y_6458_);
lean_dec(v___y_6458_);
lean_dec_ref(v___y_6457_);
lean_dec(v___y_6456_);
lean_dec_ref(v___y_6455_);
return v_res_6461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1(lean_object* v_msgData_6462_, lean_object* v_macroStack_6463_, lean_object* v___y_6464_, lean_object* v___y_6465_, lean_object* v___y_6466_, lean_object* v___y_6467_, lean_object* v___y_6468_, lean_object* v___y_6469_){
_start:
{
lean_object* v___x_6471_; 
v___x_6471_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_msgData_6462_, v_macroStack_6463_, v___y_6468_);
return v___x_6471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___boxed(lean_object* v_msgData_6472_, lean_object* v_macroStack_6473_, lean_object* v___y_6474_, lean_object* v___y_6475_, lean_object* v___y_6476_, lean_object* v___y_6477_, lean_object* v___y_6478_, lean_object* v___y_6479_, lean_object* v___y_6480_){
_start:
{
lean_object* v_res_6481_; 
v_res_6481_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1(v_msgData_6472_, v_macroStack_6473_, v___y_6474_, v___y_6475_, v___y_6476_, v___y_6477_, v___y_6478_, v___y_6479_);
lean_dec(v___y_6479_);
lean_dec_ref(v___y_6478_);
lean_dec(v___y_6477_);
lean_dec_ref(v___y_6476_);
lean_dec(v___y_6475_);
lean_dec_ref(v___y_6474_);
return v_res_6481_;
}
}
static lean_object* _init_l_Lean_Elab_WF_isNatLtWF___closed__4(void){
_start:
{
lean_object* v___x_6488_; lean_object* v___x_6489_; lean_object* v___x_6490_; 
v___x_6488_ = lean_box(0);
v___x_6489_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__3));
v___x_6490_ = l_Lean_mkConst(v___x_6489_, v___x_6488_);
return v___x_6490_;
}
}
static lean_object* _init_l_Lean_Elab_WF_isNatLtWF___closed__7(void){
_start:
{
lean_object* v___x_6495_; lean_object* v___x_6496_; lean_object* v___x_6497_; 
v___x_6495_ = lean_box(0);
v___x_6496_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__6));
v___x_6497_ = l_Lean_mkConst(v___x_6496_, v___x_6495_);
return v___x_6497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isNatLtWF(lean_object* v_wfRel_6498_, lean_object* v_a_6499_, lean_object* v_a_6500_, lean_object* v_a_6501_, lean_object* v_a_6502_){
_start:
{
lean_object* v___x_6504_; 
v___x_6504_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_wfRel_6498_, v_a_6500_);
if (lean_obj_tag(v___x_6504_) == 0)
{
lean_object* v_a_6505_; lean_object* v___x_6507_; uint8_t v_isShared_6508_; uint8_t v_isSharedCheck_6572_; 
v_a_6505_ = lean_ctor_get(v___x_6504_, 0);
v_isSharedCheck_6572_ = !lean_is_exclusive(v___x_6504_);
if (v_isSharedCheck_6572_ == 0)
{
v___x_6507_ = v___x_6504_;
v_isShared_6508_ = v_isSharedCheck_6572_;
goto v_resetjp_6506_;
}
else
{
lean_inc(v_a_6505_);
lean_dec(v___x_6504_);
v___x_6507_ = lean_box(0);
v_isShared_6508_ = v_isSharedCheck_6572_;
goto v_resetjp_6506_;
}
v_resetjp_6506_:
{
lean_object* v___x_6514_; uint8_t v___x_6515_; 
v___x_6514_ = l_Lean_Expr_cleanupAnnotations(v_a_6505_);
v___x_6515_ = l_Lean_Expr_isApp(v___x_6514_);
if (v___x_6515_ == 0)
{
lean_dec_ref(v___x_6514_);
goto v___jp_6509_;
}
else
{
lean_object* v_arg_6516_; lean_object* v___x_6517_; uint8_t v___x_6518_; 
v_arg_6516_ = lean_ctor_get(v___x_6514_, 1);
lean_inc_ref(v_arg_6516_);
v___x_6517_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6514_);
v___x_6518_ = l_Lean_Expr_isApp(v___x_6517_);
if (v___x_6518_ == 0)
{
lean_dec_ref(v___x_6517_);
lean_dec_ref(v_arg_6516_);
goto v___jp_6509_;
}
else
{
lean_object* v_arg_6519_; lean_object* v___x_6520_; uint8_t v___x_6521_; 
v_arg_6519_ = lean_ctor_get(v___x_6517_, 1);
lean_inc_ref(v_arg_6519_);
v___x_6520_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6517_);
v___x_6521_ = l_Lean_Expr_isApp(v___x_6520_);
if (v___x_6521_ == 0)
{
lean_dec_ref(v___x_6520_);
lean_dec_ref(v_arg_6519_);
lean_dec_ref(v_arg_6516_);
goto v___jp_6509_;
}
else
{
lean_object* v_arg_6522_; lean_object* v___x_6523_; uint8_t v___x_6524_; 
v_arg_6522_ = lean_ctor_get(v___x_6520_, 1);
lean_inc_ref(v_arg_6522_);
v___x_6523_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6520_);
v___x_6524_ = l_Lean_Expr_isApp(v___x_6523_);
if (v___x_6524_ == 0)
{
lean_dec_ref(v___x_6523_);
lean_dec_ref(v_arg_6522_);
lean_dec_ref(v_arg_6519_);
lean_dec_ref(v_arg_6516_);
goto v___jp_6509_;
}
else
{
lean_object* v___x_6525_; lean_object* v___x_6526_; uint8_t v___x_6527_; 
v___x_6525_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6523_);
v___x_6526_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__1));
v___x_6527_ = l_Lean_Expr_isConstOf(v___x_6525_, v___x_6526_);
lean_dec_ref(v___x_6525_);
if (v___x_6527_ == 0)
{
lean_dec_ref(v_arg_6522_);
lean_dec_ref(v_arg_6519_);
lean_dec_ref(v_arg_6516_);
goto v___jp_6509_;
}
else
{
lean_object* v___x_6528_; lean_object* v___x_6529_; 
lean_del_object(v___x_6507_);
v___x_6528_ = lean_obj_once(&l_Lean_Elab_WF_isNatLtWF___closed__4, &l_Lean_Elab_WF_isNatLtWF___closed__4_once, _init_l_Lean_Elab_WF_isNatLtWF___closed__4);
v___x_6529_ = l_Lean_Meta_isExprDefEq(v_arg_6522_, v___x_6528_, v_a_6499_, v_a_6500_, v_a_6501_, v_a_6502_);
if (lean_obj_tag(v___x_6529_) == 0)
{
lean_object* v_a_6530_; lean_object* v___x_6532_; uint8_t v_isShared_6533_; uint8_t v_isSharedCheck_6563_; 
v_a_6530_ = lean_ctor_get(v___x_6529_, 0);
v_isSharedCheck_6563_ = !lean_is_exclusive(v___x_6529_);
if (v_isSharedCheck_6563_ == 0)
{
v___x_6532_ = v___x_6529_;
v_isShared_6533_ = v_isSharedCheck_6563_;
goto v_resetjp_6531_;
}
else
{
lean_inc(v_a_6530_);
lean_dec(v___x_6529_);
v___x_6532_ = lean_box(0);
v_isShared_6533_ = v_isSharedCheck_6563_;
goto v_resetjp_6531_;
}
v_resetjp_6531_:
{
uint8_t v___x_6534_; 
v___x_6534_ = lean_unbox(v_a_6530_);
lean_dec(v_a_6530_);
if (v___x_6534_ == 0)
{
lean_object* v___x_6535_; lean_object* v___x_6537_; 
lean_dec_ref(v_arg_6519_);
lean_dec_ref(v_arg_6516_);
v___x_6535_ = lean_box(0);
if (v_isShared_6533_ == 0)
{
lean_ctor_set(v___x_6532_, 0, v___x_6535_);
v___x_6537_ = v___x_6532_;
goto v_reusejp_6536_;
}
else
{
lean_object* v_reuseFailAlloc_6538_; 
v_reuseFailAlloc_6538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6538_, 0, v___x_6535_);
v___x_6537_ = v_reuseFailAlloc_6538_;
goto v_reusejp_6536_;
}
v_reusejp_6536_:
{
return v___x_6537_;
}
}
else
{
lean_object* v___x_6539_; lean_object* v___x_6540_; 
lean_del_object(v___x_6532_);
v___x_6539_ = lean_obj_once(&l_Lean_Elab_WF_isNatLtWF___closed__7, &l_Lean_Elab_WF_isNatLtWF___closed__7_once, _init_l_Lean_Elab_WF_isNatLtWF___closed__7);
v___x_6540_ = l_Lean_Meta_isExprDefEq(v_arg_6516_, v___x_6539_, v_a_6499_, v_a_6500_, v_a_6501_, v_a_6502_);
if (lean_obj_tag(v___x_6540_) == 0)
{
lean_object* v_a_6541_; lean_object* v___x_6543_; uint8_t v_isShared_6544_; uint8_t v_isSharedCheck_6554_; 
v_a_6541_ = lean_ctor_get(v___x_6540_, 0);
v_isSharedCheck_6554_ = !lean_is_exclusive(v___x_6540_);
if (v_isSharedCheck_6554_ == 0)
{
v___x_6543_ = v___x_6540_;
v_isShared_6544_ = v_isSharedCheck_6554_;
goto v_resetjp_6542_;
}
else
{
lean_inc(v_a_6541_);
lean_dec(v___x_6540_);
v___x_6543_ = lean_box(0);
v_isShared_6544_ = v_isSharedCheck_6554_;
goto v_resetjp_6542_;
}
v_resetjp_6542_:
{
uint8_t v___x_6545_; 
v___x_6545_ = lean_unbox(v_a_6541_);
lean_dec(v_a_6541_);
if (v___x_6545_ == 0)
{
lean_object* v___x_6546_; lean_object* v___x_6548_; 
lean_dec_ref(v_arg_6519_);
v___x_6546_ = lean_box(0);
if (v_isShared_6544_ == 0)
{
lean_ctor_set(v___x_6543_, 0, v___x_6546_);
v___x_6548_ = v___x_6543_;
goto v_reusejp_6547_;
}
else
{
lean_object* v_reuseFailAlloc_6549_; 
v_reuseFailAlloc_6549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6549_, 0, v___x_6546_);
v___x_6548_ = v_reuseFailAlloc_6549_;
goto v_reusejp_6547_;
}
v_reusejp_6547_:
{
return v___x_6548_;
}
}
else
{
lean_object* v___x_6550_; lean_object* v___x_6552_; 
v___x_6550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6550_, 0, v_arg_6519_);
if (v_isShared_6544_ == 0)
{
lean_ctor_set(v___x_6543_, 0, v___x_6550_);
v___x_6552_ = v___x_6543_;
goto v_reusejp_6551_;
}
else
{
lean_object* v_reuseFailAlloc_6553_; 
v_reuseFailAlloc_6553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6553_, 0, v___x_6550_);
v___x_6552_ = v_reuseFailAlloc_6553_;
goto v_reusejp_6551_;
}
v_reusejp_6551_:
{
return v___x_6552_;
}
}
}
}
else
{
lean_object* v_a_6555_; lean_object* v___x_6557_; uint8_t v_isShared_6558_; uint8_t v_isSharedCheck_6562_; 
lean_dec_ref(v_arg_6519_);
v_a_6555_ = lean_ctor_get(v___x_6540_, 0);
v_isSharedCheck_6562_ = !lean_is_exclusive(v___x_6540_);
if (v_isSharedCheck_6562_ == 0)
{
v___x_6557_ = v___x_6540_;
v_isShared_6558_ = v_isSharedCheck_6562_;
goto v_resetjp_6556_;
}
else
{
lean_inc(v_a_6555_);
lean_dec(v___x_6540_);
v___x_6557_ = lean_box(0);
v_isShared_6558_ = v_isSharedCheck_6562_;
goto v_resetjp_6556_;
}
v_resetjp_6556_:
{
lean_object* v___x_6560_; 
if (v_isShared_6558_ == 0)
{
v___x_6560_ = v___x_6557_;
goto v_reusejp_6559_;
}
else
{
lean_object* v_reuseFailAlloc_6561_; 
v_reuseFailAlloc_6561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6561_, 0, v_a_6555_);
v___x_6560_ = v_reuseFailAlloc_6561_;
goto v_reusejp_6559_;
}
v_reusejp_6559_:
{
return v___x_6560_;
}
}
}
}
}
}
else
{
lean_object* v_a_6564_; lean_object* v___x_6566_; uint8_t v_isShared_6567_; uint8_t v_isSharedCheck_6571_; 
lean_dec_ref(v_arg_6519_);
lean_dec_ref(v_arg_6516_);
v_a_6564_ = lean_ctor_get(v___x_6529_, 0);
v_isSharedCheck_6571_ = !lean_is_exclusive(v___x_6529_);
if (v_isSharedCheck_6571_ == 0)
{
v___x_6566_ = v___x_6529_;
v_isShared_6567_ = v_isSharedCheck_6571_;
goto v_resetjp_6565_;
}
else
{
lean_inc(v_a_6564_);
lean_dec(v___x_6529_);
v___x_6566_ = lean_box(0);
v_isShared_6567_ = v_isSharedCheck_6571_;
goto v_resetjp_6565_;
}
v_resetjp_6565_:
{
lean_object* v___x_6569_; 
if (v_isShared_6567_ == 0)
{
v___x_6569_ = v___x_6566_;
goto v_reusejp_6568_;
}
else
{
lean_object* v_reuseFailAlloc_6570_; 
v_reuseFailAlloc_6570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6570_, 0, v_a_6564_);
v___x_6569_ = v_reuseFailAlloc_6570_;
goto v_reusejp_6568_;
}
v_reusejp_6568_:
{
return v___x_6569_;
}
}
}
}
}
}
}
}
v___jp_6509_:
{
lean_object* v___x_6510_; lean_object* v___x_6512_; 
v___x_6510_ = lean_box(0);
if (v_isShared_6508_ == 0)
{
lean_ctor_set(v___x_6507_, 0, v___x_6510_);
v___x_6512_ = v___x_6507_;
goto v_reusejp_6511_;
}
else
{
lean_object* v_reuseFailAlloc_6513_; 
v_reuseFailAlloc_6513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6513_, 0, v___x_6510_);
v___x_6512_ = v_reuseFailAlloc_6513_;
goto v_reusejp_6511_;
}
v_reusejp_6511_:
{
return v___x_6512_;
}
}
}
}
else
{
lean_object* v_a_6573_; lean_object* v___x_6575_; uint8_t v_isShared_6576_; uint8_t v_isSharedCheck_6580_; 
v_a_6573_ = lean_ctor_get(v___x_6504_, 0);
v_isSharedCheck_6580_ = !lean_is_exclusive(v___x_6504_);
if (v_isSharedCheck_6580_ == 0)
{
v___x_6575_ = v___x_6504_;
v_isShared_6576_ = v_isSharedCheck_6580_;
goto v_resetjp_6574_;
}
else
{
lean_inc(v_a_6573_);
lean_dec(v___x_6504_);
v___x_6575_ = lean_box(0);
v_isShared_6576_ = v_isSharedCheck_6580_;
goto v_resetjp_6574_;
}
v_resetjp_6574_:
{
lean_object* v___x_6578_; 
if (v_isShared_6576_ == 0)
{
v___x_6578_ = v___x_6575_;
goto v_reusejp_6577_;
}
else
{
lean_object* v_reuseFailAlloc_6579_; 
v_reuseFailAlloc_6579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6579_, 0, v_a_6573_);
v___x_6578_ = v_reuseFailAlloc_6579_;
goto v_reusejp_6577_;
}
v_reusejp_6577_:
{
return v___x_6578_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isNatLtWF___boxed(lean_object* v_wfRel_6581_, lean_object* v_a_6582_, lean_object* v_a_6583_, lean_object* v_a_6584_, lean_object* v_a_6585_, lean_object* v_a_6586_){
_start:
{
lean_object* v_res_6587_; 
v_res_6587_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_6581_, v_a_6582_, v_a_6583_, v_a_6584_, v_a_6585_);
lean_dec(v_a_6585_);
lean_dec_ref(v_a_6584_);
lean_dec(v_a_6583_);
lean_dec_ref(v_a_6582_);
return v_res_6587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(lean_object* v_type_6588_, lean_object* v_maxFVars_x3f_6589_, lean_object* v_k_6590_, uint8_t v_cleanupAnnotations_6591_, uint8_t v_whnfType_6592_, lean_object* v___y_6593_, lean_object* v___y_6594_, lean_object* v___y_6595_, lean_object* v___y_6596_, lean_object* v___y_6597_, lean_object* v___y_6598_){
_start:
{
lean_object* v___f_6600_; lean_object* v___x_6601_; 
lean_inc(v___y_6594_);
lean_inc_ref(v___y_6593_);
v___f_6600_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_6600_, 0, v_k_6590_);
lean_closure_set(v___f_6600_, 1, v___y_6593_);
lean_closure_set(v___f_6600_, 2, v___y_6594_);
v___x_6601_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_6588_, v_maxFVars_x3f_6589_, v___f_6600_, v_cleanupAnnotations_6591_, v_whnfType_6592_, v___y_6595_, v___y_6596_, v___y_6597_, v___y_6598_);
if (lean_obj_tag(v___x_6601_) == 0)
{
return v___x_6601_;
}
else
{
lean_object* v_a_6602_; lean_object* v___x_6604_; uint8_t v_isShared_6605_; uint8_t v_isSharedCheck_6609_; 
v_a_6602_ = lean_ctor_get(v___x_6601_, 0);
v_isSharedCheck_6609_ = !lean_is_exclusive(v___x_6601_);
if (v_isSharedCheck_6609_ == 0)
{
v___x_6604_ = v___x_6601_;
v_isShared_6605_ = v_isSharedCheck_6609_;
goto v_resetjp_6603_;
}
else
{
lean_inc(v_a_6602_);
lean_dec(v___x_6601_);
v___x_6604_ = lean_box(0);
v_isShared_6605_ = v_isSharedCheck_6609_;
goto v_resetjp_6603_;
}
v_resetjp_6603_:
{
lean_object* v___x_6607_; 
if (v_isShared_6605_ == 0)
{
v___x_6607_ = v___x_6604_;
goto v_reusejp_6606_;
}
else
{
lean_object* v_reuseFailAlloc_6608_; 
v_reuseFailAlloc_6608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6608_, 0, v_a_6602_);
v___x_6607_ = v_reuseFailAlloc_6608_;
goto v_reusejp_6606_;
}
v_reusejp_6606_:
{
return v___x_6607_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg___boxed(lean_object* v_type_6610_, lean_object* v_maxFVars_x3f_6611_, lean_object* v_k_6612_, lean_object* v_cleanupAnnotations_6613_, lean_object* v_whnfType_6614_, lean_object* v___y_6615_, lean_object* v___y_6616_, lean_object* v___y_6617_, lean_object* v___y_6618_, lean_object* v___y_6619_, lean_object* v___y_6620_, lean_object* v___y_6621_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_6622_; uint8_t v_whnfType_boxed_6623_; lean_object* v_res_6624_; 
v_cleanupAnnotations_boxed_6622_ = lean_unbox(v_cleanupAnnotations_6613_);
v_whnfType_boxed_6623_ = lean_unbox(v_whnfType_6614_);
v_res_6624_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_type_6610_, v_maxFVars_x3f_6611_, v_k_6612_, v_cleanupAnnotations_boxed_6622_, v_whnfType_boxed_6623_, v___y_6615_, v___y_6616_, v___y_6617_, v___y_6618_, v___y_6619_, v___y_6620_);
lean_dec(v___y_6620_);
lean_dec_ref(v___y_6619_);
lean_dec(v___y_6618_);
lean_dec_ref(v___y_6617_);
lean_dec(v___y_6616_);
lean_dec_ref(v___y_6615_);
return v_res_6624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0(lean_object* v_00_u03b1_6625_, lean_object* v_type_6626_, lean_object* v_maxFVars_x3f_6627_, lean_object* v_k_6628_, uint8_t v_cleanupAnnotations_6629_, uint8_t v_whnfType_6630_, lean_object* v___y_6631_, lean_object* v___y_6632_, lean_object* v___y_6633_, lean_object* v___y_6634_, lean_object* v___y_6635_, lean_object* v___y_6636_){
_start:
{
lean_object* v___x_6638_; 
v___x_6638_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_type_6626_, v_maxFVars_x3f_6627_, v_k_6628_, v_cleanupAnnotations_6629_, v_whnfType_6630_, v___y_6631_, v___y_6632_, v___y_6633_, v___y_6634_, v___y_6635_, v___y_6636_);
return v___x_6638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___boxed(lean_object* v_00_u03b1_6639_, lean_object* v_type_6640_, lean_object* v_maxFVars_x3f_6641_, lean_object* v_k_6642_, lean_object* v_cleanupAnnotations_6643_, lean_object* v_whnfType_6644_, lean_object* v___y_6645_, lean_object* v___y_6646_, lean_object* v___y_6647_, lean_object* v___y_6648_, lean_object* v___y_6649_, lean_object* v___y_6650_, lean_object* v___y_6651_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_6652_; uint8_t v_whnfType_boxed_6653_; lean_object* v_res_6654_; 
v_cleanupAnnotations_boxed_6652_ = lean_unbox(v_cleanupAnnotations_6643_);
v_whnfType_boxed_6653_ = lean_unbox(v_whnfType_6644_);
v_res_6654_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0(v_00_u03b1_6639_, v_type_6640_, v_maxFVars_x3f_6641_, v_k_6642_, v_cleanupAnnotations_boxed_6652_, v_whnfType_boxed_6653_, v___y_6645_, v___y_6646_, v___y_6647_, v___y_6648_, v___y_6649_, v___y_6650_);
lean_dec(v___y_6650_);
lean_dec_ref(v___y_6649_);
lean_dec(v___y_6648_);
lean_dec_ref(v___y_6647_);
lean_dec(v___y_6646_);
lean_dec_ref(v___y_6645_);
return v_res_6654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(lean_object* v_lctx_6655_, lean_object* v_x_6656_, lean_object* v___y_6657_, lean_object* v___y_6658_, lean_object* v___y_6659_, lean_object* v___y_6660_, lean_object* v___y_6661_, lean_object* v___y_6662_){
_start:
{
lean_object* v_keyedConfig_6664_; uint8_t v_trackZetaDelta_6665_; lean_object* v_zetaDeltaSet_6666_; lean_object* v_localInstances_6667_; lean_object* v_defEqCtx_x3f_6668_; lean_object* v_synthPendingDepth_6669_; lean_object* v_customCanUnfoldPredicate_x3f_6670_; uint8_t v_univApprox_6671_; uint8_t v_inTypeClassResolution_6672_; uint8_t v_cacheInferType_6673_; lean_object* v___x_6674_; lean_object* v___x_6675_; 
v_keyedConfig_6664_ = lean_ctor_get(v___y_6659_, 0);
v_trackZetaDelta_6665_ = lean_ctor_get_uint8(v___y_6659_, sizeof(void*)*7);
v_zetaDeltaSet_6666_ = lean_ctor_get(v___y_6659_, 1);
v_localInstances_6667_ = lean_ctor_get(v___y_6659_, 3);
v_defEqCtx_x3f_6668_ = lean_ctor_get(v___y_6659_, 4);
v_synthPendingDepth_6669_ = lean_ctor_get(v___y_6659_, 5);
v_customCanUnfoldPredicate_x3f_6670_ = lean_ctor_get(v___y_6659_, 6);
v_univApprox_6671_ = lean_ctor_get_uint8(v___y_6659_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_6672_ = lean_ctor_get_uint8(v___y_6659_, sizeof(void*)*7 + 2);
v_cacheInferType_6673_ = lean_ctor_get_uint8(v___y_6659_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_6670_);
lean_inc(v_synthPendingDepth_6669_);
lean_inc(v_defEqCtx_x3f_6668_);
lean_inc_ref(v_localInstances_6667_);
lean_inc(v_zetaDeltaSet_6666_);
lean_inc_ref(v_keyedConfig_6664_);
v___x_6674_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6674_, 0, v_keyedConfig_6664_);
lean_ctor_set(v___x_6674_, 1, v_zetaDeltaSet_6666_);
lean_ctor_set(v___x_6674_, 2, v_lctx_6655_);
lean_ctor_set(v___x_6674_, 3, v_localInstances_6667_);
lean_ctor_set(v___x_6674_, 4, v_defEqCtx_x3f_6668_);
lean_ctor_set(v___x_6674_, 5, v_synthPendingDepth_6669_);
lean_ctor_set(v___x_6674_, 6, v_customCanUnfoldPredicate_x3f_6670_);
lean_ctor_set_uint8(v___x_6674_, sizeof(void*)*7, v_trackZetaDelta_6665_);
lean_ctor_set_uint8(v___x_6674_, sizeof(void*)*7 + 1, v_univApprox_6671_);
lean_ctor_set_uint8(v___x_6674_, sizeof(void*)*7 + 2, v_inTypeClassResolution_6672_);
lean_ctor_set_uint8(v___x_6674_, sizeof(void*)*7 + 3, v_cacheInferType_6673_);
lean_inc(v___y_6662_);
lean_inc_ref(v___y_6661_);
lean_inc(v___y_6660_);
lean_inc(v___y_6658_);
lean_inc_ref(v___y_6657_);
v___x_6675_ = lean_apply_7(v_x_6656_, v___y_6657_, v___y_6658_, v___x_6674_, v___y_6660_, v___y_6661_, v___y_6662_, lean_box(0));
if (lean_obj_tag(v___x_6675_) == 0)
{
lean_object* v_a_6676_; lean_object* v___x_6678_; uint8_t v_isShared_6679_; uint8_t v_isSharedCheck_6683_; 
v_a_6676_ = lean_ctor_get(v___x_6675_, 0);
v_isSharedCheck_6683_ = !lean_is_exclusive(v___x_6675_);
if (v_isSharedCheck_6683_ == 0)
{
v___x_6678_ = v___x_6675_;
v_isShared_6679_ = v_isSharedCheck_6683_;
goto v_resetjp_6677_;
}
else
{
lean_inc(v_a_6676_);
lean_dec(v___x_6675_);
v___x_6678_ = lean_box(0);
v_isShared_6679_ = v_isSharedCheck_6683_;
goto v_resetjp_6677_;
}
v_resetjp_6677_:
{
lean_object* v___x_6681_; 
if (v_isShared_6679_ == 0)
{
v___x_6681_ = v___x_6678_;
goto v_reusejp_6680_;
}
else
{
lean_object* v_reuseFailAlloc_6682_; 
v_reuseFailAlloc_6682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6682_, 0, v_a_6676_);
v___x_6681_ = v_reuseFailAlloc_6682_;
goto v_reusejp_6680_;
}
v_reusejp_6680_:
{
return v___x_6681_;
}
}
}
else
{
return v___x_6675_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg___boxed(lean_object* v_lctx_6684_, lean_object* v_x_6685_, lean_object* v___y_6686_, lean_object* v___y_6687_, lean_object* v___y_6688_, lean_object* v___y_6689_, lean_object* v___y_6690_, lean_object* v___y_6691_, lean_object* v___y_6692_){
_start:
{
lean_object* v_res_6693_; 
v_res_6693_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v_lctx_6684_, v_x_6685_, v___y_6686_, v___y_6687_, v___y_6688_, v___y_6689_, v___y_6690_, v___y_6691_);
lean_dec(v___y_6691_);
lean_dec_ref(v___y_6690_);
lean_dec(v___y_6689_);
lean_dec_ref(v___y_6688_);
lean_dec(v___y_6687_);
lean_dec_ref(v___y_6686_);
return v_res_6693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1(lean_object* v_00_u03b1_6694_, lean_object* v_lctx_6695_, lean_object* v_x_6696_, lean_object* v___y_6697_, lean_object* v___y_6698_, lean_object* v___y_6699_, lean_object* v___y_6700_, lean_object* v___y_6701_, lean_object* v___y_6702_){
_start:
{
lean_object* v___x_6704_; 
v___x_6704_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v_lctx_6695_, v_x_6696_, v___y_6697_, v___y_6698_, v___y_6699_, v___y_6700_, v___y_6701_, v___y_6702_);
return v___x_6704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___boxed(lean_object* v_00_u03b1_6705_, lean_object* v_lctx_6706_, lean_object* v_x_6707_, lean_object* v___y_6708_, lean_object* v___y_6709_, lean_object* v___y_6710_, lean_object* v___y_6711_, lean_object* v___y_6712_, lean_object* v___y_6713_, lean_object* v___y_6714_){
_start:
{
lean_object* v_res_6715_; 
v_res_6715_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1(v_00_u03b1_6705_, v_lctx_6706_, v_x_6707_, v___y_6708_, v___y_6709_, v___y_6710_, v___y_6711_, v___y_6712_, v___y_6713_);
lean_dec(v___y_6713_);
lean_dec_ref(v___y_6712_);
lean_dec(v___y_6711_);
lean_dec_ref(v___y_6710_);
lean_dec(v___y_6709_);
lean_dec_ref(v___y_6708_);
return v_res_6715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__0(lean_object* v___x_6732_, lean_object* v___x_6733_, lean_object* v_wfRel_6734_, lean_object* v_x_6735_, lean_object* v_type_6736_, lean_object* v___y_6737_, lean_object* v___y_6738_, lean_object* v___y_6739_, lean_object* v___y_6740_, lean_object* v___y_6741_, lean_object* v___y_6742_){
_start:
{
lean_object* v___x_6744_; lean_object* v___x_6745_; lean_object* v___x_6746_; lean_object* v___x_6747_; 
v___x_6744_ = lean_unsigned_to_nat(0u);
v___x_6745_ = lean_array_get_borrowed(v___x_6732_, v_x_6735_, v___x_6744_);
v___x_6746_ = l_Lean_Expr_fvarId_x21(v___x_6745_);
v___x_6747_ = l_Lean_FVarId_getUserName___redArg(v___x_6746_, v___y_6739_, v___y_6741_, v___y_6742_);
if (lean_obj_tag(v___x_6747_) == 0)
{
lean_object* v_a_6748_; lean_object* v___x_6749_; 
v_a_6748_ = lean_ctor_get(v___x_6747_, 0);
lean_inc(v_a_6748_);
lean_dec_ref_known(v___x_6747_, 1);
lean_inc(v___y_6742_);
lean_inc_ref(v___y_6741_);
lean_inc(v___y_6740_);
lean_inc_ref(v___y_6739_);
lean_inc(v___x_6745_);
v___x_6749_ = lean_infer_type(v___x_6745_, v___y_6739_, v___y_6740_, v___y_6741_, v___y_6742_);
if (lean_obj_tag(v___x_6749_) == 0)
{
lean_object* v_a_6750_; lean_object* v___x_6751_; 
v_a_6750_ = lean_ctor_get(v___x_6749_, 0);
lean_inc_n(v_a_6750_, 2);
lean_dec_ref_known(v___x_6749_, 1);
v___x_6751_ = l_Lean_Meta_getLevel(v_a_6750_, v___y_6739_, v___y_6740_, v___y_6741_, v___y_6742_);
if (lean_obj_tag(v___x_6751_) == 0)
{
lean_object* v_a_6752_; lean_object* v___x_6753_; 
v_a_6752_ = lean_ctor_get(v___x_6751_, 0);
lean_inc(v_a_6752_);
lean_dec_ref_known(v___x_6751_, 1);
lean_inc_ref(v_type_6736_);
v___x_6753_ = l_Lean_Meta_getLevel(v_type_6736_, v___y_6739_, v___y_6740_, v___y_6741_, v___y_6742_);
if (lean_obj_tag(v___x_6753_) == 0)
{
lean_object* v_a_6754_; lean_object* v___x_6755_; lean_object* v___x_6756_; uint8_t v___x_6757_; uint8_t v___x_6758_; uint8_t v___x_6759_; lean_object* v___x_6760_; 
v_a_6754_ = lean_ctor_get(v___x_6753_, 0);
lean_inc(v_a_6754_);
lean_dec_ref_known(v___x_6753_, 1);
v___x_6755_ = lean_mk_empty_array_with_capacity(v___x_6733_);
lean_inc(v___x_6745_);
lean_inc_ref(v___x_6755_);
v___x_6756_ = lean_array_push(v___x_6755_, v___x_6745_);
v___x_6757_ = 0;
v___x_6758_ = 1;
v___x_6759_ = 1;
v___x_6760_ = l_Lean_Meta_mkLambdaFVars(v___x_6756_, v_type_6736_, v___x_6757_, v___x_6758_, v___x_6757_, v___x_6758_, v___x_6759_, v___y_6739_, v___y_6740_, v___y_6741_, v___y_6742_);
lean_dec_ref(v___x_6756_);
if (lean_obj_tag(v___x_6760_) == 0)
{
lean_object* v_a_6761_; lean_object* v___x_6762_; 
v_a_6761_ = lean_ctor_get(v___x_6760_, 0);
lean_inc(v_a_6761_);
lean_dec_ref_known(v___x_6760_, 1);
lean_inc_ref(v_wfRel_6734_);
v___x_6762_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_6734_, v___y_6739_, v___y_6740_, v___y_6741_, v___y_6742_);
if (lean_obj_tag(v___x_6762_) == 0)
{
lean_object* v_a_6763_; lean_object* v___x_6765_; uint8_t v_isShared_6766_; uint8_t v_isSharedCheck_6807_; 
v_a_6763_ = lean_ctor_get(v___x_6762_, 0);
v_isSharedCheck_6807_ = !lean_is_exclusive(v___x_6762_);
if (v_isSharedCheck_6807_ == 0)
{
v___x_6765_ = v___x_6762_;
v_isShared_6766_ = v_isSharedCheck_6807_;
goto v_resetjp_6764_;
}
else
{
lean_inc(v_a_6763_);
lean_dec(v___x_6762_);
v___x_6765_ = lean_box(0);
v_isShared_6766_ = v_isSharedCheck_6807_;
goto v_resetjp_6764_;
}
v_resetjp_6764_:
{
if (lean_obj_tag(v_a_6763_) == 1)
{
lean_object* v_val_6767_; lean_object* v___x_6768_; lean_object* v___x_6769_; lean_object* v___x_6770_; lean_object* v___x_6771_; lean_object* v___x_6772_; lean_object* v___x_6773_; lean_object* v___x_6774_; lean_object* v___x_6776_; 
lean_dec_ref(v___x_6755_);
lean_dec_ref(v_wfRel_6734_);
lean_dec(v___x_6733_);
v_val_6767_ = lean_ctor_get(v_a_6763_, 0);
lean_inc(v_val_6767_);
lean_dec_ref_known(v_a_6763_, 1);
v___x_6768_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__2));
v___x_6769_ = lean_box(0);
v___x_6770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6770_, 0, v_a_6754_);
lean_ctor_set(v___x_6770_, 1, v___x_6769_);
v___x_6771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6771_, 0, v_a_6752_);
lean_ctor_set(v___x_6771_, 1, v___x_6770_);
v___x_6772_ = l_Lean_mkConst(v___x_6768_, v___x_6771_);
v___x_6773_ = l_Lean_mkApp3(v___x_6772_, v_a_6750_, v_a_6761_, v_val_6767_);
v___x_6774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6774_, 0, v___x_6773_);
lean_ctor_set(v___x_6774_, 1, v_a_6748_);
if (v_isShared_6766_ == 0)
{
lean_ctor_set(v___x_6765_, 0, v___x_6774_);
v___x_6776_ = v___x_6765_;
goto v_reusejp_6775_;
}
else
{
lean_object* v_reuseFailAlloc_6777_; 
v_reuseFailAlloc_6777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6777_, 0, v___x_6774_);
v___x_6776_ = v_reuseFailAlloc_6777_;
goto v_reusejp_6775_;
}
v_reusejp_6775_:
{
return v___x_6776_;
}
}
else
{
lean_object* v___x_6778_; lean_object* v___x_6779_; lean_object* v___x_6780_; lean_object* v___x_6781_; lean_object* v___x_6782_; lean_object* v___x_6783_; 
lean_del_object(v___x_6765_);
lean_dec(v_a_6763_);
v___x_6778_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__4));
lean_inc_ref(v_wfRel_6734_);
v___x_6779_ = l_Lean_mkProj(v___x_6778_, v___x_6744_, v_wfRel_6734_);
v___x_6780_ = l_Lean_mkProj(v___x_6778_, v___x_6733_, v_wfRel_6734_);
v___x_6781_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__6));
v___x_6782_ = lean_array_push(v___x_6755_, v___x_6780_);
v___x_6783_ = l_Lean_Meta_mkAppM(v___x_6781_, v___x_6782_, v___y_6739_, v___y_6740_, v___y_6741_, v___y_6742_);
if (lean_obj_tag(v___x_6783_) == 0)
{
lean_object* v_a_6784_; lean_object* v___x_6786_; uint8_t v_isShared_6787_; uint8_t v_isSharedCheck_6798_; 
v_a_6784_ = lean_ctor_get(v___x_6783_, 0);
v_isSharedCheck_6798_ = !lean_is_exclusive(v___x_6783_);
if (v_isSharedCheck_6798_ == 0)
{
v___x_6786_ = v___x_6783_;
v_isShared_6787_ = v_isSharedCheck_6798_;
goto v_resetjp_6785_;
}
else
{
lean_inc(v_a_6784_);
lean_dec(v___x_6783_);
v___x_6786_ = lean_box(0);
v_isShared_6787_ = v_isSharedCheck_6798_;
goto v_resetjp_6785_;
}
v_resetjp_6785_:
{
lean_object* v___x_6788_; lean_object* v___x_6789_; lean_object* v___x_6790_; lean_object* v___x_6791_; lean_object* v___x_6792_; lean_object* v___x_6793_; lean_object* v___x_6794_; lean_object* v___x_6796_; 
v___x_6788_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__7));
v___x_6789_ = lean_box(0);
v___x_6790_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6790_, 0, v_a_6754_);
lean_ctor_set(v___x_6790_, 1, v___x_6789_);
v___x_6791_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6791_, 0, v_a_6752_);
lean_ctor_set(v___x_6791_, 1, v___x_6790_);
v___x_6792_ = l_Lean_mkConst(v___x_6788_, v___x_6791_);
v___x_6793_ = l_Lean_mkApp4(v___x_6792_, v_a_6750_, v_a_6761_, v___x_6779_, v_a_6784_);
v___x_6794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6794_, 0, v___x_6793_);
lean_ctor_set(v___x_6794_, 1, v_a_6748_);
if (v_isShared_6787_ == 0)
{
lean_ctor_set(v___x_6786_, 0, v___x_6794_);
v___x_6796_ = v___x_6786_;
goto v_reusejp_6795_;
}
else
{
lean_object* v_reuseFailAlloc_6797_; 
v_reuseFailAlloc_6797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6797_, 0, v___x_6794_);
v___x_6796_ = v_reuseFailAlloc_6797_;
goto v_reusejp_6795_;
}
v_reusejp_6795_:
{
return v___x_6796_;
}
}
}
else
{
lean_object* v_a_6799_; lean_object* v___x_6801_; uint8_t v_isShared_6802_; uint8_t v_isSharedCheck_6806_; 
lean_dec_ref(v___x_6779_);
lean_dec(v_a_6761_);
lean_dec(v_a_6754_);
lean_dec(v_a_6752_);
lean_dec(v_a_6750_);
lean_dec(v_a_6748_);
v_a_6799_ = lean_ctor_get(v___x_6783_, 0);
v_isSharedCheck_6806_ = !lean_is_exclusive(v___x_6783_);
if (v_isSharedCheck_6806_ == 0)
{
v___x_6801_ = v___x_6783_;
v_isShared_6802_ = v_isSharedCheck_6806_;
goto v_resetjp_6800_;
}
else
{
lean_inc(v_a_6799_);
lean_dec(v___x_6783_);
v___x_6801_ = lean_box(0);
v_isShared_6802_ = v_isSharedCheck_6806_;
goto v_resetjp_6800_;
}
v_resetjp_6800_:
{
lean_object* v___x_6804_; 
if (v_isShared_6802_ == 0)
{
v___x_6804_ = v___x_6801_;
goto v_reusejp_6803_;
}
else
{
lean_object* v_reuseFailAlloc_6805_; 
v_reuseFailAlloc_6805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6805_, 0, v_a_6799_);
v___x_6804_ = v_reuseFailAlloc_6805_;
goto v_reusejp_6803_;
}
v_reusejp_6803_:
{
return v___x_6804_;
}
}
}
}
}
}
else
{
lean_object* v_a_6808_; lean_object* v___x_6810_; uint8_t v_isShared_6811_; uint8_t v_isSharedCheck_6815_; 
lean_dec(v_a_6761_);
lean_dec_ref(v___x_6755_);
lean_dec(v_a_6754_);
lean_dec(v_a_6752_);
lean_dec(v_a_6750_);
lean_dec(v_a_6748_);
lean_dec_ref(v_wfRel_6734_);
lean_dec(v___x_6733_);
v_a_6808_ = lean_ctor_get(v___x_6762_, 0);
v_isSharedCheck_6815_ = !lean_is_exclusive(v___x_6762_);
if (v_isSharedCheck_6815_ == 0)
{
v___x_6810_ = v___x_6762_;
v_isShared_6811_ = v_isSharedCheck_6815_;
goto v_resetjp_6809_;
}
else
{
lean_inc(v_a_6808_);
lean_dec(v___x_6762_);
v___x_6810_ = lean_box(0);
v_isShared_6811_ = v_isSharedCheck_6815_;
goto v_resetjp_6809_;
}
v_resetjp_6809_:
{
lean_object* v___x_6813_; 
if (v_isShared_6811_ == 0)
{
v___x_6813_ = v___x_6810_;
goto v_reusejp_6812_;
}
else
{
lean_object* v_reuseFailAlloc_6814_; 
v_reuseFailAlloc_6814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6814_, 0, v_a_6808_);
v___x_6813_ = v_reuseFailAlloc_6814_;
goto v_reusejp_6812_;
}
v_reusejp_6812_:
{
return v___x_6813_;
}
}
}
}
else
{
lean_object* v_a_6816_; lean_object* v___x_6818_; uint8_t v_isShared_6819_; uint8_t v_isSharedCheck_6823_; 
lean_dec_ref(v___x_6755_);
lean_dec(v_a_6754_);
lean_dec(v_a_6752_);
lean_dec(v_a_6750_);
lean_dec(v_a_6748_);
lean_dec_ref(v_wfRel_6734_);
lean_dec(v___x_6733_);
v_a_6816_ = lean_ctor_get(v___x_6760_, 0);
v_isSharedCheck_6823_ = !lean_is_exclusive(v___x_6760_);
if (v_isSharedCheck_6823_ == 0)
{
v___x_6818_ = v___x_6760_;
v_isShared_6819_ = v_isSharedCheck_6823_;
goto v_resetjp_6817_;
}
else
{
lean_inc(v_a_6816_);
lean_dec(v___x_6760_);
v___x_6818_ = lean_box(0);
v_isShared_6819_ = v_isSharedCheck_6823_;
goto v_resetjp_6817_;
}
v_resetjp_6817_:
{
lean_object* v___x_6821_; 
if (v_isShared_6819_ == 0)
{
v___x_6821_ = v___x_6818_;
goto v_reusejp_6820_;
}
else
{
lean_object* v_reuseFailAlloc_6822_; 
v_reuseFailAlloc_6822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6822_, 0, v_a_6816_);
v___x_6821_ = v_reuseFailAlloc_6822_;
goto v_reusejp_6820_;
}
v_reusejp_6820_:
{
return v___x_6821_;
}
}
}
}
else
{
lean_object* v_a_6824_; lean_object* v___x_6826_; uint8_t v_isShared_6827_; uint8_t v_isSharedCheck_6831_; 
lean_dec(v_a_6752_);
lean_dec(v_a_6750_);
lean_dec(v_a_6748_);
lean_dec_ref(v_type_6736_);
lean_dec_ref(v_wfRel_6734_);
lean_dec(v___x_6733_);
v_a_6824_ = lean_ctor_get(v___x_6753_, 0);
v_isSharedCheck_6831_ = !lean_is_exclusive(v___x_6753_);
if (v_isSharedCheck_6831_ == 0)
{
v___x_6826_ = v___x_6753_;
v_isShared_6827_ = v_isSharedCheck_6831_;
goto v_resetjp_6825_;
}
else
{
lean_inc(v_a_6824_);
lean_dec(v___x_6753_);
v___x_6826_ = lean_box(0);
v_isShared_6827_ = v_isSharedCheck_6831_;
goto v_resetjp_6825_;
}
v_resetjp_6825_:
{
lean_object* v___x_6829_; 
if (v_isShared_6827_ == 0)
{
v___x_6829_ = v___x_6826_;
goto v_reusejp_6828_;
}
else
{
lean_object* v_reuseFailAlloc_6830_; 
v_reuseFailAlloc_6830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6830_, 0, v_a_6824_);
v___x_6829_ = v_reuseFailAlloc_6830_;
goto v_reusejp_6828_;
}
v_reusejp_6828_:
{
return v___x_6829_;
}
}
}
}
else
{
lean_object* v_a_6832_; lean_object* v___x_6834_; uint8_t v_isShared_6835_; uint8_t v_isSharedCheck_6839_; 
lean_dec(v_a_6750_);
lean_dec(v_a_6748_);
lean_dec_ref(v_type_6736_);
lean_dec_ref(v_wfRel_6734_);
lean_dec(v___x_6733_);
v_a_6832_ = lean_ctor_get(v___x_6751_, 0);
v_isSharedCheck_6839_ = !lean_is_exclusive(v___x_6751_);
if (v_isSharedCheck_6839_ == 0)
{
v___x_6834_ = v___x_6751_;
v_isShared_6835_ = v_isSharedCheck_6839_;
goto v_resetjp_6833_;
}
else
{
lean_inc(v_a_6832_);
lean_dec(v___x_6751_);
v___x_6834_ = lean_box(0);
v_isShared_6835_ = v_isSharedCheck_6839_;
goto v_resetjp_6833_;
}
v_resetjp_6833_:
{
lean_object* v___x_6837_; 
if (v_isShared_6835_ == 0)
{
v___x_6837_ = v___x_6834_;
goto v_reusejp_6836_;
}
else
{
lean_object* v_reuseFailAlloc_6838_; 
v_reuseFailAlloc_6838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6838_, 0, v_a_6832_);
v___x_6837_ = v_reuseFailAlloc_6838_;
goto v_reusejp_6836_;
}
v_reusejp_6836_:
{
return v___x_6837_;
}
}
}
}
else
{
lean_object* v_a_6840_; lean_object* v___x_6842_; uint8_t v_isShared_6843_; uint8_t v_isSharedCheck_6847_; 
lean_dec(v_a_6748_);
lean_dec_ref(v_type_6736_);
lean_dec_ref(v_wfRel_6734_);
lean_dec(v___x_6733_);
v_a_6840_ = lean_ctor_get(v___x_6749_, 0);
v_isSharedCheck_6847_ = !lean_is_exclusive(v___x_6749_);
if (v_isSharedCheck_6847_ == 0)
{
v___x_6842_ = v___x_6749_;
v_isShared_6843_ = v_isSharedCheck_6847_;
goto v_resetjp_6841_;
}
else
{
lean_inc(v_a_6840_);
lean_dec(v___x_6749_);
v___x_6842_ = lean_box(0);
v_isShared_6843_ = v_isSharedCheck_6847_;
goto v_resetjp_6841_;
}
v_resetjp_6841_:
{
lean_object* v___x_6845_; 
if (v_isShared_6843_ == 0)
{
v___x_6845_ = v___x_6842_;
goto v_reusejp_6844_;
}
else
{
lean_object* v_reuseFailAlloc_6846_; 
v_reuseFailAlloc_6846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6846_, 0, v_a_6840_);
v___x_6845_ = v_reuseFailAlloc_6846_;
goto v_reusejp_6844_;
}
v_reusejp_6844_:
{
return v___x_6845_;
}
}
}
}
else
{
lean_object* v_a_6848_; lean_object* v___x_6850_; uint8_t v_isShared_6851_; uint8_t v_isSharedCheck_6855_; 
lean_dec_ref(v_type_6736_);
lean_dec_ref(v_wfRel_6734_);
lean_dec(v___x_6733_);
v_a_6848_ = lean_ctor_get(v___x_6747_, 0);
v_isSharedCheck_6855_ = !lean_is_exclusive(v___x_6747_);
if (v_isSharedCheck_6855_ == 0)
{
v___x_6850_ = v___x_6747_;
v_isShared_6851_ = v_isSharedCheck_6855_;
goto v_resetjp_6849_;
}
else
{
lean_inc(v_a_6848_);
lean_dec(v___x_6747_);
v___x_6850_ = lean_box(0);
v_isShared_6851_ = v_isSharedCheck_6855_;
goto v_resetjp_6849_;
}
v_resetjp_6849_:
{
lean_object* v___x_6853_; 
if (v_isShared_6851_ == 0)
{
v___x_6853_ = v___x_6850_;
goto v_reusejp_6852_;
}
else
{
lean_object* v_reuseFailAlloc_6854_; 
v_reuseFailAlloc_6854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6854_, 0, v_a_6848_);
v___x_6853_ = v_reuseFailAlloc_6854_;
goto v_reusejp_6852_;
}
v_reusejp_6852_:
{
return v___x_6853_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__0___boxed(lean_object* v___x_6856_, lean_object* v___x_6857_, lean_object* v_wfRel_6858_, lean_object* v_x_6859_, lean_object* v_type_6860_, lean_object* v___y_6861_, lean_object* v___y_6862_, lean_object* v___y_6863_, lean_object* v___y_6864_, lean_object* v___y_6865_, lean_object* v___y_6866_, lean_object* v___y_6867_){
_start:
{
lean_object* v_res_6868_; 
v_res_6868_ = l_Lean_Elab_WF_mkFix___lam__0(v___x_6856_, v___x_6857_, v_wfRel_6858_, v_x_6859_, v_type_6860_, v___y_6861_, v___y_6862_, v___y_6863_, v___y_6864_, v___y_6865_, v___y_6866_);
lean_dec(v___y_6866_);
lean_dec_ref(v___y_6865_);
lean_dec(v___y_6864_);
lean_dec_ref(v___y_6863_);
lean_dec(v___y_6862_);
lean_dec_ref(v___y_6861_);
lean_dec_ref(v_x_6859_);
lean_dec_ref(v___x_6856_);
return v_res_6868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__1(lean_object* v_prefixArgs_6869_, lean_object* v_declName_6870_, lean_object* v_x_6871_, lean_object* v_F_6872_, lean_object* v_val_6873_, lean_object* v___y_6874_, lean_object* v___y_6875_, lean_object* v___y_6876_, lean_object* v___y_6877_, lean_object* v___y_6878_, lean_object* v___y_6879_){
_start:
{
lean_object* v___x_6881_; lean_object* v___x_6882_; lean_object* v___x_6883_; 
v___x_6881_ = lean_array_get_size(v_prefixArgs_6869_);
v___x_6882_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___boxed), 11, 2);
lean_closure_set(v___x_6882_, 0, v_declName_6870_);
lean_closure_set(v___x_6882_, 1, v___x_6881_);
v___x_6883_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v_x_6871_, v_F_6872_, v_val_6873_, v___x_6882_, v___y_6874_, v___y_6875_, v___y_6876_, v___y_6877_, v___y_6878_, v___y_6879_);
return v___x_6883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__1___boxed(lean_object* v_prefixArgs_6884_, lean_object* v_declName_6885_, lean_object* v_x_6886_, lean_object* v_F_6887_, lean_object* v_val_6888_, lean_object* v___y_6889_, lean_object* v___y_6890_, lean_object* v___y_6891_, lean_object* v___y_6892_, lean_object* v___y_6893_, lean_object* v___y_6894_, lean_object* v___y_6895_){
_start:
{
lean_object* v_res_6896_; 
v_res_6896_ = l_Lean_Elab_WF_mkFix___lam__1(v_prefixArgs_6884_, v_declName_6885_, v_x_6886_, v_F_6887_, v_val_6888_, v___y_6889_, v___y_6890_, v___y_6891_, v___y_6892_, v___y_6893_, v___y_6894_);
lean_dec(v___y_6894_);
lean_dec_ref(v___y_6893_);
lean_dec(v___y_6892_);
lean_dec_ref(v___y_6891_);
lean_dec(v___y_6890_);
lean_dec_ref(v___y_6889_);
lean_dec_ref(v_prefixArgs_6884_);
return v_res_6896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__2(lean_object* v___x_6897_, lean_object* v___x_6898_, lean_object* v___x_6899_, lean_object* v___f_6900_, lean_object* v_funNames_6901_, lean_object* v_argsPacker_6902_, lean_object* v_decrTactics_6903_, uint8_t v___x_6904_, lean_object* v_fst_6905_, lean_object* v_prefixArgs_6906_, lean_object* v___y_6907_, lean_object* v___y_6908_, lean_object* v___y_6909_, lean_object* v___y_6910_, lean_object* v___y_6911_, lean_object* v___y_6912_){
_start:
{
lean_object* v___x_6914_; 
lean_inc_ref(v___x_6898_);
lean_inc_ref(v___x_6897_);
v___x_6914_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v___x_6897_, v___x_6898_, v___x_6899_, v___f_6900_, v___y_6907_, v___y_6908_, v___y_6909_, v___y_6910_, v___y_6911_, v___y_6912_);
if (lean_obj_tag(v___x_6914_) == 0)
{
lean_object* v_a_6915_; lean_object* v___x_6916_; 
v_a_6915_ = lean_ctor_get(v___x_6914_, 0);
lean_inc(v_a_6915_);
lean_dec_ref_known(v___x_6914_, 1);
v___x_6916_ = l_Lean_Elab_WF_solveDecreasingGoals(v_funNames_6901_, v_argsPacker_6902_, v_decrTactics_6903_, v_a_6915_, v___y_6909_, v___y_6910_, v___y_6911_, v___y_6912_);
if (lean_obj_tag(v___x_6916_) == 0)
{
lean_object* v_a_6917_; lean_object* v___x_6918_; lean_object* v___x_6919_; lean_object* v___x_6920_; lean_object* v___x_6921_; uint8_t v___x_6922_; uint8_t v___x_6923_; lean_object* v___x_6924_; 
v_a_6917_ = lean_ctor_get(v___x_6916_, 0);
lean_inc(v_a_6917_);
lean_dec_ref_known(v___x_6916_, 1);
v___x_6918_ = lean_unsigned_to_nat(2u);
v___x_6919_ = lean_mk_empty_array_with_capacity(v___x_6918_);
v___x_6920_ = lean_array_push(v___x_6919_, v___x_6897_);
v___x_6921_ = lean_array_push(v___x_6920_, v___x_6898_);
v___x_6922_ = 1;
v___x_6923_ = 1;
v___x_6924_ = l_Lean_Meta_mkLambdaFVars(v___x_6921_, v_a_6917_, v___x_6904_, v___x_6922_, v___x_6904_, v___x_6922_, v___x_6923_, v___y_6909_, v___y_6910_, v___y_6911_, v___y_6912_);
lean_dec_ref(v___x_6921_);
if (lean_obj_tag(v___x_6924_) == 0)
{
lean_object* v_a_6925_; lean_object* v___x_6926_; lean_object* v___x_6927_; 
v_a_6925_ = lean_ctor_get(v___x_6924_, 0);
lean_inc(v_a_6925_);
lean_dec_ref_known(v___x_6924_, 1);
v___x_6926_ = l_Lean_Expr_app___override(v_fst_6905_, v_a_6925_);
v___x_6927_ = l_Lean_Meta_mkLambdaFVars(v_prefixArgs_6906_, v___x_6926_, v___x_6904_, v___x_6922_, v___x_6904_, v___x_6922_, v___x_6923_, v___y_6909_, v___y_6910_, v___y_6911_, v___y_6912_);
return v___x_6927_;
}
else
{
lean_dec_ref(v_fst_6905_);
return v___x_6924_;
}
}
else
{
lean_dec_ref(v_fst_6905_);
lean_dec_ref(v___x_6898_);
lean_dec_ref(v___x_6897_);
return v___x_6916_;
}
}
else
{
lean_dec_ref(v_fst_6905_);
lean_dec_ref(v_decrTactics_6903_);
lean_dec_ref(v_argsPacker_6902_);
lean_dec_ref(v_funNames_6901_);
lean_dec_ref(v___x_6898_);
lean_dec_ref(v___x_6897_);
return v___x_6914_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__2___boxed(lean_object** _args){
lean_object* v___x_6928_ = _args[0];
lean_object* v___x_6929_ = _args[1];
lean_object* v___x_6930_ = _args[2];
lean_object* v___f_6931_ = _args[3];
lean_object* v_funNames_6932_ = _args[4];
lean_object* v_argsPacker_6933_ = _args[5];
lean_object* v_decrTactics_6934_ = _args[6];
lean_object* v___x_6935_ = _args[7];
lean_object* v_fst_6936_ = _args[8];
lean_object* v_prefixArgs_6937_ = _args[9];
lean_object* v___y_6938_ = _args[10];
lean_object* v___y_6939_ = _args[11];
lean_object* v___y_6940_ = _args[12];
lean_object* v___y_6941_ = _args[13];
lean_object* v___y_6942_ = _args[14];
lean_object* v___y_6943_ = _args[15];
lean_object* v___y_6944_ = _args[16];
_start:
{
uint8_t v___x_5940__boxed_6945_; lean_object* v_res_6946_; 
v___x_5940__boxed_6945_ = lean_unbox(v___x_6935_);
v_res_6946_ = l_Lean_Elab_WF_mkFix___lam__2(v___x_6928_, v___x_6929_, v___x_6930_, v___f_6931_, v_funNames_6932_, v_argsPacker_6933_, v_decrTactics_6934_, v___x_5940__boxed_6945_, v_fst_6936_, v_prefixArgs_6937_, v___y_6938_, v___y_6939_, v___y_6940_, v___y_6941_, v___y_6942_, v___y_6943_);
lean_dec(v___y_6943_);
lean_dec_ref(v___y_6942_);
lean_dec(v___y_6941_);
lean_dec_ref(v___y_6940_);
lean_dec(v___y_6939_);
lean_dec_ref(v___y_6938_);
lean_dec_ref(v_prefixArgs_6937_);
return v_res_6946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__3(lean_object* v___x_6947_, lean_object* v_snd_6948_, lean_object* v___x_6949_, lean_object* v_prefixArgs_6950_, lean_object* v_value_6951_, lean_object* v___f_6952_, lean_object* v_funNames_6953_, lean_object* v_argsPacker_6954_, lean_object* v_decrTactics_6955_, uint8_t v___x_6956_, lean_object* v_fst_6957_, lean_object* v_xs_6958_, lean_object* v_x_6959_, lean_object* v___y_6960_, lean_object* v___y_6961_, lean_object* v___y_6962_, lean_object* v___y_6963_, lean_object* v___y_6964_, lean_object* v___y_6965_){
_start:
{
lean_object* v_lctx_6967_; lean_object* v___x_6968_; lean_object* v___x_6969_; lean_object* v___x_6970_; lean_object* v___x_6971_; lean_object* v___x_6972_; lean_object* v___x_6973_; lean_object* v___x_6974_; lean_object* v___x_6975_; lean_object* v___f_6976_; lean_object* v___x_6977_; 
v_lctx_6967_ = lean_ctor_get(v___y_6962_, 2);
v___x_6968_ = lean_unsigned_to_nat(0u);
v___x_6969_ = lean_array_get_borrowed(v___x_6947_, v_xs_6958_, v___x_6968_);
v___x_6970_ = l_Lean_Expr_fvarId_x21(v___x_6969_);
lean_inc_ref(v_lctx_6967_);
v___x_6971_ = l_Lean_LocalContext_setUserName(v_lctx_6967_, v___x_6970_, v_snd_6948_);
v___x_6972_ = lean_array_get_borrowed(v___x_6947_, v_xs_6958_, v___x_6949_);
lean_inc_n(v___x_6969_, 2);
lean_inc_ref(v_prefixArgs_6950_);
v___x_6973_ = lean_array_push(v_prefixArgs_6950_, v___x_6969_);
v___x_6974_ = l_Lean_Expr_beta(v_value_6951_, v___x_6973_);
v___x_6975_ = lean_box(v___x_6956_);
lean_inc(v___x_6972_);
v___f_6976_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__2___boxed), 17, 10);
lean_closure_set(v___f_6976_, 0, v___x_6969_);
lean_closure_set(v___f_6976_, 1, v___x_6972_);
lean_closure_set(v___f_6976_, 2, v___x_6974_);
lean_closure_set(v___f_6976_, 3, v___f_6952_);
lean_closure_set(v___f_6976_, 4, v_funNames_6953_);
lean_closure_set(v___f_6976_, 5, v_argsPacker_6954_);
lean_closure_set(v___f_6976_, 6, v_decrTactics_6955_);
lean_closure_set(v___f_6976_, 7, v___x_6975_);
lean_closure_set(v___f_6976_, 8, v_fst_6957_);
lean_closure_set(v___f_6976_, 9, v_prefixArgs_6950_);
v___x_6977_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v___x_6971_, v___f_6976_, v___y_6960_, v___y_6961_, v___y_6962_, v___y_6963_, v___y_6964_, v___y_6965_);
return v___x_6977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__3___boxed(lean_object** _args){
lean_object* v___x_6978_ = _args[0];
lean_object* v_snd_6979_ = _args[1];
lean_object* v___x_6980_ = _args[2];
lean_object* v_prefixArgs_6981_ = _args[3];
lean_object* v_value_6982_ = _args[4];
lean_object* v___f_6983_ = _args[5];
lean_object* v_funNames_6984_ = _args[6];
lean_object* v_argsPacker_6985_ = _args[7];
lean_object* v_decrTactics_6986_ = _args[8];
lean_object* v___x_6987_ = _args[9];
lean_object* v_fst_6988_ = _args[10];
lean_object* v_xs_6989_ = _args[11];
lean_object* v_x_6990_ = _args[12];
lean_object* v___y_6991_ = _args[13];
lean_object* v___y_6992_ = _args[14];
lean_object* v___y_6993_ = _args[15];
lean_object* v___y_6994_ = _args[16];
lean_object* v___y_6995_ = _args[17];
lean_object* v___y_6996_ = _args[18];
lean_object* v___y_6997_ = _args[19];
_start:
{
uint8_t v___x_6010__boxed_6998_; lean_object* v_res_6999_; 
v___x_6010__boxed_6998_ = lean_unbox(v___x_6987_);
v_res_6999_ = l_Lean_Elab_WF_mkFix___lam__3(v___x_6978_, v_snd_6979_, v___x_6980_, v_prefixArgs_6981_, v_value_6982_, v___f_6983_, v_funNames_6984_, v_argsPacker_6985_, v_decrTactics_6986_, v___x_6010__boxed_6998_, v_fst_6988_, v_xs_6989_, v_x_6990_, v___y_6991_, v___y_6992_, v___y_6993_, v___y_6994_, v___y_6995_, v___y_6996_);
lean_dec(v___y_6996_);
lean_dec_ref(v___y_6995_);
lean_dec(v___y_6994_);
lean_dec_ref(v___y_6993_);
lean_dec(v___y_6992_);
lean_dec_ref(v___y_6991_);
lean_dec_ref(v_x_6990_);
lean_dec_ref(v_xs_6989_);
lean_dec(v___x_6980_);
lean_dec_ref(v___x_6978_);
return v_res_6999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix(lean_object* v_preDef_7004_, lean_object* v_prefixArgs_7005_, lean_object* v_argsPacker_7006_, lean_object* v_wfRel_7007_, lean_object* v_funNames_7008_, lean_object* v_decrTactics_7009_, lean_object* v_a_7010_, lean_object* v_a_7011_, lean_object* v_a_7012_, lean_object* v_a_7013_, lean_object* v_a_7014_, lean_object* v_a_7015_){
_start:
{
lean_object* v_declName_7017_; lean_object* v_type_7018_; lean_object* v_value_7019_; lean_object* v___x_7020_; 
v_declName_7017_ = lean_ctor_get(v_preDef_7004_, 3);
lean_inc(v_declName_7017_);
v_type_7018_ = lean_ctor_get(v_preDef_7004_, 6);
lean_inc_ref(v_type_7018_);
v_value_7019_ = lean_ctor_get(v_preDef_7004_, 7);
lean_inc_ref(v_value_7019_);
lean_dec_ref(v_preDef_7004_);
v___x_7020_ = l_Lean_Meta_instantiateForall(v_type_7018_, v_prefixArgs_7005_, v_a_7012_, v_a_7013_, v_a_7014_, v_a_7015_);
if (lean_obj_tag(v___x_7020_) == 0)
{
lean_object* v_a_7021_; lean_object* v___x_7022_; lean_object* v___x_7023_; lean_object* v___f_7024_; lean_object* v___x_7025_; uint8_t v___x_7026_; lean_object* v___x_7027_; 
v_a_7021_ = lean_ctor_get(v___x_7020_, 0);
lean_inc(v_a_7021_);
lean_dec_ref_known(v___x_7020_, 1);
v___x_7022_ = l_Lean_instInhabitedExpr;
v___x_7023_ = lean_unsigned_to_nat(1u);
v___f_7024_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__0___boxed), 12, 3);
lean_closure_set(v___f_7024_, 0, v___x_7022_);
lean_closure_set(v___f_7024_, 1, v___x_7023_);
lean_closure_set(v___f_7024_, 2, v_wfRel_7007_);
v___x_7025_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___closed__0));
v___x_7026_ = 0;
v___x_7027_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_a_7021_, v___x_7025_, v___f_7024_, v___x_7026_, v___x_7026_, v_a_7010_, v_a_7011_, v_a_7012_, v_a_7013_, v_a_7014_, v_a_7015_);
if (lean_obj_tag(v___x_7027_) == 0)
{
lean_object* v_a_7028_; lean_object* v_fst_7029_; lean_object* v_snd_7030_; lean_object* v___x_7031_; 
v_a_7028_ = lean_ctor_get(v___x_7027_, 0);
lean_inc(v_a_7028_);
lean_dec_ref_known(v___x_7027_, 1);
v_fst_7029_ = lean_ctor_get(v_a_7028_, 0);
lean_inc_n(v_fst_7029_, 2);
v_snd_7030_ = lean_ctor_get(v_a_7028_, 1);
lean_inc(v_snd_7030_);
lean_dec(v_a_7028_);
lean_inc(v_a_7015_);
lean_inc_ref(v_a_7014_);
lean_inc(v_a_7013_);
lean_inc_ref(v_a_7012_);
v___x_7031_ = lean_infer_type(v_fst_7029_, v_a_7012_, v_a_7013_, v_a_7014_, v_a_7015_);
if (lean_obj_tag(v___x_7031_) == 0)
{
lean_object* v_a_7032_; lean_object* v___x_7033_; 
v_a_7032_ = lean_ctor_get(v___x_7031_, 0);
lean_inc(v_a_7032_);
lean_dec_ref_known(v___x_7031_, 1);
lean_inc(v_a_7015_);
lean_inc_ref(v_a_7014_);
lean_inc(v_a_7013_);
lean_inc_ref(v_a_7012_);
v___x_7033_ = lean_whnf(v_a_7032_, v_a_7012_, v_a_7013_, v_a_7014_, v_a_7015_);
if (lean_obj_tag(v___x_7033_) == 0)
{
lean_object* v_a_7034_; lean_object* v___f_7035_; lean_object* v___x_7036_; lean_object* v___f_7037_; lean_object* v___x_7038_; lean_object* v___x_7039_; lean_object* v___x_7040_; 
v_a_7034_ = lean_ctor_get(v___x_7033_, 0);
lean_inc(v_a_7034_);
lean_dec_ref_known(v___x_7033_, 1);
lean_inc_ref(v_prefixArgs_7005_);
v___f_7035_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__1___boxed), 12, 2);
lean_closure_set(v___f_7035_, 0, v_prefixArgs_7005_);
lean_closure_set(v___f_7035_, 1, v_declName_7017_);
v___x_7036_ = lean_box(v___x_7026_);
v___f_7037_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__3___boxed), 20, 11);
lean_closure_set(v___f_7037_, 0, v___x_7022_);
lean_closure_set(v___f_7037_, 1, v_snd_7030_);
lean_closure_set(v___f_7037_, 2, v___x_7023_);
lean_closure_set(v___f_7037_, 3, v_prefixArgs_7005_);
lean_closure_set(v___f_7037_, 4, v_value_7019_);
lean_closure_set(v___f_7037_, 5, v___f_7035_);
lean_closure_set(v___f_7037_, 6, v_funNames_7008_);
lean_closure_set(v___f_7037_, 7, v_argsPacker_7006_);
lean_closure_set(v___f_7037_, 8, v_decrTactics_7009_);
lean_closure_set(v___f_7037_, 9, v___x_7036_);
lean_closure_set(v___f_7037_, 10, v_fst_7029_);
v___x_7038_ = l_Lean_Expr_bindingDomain_x21(v_a_7034_);
lean_dec(v_a_7034_);
v___x_7039_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___closed__1));
v___x_7040_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v___x_7038_, v___x_7039_, v___f_7037_, v___x_7026_, v___x_7026_, v_a_7010_, v_a_7011_, v_a_7012_, v_a_7013_, v_a_7014_, v_a_7015_);
return v___x_7040_;
}
else
{
lean_dec(v_snd_7030_);
lean_dec(v_fst_7029_);
lean_dec_ref(v_value_7019_);
lean_dec(v_declName_7017_);
lean_dec_ref(v_decrTactics_7009_);
lean_dec_ref(v_funNames_7008_);
lean_dec_ref(v_argsPacker_7006_);
lean_dec_ref(v_prefixArgs_7005_);
return v___x_7033_;
}
}
else
{
lean_dec(v_snd_7030_);
lean_dec(v_fst_7029_);
lean_dec_ref(v_value_7019_);
lean_dec(v_declName_7017_);
lean_dec_ref(v_decrTactics_7009_);
lean_dec_ref(v_funNames_7008_);
lean_dec_ref(v_argsPacker_7006_);
lean_dec_ref(v_prefixArgs_7005_);
return v___x_7031_;
}
}
else
{
lean_object* v_a_7041_; lean_object* v___x_7043_; uint8_t v_isShared_7044_; uint8_t v_isSharedCheck_7048_; 
lean_dec_ref(v_value_7019_);
lean_dec(v_declName_7017_);
lean_dec_ref(v_decrTactics_7009_);
lean_dec_ref(v_funNames_7008_);
lean_dec_ref(v_argsPacker_7006_);
lean_dec_ref(v_prefixArgs_7005_);
v_a_7041_ = lean_ctor_get(v___x_7027_, 0);
v_isSharedCheck_7048_ = !lean_is_exclusive(v___x_7027_);
if (v_isSharedCheck_7048_ == 0)
{
v___x_7043_ = v___x_7027_;
v_isShared_7044_ = v_isSharedCheck_7048_;
goto v_resetjp_7042_;
}
else
{
lean_inc(v_a_7041_);
lean_dec(v___x_7027_);
v___x_7043_ = lean_box(0);
v_isShared_7044_ = v_isSharedCheck_7048_;
goto v_resetjp_7042_;
}
v_resetjp_7042_:
{
lean_object* v___x_7046_; 
if (v_isShared_7044_ == 0)
{
v___x_7046_ = v___x_7043_;
goto v_reusejp_7045_;
}
else
{
lean_object* v_reuseFailAlloc_7047_; 
v_reuseFailAlloc_7047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7047_, 0, v_a_7041_);
v___x_7046_ = v_reuseFailAlloc_7047_;
goto v_reusejp_7045_;
}
v_reusejp_7045_:
{
return v___x_7046_;
}
}
}
}
else
{
lean_dec_ref(v_value_7019_);
lean_dec(v_declName_7017_);
lean_dec_ref(v_decrTactics_7009_);
lean_dec_ref(v_funNames_7008_);
lean_dec_ref(v_wfRel_7007_);
lean_dec_ref(v_argsPacker_7006_);
lean_dec_ref(v_prefixArgs_7005_);
return v___x_7020_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___boxed(lean_object* v_preDef_7049_, lean_object* v_prefixArgs_7050_, lean_object* v_argsPacker_7051_, lean_object* v_wfRel_7052_, lean_object* v_funNames_7053_, lean_object* v_decrTactics_7054_, lean_object* v_a_7055_, lean_object* v_a_7056_, lean_object* v_a_7057_, lean_object* v_a_7058_, lean_object* v_a_7059_, lean_object* v_a_7060_, lean_object* v_a_7061_){
_start:
{
lean_object* v_res_7062_; 
v_res_7062_ = l_Lean_Elab_WF_mkFix(v_preDef_7049_, v_prefixArgs_7050_, v_argsPacker_7051_, v_wfRel_7052_, v_funNames_7053_, v_decrTactics_7054_, v_a_7055_, v_a_7056_, v_a_7057_, v_a_7058_, v_a_7059_, v_a_7060_);
lean_dec(v_a_7060_);
lean_dec_ref(v_a_7059_);
lean_dec(v_a_7058_);
lean_dec_ref(v_a_7057_);
lean_dec(v_a_7056_);
lean_dec_ref(v_a_7055_);
return v_res_7062_;
}
}
lean_object* runtime_initialize_Lean_Data_Array(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_ArgsPacker(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_MatcherApp_Transform(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cleanup(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_HasConstCache(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Fix(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Data_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_WF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_ArgsPacker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_MatcherApp_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cleanup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_HasConstCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_WF_debug_definition_wf_replaceRecApps = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_WF_debug_definition_wf_replaceRecApps);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_PreDefinition_WF_Fix(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Array(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_WF_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_ArgsPacker(uint8_t builtin);
lean_object* initialize_Lean_Meta_Match_MatcherApp_Transform(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cleanup(uint8_t builtin);
lean_object* initialize_Lean_Util_HasConstCache(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_WF_Fix(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_ArgsPacker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatcherApp_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cleanup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_HasConstCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_WF_Fix(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_PreDefinition_WF_Fix(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_PreDefinition_WF_Fix(builtin);
}
#ifdef __cplusplus
}
#endif
