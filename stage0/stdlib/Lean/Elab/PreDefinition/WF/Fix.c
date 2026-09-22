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
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
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
lean_object* l_Lean_Elab_Tactic_evalTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Elab_Term_withDeclName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRecAppWithSyntax(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_HasConstCache_containsUnsafe(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMData(lean_object*, lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
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
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_addArg_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_altNumParams(lean_object*);
lean_object* l_Lean_Meta_MatcherApp_toExpr(lean_object*);
lean_object* l_Lean_Elab_ensureNoRecFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addPPExplicitToExposeDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
extern lean_object* l_Lean_instInhabitedLocalDecl_default;
lean_object* l_Lean_LocalContext_size(lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_local_ctx_is_empty(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalContext_contains(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_setUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM___redArg();
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12_spec__22___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0;
static const lean_closure_object l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__1 = (const lean_object*)&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__2 = (const lean_object*)&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__3 = (const lean_object*)&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__4 = (const lean_object*)&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__4_value;
static const lean_closure_object l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__5 = (const lean_object*)&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__5_value;
static const lean_closure_object l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__6 = (const lean_object*)&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Meta.Match.MatcherApp.Basic"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Meta.matchMatcherApp\?"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "expected constructor"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0;
static lean_once_cell_t l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1;
static lean_once_cell_t l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2;
static const lean_ctor_object l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__3 = (const lean_object*)&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "unexpected matcher application alternative"};
static const lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__0 = (const lean_object*)&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__0_value;
static lean_once_cell_t l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1;
static const lean_string_object l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "\nat application"};
static const lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__2 = (const lean_object*)&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__2_value;
static lean_once_cell_t l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12_spec__22(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "type of functorial "};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " is"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "replaceRecApps:"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__6 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "PSigma"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 171, 149, 177, 120, 131, 37, 223)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(248, 249, 30, 71, 49, 108, 60, 175)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__2_value;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_WF_mkFix___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "WellFounded"};
static const lean_object* l_Lean_Elab_WF_mkFix___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_WF_mkFix___lam__1___closed__0_value;
static const lean_string_object l_Lean_Elab_WF_mkFix___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fix"};
static const lean_object* l_Lean_Elab_WF_mkFix___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_WF_mkFix___lam__1___closed__1_value;
static const lean_ctor_object l_Lean_Elab_WF_mkFix___lam__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_mkFix___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(153, 177, 70, 214, 156, 62, 227, 219)}};
static const lean_ctor_object l_Lean_Elab_WF_mkFix___lam__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_WF_mkFix___lam__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_WF_isNatLtWF___closed__2_value),LEAN_SCALAR_PTR_LITERAL(209, 126, 194, 128, 117, 36, 224, 78)}};
static const lean_ctor_object l_Lean_Elab_WF_mkFix___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_WF_mkFix___lam__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_WF_mkFix___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(196, 0, 160, 225, 119, 146, 123, 62)}};
static const lean_object* l_Lean_Elab_WF_mkFix___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_WF_mkFix___lam__1___closed__2_value;
static const lean_string_object l_Lean_Elab_WF_mkFix___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "WellFoundedRelation"};
static const lean_object* l_Lean_Elab_WF_mkFix___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_WF_mkFix___lam__1___closed__3_value;
static const lean_ctor_object l_Lean_Elab_WF_mkFix___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_mkFix___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(247, 146, 95, 132, 177, 137, 153, 47)}};
static const lean_object* l_Lean_Elab_WF_mkFix___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_WF_mkFix___lam__1___closed__4_value;
static const lean_string_object l_Lean_Elab_WF_mkFix___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "opaqueId"};
static const lean_object* l_Lean_Elab_WF_mkFix___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_WF_mkFix___lam__1___closed__5_value;
static const lean_ctor_object l_Lean_Elab_WF_mkFix___lam__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Fix_34085118____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_WF_mkFix___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_WF_mkFix___lam__1___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_WF_mkFix___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(194, 89, 34, 148, 92, 203, 118, 146)}};
static const lean_object* l_Lean_Elab_WF_mkFix___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_WF_mkFix___lam__1___closed__6_value;
static const lean_ctor_object l_Lean_Elab_WF_mkFix___lam__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_mkFix___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(153, 177, 70, 214, 156, 62, 227, 219)}};
static const lean_ctor_object l_Lean_Elab_WF_mkFix___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_WF_mkFix___lam__1___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_WF_mkFix___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(172, 133, 211, 204, 28, 206, 53, 233)}};
static const lean_object* l_Lean_Elab_WF_mkFix___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_WF_mkFix___lam__1___closed__7_value;
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
v_ref_75_ = lean_ctor_get(v_a_72_, 2);
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
lean_object* v___x_134_; lean_object* v_env_135_; lean_object* v___x_136_; lean_object* v_toCold_137_; lean_object* v_mctx_138_; lean_object* v_lctx_139_; lean_object* v_options_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_134_ = lean_st_ref_get(v___y_132_);
v_env_135_ = lean_ctor_get(v___x_134_, 0);
lean_inc_ref(v_env_135_);
lean_dec(v___x_134_);
v___x_136_ = lean_st_ref_get(v___y_130_);
v_toCold_137_ = lean_ctor_get(v___y_131_, 0);
v_mctx_138_ = lean_ctor_get(v___x_136_, 0);
lean_inc_ref(v_mctx_138_);
lean_dec(v___x_136_);
v_lctx_139_ = lean_ctor_get(v___y_129_, 2);
v_options_140_ = lean_ctor_get(v_toCold_137_, 2);
lean_inc_ref(v_options_140_);
lean_inc_ref(v_lctx_139_);
v___x_141_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_141_, 0, v_env_135_);
lean_ctor_set(v___x_141_, 1, v_mctx_138_);
lean_ctor_set(v___x_141_, 2, v_lctx_139_);
lean_ctor_set(v___x_141_, 3, v_options_140_);
v___x_142_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
lean_ctor_set(v___x_142_, 1, v_msgData_128_);
v___x_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1___boxed(lean_object* v_msgData_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msgData_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
lean_dec(v___y_146_);
lean_dec_ref(v___y_145_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(lean_object* v_msg_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
lean_object* v_ref_157_; lean_object* v___x_158_; lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_167_; 
v_ref_157_ = lean_ctor_get(v___y_154_, 2);
v___x_158_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_);
v_a_159_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_167_ == 0)
{
v___x_161_ = v___x_158_;
v_isShared_162_ = v_isSharedCheck_167_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v___x_158_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_167_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_163_; lean_object* v___x_165_; 
lean_inc(v_ref_157_);
v___x_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_163_, 0, v_ref_157_);
lean_ctor_set(v___x_163_, 1, v_a_159_);
if (v_isShared_162_ == 0)
{
lean_ctor_set_tag(v___x_161_, 1);
lean_ctor_set(v___x_161_, 0, v___x_163_);
v___x_165_ = v___x_161_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v___x_163_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg___boxed(lean_object* v_msg_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v_msg_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
return v_res_174_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__3(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_178_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__2));
v___x_179_ = lean_unsigned_to_nat(14u);
v___x_180_ = lean_unsigned_to_nat(22u);
v___x_181_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__1));
v___x_182_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__0));
v___x_183_ = l_mkPanicMessageWithDecl(v___x_182_, v___x_181_, v___x_180_, v___x_179_, v___x_178_);
return v___x_183_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__5(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__4));
v___x_186_ = l_Lean_stringToMessageData(v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId(lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_){
_start:
{
lean_object* v___y_193_; lean_object* v___y_197_; lean_object* v_lctx_201_; lean_object* v___x_202_; uint8_t v___x_212_; 
v_lctx_201_ = lean_ctor_get(v_a_187_, 2);
v___x_202_ = lean_box(0);
lean_inc_ref(v_lctx_201_);
v___x_212_ = lean_local_ctx_is_empty(v_lctx_201_);
if (v___x_212_ == 0)
{
goto v___jp_203_;
}
else
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_222_; 
v___x_213_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__5);
v___x_214_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v___x_213_, v_a_187_, v_a_188_, v_a_189_, v_a_190_);
v_a_215_ = lean_ctor_get(v___x_214_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_222_ == 0)
{
v___x_217_ = v___x_214_;
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v___x_214_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_220_; 
if (v_isShared_218_ == 0)
{
v___x_220_ = v___x_217_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_a_215_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
v___jp_192_:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = l_Lean_LocalDecl_fvarId(v___y_193_);
lean_dec_ref(v___y_193_);
v___x_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
return v___x_195_;
}
v___jp_196_:
{
if (lean_obj_tag(v___y_197_) == 0)
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___closed__3);
v___x_199_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__0(v___x_198_);
v___y_193_ = v___x_199_;
goto v___jp_192_;
}
else
{
lean_object* v_val_200_; 
v_val_200_ = lean_ctor_get(v___y_197_, 0);
lean_inc(v_val_200_);
lean_dec_ref_known(v___y_197_, 1);
v___y_193_ = v_val_200_;
goto v___jp_192_;
}
}
v___jp_203_:
{
lean_object* v_decls_204_; lean_object* v_size_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; 
v_decls_204_ = lean_ctor_get(v_lctx_201_, 1);
v_size_205_ = lean_ctor_get(v_decls_204_, 2);
v___x_206_ = l_Lean_LocalContext_size(v_lctx_201_);
v___x_207_ = lean_unsigned_to_nat(1u);
v___x_208_ = lean_nat_sub(v___x_206_, v___x_207_);
lean_dec(v___x_206_);
v___x_209_ = lean_nat_dec_lt(v___x_208_, v_size_205_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; 
lean_dec(v___x_208_);
v___x_210_ = l_outOfBounds___redArg(v___x_202_);
v___y_197_ = v___x_210_;
goto v___jp_196_;
}
else
{
lean_object* v___x_211_; 
v___x_211_ = l_Lean_PersistentArray_get_x21___redArg(v___x_202_, v_decls_204_, v___x_208_);
lean_dec(v___x_208_);
v___y_197_ = v___x_211_;
goto v___jp_196_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId___boxed(lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId(v_a_223_, v_a_224_, v_a_225_, v_a_226_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1(lean_object* v_00_u03b1_229_, lean_object* v_msg_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v_msg_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___boxed(lean_object* v_00_u03b1_237_, lean_object* v_msg_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1(v_00_u03b1_237_, v_msg_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___redArg(lean_object* v_lctxid_245_, lean_object* v_a_246_){
_start:
{
lean_object* v_lctx_248_; uint8_t v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v_lctx_248_ = lean_ctor_get(v_a_246_, 2);
v___x_249_ = l_Lean_LocalContext_contains(v_lctx_248_, v_lctxid_245_);
v___x_250_ = lean_box(v___x_249_);
v___x_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___redArg___boxed(lean_object* v_lctxid_252_, lean_object* v_a_253_, lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___redArg(v_lctxid_252_, v_a_253_);
lean_dec_ref(v_a_253_);
lean_dec(v_lctxid_252_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid(lean_object* v_lctxid_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___redArg(v_lctxid_256_, v_a_257_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___boxed(lean_object* v_lctxid_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid(v_lctxid_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_);
lean_dec(v_a_267_);
lean_dec_ref(v_a_266_);
lean_dec(v_a_265_);
lean_dec_ref(v_a_264_);
lean_dec(v_lctxid_263_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___redArg(lean_object* v_recFnName_270_, lean_object* v_e_271_, lean_object* v_a_272_){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v_fst_279_; lean_object* v_snd_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_274_ = lean_unsigned_to_nat(1u);
v___x_275_ = lean_mk_empty_array_with_capacity(v___x_274_);
v___x_276_ = lean_array_push(v___x_275_, v_recFnName_270_);
v___x_277_ = lean_st_ref_take(v_a_272_);
v___x_278_ = l_Lean_HasConstCache_containsUnsafe(v___x_276_, v_e_271_, v___x_277_);
lean_dec_ref(v___x_276_);
v_fst_279_ = lean_ctor_get(v___x_278_, 0);
lean_inc(v_fst_279_);
v_snd_280_ = lean_ctor_get(v___x_278_, 1);
lean_inc(v_snd_280_);
lean_dec_ref(v___x_278_);
v___x_281_ = lean_st_ref_put(v_a_272_, v_snd_280_);
v___x_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_282_, 0, v_fst_279_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___redArg___boxed(lean_object* v_recFnName_283_, lean_object* v_e_284_, lean_object* v_a_285_, lean_object* v_a_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___redArg(v_recFnName_283_, v_e_284_, v_a_285_);
lean_dec(v_a_285_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn(lean_object* v_recFnName_288_, lean_object* v_e_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___redArg(v_recFnName_288_, v_e_289_, v_a_290_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___boxed(lean_object* v_recFnName_300_, lean_object* v_e_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn(v_recFnName_300_, v_e_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
lean_dec(v_a_309_);
lean_dec_ref(v_a_308_);
lean_dec(v_a_307_);
lean_dec_ref(v_a_306_);
lean_dec(v_a_305_);
lean_dec_ref(v_a_304_);
lean_dec(v_a_303_);
lean_dec(v_a_302_);
return v_res_311_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_312_; double v___x_313_; 
v___x_312_ = lean_unsigned_to_nat(0u);
v___x_313_ = lean_float_of_nat(v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(lean_object* v_cls_317_, lean_object* v_msg_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v_ref_324_; lean_object* v___x_325_; lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_370_; 
v_ref_324_ = lean_ctor_get(v___y_321_, 2);
v___x_325_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_);
v_a_326_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_370_ == 0)
{
v___x_328_ = v___x_325_;
v_isShared_329_ = v_isSharedCheck_370_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_325_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_370_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; lean_object* v_traceState_331_; lean_object* v_env_332_; lean_object* v_nextMacroScope_333_; lean_object* v_ngen_334_; lean_object* v_auxDeclNGen_335_; lean_object* v_cache_336_; lean_object* v_messages_337_; lean_object* v_infoState_338_; lean_object* v_snapshotTasks_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_369_; 
v___x_330_ = lean_st_ref_take(v___y_322_);
v_traceState_331_ = lean_ctor_get(v___x_330_, 4);
v_env_332_ = lean_ctor_get(v___x_330_, 0);
v_nextMacroScope_333_ = lean_ctor_get(v___x_330_, 1);
v_ngen_334_ = lean_ctor_get(v___x_330_, 2);
v_auxDeclNGen_335_ = lean_ctor_get(v___x_330_, 3);
v_cache_336_ = lean_ctor_get(v___x_330_, 5);
v_messages_337_ = lean_ctor_get(v___x_330_, 6);
v_infoState_338_ = lean_ctor_get(v___x_330_, 7);
v_snapshotTasks_339_ = lean_ctor_get(v___x_330_, 8);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_369_ == 0)
{
v___x_341_ = v___x_330_;
v_isShared_342_ = v_isSharedCheck_369_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_snapshotTasks_339_);
lean_inc(v_infoState_338_);
lean_inc(v_messages_337_);
lean_inc(v_cache_336_);
lean_inc(v_traceState_331_);
lean_inc(v_auxDeclNGen_335_);
lean_inc(v_ngen_334_);
lean_inc(v_nextMacroScope_333_);
lean_inc(v_env_332_);
lean_dec(v___x_330_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_369_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
uint64_t v_tid_343_; lean_object* v_traces_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_368_; 
v_tid_343_ = lean_ctor_get_uint64(v_traceState_331_, sizeof(void*)*1);
v_traces_344_ = lean_ctor_get(v_traceState_331_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v_traceState_331_);
if (v_isSharedCheck_368_ == 0)
{
v___x_346_ = v_traceState_331_;
v_isShared_347_ = v_isSharedCheck_368_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_traces_344_);
lean_dec(v_traceState_331_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_368_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_348_; lean_object* v___x_349_; double v___x_350_; uint8_t v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_359_; 
v___x_348_ = lean_box(0);
v___x_349_ = lean_box(0);
v___x_350_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0);
v___x_351_ = 0;
v___x_352_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__1));
v___x_353_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_353_, 0, v_cls_317_);
lean_ctor_set(v___x_353_, 1, v___x_349_);
lean_ctor_set(v___x_353_, 2, v___x_352_);
lean_ctor_set_float(v___x_353_, sizeof(void*)*3, v___x_350_);
lean_ctor_set_float(v___x_353_, sizeof(void*)*3 + 8, v___x_350_);
lean_ctor_set_uint8(v___x_353_, sizeof(void*)*3 + 16, v___x_351_);
v___x_354_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__2));
v___x_355_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_355_, 0, v___x_353_);
lean_ctor_set(v___x_355_, 1, v_a_326_);
lean_ctor_set(v___x_355_, 2, v___x_354_);
lean_inc(v_ref_324_);
v___x_356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_356_, 0, v_ref_324_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
v___x_357_ = l_Lean_PersistentArray_push___redArg(v_traces_344_, v___x_356_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 0, v___x_357_);
v___x_359_ = v___x_346_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_357_);
lean_ctor_set_uint64(v_reuseFailAlloc_367_, sizeof(void*)*1, v_tid_343_);
v___x_359_ = v_reuseFailAlloc_367_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
lean_object* v___x_361_; 
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 4, v___x_359_);
v___x_361_ = v___x_341_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_env_332_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v_nextMacroScope_333_);
lean_ctor_set(v_reuseFailAlloc_366_, 2, v_ngen_334_);
lean_ctor_set(v_reuseFailAlloc_366_, 3, v_auxDeclNGen_335_);
lean_ctor_set(v_reuseFailAlloc_366_, 4, v___x_359_);
lean_ctor_set(v_reuseFailAlloc_366_, 5, v_cache_336_);
lean_ctor_set(v_reuseFailAlloc_366_, 6, v_messages_337_);
lean_ctor_set(v_reuseFailAlloc_366_, 7, v_infoState_338_);
lean_ctor_set(v_reuseFailAlloc_366_, 8, v_snapshotTasks_339_);
v___x_361_ = v_reuseFailAlloc_366_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
lean_object* v___x_362_; lean_object* v___x_364_; 
v___x_362_ = lean_st_ref_put(v___y_322_, v___x_361_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 0, v___x_348_);
v___x_364_ = v___x_328_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_348_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___boxed(lean_object* v_cls_371_, lean_object* v_msg_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(v_cls_371_, v_msg_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12_spec__22___redArg(lean_object* v_x_379_, lean_object* v_x_380_){
_start:
{
if (lean_obj_tag(v_x_380_) == 0)
{
return v_x_379_;
}
else
{
lean_object* v_key_381_; lean_object* v_value_382_; lean_object* v_tail_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_406_; 
v_key_381_ = lean_ctor_get(v_x_380_, 0);
v_value_382_ = lean_ctor_get(v_x_380_, 1);
v_tail_383_ = lean_ctor_get(v_x_380_, 2);
v_isSharedCheck_406_ = !lean_is_exclusive(v_x_380_);
if (v_isSharedCheck_406_ == 0)
{
v___x_385_ = v_x_380_;
v_isShared_386_ = v_isSharedCheck_406_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_tail_383_);
lean_inc(v_value_382_);
lean_inc(v_key_381_);
lean_dec(v_x_380_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_406_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_387_; uint64_t v___x_388_; uint64_t v___x_389_; uint64_t v___x_390_; uint64_t v_fold_391_; uint64_t v___x_392_; uint64_t v___x_393_; uint64_t v___x_394_; size_t v___x_395_; size_t v___x_396_; size_t v___x_397_; size_t v___x_398_; size_t v___x_399_; lean_object* v___x_400_; lean_object* v___x_402_; 
v___x_387_ = lean_array_get_size(v_x_379_);
v___x_388_ = l_Lean_Expr_hash(v_key_381_);
v___x_389_ = 32ULL;
v___x_390_ = lean_uint64_shift_right(v___x_388_, v___x_389_);
v_fold_391_ = lean_uint64_xor(v___x_388_, v___x_390_);
v___x_392_ = 16ULL;
v___x_393_ = lean_uint64_shift_right(v_fold_391_, v___x_392_);
v___x_394_ = lean_uint64_xor(v_fold_391_, v___x_393_);
v___x_395_ = lean_uint64_to_usize(v___x_394_);
v___x_396_ = lean_usize_of_nat(v___x_387_);
v___x_397_ = ((size_t)1ULL);
v___x_398_ = lean_usize_sub(v___x_396_, v___x_397_);
v___x_399_ = lean_usize_land(v___x_395_, v___x_398_);
v___x_400_ = lean_array_uget_borrowed(v_x_379_, v___x_399_);
lean_inc(v___x_400_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 2, v___x_400_);
v___x_402_ = v___x_385_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_key_381_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_value_382_);
lean_ctor_set(v_reuseFailAlloc_405_, 2, v___x_400_);
v___x_402_ = v_reuseFailAlloc_405_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
lean_object* v___x_403_; 
v___x_403_ = lean_array_uset(v_x_379_, v___x_399_, v___x_402_);
v_x_379_ = v___x_403_;
v_x_380_ = v_tail_383_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12___redArg(lean_object* v_i_407_, lean_object* v_source_408_, lean_object* v_target_409_){
_start:
{
lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_410_ = lean_array_get_size(v_source_408_);
v___x_411_ = lean_nat_dec_lt(v_i_407_, v___x_410_);
if (v___x_411_ == 0)
{
lean_dec_ref(v_source_408_);
lean_dec(v_i_407_);
return v_target_409_;
}
else
{
lean_object* v_es_412_; lean_object* v___x_413_; lean_object* v_source_414_; lean_object* v_target_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v_es_412_ = lean_array_fget(v_source_408_, v_i_407_);
v___x_413_ = lean_box(0);
v_source_414_ = lean_array_fset(v_source_408_, v_i_407_, v___x_413_);
v_target_415_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12_spec__22___redArg(v_target_409_, v_es_412_);
v___x_416_ = lean_unsigned_to_nat(1u);
v___x_417_ = lean_nat_add(v_i_407_, v___x_416_);
lean_dec(v_i_407_);
v_i_407_ = v___x_417_;
v_source_408_ = v_source_414_;
v_target_409_ = v_target_415_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5___redArg(lean_object* v_data_419_){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v_nbuckets_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_420_ = lean_array_get_size(v_data_419_);
v___x_421_ = lean_unsigned_to_nat(2u);
v_nbuckets_422_ = lean_nat_mul(v___x_420_, v___x_421_);
v___x_423_ = lean_unsigned_to_nat(0u);
v___x_424_ = lean_box(0);
v___x_425_ = lean_mk_array(v_nbuckets_422_, v___x_424_);
v___x_426_ = lean_array_propagate_mark(v_data_419_, v___x_425_);
v___x_427_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12___redArg(v___x_423_, v_data_419_, v___x_426_);
return v___x_427_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg(lean_object* v_a_428_, lean_object* v_x_429_){
_start:
{
if (lean_obj_tag(v_x_429_) == 0)
{
uint8_t v___x_430_; 
v___x_430_ = 0;
return v___x_430_;
}
else
{
lean_object* v_key_431_; lean_object* v_tail_432_; uint8_t v___x_433_; 
v_key_431_ = lean_ctor_get(v_x_429_, 0);
v_tail_432_ = lean_ctor_get(v_x_429_, 2);
v___x_433_ = lean_expr_eqv(v_key_431_, v_a_428_);
if (v___x_433_ == 0)
{
v_x_429_ = v_tail_432_;
goto _start;
}
else
{
return v___x_433_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg___boxed(lean_object* v_a_435_, lean_object* v_x_436_){
_start:
{
uint8_t v_res_437_; lean_object* v_r_438_; 
v_res_437_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg(v_a_435_, v_x_436_);
lean_dec(v_x_436_);
lean_dec_ref(v_a_435_);
v_r_438_ = lean_box(v_res_437_);
return v_r_438_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6___redArg(lean_object* v_a_439_, lean_object* v_b_440_, lean_object* v_x_441_){
_start:
{
if (lean_obj_tag(v_x_441_) == 0)
{
lean_dec(v_b_440_);
lean_dec_ref(v_a_439_);
return v_x_441_;
}
else
{
lean_object* v_key_442_; lean_object* v_value_443_; lean_object* v_tail_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_456_; 
v_key_442_ = lean_ctor_get(v_x_441_, 0);
v_value_443_ = lean_ctor_get(v_x_441_, 1);
v_tail_444_ = lean_ctor_get(v_x_441_, 2);
v_isSharedCheck_456_ = !lean_is_exclusive(v_x_441_);
if (v_isSharedCheck_456_ == 0)
{
v___x_446_ = v_x_441_;
v_isShared_447_ = v_isSharedCheck_456_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_tail_444_);
lean_inc(v_value_443_);
lean_inc(v_key_442_);
lean_dec(v_x_441_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_456_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
uint8_t v___x_448_; 
v___x_448_ = lean_expr_eqv(v_key_442_, v_a_439_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; lean_object* v___x_451_; 
v___x_449_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6___redArg(v_a_439_, v_b_440_, v_tail_444_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 2, v___x_449_);
v___x_451_ = v___x_446_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_key_442_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_value_443_);
lean_ctor_set(v_reuseFailAlloc_452_, 2, v___x_449_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
else
{
lean_object* v___x_454_; 
lean_dec(v_value_443_);
lean_dec(v_key_442_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 1, v_b_440_);
lean_ctor_set(v___x_446_, 0, v_a_439_);
v___x_454_ = v___x_446_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_a_439_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_b_440_);
lean_ctor_set(v_reuseFailAlloc_455_, 2, v_tail_444_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4___redArg(lean_object* v_m_457_, lean_object* v_a_458_, lean_object* v_b_459_){
_start:
{
lean_object* v_size_460_; lean_object* v_buckets_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_504_; 
v_size_460_ = lean_ctor_get(v_m_457_, 0);
v_buckets_461_ = lean_ctor_get(v_m_457_, 1);
v_isSharedCheck_504_ = !lean_is_exclusive(v_m_457_);
if (v_isSharedCheck_504_ == 0)
{
v___x_463_ = v_m_457_;
v_isShared_464_ = v_isSharedCheck_504_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_buckets_461_);
lean_inc(v_size_460_);
lean_dec(v_m_457_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_504_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_465_; uint64_t v___x_466_; uint64_t v___x_467_; uint64_t v___x_468_; uint64_t v_fold_469_; uint64_t v___x_470_; uint64_t v___x_471_; uint64_t v___x_472_; size_t v___x_473_; size_t v___x_474_; size_t v___x_475_; size_t v___x_476_; size_t v___x_477_; lean_object* v_bkt_478_; uint8_t v___x_479_; 
v___x_465_ = lean_array_get_size(v_buckets_461_);
v___x_466_ = l_Lean_Expr_hash(v_a_458_);
v___x_467_ = 32ULL;
v___x_468_ = lean_uint64_shift_right(v___x_466_, v___x_467_);
v_fold_469_ = lean_uint64_xor(v___x_466_, v___x_468_);
v___x_470_ = 16ULL;
v___x_471_ = lean_uint64_shift_right(v_fold_469_, v___x_470_);
v___x_472_ = lean_uint64_xor(v_fold_469_, v___x_471_);
v___x_473_ = lean_uint64_to_usize(v___x_472_);
v___x_474_ = lean_usize_of_nat(v___x_465_);
v___x_475_ = ((size_t)1ULL);
v___x_476_ = lean_usize_sub(v___x_474_, v___x_475_);
v___x_477_ = lean_usize_land(v___x_473_, v___x_476_);
v_bkt_478_ = lean_array_uget_borrowed(v_buckets_461_, v___x_477_);
v___x_479_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg(v_a_458_, v_bkt_478_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; lean_object* v_size_x27_481_; lean_object* v___x_482_; lean_object* v_buckets_x27_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_480_ = lean_unsigned_to_nat(1u);
v_size_x27_481_ = lean_nat_add(v_size_460_, v___x_480_);
lean_dec(v_size_460_);
lean_inc(v_bkt_478_);
v___x_482_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_482_, 0, v_a_458_);
lean_ctor_set(v___x_482_, 1, v_b_459_);
lean_ctor_set(v___x_482_, 2, v_bkt_478_);
v_buckets_x27_483_ = lean_array_uset(v_buckets_461_, v___x_477_, v___x_482_);
v___x_484_ = lean_unsigned_to_nat(4u);
v___x_485_ = lean_nat_mul(v_size_x27_481_, v___x_484_);
v___x_486_ = lean_unsigned_to_nat(3u);
v___x_487_ = lean_nat_div(v___x_485_, v___x_486_);
lean_dec(v___x_485_);
v___x_488_ = lean_array_get_size(v_buckets_x27_483_);
v___x_489_ = lean_nat_dec_le(v___x_487_, v___x_488_);
lean_dec(v___x_487_);
if (v___x_489_ == 0)
{
lean_object* v_val_490_; lean_object* v___x_492_; 
v_val_490_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5___redArg(v_buckets_x27_483_);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 1, v_val_490_);
lean_ctor_set(v___x_463_, 0, v_size_x27_481_);
v___x_492_ = v___x_463_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_size_x27_481_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_val_490_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
else
{
lean_object* v___x_495_; 
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 1, v_buckets_x27_483_);
lean_ctor_set(v___x_463_, 0, v_size_x27_481_);
v___x_495_ = v___x_463_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_size_x27_481_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_buckets_x27_483_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
else
{
lean_object* v___x_497_; lean_object* v_buckets_x27_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_502_; 
lean_inc(v_bkt_478_);
v___x_497_ = lean_box(0);
v_buckets_x27_498_ = lean_array_uset(v_buckets_461_, v___x_477_, v___x_497_);
v___x_499_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6___redArg(v_a_458_, v_b_459_, v_bkt_478_);
v___x_500_ = lean_array_uset(v_buckets_x27_498_, v___x_477_, v___x_499_);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 1, v___x_500_);
v___x_502_ = v___x_463_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_size_460_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v___x_500_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(lean_object* v_msg_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
lean_object* v_ref_511_; lean_object* v___x_512_; lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_521_; 
v_ref_511_ = lean_ctor_get(v___y_508_, 2);
v___x_512_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_);
v_a_513_ = lean_ctor_get(v___x_512_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_521_ == 0)
{
v___x_515_ = v___x_512_;
v_isShared_516_ = v_isSharedCheck_521_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_512_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_521_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_517_; lean_object* v___x_519_; 
lean_inc(v_ref_511_);
v___x_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_517_, 0, v_ref_511_);
lean_ctor_set(v___x_517_, 1, v_a_513_);
if (v_isShared_516_ == 0)
{
lean_ctor_set_tag(v___x_515_, 1);
lean_ctor_set(v___x_515_, 0, v___x_517_);
v___x_519_ = v___x_515_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg___boxed(lean_object* v_msg_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v_msg_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
return v_res_528_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__1(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__0));
v___x_531_ = l_Lean_stringToMessageData(v___x_530_);
return v___x_531_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__2));
v___x_534_ = l_Lean_stringToMessageData(v___x_533_);
return v___x_534_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__5(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__4));
v___x_537_ = l_Lean_stringToMessageData(v___x_536_);
return v___x_537_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__7(void){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__6));
v___x_540_ = l_Lean_stringToMessageData(v___x_539_);
return v___x_540_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__9(void){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__8));
v___x_543_ = l_Lean_stringToMessageData(v___x_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0(lean_object* v_e_544_, lean_object* v_a_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v___x_629_; 
lean_inc_ref(v_a_545_);
v___x_629_ = l_Lean_Meta_isTypeCorrect(v_a_545_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; uint8_t v___x_631_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
lean_inc(v_a_630_);
lean_dec_ref_known(v___x_629_, 1);
v___x_631_ = lean_unbox(v_a_630_);
lean_dec(v_a_630_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_632_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__9, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__9);
lean_inc_ref(v_e_544_);
v___x_633_ = l_Lean_indentExpr(v_e_544_);
v___x_634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_632_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
v___x_635_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3);
v___x_636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_634_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
lean_inc_ref(v_a_545_);
v___x_637_ = l_Lean_indentExpr(v_a_545_);
v___x_638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_636_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
v___x_639_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v___x_638_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_dec_ref_known(v___x_639_, 1);
goto v___jp_555_;
}
else
{
lean_dec_ref(v_a_545_);
lean_dec_ref(v_e_544_);
return v___x_639_;
}
}
else
{
goto v___jp_555_;
}
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_dec_ref(v_a_545_);
lean_dec_ref(v_e_544_);
v_a_640_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_629_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_629_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
v___jp_555_:
{
lean_object* v___x_556_; 
lean_inc(v___y_553_);
lean_inc_ref(v___y_552_);
lean_inc(v___y_551_);
lean_inc_ref(v___y_550_);
lean_inc_ref(v_e_544_);
v___x_556_ = lean_infer_type(v_e_544_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v_a_557_; lean_object* v___x_558_; 
v_a_557_ = lean_ctor_get(v___x_556_, 0);
lean_inc(v_a_557_);
lean_dec_ref_known(v___x_556_, 1);
lean_inc(v___y_553_);
lean_inc_ref(v___y_552_);
lean_inc(v___y_551_);
lean_inc_ref(v___y_550_);
lean_inc_ref(v_a_545_);
v___x_558_ = lean_infer_type(v_a_545_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; lean_object* v___x_560_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
lean_inc_n(v_a_559_, 2);
lean_dec_ref_known(v___x_558_, 1);
lean_inc(v_a_557_);
v___x_560_ = l_Lean_Meta_isExprDefEq(v_a_557_, v_a_559_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_604_; 
v_a_561_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_604_ == 0)
{
v___x_563_ = v___x_560_;
v_isShared_564_ = v_isSharedCheck_604_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_560_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_604_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
uint8_t v___x_565_; 
v___x_565_ = lean_unbox(v_a_561_);
lean_dec(v_a_561_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; 
lean_del_object(v___x_563_);
v___x_566_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_a_557_, v_a_559_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v_a_567_; lean_object* v_fst_568_; lean_object* v_snd_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_591_; 
v_a_567_ = lean_ctor_get(v___x_566_, 0);
lean_inc(v_a_567_);
lean_dec_ref_known(v___x_566_, 1);
v_fst_568_ = lean_ctor_get(v_a_567_, 0);
v_snd_569_ = lean_ctor_get(v_a_567_, 1);
v_isSharedCheck_591_ = !lean_is_exclusive(v_a_567_);
if (v_isSharedCheck_591_ == 0)
{
v___x_571_ = v_a_567_;
v_isShared_572_ = v_isSharedCheck_591_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_snd_569_);
lean_inc(v_fst_568_);
lean_dec(v_a_567_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_591_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_576_; 
v___x_573_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__1);
v___x_574_ = l_Lean_indentExpr(v_e_544_);
if (v_isShared_572_ == 0)
{
lean_ctor_set_tag(v___x_571_, 7);
lean_ctor_set(v___x_571_, 1, v___x_574_);
lean_ctor_set(v___x_571_, 0, v___x_573_);
v___x_576_ = v___x_571_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_573_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v___x_574_);
v___x_576_ = v_reuseFailAlloc_590_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_577_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3);
v___x_578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_576_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
v___x_579_ = l_Lean_indentExpr(v_a_545_);
v___x_580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_578_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
v___x_581_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__5);
v___x_582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_580_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
v___x_583_ = l_Lean_indentExpr(v_fst_568_);
v___x_584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_582_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
v___x_585_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__7, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__7);
v___x_586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_584_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
v___x_587_ = l_Lean_indentExpr(v_snd_569_);
v___x_588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_586_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
v___x_589_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v___x_588_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
return v___x_589_;
}
}
}
else
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
lean_dec_ref(v_a_545_);
lean_dec_ref(v_e_544_);
v_a_592_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_566_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_566_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
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
else
{
lean_object* v___x_600_; lean_object* v___x_602_; 
lean_dec(v_a_559_);
lean_dec(v_a_557_);
lean_dec_ref(v_a_545_);
lean_dec_ref(v_e_544_);
v___x_600_ = lean_box(0);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 0, v___x_600_);
v___x_602_ = v___x_563_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_600_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
else
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_612_; 
lean_dec(v_a_559_);
lean_dec(v_a_557_);
lean_dec_ref(v_a_545_);
lean_dec_ref(v_e_544_);
v_a_605_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_612_ == 0)
{
v___x_607_ = v___x_560_;
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_560_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_608_ == 0)
{
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_a_605_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
else
{
lean_object* v_a_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_620_; 
lean_dec(v_a_557_);
lean_dec_ref(v_a_545_);
lean_dec_ref(v_e_544_);
v_a_613_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_620_ == 0)
{
v___x_615_ = v___x_558_;
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_dec(v___x_558_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_618_; 
if (v_isShared_616_ == 0)
{
v___x_618_ = v___x_615_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_a_613_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
}
else
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
lean_dec_ref(v_a_545_);
lean_dec_ref(v_e_544_);
v_a_621_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v___x_556_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_556_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_621_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___boxed(lean_object* v_e_648_, lean_object* v_a_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0(v_e_648_, v_a_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
lean_dec(v___y_650_);
return v_res_659_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0(void){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_660_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0);
v___x_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_662_, 0, v___x_661_);
return v___x_662_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__2(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_663_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1);
v___x_664_ = lean_unsigned_to_nat(0u);
v___x_665_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
lean_ctor_set(v___x_665_, 2, v___x_664_);
lean_ctor_set(v___x_665_, 3, v___x_664_);
lean_ctor_set(v___x_665_, 4, v___x_663_);
lean_ctor_set(v___x_665_, 5, v___x_663_);
lean_ctor_set(v___x_665_, 6, v___x_663_);
lean_ctor_set(v___x_665_, 7, v___x_663_);
lean_ctor_set(v___x_665_, 8, v___x_663_);
lean_ctor_set(v___x_665_, 9, v___x_663_);
lean_ctor_set(v___x_665_, 10, v___x_663_);
return v___x_665_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__3(void){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_666_ = lean_unsigned_to_nat(32u);
v___x_667_ = lean_mk_empty_array_with_capacity(v___x_666_);
v___x_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
return v___x_668_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__4(void){
_start:
{
size_t v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_669_ = ((size_t)5ULL);
v___x_670_ = lean_unsigned_to_nat(0u);
v___x_671_ = lean_unsigned_to_nat(32u);
v___x_672_ = lean_mk_empty_array_with_capacity(v___x_671_);
v___x_673_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__3);
v___x_674_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_674_, 0, v___x_673_);
lean_ctor_set(v___x_674_, 1, v___x_672_);
lean_ctor_set(v___x_674_, 2, v___x_670_);
lean_ctor_set(v___x_674_, 3, v___x_670_);
lean_ctor_set_usize(v___x_674_, 4, v___x_669_);
return v___x_674_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__5(void){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_675_ = lean_box(1);
v___x_676_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__4);
v___x_677_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1);
v___x_678_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
lean_ctor_set(v___x_678_, 1, v___x_676_);
lean_ctor_set(v___x_678_, 2, v___x_675_);
return v___x_678_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7(void){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__6));
v___x_681_ = l_Lean_stringToMessageData(v___x_680_);
return v___x_681_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__9(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__8));
v___x_684_ = l_Lean_stringToMessageData(v___x_683_);
return v___x_684_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__11(void){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__10));
v___x_687_ = l_Lean_stringToMessageData(v___x_686_);
return v___x_687_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__13(void){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__12));
v___x_690_ = l_Lean_stringToMessageData(v___x_689_);
return v___x_690_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__15(void){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__14));
v___x_693_ = l_Lean_stringToMessageData(v___x_692_);
return v___x_693_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__17(void){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__16));
v___x_696_ = l_Lean_stringToMessageData(v___x_695_);
return v___x_696_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__19(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__18));
v___x_699_ = l_Lean_stringToMessageData(v___x_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(lean_object* v_msg_700_, lean_object* v_declHint_701_, lean_object* v___y_702_){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v_env_706_; uint8_t v___x_707_; 
v___x_704_ = lean_box(0);
v___x_705_ = lean_st_ref_get(v___y_702_);
v_env_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc_ref(v_env_706_);
lean_dec(v___x_705_);
v___x_707_ = l_Lean_Name_isAnonymous(v_declHint_701_);
if (v___x_707_ == 0)
{
uint8_t v_isExporting_708_; 
v_isExporting_708_ = lean_ctor_get_uint8(v_env_706_, sizeof(void*)*8);
if (v_isExporting_708_ == 0)
{
lean_object* v___x_709_; 
lean_dec_ref(v_env_706_);
lean_dec(v_declHint_701_);
v___x_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_709_, 0, v_msg_700_);
return v___x_709_;
}
else
{
lean_object* v___x_710_; uint8_t v___x_711_; 
lean_inc_ref(v_env_706_);
v___x_710_ = l_Lean_Environment_setExporting(v_env_706_, v___x_707_);
lean_inc(v_declHint_701_);
lean_inc_ref(v___x_710_);
v___x_711_ = l_Lean_Environment_contains(v___x_710_, v_declHint_701_, v_isExporting_708_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; 
lean_dec_ref(v___x_710_);
lean_dec_ref(v_env_706_);
lean_dec(v_declHint_701_);
v___x_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_712_, 0, v_msg_700_);
return v___x_712_;
}
else
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v_c_718_; lean_object* v___x_719_; 
v___x_713_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__2);
v___x_714_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__5);
v___x_715_ = l_Lean_Options_empty;
v___x_716_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_716_, 0, v___x_710_);
lean_ctor_set(v___x_716_, 1, v___x_713_);
lean_ctor_set(v___x_716_, 2, v___x_714_);
lean_ctor_set(v___x_716_, 3, v___x_715_);
lean_inc(v_declHint_701_);
v___x_717_ = l_Lean_MessageData_ofConstName(v_declHint_701_, v___x_707_);
v_c_718_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_718_, 0, v___x_716_);
lean_ctor_set(v_c_718_, 1, v___x_717_);
v___x_719_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_706_, v_declHint_701_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
lean_dec_ref(v_env_706_);
lean_dec(v_declHint_701_);
v___x_720_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7);
v___x_721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
lean_ctor_set(v___x_721_, 1, v_c_718_);
v___x_722_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__9);
v___x_723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_721_);
lean_ctor_set(v___x_723_, 1, v___x_722_);
v___x_724_ = l_Lean_MessageData_note(v___x_723_);
v___x_725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_725_, 0, v_msg_700_);
lean_ctor_set(v___x_725_, 1, v___x_724_);
v___x_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
return v___x_726_;
}
else
{
lean_object* v_val_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_761_; 
v_val_727_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_761_ == 0)
{
v___x_729_ = v___x_719_;
v_isShared_730_ = v_isSharedCheck_761_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_val_727_);
lean_dec(v___x_719_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_761_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v_mod_733_; uint8_t v___x_734_; 
v___x_731_ = l_Lean_Environment_header(v_env_706_);
lean_dec_ref(v_env_706_);
v___x_732_ = l_Lean_EnvironmentHeader_moduleNames(v___x_731_);
v_mod_733_ = lean_array_get(v___x_704_, v___x_732_, v_val_727_);
lean_dec(v_val_727_);
lean_dec_ref(v___x_732_);
v___x_734_ = l_Lean_isPrivateName(v_declHint_701_);
lean_dec(v_declHint_701_);
if (v___x_734_ == 0)
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_746_; 
v___x_735_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__11);
v___x_736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
lean_ctor_set(v___x_736_, 1, v_c_718_);
v___x_737_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__13);
v___x_738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_736_);
lean_ctor_set(v___x_738_, 1, v___x_737_);
v___x_739_ = l_Lean_MessageData_ofName(v_mod_733_);
v___x_740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_738_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
v___x_741_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__15);
v___x_742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_740_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = l_Lean_MessageData_note(v___x_742_);
v___x_744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_744_, 0, v_msg_700_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
if (v_isShared_730_ == 0)
{
lean_ctor_set_tag(v___x_729_, 0);
lean_ctor_set(v___x_729_, 0, v___x_744_);
v___x_746_ = v___x_729_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_744_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
else
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_759_; 
v___x_748_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7);
v___x_749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
lean_ctor_set(v___x_749_, 1, v_c_718_);
v___x_750_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__17);
v___x_751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_749_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
v___x_752_ = l_Lean_MessageData_ofName(v_mod_733_);
v___x_753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_751_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__19);
v___x_755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_753_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
v___x_756_ = l_Lean_MessageData_note(v___x_755_);
v___x_757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_757_, 0, v_msg_700_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
if (v_isShared_730_ == 0)
{
lean_ctor_set_tag(v___x_729_, 0);
lean_ctor_set(v___x_729_, 0, v___x_757_);
v___x_759_ = v___x_729_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_757_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_762_; 
lean_dec_ref(v_env_706_);
lean_dec(v_declHint_701_);
v___x_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_762_, 0, v_msg_700_);
return v___x_762_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___boxed(lean_object* v_msg_763_, lean_object* v_declHint_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(v_msg_763_, v_declHint_764_, v___y_765_);
lean_dec(v___y_765_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30(lean_object* v_msg_768_, lean_object* v_declHint_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v___x_779_; lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_789_; 
v___x_779_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(v_msg_768_, v_declHint_769_, v___y_777_);
v_a_780_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_789_ == 0)
{
v___x_782_ = v___x_779_;
v_isShared_783_ = v_isSharedCheck_789_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_779_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_789_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_787_; 
v___x_784_ = l_Lean_unknownIdentifierMessageTag;
v___x_785_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_784_);
lean_ctor_set(v___x_785_, 1, v_a_780_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v___x_785_);
v___x_787_ = v___x_782_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_785_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30___boxed(lean_object* v_msg_790_, lean_object* v_declHint_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30(v_msg_790_, v_declHint_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v___y_793_);
lean_dec(v___y_792_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(lean_object* v_ref_802_, lean_object* v_msg_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v_toCold_813_; lean_object* v_currRecDepth_814_; lean_object* v_ref_815_; uint8_t v_diag_816_; uint8_t v_suppressElabErrors_817_; lean_object* v_ref_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v_toCold_813_ = lean_ctor_get(v___y_810_, 0);
v_currRecDepth_814_ = lean_ctor_get(v___y_810_, 1);
v_ref_815_ = lean_ctor_get(v___y_810_, 2);
v_diag_816_ = lean_ctor_get_uint8(v___y_810_, sizeof(void*)*3);
v_suppressElabErrors_817_ = lean_ctor_get_uint8(v___y_810_, sizeof(void*)*3 + 1);
v_ref_818_ = l_Lean_replaceRef(v_ref_802_, v_ref_815_);
lean_inc(v_currRecDepth_814_);
lean_inc_ref(v_toCold_813_);
v___x_819_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_819_, 0, v_toCold_813_);
lean_ctor_set(v___x_819_, 1, v_currRecDepth_814_);
lean_ctor_set(v___x_819_, 2, v_ref_818_);
lean_ctor_set_uint8(v___x_819_, sizeof(void*)*3, v_diag_816_);
lean_ctor_set_uint8(v___x_819_, sizeof(void*)*3 + 1, v_suppressElabErrors_817_);
v___x_820_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v_msg_803_, v___y_808_, v___y_809_, v___x_819_, v___y_811_);
lean_dec_ref_known(v___x_819_, 3);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg___boxed(lean_object* v_ref_821_, lean_object* v_msg_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(v_ref_821_, v_msg_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
lean_dec(v___y_823_);
lean_dec(v_ref_821_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(lean_object* v_ref_833_, lean_object* v_msg_834_, lean_object* v_declHint_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v___x_845_; lean_object* v_a_846_; lean_object* v___x_847_; 
v___x_845_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30(v_msg_834_, v_declHint_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
v_a_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_a_846_);
lean_dec_ref(v___x_845_);
v___x_847_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(v_ref_833_, v_a_846_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg___boxed(lean_object* v_ref_848_, lean_object* v_msg_849_, lean_object* v_declHint_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(v_ref_848_, v_msg_849_, v_declHint_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec(v___y_851_);
lean_dec(v_ref_848_);
return v_res_860_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1(void){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__0));
v___x_863_ = l_Lean_stringToMessageData(v___x_862_);
return v___x_863_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3(void){
_start:
{
lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_865_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__2));
v___x_866_ = l_Lean_stringToMessageData(v___x_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(lean_object* v_ref_867_, lean_object* v_constName_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
lean_object* v___x_878_; uint8_t v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_878_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1);
v___x_879_ = 0;
lean_inc(v_constName_868_);
v___x_880_ = l_Lean_MessageData_ofConstName(v_constName_868_, v___x_879_);
v___x_881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_878_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v___x_882_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3);
v___x_883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_881_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
v___x_884_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(v_ref_867_, v___x_883_, v_constName_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___boxed(lean_object* v_ref_885_, lean_object* v_constName_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(v_ref_885_, v_constName_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_888_);
lean_dec(v___y_887_);
lean_dec(v_ref_885_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(lean_object* v_constName_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v_ref_907_; lean_object* v___x_908_; 
v_ref_907_ = lean_ctor_get(v___y_904_, 2);
v___x_908_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(v_ref_907_, v_constName_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg___boxed(lean_object* v_constName_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(v_constName_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
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
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(lean_object* v_constName_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v___x_930_; lean_object* v_env_931_; uint8_t v___x_932_; lean_object* v___x_933_; 
v___x_930_ = lean_st_ref_get(v___y_928_);
v_env_931_ = lean_ctor_get(v___x_930_, 0);
lean_inc_ref(v_env_931_);
lean_dec(v___x_930_);
v___x_932_ = 0;
lean_inc(v_constName_920_);
v___x_933_ = l_Lean_Environment_find_x3f(v_env_931_, v_constName_920_, v___x_932_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v___x_934_; 
v___x_934_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(v_constName_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
return v___x_934_;
}
else
{
lean_object* v_val_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_942_; 
lean_dec(v_constName_920_);
v_val_935_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_942_ == 0)
{
v___x_937_ = v___x_933_;
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_val_935_);
lean_dec(v___x_933_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_938_ == 0)
{
lean_ctor_set_tag(v___x_937_, 0);
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_val_935_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18___boxed(lean_object* v_constName_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(v_constName_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec(v___y_944_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(lean_object* v_declName_954_, lean_object* v___y_955_){
_start:
{
lean_object* v___x_957_; lean_object* v_env_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_957_ = lean_st_ref_get(v___y_955_);
v_env_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc_ref(v_env_958_);
lean_dec(v___x_957_);
v___x_959_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_958_, v_declName_954_);
v___x_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg___boxed(lean_object* v_declName_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(v_declName_961_, v___y_962_);
lean_dec(v___y_962_);
return v_res_964_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0(void){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l_instMonadEIO___redArg();
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19(lean_object* v_msg_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v_toApplicative_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_1077_; 
v___x_982_ = lean_obj_once(&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0, &l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0_once, _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0);
v___x_983_ = l_StateRefT_x27_instMonad___redArg(v___x_982_);
v_toApplicative_984_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_1077_ == 0)
{
lean_object* v_unused_1078_; 
v_unused_1078_ = lean_ctor_get(v___x_983_, 1);
lean_dec(v_unused_1078_);
v___x_986_ = v___x_983_;
v_isShared_987_ = v_isSharedCheck_1077_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_toApplicative_984_);
lean_dec(v___x_983_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_1077_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v_toFunctor_988_; lean_object* v_toSeq_989_; lean_object* v_toSeqLeft_990_; lean_object* v_toSeqRight_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1075_; 
v_toFunctor_988_ = lean_ctor_get(v_toApplicative_984_, 0);
v_toSeq_989_ = lean_ctor_get(v_toApplicative_984_, 2);
v_toSeqLeft_990_ = lean_ctor_get(v_toApplicative_984_, 3);
v_toSeqRight_991_ = lean_ctor_get(v_toApplicative_984_, 4);
v_isSharedCheck_1075_ = !lean_is_exclusive(v_toApplicative_984_);
if (v_isSharedCheck_1075_ == 0)
{
lean_object* v_unused_1076_; 
v_unused_1076_ = lean_ctor_get(v_toApplicative_984_, 1);
lean_dec(v_unused_1076_);
v___x_993_ = v_toApplicative_984_;
v_isShared_994_ = v_isSharedCheck_1075_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_toSeqRight_991_);
lean_inc(v_toSeqLeft_990_);
lean_inc(v_toSeq_989_);
lean_inc(v_toFunctor_988_);
lean_dec(v_toApplicative_984_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1075_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___f_995_; lean_object* v___f_996_; lean_object* v___f_997_; lean_object* v___f_998_; lean_object* v___x_999_; lean_object* v___f_1000_; lean_object* v___f_1001_; lean_object* v___f_1002_; lean_object* v___x_1004_; 
v___f_995_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__1));
v___f_996_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__2));
lean_inc_ref(v_toFunctor_988_);
v___f_997_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_997_, 0, v_toFunctor_988_);
v___f_998_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_998_, 0, v_toFunctor_988_);
v___x_999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_999_, 0, v___f_997_);
lean_ctor_set(v___x_999_, 1, v___f_998_);
v___f_1000_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1000_, 0, v_toSeqRight_991_);
v___f_1001_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1001_, 0, v_toSeqLeft_990_);
v___f_1002_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1002_, 0, v_toSeq_989_);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 4, v___f_1000_);
lean_ctor_set(v___x_993_, 3, v___f_1001_);
lean_ctor_set(v___x_993_, 2, v___f_1002_);
lean_ctor_set(v___x_993_, 1, v___f_995_);
lean_ctor_set(v___x_993_, 0, v___x_999_);
v___x_1004_ = v___x_993_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_999_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v___f_995_);
lean_ctor_set(v_reuseFailAlloc_1074_, 2, v___f_1002_);
lean_ctor_set(v_reuseFailAlloc_1074_, 3, v___f_1001_);
lean_ctor_set(v_reuseFailAlloc_1074_, 4, v___f_1000_);
v___x_1004_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
lean_object* v___x_1006_; 
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 1, v___f_996_);
lean_ctor_set(v___x_986_, 0, v___x_1004_);
v___x_1006_ = v___x_986_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1004_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v___f_996_);
v___x_1006_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
lean_object* v___x_1007_; lean_object* v_toApplicative_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1071_; 
v___x_1007_ = l_StateRefT_x27_instMonad___redArg(v___x_1006_);
v_toApplicative_1008_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1071_ == 0)
{
lean_object* v_unused_1072_; 
v_unused_1072_ = lean_ctor_get(v___x_1007_, 1);
lean_dec(v_unused_1072_);
v___x_1010_ = v___x_1007_;
v_isShared_1011_ = v_isSharedCheck_1071_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_toApplicative_1008_);
lean_dec(v___x_1007_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1071_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v_toFunctor_1012_; lean_object* v_toSeq_1013_; lean_object* v_toSeqLeft_1014_; lean_object* v_toSeqRight_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1069_; 
v_toFunctor_1012_ = lean_ctor_get(v_toApplicative_1008_, 0);
v_toSeq_1013_ = lean_ctor_get(v_toApplicative_1008_, 2);
v_toSeqLeft_1014_ = lean_ctor_get(v_toApplicative_1008_, 3);
v_toSeqRight_1015_ = lean_ctor_get(v_toApplicative_1008_, 4);
v_isSharedCheck_1069_ = !lean_is_exclusive(v_toApplicative_1008_);
if (v_isSharedCheck_1069_ == 0)
{
lean_object* v_unused_1070_; 
v_unused_1070_ = lean_ctor_get(v_toApplicative_1008_, 1);
lean_dec(v_unused_1070_);
v___x_1017_ = v_toApplicative_1008_;
v_isShared_1018_ = v_isSharedCheck_1069_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_toSeqRight_1015_);
lean_inc(v_toSeqLeft_1014_);
lean_inc(v_toSeq_1013_);
lean_inc(v_toFunctor_1012_);
lean_dec(v_toApplicative_1008_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1069_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___f_1019_; lean_object* v___f_1020_; lean_object* v___f_1021_; lean_object* v___f_1022_; lean_object* v___x_1023_; lean_object* v___f_1024_; lean_object* v___f_1025_; lean_object* v___f_1026_; lean_object* v___x_1028_; 
v___f_1019_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__3));
v___f_1020_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__4));
lean_inc_ref(v_toFunctor_1012_);
v___f_1021_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1021_, 0, v_toFunctor_1012_);
v___f_1022_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1022_, 0, v_toFunctor_1012_);
v___x_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___f_1021_);
lean_ctor_set(v___x_1023_, 1, v___f_1022_);
v___f_1024_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1024_, 0, v_toSeqRight_1015_);
v___f_1025_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1025_, 0, v_toSeqLeft_1014_);
v___f_1026_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1026_, 0, v_toSeq_1013_);
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 4, v___f_1024_);
lean_ctor_set(v___x_1017_, 3, v___f_1025_);
lean_ctor_set(v___x_1017_, 2, v___f_1026_);
lean_ctor_set(v___x_1017_, 1, v___f_1019_);
lean_ctor_set(v___x_1017_, 0, v___x_1023_);
v___x_1028_ = v___x_1017_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1023_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v___f_1019_);
lean_ctor_set(v_reuseFailAlloc_1068_, 2, v___f_1026_);
lean_ctor_set(v_reuseFailAlloc_1068_, 3, v___f_1025_);
lean_ctor_set(v_reuseFailAlloc_1068_, 4, v___f_1024_);
v___x_1028_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
lean_object* v___x_1030_; 
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 1, v___f_1020_);
lean_ctor_set(v___x_1010_, 0, v___x_1028_);
v___x_1030_ = v___x_1010_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1028_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v___f_1020_);
v___x_1030_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
lean_object* v___x_1031_; lean_object* v_toApplicative_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1065_; 
v___x_1031_ = l_StateRefT_x27_instMonad___redArg(v___x_1030_);
v_toApplicative_1032_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1065_ == 0)
{
lean_object* v_unused_1066_; 
v_unused_1066_ = lean_ctor_get(v___x_1031_, 1);
lean_dec(v_unused_1066_);
v___x_1034_ = v___x_1031_;
v_isShared_1035_ = v_isSharedCheck_1065_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_toApplicative_1032_);
lean_dec(v___x_1031_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1065_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v_toFunctor_1036_; lean_object* v_toSeq_1037_; lean_object* v_toSeqLeft_1038_; lean_object* v_toSeqRight_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1063_; 
v_toFunctor_1036_ = lean_ctor_get(v_toApplicative_1032_, 0);
v_toSeq_1037_ = lean_ctor_get(v_toApplicative_1032_, 2);
v_toSeqLeft_1038_ = lean_ctor_get(v_toApplicative_1032_, 3);
v_toSeqRight_1039_ = lean_ctor_get(v_toApplicative_1032_, 4);
v_isSharedCheck_1063_ = !lean_is_exclusive(v_toApplicative_1032_);
if (v_isSharedCheck_1063_ == 0)
{
lean_object* v_unused_1064_; 
v_unused_1064_ = lean_ctor_get(v_toApplicative_1032_, 1);
lean_dec(v_unused_1064_);
v___x_1041_ = v_toApplicative_1032_;
v_isShared_1042_ = v_isSharedCheck_1063_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_toSeqRight_1039_);
lean_inc(v_toSeqLeft_1038_);
lean_inc(v_toSeq_1037_);
lean_inc(v_toFunctor_1036_);
lean_dec(v_toApplicative_1032_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1063_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___f_1043_; lean_object* v___f_1044_; lean_object* v___f_1045_; lean_object* v___f_1046_; lean_object* v___x_1047_; lean_object* v___f_1048_; lean_object* v___f_1049_; lean_object* v___f_1050_; lean_object* v___x_1052_; 
v___f_1043_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__5));
v___f_1044_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__6));
lean_inc_ref(v_toFunctor_1036_);
v___f_1045_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1045_, 0, v_toFunctor_1036_);
v___f_1046_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1046_, 0, v_toFunctor_1036_);
v___x_1047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___f_1045_);
lean_ctor_set(v___x_1047_, 1, v___f_1046_);
v___f_1048_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1048_, 0, v_toSeqRight_1039_);
v___f_1049_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1049_, 0, v_toSeqLeft_1038_);
v___f_1050_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1050_, 0, v_toSeq_1037_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 4, v___f_1048_);
lean_ctor_set(v___x_1041_, 3, v___f_1049_);
lean_ctor_set(v___x_1041_, 2, v___f_1050_);
lean_ctor_set(v___x_1041_, 1, v___f_1043_);
lean_ctor_set(v___x_1041_, 0, v___x_1047_);
v___x_1052_ = v___x_1041_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1047_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v___f_1043_);
lean_ctor_set(v_reuseFailAlloc_1062_, 2, v___f_1050_);
lean_ctor_set(v_reuseFailAlloc_1062_, 3, v___f_1049_);
lean_ctor_set(v_reuseFailAlloc_1062_, 4, v___f_1048_);
v___x_1052_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
lean_object* v___x_1054_; 
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 1, v___f_1044_);
lean_ctor_set(v___x_1034_, 0, v___x_1052_);
v___x_1054_ = v___x_1034_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1052_);
lean_ctor_set(v_reuseFailAlloc_1061_, 1, v___f_1044_);
v___x_1054_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_49652__overap_1059_; lean_object* v___x_1060_; 
v___x_1055_ = l_StateRefT_x27_instMonad___redArg(v___x_1054_);
v___x_1056_ = l_StateRefT_x27_instMonad___redArg(v___x_1055_);
v___x_1057_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_1058_ = l_instInhabitedOfMonad___redArg(v___x_1056_, v___x_1057_);
v___x_49652__overap_1059_ = lean_panic_fn_borrowed(v___x_1058_, v_msg_972_);
lean_dec(v___x_1058_);
lean_inc(v___y_980_);
lean_inc_ref(v___y_979_);
lean_inc(v___y_978_);
lean_inc_ref(v___y_977_);
lean_inc(v___y_976_);
lean_inc_ref(v___y_975_);
lean_inc(v___y_974_);
lean_inc(v___y_973_);
v___x_1060_ = lean_apply_9(v___x_49652__overap_1059_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, lean_box(0));
return v___x_1060_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___boxed(lean_object* v_msg_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19(v_msg_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec(v___y_1080_);
return v_res_1089_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3(void){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1093_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__2));
v___x_1094_ = lean_unsigned_to_nat(53u);
v___x_1095_ = lean_unsigned_to_nat(62u);
v___x_1096_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__1));
v___x_1097_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__0));
v___x_1098_ = l_mkPanicMessageWithDecl(v___x_1097_, v___x_1096_, v___x_1095_, v___x_1094_, v___x_1093_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21(size_t v_sz_1099_, size_t v_i_1100_, lean_object* v_bs_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
uint8_t v___x_1111_; 
v___x_1111_ = lean_usize_dec_lt(v_i_1100_, v_sz_1099_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; 
v___x_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1112_, 0, v_bs_1101_);
return v___x_1112_;
}
else
{
lean_object* v_v_1113_; lean_object* v___x_1114_; lean_object* v_bs_x27_1115_; lean_object* v_a_1117_; lean_object* v___x_1122_; 
v_v_1113_ = lean_array_uget(v_bs_1101_, v_i_1100_);
v___x_1114_ = lean_unsigned_to_nat(0u);
v_bs_x27_1115_ = lean_array_uset(v_bs_1101_, v_i_1100_, v___x_1114_);
v___x_1122_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(v_v_1113_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_a_1123_; 
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_a_1123_);
lean_dec_ref_known(v___x_1122_, 1);
if (lean_obj_tag(v_a_1123_) == 6)
{
lean_object* v_val_1124_; lean_object* v_numFields_1125_; uint8_t v___x_1126_; lean_object* v___x_1127_; 
v_val_1124_ = lean_ctor_get(v_a_1123_, 0);
lean_inc_ref(v_val_1124_);
lean_dec_ref_known(v_a_1123_, 1);
v_numFields_1125_ = lean_ctor_get(v_val_1124_, 4);
lean_inc(v_numFields_1125_);
lean_dec_ref(v_val_1124_);
v___x_1126_ = 0;
v___x_1127_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1127_, 0, v_numFields_1125_);
lean_ctor_set(v___x_1127_, 1, v___x_1114_);
lean_ctor_set_uint8(v___x_1127_, sizeof(void*)*2, v___x_1126_);
v_a_1117_ = v___x_1127_;
goto v___jp_1116_;
}
else
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
lean_dec(v_a_1123_);
v___x_1128_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3);
v___x_1129_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19(v___x_1128_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v_a_1130_; 
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_a_1130_);
lean_dec_ref_known(v___x_1129_, 1);
v_a_1117_ = v_a_1130_;
goto v___jp_1116_;
}
else
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
lean_dec_ref(v_bs_x27_1115_);
v_a_1131_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1129_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1129_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
}
else
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
lean_dec_ref(v_bs_x27_1115_);
v_a_1139_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1141_ = v___x_1122_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1122_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_a_1139_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
v___jp_1116_:
{
size_t v___x_1118_; size_t v___x_1119_; lean_object* v___x_1120_; 
v___x_1118_ = ((size_t)1ULL);
v___x_1119_ = lean_usize_add(v_i_1100_, v___x_1118_);
v___x_1120_ = lean_array_uset(v_bs_x27_1115_, v_i_1100_, v_a_1117_);
v_i_1100_ = v___x_1119_;
v_bs_1101_ = v___x_1120_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___boxed(lean_object* v_sz_1147_, lean_object* v_i_1148_, lean_object* v_bs_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
size_t v_sz_boxed_1159_; size_t v_i_boxed_1160_; lean_object* v_res_1161_; 
v_sz_boxed_1159_ = lean_unbox_usize(v_sz_1147_);
lean_dec(v_sz_1147_);
v_i_boxed_1160_ = lean_unbox_usize(v_i_1148_);
lean_dec(v_i_1148_);
v_res_1161_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21(v_sz_boxed_1159_, v_i_boxed_1160_, v_bs_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
lean_dec(v___y_1150_);
return v_res_1161_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0(void){
_start:
{
lean_object* v___x_1162_; lean_object* v_dummy_1163_; 
v___x_1162_ = lean_box(0);
v_dummy_1163_ = l_Lean_Expr_sort___override(v___x_1162_);
return v_dummy_1163_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1(void){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1164_ = lean_box(0);
v___x_1165_ = lean_unsigned_to_nat(16u);
v___x_1166_ = lean_mk_array(v___x_1165_, v___x_1164_);
return v___x_1166_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2(void){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1167_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1);
v___x_1168_ = lean_unsigned_to_nat(0u);
v___x_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1168_);
lean_ctor_set(v___x_1169_, 1, v___x_1167_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(lean_object* v_e_1172_, uint8_t v_alsoCasesOn_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
uint8_t v___x_1186_; 
v___x_1186_ = l_Lean_Expr_isApp(v_e_1172_);
if (v___x_1186_ == 0)
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
lean_dec_ref(v_e_1172_);
v___x_1187_ = lean_box(0);
v___x_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1187_);
return v___x_1188_;
}
else
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Lean_Expr_getAppFn(v_e_1172_);
if (lean_obj_tag(v___x_1189_) == 4)
{
lean_object* v_declName_1190_; lean_object* v_us_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1346_; 
v_declName_1190_ = lean_ctor_get(v___x_1189_, 0);
lean_inc_n(v_declName_1190_, 2);
v_us_1191_ = lean_ctor_get(v___x_1189_, 1);
lean_inc(v_us_1191_);
lean_dec_ref_known(v___x_1189_, 2);
v___x_1192_ = l_Lean_instInhabitedExpr;
v___x_1193_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(v_declName_1190_, v___y_1181_);
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1196_ = v___x_1193_;
v_isShared_1197_ = v_isSharedCheck_1346_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1193_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1346_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
if (lean_obj_tag(v_a_1194_) == 1)
{
lean_object* v_val_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1239_; 
v_val_1198_ = lean_ctor_get(v_a_1194_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v_a_1194_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1200_ = v_a_1194_;
v_isShared_1201_ = v_isSharedCheck_1239_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_val_1198_);
lean_dec(v_a_1194_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1239_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v_dummy_1202_; lean_object* v_nargs_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v_args_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; uint8_t v___x_1210_; 
v_dummy_1202_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
v_nargs_1203_ = l_Lean_Expr_getAppNumArgs(v_e_1172_);
lean_inc(v_nargs_1203_);
v___x_1204_ = lean_mk_array(v_nargs_1203_, v_dummy_1202_);
v___x_1205_ = lean_unsigned_to_nat(1u);
v___x_1206_ = lean_nat_sub(v_nargs_1203_, v___x_1205_);
lean_dec(v_nargs_1203_);
v_args_1207_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1172_, v___x_1204_, v___x_1206_);
v___x_1208_ = lean_array_get_size(v_args_1207_);
v___x_1209_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_1198_);
v___x_1210_ = lean_nat_dec_lt(v___x_1208_, v___x_1209_);
lean_dec(v___x_1209_);
if (v___x_1210_ == 0)
{
lean_object* v_numParams_1211_; lean_object* v_numDiscrs_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1230_; 
v_numParams_1211_ = lean_ctor_get(v_val_1198_, 0);
v_numDiscrs_1212_ = lean_ctor_get(v_val_1198_, 1);
v___x_1213_ = lean_array_mk(v_us_1191_);
v___x_1214_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1211_);
v___x_1215_ = l_Array_extract___redArg(v_args_1207_, v___x_1214_, v_numParams_1211_);
v___x_1216_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_1198_);
v___x_1217_ = lean_array_get(v___x_1192_, v_args_1207_, v___x_1216_);
lean_dec(v___x_1216_);
v___x_1218_ = lean_nat_add(v_numParams_1211_, v___x_1205_);
v___x_1219_ = lean_nat_add(v___x_1218_, v_numDiscrs_1212_);
lean_inc(v___x_1219_);
lean_inc_ref_n(v_args_1207_, 2);
v___x_1220_ = l_Array_toSubarray___redArg(v_args_1207_, v___x_1218_, v___x_1219_);
v___x_1221_ = l_Subarray_copy___redArg(v___x_1220_);
v___x_1222_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1198_);
v___x_1223_ = lean_nat_add(v___x_1219_, v___x_1222_);
lean_dec(v___x_1222_);
lean_inc(v___x_1223_);
v___x_1224_ = l_Array_toSubarray___redArg(v_args_1207_, v___x_1219_, v___x_1223_);
v___x_1225_ = l_Subarray_copy___redArg(v___x_1224_);
v___x_1226_ = l_Array_toSubarray___redArg(v_args_1207_, v___x_1223_, v___x_1208_);
v___x_1227_ = l_Subarray_copy___redArg(v___x_1226_);
v___x_1228_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1228_, 0, v_val_1198_);
lean_ctor_set(v___x_1228_, 1, v_declName_1190_);
lean_ctor_set(v___x_1228_, 2, v___x_1213_);
lean_ctor_set(v___x_1228_, 3, v___x_1215_);
lean_ctor_set(v___x_1228_, 4, v___x_1217_);
lean_ctor_set(v___x_1228_, 5, v___x_1221_);
lean_ctor_set(v___x_1228_, 6, v___x_1225_);
lean_ctor_set(v___x_1228_, 7, v___x_1227_);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 0, v___x_1228_);
v___x_1230_ = v___x_1200_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1228_);
v___x_1230_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
lean_object* v___x_1232_; 
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 0, v___x_1230_);
v___x_1232_ = v___x_1196_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v___x_1230_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
else
{
lean_object* v___x_1235_; lean_object* v___x_1237_; 
lean_dec_ref(v_args_1207_);
lean_del_object(v___x_1200_);
lean_dec(v_val_1198_);
lean_dec(v_us_1191_);
lean_dec(v_declName_1190_);
v___x_1235_ = lean_box(0);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 0, v___x_1235_);
v___x_1237_ = v___x_1196_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v___x_1235_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
}
else
{
lean_object* v___x_1240_; 
lean_del_object(v___x_1196_);
lean_dec(v_a_1194_);
v___x_1240_ = lean_st_ref_get(v___y_1181_);
if (v_alsoCasesOn_1173_ == 0)
{
lean_dec(v___x_1240_);
lean_dec(v_us_1191_);
lean_dec(v_declName_1190_);
lean_dec_ref(v_e_1172_);
goto v___jp_1183_;
}
else
{
lean_object* v_env_1241_; uint8_t v___x_1242_; 
v_env_1241_ = lean_ctor_get(v___x_1240_, 0);
lean_inc_ref(v_env_1241_);
lean_dec(v___x_1240_);
lean_inc(v_declName_1190_);
v___x_1242_ = l_Lean_isCasesOnRecursor(v_env_1241_, v_declName_1190_);
if (v___x_1242_ == 0)
{
lean_dec(v_us_1191_);
lean_dec(v_declName_1190_);
lean_dec_ref(v_e_1172_);
goto v___jp_1183_;
}
else
{
lean_object* v_indName_1243_; lean_object* v___x_1244_; 
v_indName_1243_ = l_Lean_Name_getPrefix(v_declName_1190_);
v___x_1244_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(v_indName_1243_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1337_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1247_ = v___x_1244_;
v_isShared_1248_ = v_isSharedCheck_1337_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1244_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1337_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
if (lean_obj_tag(v_a_1245_) == 5)
{
lean_object* v_val_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1332_; 
v_val_1249_ = lean_ctor_get(v_a_1245_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v_a_1245_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1251_ = v_a_1245_;
v_isShared_1252_ = v_isSharedCheck_1332_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_val_1249_);
lean_dec(v_a_1245_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1332_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v_toConstantVal_1253_; lean_object* v_numParams_1254_; lean_object* v_numIndices_1255_; lean_object* v_ctors_1256_; lean_object* v_nargs_1257_; lean_object* v_dummy_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v_args_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; uint8_t v___x_1269_; 
v_toConstantVal_1253_ = lean_ctor_get(v_val_1249_, 0);
lean_inc_ref(v_toConstantVal_1253_);
v_numParams_1254_ = lean_ctor_get(v_val_1249_, 1);
lean_inc(v_numParams_1254_);
v_numIndices_1255_ = lean_ctor_get(v_val_1249_, 2);
lean_inc(v_numIndices_1255_);
v_ctors_1256_ = lean_ctor_get(v_val_1249_, 4);
lean_inc(v_ctors_1256_);
v_nargs_1257_ = l_Lean_Expr_getAppNumArgs(v_e_1172_);
v_dummy_1258_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v_nargs_1257_);
v___x_1259_ = lean_mk_array(v_nargs_1257_, v_dummy_1258_);
v___x_1260_ = lean_unsigned_to_nat(1u);
v___x_1261_ = lean_nat_sub(v_nargs_1257_, v___x_1260_);
lean_dec(v_nargs_1257_);
v_args_1262_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1172_, v___x_1259_, v___x_1261_);
v___x_1263_ = lean_nat_add(v_numParams_1254_, v___x_1260_);
v___x_1264_ = lean_nat_add(v___x_1263_, v_numIndices_1255_);
v___x_1265_ = lean_nat_add(v___x_1264_, v___x_1260_);
lean_dec(v___x_1264_);
v___x_1266_ = l_Lean_InductiveVal_numCtors(v_val_1249_);
lean_dec_ref(v_val_1249_);
v___x_1267_ = lean_nat_add(v___x_1265_, v___x_1266_);
lean_dec(v___x_1266_);
v___x_1268_ = lean_array_get_size(v_args_1262_);
v___x_1269_ = lean_nat_dec_le(v___x_1267_, v___x_1268_);
if (v___x_1269_ == 0)
{
lean_object* v___x_1270_; lean_object* v___x_1272_; 
lean_dec(v___x_1267_);
lean_dec(v___x_1265_);
lean_dec(v___x_1263_);
lean_dec_ref(v_args_1262_);
lean_dec(v_ctors_1256_);
lean_dec(v_numIndices_1255_);
lean_dec(v_numParams_1254_);
lean_dec_ref(v_toConstantVal_1253_);
lean_del_object(v___x_1251_);
lean_dec(v_us_1191_);
lean_dec(v_declName_1190_);
v___x_1270_ = lean_box(0);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 0, v___x_1270_);
v___x_1272_ = v___x_1247_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1270_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
else
{
lean_object* v___x_1274_; lean_object* v_params_1275_; lean_object* v_motive_1276_; lean_object* v_discrs_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v_discrInfos_1280_; lean_object* v_alts_1281_; lean_object* v___y_1283_; lean_object* v___y_1284_; lean_object* v_lower_1323_; lean_object* v_upper_1324_; uint8_t v___x_1331_; 
lean_del_object(v___x_1247_);
v___x_1274_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1254_);
lean_inc_ref_n(v_args_1262_, 3);
v_params_1275_ = l_Array_toSubarray___redArg(v_args_1262_, v___x_1274_, v_numParams_1254_);
v_motive_1276_ = lean_array_get(v___x_1192_, v_args_1262_, v_numParams_1254_);
lean_dec(v_numParams_1254_);
lean_inc(v___x_1265_);
v_discrs_1277_ = l_Array_toSubarray___redArg(v_args_1262_, v___x_1263_, v___x_1265_);
v___x_1278_ = lean_nat_add(v_numIndices_1255_, v___x_1260_);
lean_dec(v_numIndices_1255_);
v___x_1279_ = lean_box(0);
v_discrInfos_1280_ = lean_mk_array(v___x_1278_, v___x_1279_);
lean_inc(v___x_1267_);
v_alts_1281_ = l_Array_toSubarray___redArg(v_args_1262_, v___x_1265_, v___x_1267_);
v___x_1331_ = lean_nat_dec_le(v___x_1267_, v___x_1274_);
if (v___x_1331_ == 0)
{
v_lower_1323_ = v___x_1267_;
v_upper_1324_ = v___x_1268_;
goto v___jp_1322_;
}
else
{
lean_dec(v___x_1267_);
v_lower_1323_ = v___x_1274_;
v_upper_1324_ = v___x_1268_;
goto v___jp_1322_;
}
v___jp_1282_:
{
lean_object* v___x_1285_; size_t v_sz_1286_; size_t v___x_1287_; lean_object* v___x_1288_; 
v___x_1285_ = lean_array_mk(v_ctors_1256_);
v_sz_1286_ = lean_array_size(v___x_1285_);
v___x_1287_ = ((size_t)0ULL);
v___x_1288_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21(v_sz_1286_, v___x_1287_, v___x_1285_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1313_; 
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1291_ = v___x_1288_;
v_isShared_1292_ = v_isSharedCheck_1313_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1288_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1313_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v_start_1293_; lean_object* v_stop_1294_; lean_object* v_start_1295_; lean_object* v_stop_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1308_; 
v_start_1293_ = lean_ctor_get(v_params_1275_, 1);
lean_inc(v_start_1293_);
v_stop_1294_ = lean_ctor_get(v_params_1275_, 2);
lean_inc(v_stop_1294_);
v_start_1295_ = lean_ctor_get(v_discrs_1277_, 1);
lean_inc(v_start_1295_);
v_stop_1296_ = lean_ctor_get(v_discrs_1277_, 2);
lean_inc(v_stop_1296_);
v___x_1297_ = lean_nat_sub(v_stop_1294_, v_start_1293_);
lean_dec(v_start_1293_);
lean_dec(v_stop_1294_);
v___x_1298_ = lean_nat_sub(v_stop_1296_, v_start_1295_);
lean_dec(v_start_1295_);
lean_dec(v_stop_1296_);
v___x_1299_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2);
v___x_1300_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1297_);
lean_ctor_set(v___x_1300_, 1, v___x_1298_);
lean_ctor_set(v___x_1300_, 2, v_a_1289_);
lean_ctor_set(v___x_1300_, 3, v___y_1284_);
lean_ctor_set(v___x_1300_, 4, v_discrInfos_1280_);
lean_ctor_set(v___x_1300_, 5, v___x_1299_);
v___x_1301_ = lean_array_mk(v_us_1191_);
v___x_1302_ = l_Subarray_copy___redArg(v_params_1275_);
v___x_1303_ = l_Subarray_copy___redArg(v_discrs_1277_);
v___x_1304_ = l_Subarray_copy___redArg(v_alts_1281_);
v___x_1305_ = l_Subarray_copy___redArg(v___y_1283_);
v___x_1306_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1300_);
lean_ctor_set(v___x_1306_, 1, v_declName_1190_);
lean_ctor_set(v___x_1306_, 2, v___x_1301_);
lean_ctor_set(v___x_1306_, 3, v___x_1302_);
lean_ctor_set(v___x_1306_, 4, v_motive_1276_);
lean_ctor_set(v___x_1306_, 5, v___x_1303_);
lean_ctor_set(v___x_1306_, 6, v___x_1304_);
lean_ctor_set(v___x_1306_, 7, v___x_1305_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set_tag(v___x_1251_, 1);
lean_ctor_set(v___x_1251_, 0, v___x_1306_);
v___x_1308_ = v___x_1251_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1306_);
v___x_1308_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
lean_object* v___x_1310_; 
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 0, v___x_1308_);
v___x_1310_ = v___x_1291_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v___x_1308_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1321_; 
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec_ref(v_alts_1281_);
lean_dec_ref(v_discrInfos_1280_);
lean_dec_ref(v_discrs_1277_);
lean_dec(v_motive_1276_);
lean_dec_ref(v_params_1275_);
lean_del_object(v___x_1251_);
lean_dec(v_us_1191_);
lean_dec(v_declName_1190_);
v_a_1314_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1316_ = v___x_1288_;
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1288_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1314_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
v___jp_1322_:
{
lean_object* v_levelParams_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; uint8_t v___x_1329_; 
v_levelParams_1325_ = lean_ctor_get(v_toConstantVal_1253_, 1);
lean_inc(v_levelParams_1325_);
lean_dec_ref(v_toConstantVal_1253_);
v___x_1326_ = l_Array_toSubarray___redArg(v_args_1262_, v_lower_1323_, v_upper_1324_);
v___x_1327_ = l_List_lengthTR___redArg(v_levelParams_1325_);
lean_dec(v_levelParams_1325_);
v___x_1328_ = l_List_lengthTR___redArg(v_us_1191_);
v___x_1329_ = lean_nat_dec_eq(v___x_1327_, v___x_1328_);
lean_dec(v___x_1328_);
lean_dec(v___x_1327_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; 
v___x_1330_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__3));
v___y_1283_ = v___x_1326_;
v___y_1284_ = v___x_1330_;
goto v___jp_1282_;
}
else
{
v___y_1283_ = v___x_1326_;
v___y_1284_ = v___x_1279_;
goto v___jp_1282_;
}
}
}
}
}
else
{
lean_object* v___x_1333_; lean_object* v___x_1335_; 
lean_dec(v_a_1245_);
lean_dec(v_us_1191_);
lean_dec(v_declName_1190_);
lean_dec_ref(v_e_1172_);
v___x_1333_ = lean_box(0);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 0, v___x_1333_);
v___x_1335_ = v___x_1247_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1333_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
else
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1345_; 
lean_dec(v_us_1191_);
lean_dec(v_declName_1190_);
lean_dec_ref(v_e_1172_);
v_a_1338_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1340_ = v___x_1244_;
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1244_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1343_; 
if (v_isShared_1341_ == 0)
{
v___x_1343_ = v___x_1340_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_a_1338_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
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
lean_dec_ref(v___x_1189_);
lean_dec_ref(v_e_1172_);
goto v___jp_1183_;
}
}
v___jp_1183_:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1184_ = lean_box(0);
v___x_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
return v___x_1185_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___boxed(lean_object* v_e_1347_, lean_object* v_alsoCasesOn_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
uint8_t v_alsoCasesOn_boxed_1358_; lean_object* v_res_1359_; 
v_alsoCasesOn_boxed_1358_ = lean_unbox(v_alsoCasesOn_1348_);
v_res_1359_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(v_e_1347_, v_alsoCasesOn_boxed_1358_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
lean_dec(v___y_1350_);
lean_dec(v___y_1349_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0(lean_object* v_k_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v_b_1365_, lean_object* v_c_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v___x_1372_; 
lean_inc(v___y_1370_);
lean_inc_ref(v___y_1369_);
lean_inc(v___y_1368_);
lean_inc_ref(v___y_1367_);
lean_inc(v___y_1364_);
lean_inc_ref(v___y_1363_);
lean_inc(v___y_1362_);
lean_inc(v___y_1361_);
v___x_1372_ = lean_apply_11(v_k_1360_, v_b_1365_, v_c_1366_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, lean_box(0));
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0___boxed(lean_object* v_k_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v_b_1378_, lean_object* v_c_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0(v_k_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v_b_1378_, v_c_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec(v___y_1374_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(lean_object* v_e_1386_, lean_object* v_maxFVars_1387_, lean_object* v_k_1388_, uint8_t v_cleanupAnnotations_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v___f_1399_; uint8_t v___x_1400_; uint8_t v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
lean_inc(v___y_1393_);
lean_inc_ref(v___y_1392_);
lean_inc(v___y_1391_);
lean_inc(v___y_1390_);
v___f_1399_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1399_, 0, v_k_1388_);
lean_closure_set(v___f_1399_, 1, v___y_1390_);
lean_closure_set(v___f_1399_, 2, v___y_1391_);
lean_closure_set(v___f_1399_, 3, v___y_1392_);
lean_closure_set(v___f_1399_, 4, v___y_1393_);
v___x_1400_ = 1;
v___x_1401_ = 0;
v___x_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1402_, 0, v_maxFVars_1387_);
v___x_1403_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1386_, v___x_1400_, v___x_1401_, v___x_1400_, v___x_1401_, v___x_1402_, v___f_1399_, v_cleanupAnnotations_1389_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
lean_dec_ref_known(v___x_1402_, 1);
if (lean_obj_tag(v___x_1403_) == 0)
{
return v___x_1403_;
}
else
{
lean_object* v_a_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1411_; 
v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1406_ = v___x_1403_;
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_a_1404_);
lean_dec(v___x_1403_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1409_; 
if (v_isShared_1407_ == 0)
{
v___x_1409_ = v___x_1406_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_a_1404_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___boxed(lean_object* v_e_1412_, lean_object* v_maxFVars_1413_, lean_object* v_k_1414_, lean_object* v_cleanupAnnotations_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1425_; lean_object* v_res_1426_; 
v_cleanupAnnotations_boxed_1425_ = lean_unbox(v_cleanupAnnotations_1415_);
v_res_1426_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(v_e_1412_, v_maxFVars_1413_, v_k_1414_, v_cleanupAnnotations_boxed_1425_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec(v___y_1416_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0(lean_object* v_k_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v_b_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v___x_1438_; 
lean_inc(v___y_1436_);
lean_inc_ref(v___y_1435_);
lean_inc(v___y_1434_);
lean_inc_ref(v___y_1433_);
lean_inc(v___y_1431_);
lean_inc_ref(v___y_1430_);
lean_inc(v___y_1429_);
lean_inc(v___y_1428_);
v___x_1438_ = lean_apply_10(v_k_1427_, v_b_1432_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, lean_box(0));
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0___boxed(lean_object* v_k_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v_b_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0(v_k_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v_b_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec(v___y_1440_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(lean_object* v_name_1451_, lean_object* v_type_1452_, lean_object* v_val_1453_, lean_object* v_k_1454_, uint8_t v_nondep_1455_, uint8_t v_kind_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v___f_1466_; lean_object* v___x_1467_; 
lean_inc(v___y_1460_);
lean_inc_ref(v___y_1459_);
lean_inc(v___y_1458_);
lean_inc(v___y_1457_);
v___f_1466_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1466_, 0, v_k_1454_);
lean_closure_set(v___f_1466_, 1, v___y_1457_);
lean_closure_set(v___f_1466_, 2, v___y_1458_);
lean_closure_set(v___f_1466_, 3, v___y_1459_);
lean_closure_set(v___f_1466_, 4, v___y_1460_);
v___x_1467_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1451_, v_type_1452_, v_val_1453_, v___f_1466_, v_nondep_1455_, v_kind_1456_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
if (lean_obj_tag(v___x_1467_) == 0)
{
return v___x_1467_;
}
else
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
v_a_1468_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___x_1467_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1467_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_a_1468_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg___boxed(lean_object* v_name_1476_, lean_object* v_type_1477_, lean_object* v_val_1478_, lean_object* v_k_1479_, lean_object* v_nondep_1480_, lean_object* v_kind_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
uint8_t v_nondep_boxed_1491_; uint8_t v_kind_boxed_1492_; lean_object* v_res_1493_; 
v_nondep_boxed_1491_ = lean_unbox(v_nondep_1480_);
v_kind_boxed_1492_ = lean_unbox(v_kind_1481_);
v_res_1493_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(v_name_1476_, v_type_1477_, v_val_1478_, v_k_1479_, v_nondep_boxed_1491_, v_kind_boxed_1492_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec(v___y_1483_);
lean_dec(v___y_1482_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0(lean_object* v_k_1494_, uint8_t v_usedLetOnly_1495_, lean_object* v_x_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v___x_1506_; 
lean_inc(v___y_1504_);
lean_inc_ref(v___y_1503_);
lean_inc(v___y_1502_);
lean_inc_ref(v___y_1501_);
lean_inc(v___y_1500_);
lean_inc_ref(v___y_1499_);
lean_inc(v___y_1498_);
lean_inc(v___y_1497_);
lean_inc_ref(v_x_1496_);
v___x_1506_ = lean_apply_10(v_k_1494_, v_x_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, lean_box(0));
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_object* v_a_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; uint8_t v___x_1511_; uint8_t v___x_1512_; lean_object* v___x_1513_; 
v_a_1507_ = lean_ctor_get(v___x_1506_, 0);
lean_inc(v_a_1507_);
lean_dec_ref_known(v___x_1506_, 1);
v___x_1508_ = lean_unsigned_to_nat(1u);
v___x_1509_ = lean_mk_empty_array_with_capacity(v___x_1508_);
v___x_1510_ = lean_array_push(v___x_1509_, v_x_1496_);
v___x_1511_ = 0;
v___x_1512_ = 1;
v___x_1513_ = l_Lean_Meta_mkLetFVars(v___x_1510_, v_a_1507_, v_usedLetOnly_1495_, v___x_1511_, v___x_1512_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
lean_dec_ref(v___x_1510_);
return v___x_1513_;
}
else
{
lean_dec_ref(v_x_1496_);
return v___x_1506_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0___boxed(lean_object* v_k_1514_, lean_object* v_usedLetOnly_1515_, lean_object* v_x_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
uint8_t v_usedLetOnly_boxed_1526_; lean_object* v_res_1527_; 
v_usedLetOnly_boxed_1526_ = lean_unbox(v_usedLetOnly_1515_);
v_res_1527_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0(v_k_1514_, v_usedLetOnly_boxed_1526_, v_x_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec(v___y_1517_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(lean_object* v_name_1528_, lean_object* v_type_1529_, lean_object* v_val_1530_, lean_object* v_k_1531_, uint8_t v_nondep_1532_, uint8_t v_kind_1533_, uint8_t v_usedLetOnly_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v___x_1544_; lean_object* v___f_1545_; lean_object* v___x_1546_; 
v___x_1544_ = lean_box(v_usedLetOnly_1534_);
v___f_1545_ = lean_alloc_closure((void*)(l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0___boxed), 12, 2);
lean_closure_set(v___f_1545_, 0, v_k_1531_);
lean_closure_set(v___f_1545_, 1, v___x_1544_);
v___x_1546_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(v_name_1528_, v_type_1529_, v_val_1530_, v___f_1545_, v_nondep_1532_, v_kind_1533_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___boxed(lean_object* v_name_1547_, lean_object* v_type_1548_, lean_object* v_val_1549_, lean_object* v_k_1550_, lean_object* v_nondep_1551_, lean_object* v_kind_1552_, lean_object* v_usedLetOnly_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
uint8_t v_nondep_boxed_1563_; uint8_t v_kind_boxed_1564_; uint8_t v_usedLetOnly_boxed_1565_; lean_object* v_res_1566_; 
v_nondep_boxed_1563_ = lean_unbox(v_nondep_1551_);
v_kind_boxed_1564_ = lean_unbox(v_kind_1552_);
v_usedLetOnly_boxed_1565_ = lean_unbox(v_usedLetOnly_1553_);
v_res_1566_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(v_name_1547_, v_type_1548_, v_val_1549_, v_k_1550_, v_nondep_boxed_1563_, v_kind_boxed_1564_, v_usedLetOnly_boxed_1565_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec(v___y_1555_);
lean_dec(v___y_1554_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(lean_object* v_name_1567_, uint8_t v_bi_1568_, lean_object* v_type_1569_, lean_object* v_k_1570_, uint8_t v_kind_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v___f_1581_; lean_object* v___x_1582_; 
lean_inc(v___y_1575_);
lean_inc_ref(v___y_1574_);
lean_inc(v___y_1573_);
lean_inc(v___y_1572_);
v___f_1581_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1581_, 0, v_k_1570_);
lean_closure_set(v___f_1581_, 1, v___y_1572_);
lean_closure_set(v___f_1581_, 2, v___y_1573_);
lean_closure_set(v___f_1581_, 3, v___y_1574_);
lean_closure_set(v___f_1581_, 4, v___y_1575_);
v___x_1582_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1567_, v_bi_1568_, v_type_1569_, v___f_1581_, v_kind_1571_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
if (lean_obj_tag(v___x_1582_) == 0)
{
return v___x_1582_;
}
else
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1585_ = v___x_1582_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1582_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1583_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___boxed(lean_object* v_name_1591_, lean_object* v_bi_1592_, lean_object* v_type_1593_, lean_object* v_k_1594_, lean_object* v_kind_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
uint8_t v_bi_boxed_1605_; uint8_t v_kind_boxed_1606_; lean_object* v_res_1607_; 
v_bi_boxed_1605_ = lean_unbox(v_bi_1592_);
v_kind_boxed_1606_ = lean_unbox(v_kind_1595_);
v_res_1607_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_name_1591_, v_bi_boxed_1605_, v_type_1593_, v_k_1594_, v_kind_boxed_1606_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec(v___y_1597_);
lean_dec(v___y_1596_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0(lean_object* v_k_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0___boxed(lean_object* v_k_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0(v_k_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_dec(v___y_1620_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(lean_object* v_k_1630_, uint8_t v_allowLevelAssignments_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
lean_object* v___f_1641_; lean_object* v___x_1642_; 
lean_inc(v___y_1635_);
lean_inc_ref(v___y_1634_);
lean_inc(v___y_1633_);
lean_inc(v___y_1632_);
v___f_1641_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0___boxed), 10, 5);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___boxed(lean_object* v_k_1651_, lean_object* v_allowLevelAssignments_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1662_; lean_object* v_res_1663_; 
v_allowLevelAssignments_boxed_1662_ = lean_unbox(v_allowLevelAssignments_1652_);
v_res_1663_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v_k_1651_, v_allowLevelAssignments_boxed_1662_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(lean_object* v_a_1664_, lean_object* v_x_1665_){
_start:
{
if (lean_obj_tag(v_x_1665_) == 0)
{
lean_object* v___x_1666_; 
v___x_1666_ = lean_box(0);
return v___x_1666_;
}
else
{
lean_object* v_key_1667_; lean_object* v_value_1668_; lean_object* v_tail_1669_; uint8_t v___x_1670_; 
v_key_1667_ = lean_ctor_get(v_x_1665_, 0);
v_value_1668_ = lean_ctor_get(v_x_1665_, 1);
v_tail_1669_ = lean_ctor_get(v_x_1665_, 2);
v___x_1670_ = lean_expr_eqv(v_key_1667_, v_a_1664_);
if (v___x_1670_ == 0)
{
v_x_1665_ = v_tail_1669_;
goto _start;
}
else
{
lean_object* v___x_1672_; 
lean_inc(v_value_1668_);
v___x_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1672_, 0, v_value_1668_);
return v___x_1672_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg___boxed(lean_object* v_a_1673_, lean_object* v_x_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(v_a_1673_, v_x_1674_);
lean_dec(v_x_1674_);
lean_dec_ref(v_a_1673_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(lean_object* v_m_1676_, lean_object* v_a_1677_){
_start:
{
lean_object* v_buckets_1678_; lean_object* v___x_1679_; uint64_t v___x_1680_; uint64_t v___x_1681_; uint64_t v___x_1682_; uint64_t v_fold_1683_; uint64_t v___x_1684_; uint64_t v___x_1685_; uint64_t v___x_1686_; size_t v___x_1687_; size_t v___x_1688_; size_t v___x_1689_; size_t v___x_1690_; size_t v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v_buckets_1678_ = lean_ctor_get(v_m_1676_, 1);
v___x_1679_ = lean_array_get_size(v_buckets_1678_);
v___x_1680_ = l_Lean_Expr_hash(v_a_1677_);
v___x_1681_ = 32ULL;
v___x_1682_ = lean_uint64_shift_right(v___x_1680_, v___x_1681_);
v_fold_1683_ = lean_uint64_xor(v___x_1680_, v___x_1682_);
v___x_1684_ = 16ULL;
v___x_1685_ = lean_uint64_shift_right(v_fold_1683_, v___x_1684_);
v___x_1686_ = lean_uint64_xor(v_fold_1683_, v___x_1685_);
v___x_1687_ = lean_uint64_to_usize(v___x_1686_);
v___x_1688_ = lean_usize_of_nat(v___x_1679_);
v___x_1689_ = ((size_t)1ULL);
v___x_1690_ = lean_usize_sub(v___x_1688_, v___x_1689_);
v___x_1691_ = lean_usize_land(v___x_1687_, v___x_1690_);
v___x_1692_ = lean_array_uget_borrowed(v_buckets_1678_, v___x_1691_);
v___x_1693_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(v_a_1677_, v___x_1692_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg___boxed(lean_object* v_m_1694_, lean_object* v_a_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v_m_1694_, v_a_1695_);
lean_dec_ref(v_a_1695_);
lean_dec_ref(v_m_1694_);
return v_res_1696_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(lean_object* v_opts_1697_, lean_object* v_opt_1698_){
_start:
{
lean_object* v_name_1699_; lean_object* v_defValue_1700_; lean_object* v_map_1701_; lean_object* v___x_1702_; 
v_name_1699_ = lean_ctor_get(v_opt_1698_, 0);
v_defValue_1700_ = lean_ctor_get(v_opt_1698_, 1);
v_map_1701_ = lean_ctor_get(v_opts_1697_, 0);
v___x_1702_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1701_, v_name_1699_);
if (lean_obj_tag(v___x_1702_) == 0)
{
uint8_t v___x_1703_; 
v___x_1703_ = lean_unbox(v_defValue_1700_);
return v___x_1703_;
}
else
{
lean_object* v_val_1704_; 
v_val_1704_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_val_1704_);
lean_dec_ref_known(v___x_1702_, 1);
if (lean_obj_tag(v_val_1704_) == 1)
{
uint8_t v_v_1705_; 
v_v_1705_ = lean_ctor_get_uint8(v_val_1704_, 0);
lean_dec_ref_known(v_val_1704_, 0);
return v_v_1705_;
}
else
{
uint8_t v___x_1706_; 
lean_dec(v_val_1704_);
v___x_1706_ = lean_unbox(v_defValue_1700_);
return v___x_1706_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5___boxed(lean_object* v_opts_1707_, lean_object* v_opt_1708_){
_start:
{
uint8_t v_res_1709_; lean_object* v_r_1710_; 
v_res_1709_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v_opts_1707_, v_opt_1708_);
lean_dec_ref(v_opt_1708_);
lean_dec_ref(v_opts_1707_);
v_r_1710_ = lean_box(v_res_1709_);
return v_r_1710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(lean_object* v_a_1711_, lean_object* v_b_1712_){
_start:
{
lean_object* v_array_1713_; lean_object* v_start_1714_; lean_object* v_stop_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1728_; 
v_array_1713_ = lean_ctor_get(v_a_1711_, 0);
v_start_1714_ = lean_ctor_get(v_a_1711_, 1);
v_stop_1715_ = lean_ctor_get(v_a_1711_, 2);
v_isSharedCheck_1728_ = !lean_is_exclusive(v_a_1711_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1717_ = v_a_1711_;
v_isShared_1718_ = v_isSharedCheck_1728_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_stop_1715_);
lean_inc(v_start_1714_);
lean_inc(v_array_1713_);
lean_dec(v_a_1711_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1728_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
uint8_t v___x_1719_; 
v___x_1719_ = lean_nat_dec_lt(v_start_1714_, v_stop_1715_);
if (v___x_1719_ == 0)
{
lean_del_object(v___x_1717_);
lean_dec(v_stop_1715_);
lean_dec(v_start_1714_);
lean_dec_ref(v_array_1713_);
return v_b_1712_;
}
else
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1723_; 
v___x_1720_ = lean_unsigned_to_nat(1u);
v___x_1721_ = lean_nat_add(v_start_1714_, v___x_1720_);
lean_inc_ref(v_array_1713_);
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 1, v___x_1721_);
v___x_1723_ = v___x_1717_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_array_1713_);
lean_ctor_set(v_reuseFailAlloc_1727_, 1, v___x_1721_);
lean_ctor_set(v_reuseFailAlloc_1727_, 2, v_stop_1715_);
v___x_1723_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1724_ = lean_array_fget(v_array_1713_, v_start_1714_);
lean_dec(v_start_1714_);
lean_dec_ref(v_array_1713_);
v___x_1725_ = lean_array_push(v_b_1712_, v___x_1724_);
v_a_1711_ = v___x_1723_;
v_b_1712_ = v___x_1725_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0(lean_object* v_body_1729_, lean_object* v_recFnName_1730_, lean_object* v_fixedPrefixSize_1731_, lean_object* v_F_1732_, lean_object* v_x_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1743_ = lean_expr_instantiate1(v_body_1729_, v_x_1733_);
v___x_1744_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1730_, v_fixedPrefixSize_1731_, v_F_1732_, v___x_1743_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v_a_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; uint8_t v___x_1749_; uint8_t v___x_1750_; uint8_t v___x_1751_; lean_object* v___x_1752_; 
v_a_1745_ = lean_ctor_get(v___x_1744_, 0);
lean_inc(v_a_1745_);
lean_dec_ref_known(v___x_1744_, 1);
v___x_1746_ = lean_unsigned_to_nat(1u);
v___x_1747_ = lean_mk_empty_array_with_capacity(v___x_1746_);
v___x_1748_ = lean_array_push(v___x_1747_, v_x_1733_);
v___x_1749_ = 0;
v___x_1750_ = 1;
v___x_1751_ = 1;
v___x_1752_ = l_Lean_Meta_mkLambdaFVars(v___x_1748_, v_a_1745_, v___x_1749_, v___x_1750_, v___x_1749_, v___x_1750_, v___x_1751_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
lean_dec_ref(v___x_1748_);
return v___x_1752_;
}
else
{
lean_dec_ref(v_x_1733_);
return v___x_1744_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0___boxed(lean_object* v_body_1753_, lean_object* v_recFnName_1754_, lean_object* v_fixedPrefixSize_1755_, lean_object* v_F_1756_, lean_object* v_x_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0(v_body_1753_, v_recFnName_1754_, v_fixedPrefixSize_1755_, v_F_1756_, v_x_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v_body_1753_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1(lean_object* v_body_1768_, lean_object* v_recFnName_1769_, lean_object* v_fixedPrefixSize_1770_, lean_object* v_F_1771_, lean_object* v_x_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1782_ = lean_expr_instantiate1(v_body_1768_, v_x_1772_);
v___x_1783_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1769_, v_fixedPrefixSize_1770_, v_F_1771_, v___x_1782_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v_a_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; uint8_t v___x_1788_; uint8_t v___x_1789_; uint8_t v___x_1790_; lean_object* v___x_1791_; 
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_a_1784_);
lean_dec_ref_known(v___x_1783_, 1);
v___x_1785_ = lean_unsigned_to_nat(1u);
v___x_1786_ = lean_mk_empty_array_with_capacity(v___x_1785_);
v___x_1787_ = lean_array_push(v___x_1786_, v_x_1772_);
v___x_1788_ = 0;
v___x_1789_ = 1;
v___x_1790_ = 1;
v___x_1791_ = l_Lean_Meta_mkForallFVars(v___x_1787_, v_a_1784_, v___x_1788_, v___x_1789_, v___x_1789_, v___x_1790_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
lean_dec_ref(v___x_1787_);
return v___x_1791_;
}
else
{
lean_dec_ref(v_x_1772_);
return v___x_1783_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1___boxed(lean_object* v_body_1792_, lean_object* v_recFnName_1793_, lean_object* v_fixedPrefixSize_1794_, lean_object* v_F_1795_, lean_object* v_x_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1(v_body_1792_, v_recFnName_1793_, v_fixedPrefixSize_1794_, v_F_1795_, v_x_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1799_);
lean_dec(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec_ref(v_body_1792_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2___boxed(lean_object* v_body_1807_, lean_object* v_recFnName_1808_, lean_object* v_fixedPrefixSize_1809_, lean_object* v_F_1810_, lean_object* v_x_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2(v_body_1807_, v_recFnName_1808_, v_fixedPrefixSize_1809_, v_F_1810_, v_x_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v_x_1811_);
lean_dec_ref(v_body_1807_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(lean_object* v_recFnName_1824_, lean_object* v_fixedPrefixSize_1825_, lean_object* v_F_1826_, size_t v_sz_1827_, size_t v_i_1828_, lean_object* v_bs_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
uint8_t v___x_1839_; 
v___x_1839_ = lean_usize_dec_lt(v_i_1828_, v_sz_1827_);
if (v___x_1839_ == 0)
{
lean_object* v___x_1840_; 
lean_dec_ref(v_F_1826_);
lean_dec(v_fixedPrefixSize_1825_);
lean_dec(v_recFnName_1824_);
v___x_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1840_, 0, v_bs_1829_);
return v___x_1840_;
}
else
{
lean_object* v_v_1841_; lean_object* v___x_1842_; lean_object* v_bs_x27_1843_; lean_object* v___x_1844_; 
v_v_1841_ = lean_array_uget(v_bs_1829_, v_i_1828_);
v___x_1842_ = lean_unsigned_to_nat(0u);
v_bs_x27_1843_ = lean_array_uset(v_bs_1829_, v_i_1828_, v___x_1842_);
lean_inc_ref(v_F_1826_);
lean_inc(v_fixedPrefixSize_1825_);
lean_inc(v_recFnName_1824_);
v___x_1844_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1824_, v_fixedPrefixSize_1825_, v_F_1826_, v_v_1841_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v_a_1845_; size_t v___x_1846_; size_t v___x_1847_; lean_object* v___x_1848_; 
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
lean_inc(v_a_1845_);
lean_dec_ref_known(v___x_1844_, 1);
v___x_1846_ = ((size_t)1ULL);
v___x_1847_ = lean_usize_add(v_i_1828_, v___x_1846_);
v___x_1848_ = lean_array_uset(v_bs_x27_1843_, v_i_1828_, v_a_1845_);
v_i_1828_ = v___x_1847_;
v_bs_1829_ = v___x_1848_;
goto _start;
}
else
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1857_; 
lean_dec_ref(v_bs_x27_1843_);
lean_dec_ref(v_F_1826_);
lean_dec(v_fixedPrefixSize_1825_);
lean_dec(v_recFnName_1824_);
v_a_1850_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1852_ = v___x_1844_;
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1844_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1855_; 
if (v_isShared_1853_ == 0)
{
v___x_1855_ = v___x_1852_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_a_1850_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4(void){
_start:
{
lean_object* v_cls_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v_cls_1865_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_1866_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__3));
v___x_1867_ = l_Lean_Name_append(v___x_1866_, v_cls_1865_);
return v___x_1867_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6(void){
_start:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1869_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5));
v___x_1870_ = l_Lean_stringToMessageData(v___x_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(lean_object* v_recFnName_1871_, lean_object* v_fixedPrefixSize_1872_, lean_object* v_F_1873_, lean_object* v_e_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_){
_start:
{
lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; uint8_t v___x_1899_; 
v___x_1896_ = l_Lean_Expr_getAppNumArgs(v_e_1874_);
v___x_1897_ = lean_unsigned_to_nat(1u);
v___x_1898_ = lean_nat_add(v_fixedPrefixSize_1872_, v___x_1897_);
v___x_1899_ = lean_nat_dec_lt(v___x_1896_, v___x_1898_);
if (v___x_1899_ == 0)
{
lean_object* v___x_1900_; lean_object* v_dummy_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v_args_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1900_ = l_Lean_instInhabitedExpr;
v_dummy_1901_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_1896_);
v___x_1902_ = lean_mk_array(v___x_1896_, v_dummy_1901_);
v___x_1903_ = lean_nat_sub(v___x_1896_, v___x_1897_);
lean_dec(v___x_1896_);
v_args_1904_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1874_, v___x_1902_, v___x_1903_);
v___x_1905_ = lean_array_get(v___x_1900_, v_args_1904_, v_fixedPrefixSize_1872_);
lean_inc_ref(v_F_1873_);
lean_inc(v_fixedPrefixSize_1872_);
lean_inc(v_recFnName_1871_);
v___x_1906_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1871_, v_fixedPrefixSize_1872_, v_F_1873_, v___x_1905_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
lean_inc(v_a_1907_);
lean_dec_ref_known(v___x_1906_, 1);
lean_inc_ref(v_F_1873_);
v___x_1908_ = l_Lean_Expr_app___override(v_F_1873_, v_a_1907_);
lean_inc(v_a_1882_);
lean_inc_ref(v_a_1881_);
lean_inc(v_a_1880_);
lean_inc_ref(v_a_1879_);
lean_inc_ref(v___x_1908_);
v___x_1909_ = lean_infer_type(v___x_1908_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v_a_1910_; lean_object* v___x_1911_; 
v_a_1910_ = lean_ctor_get(v___x_1909_, 0);
lean_inc(v_a_1910_);
lean_dec_ref_known(v___x_1909_, 1);
lean_inc(v_a_1882_);
lean_inc_ref(v_a_1881_);
lean_inc(v_a_1880_);
lean_inc_ref(v_a_1879_);
v___x_1911_ = lean_whnf(v_a_1910_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1912_);
lean_dec_ref_known(v___x_1911_, 1);
v___x_1913_ = l_Lean_Expr_bindingDomain_x21(v_a_1912_);
lean_dec(v_a_1912_);
v___x_1914_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg(v___x_1913_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_a_1915_; lean_object* v___x_1916_; lean_object* v_lower_1918_; lean_object* v_upper_1919_; lean_object* v___x_1943_; lean_object* v___x_1944_; uint8_t v___x_1945_; 
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
lean_inc(v_a_1915_);
lean_dec_ref_known(v___x_1914_, 1);
v___x_1916_ = l_Lean_Expr_app___override(v___x_1908_, v_a_1915_);
v___x_1943_ = lean_unsigned_to_nat(0u);
v___x_1944_ = lean_array_get_size(v_args_1904_);
v___x_1945_ = lean_nat_dec_le(v___x_1898_, v___x_1943_);
if (v___x_1945_ == 0)
{
v_lower_1918_ = v___x_1898_;
v_upper_1919_ = v___x_1944_;
goto v___jp_1917_;
}
else
{
lean_dec(v___x_1898_);
v_lower_1918_ = v___x_1943_;
v_upper_1919_ = v___x_1944_;
goto v___jp_1917_;
}
v___jp_1917_:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; size_t v_sz_1923_; size_t v___x_1924_; lean_object* v___x_1925_; 
v___x_1920_ = l_Array_toSubarray___redArg(v_args_1904_, v_lower_1918_, v_upper_1919_);
v___x_1921_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
v___x_1922_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(v___x_1920_, v___x_1921_);
v_sz_1923_ = lean_array_size(v___x_1922_);
v___x_1924_ = ((size_t)0ULL);
v___x_1925_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_1871_, v_fixedPrefixSize_1872_, v_F_1873_, v_sz_1923_, v___x_1924_, v___x_1922_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1934_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1928_ = v___x_1925_;
v_isShared_1929_ = v_isSharedCheck_1934_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1925_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1934_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1930_; lean_object* v___x_1932_; 
v___x_1930_ = l_Lean_mkAppN(v___x_1916_, v_a_1926_);
lean_dec(v_a_1926_);
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 0, v___x_1930_);
v___x_1932_ = v___x_1928_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v___x_1930_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
else
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1942_; 
lean_dec_ref(v___x_1916_);
v_a_1935_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1937_ = v___x_1925_;
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1925_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1940_; 
if (v_isShared_1938_ == 0)
{
v___x_1940_ = v___x_1937_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_a_1935_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1908_);
lean_dec_ref(v_args_1904_);
lean_dec(v___x_1898_);
lean_dec_ref(v_F_1873_);
lean_dec(v_fixedPrefixSize_1872_);
lean_dec(v_recFnName_1871_);
return v___x_1914_;
}
}
else
{
lean_dec_ref(v___x_1908_);
lean_dec_ref(v_args_1904_);
lean_dec(v___x_1898_);
lean_dec_ref(v_F_1873_);
lean_dec(v_fixedPrefixSize_1872_);
lean_dec(v_recFnName_1871_);
return v___x_1911_;
}
}
else
{
lean_dec_ref(v___x_1908_);
lean_dec_ref(v_args_1904_);
lean_dec(v___x_1898_);
lean_dec_ref(v_F_1873_);
lean_dec(v_fixedPrefixSize_1872_);
lean_dec(v_recFnName_1871_);
return v___x_1909_;
}
}
else
{
lean_dec_ref(v_args_1904_);
lean_dec(v___x_1898_);
lean_dec_ref(v_F_1873_);
lean_dec(v_fixedPrefixSize_1872_);
lean_dec(v_recFnName_1871_);
return v___x_1906_;
}
}
else
{
lean_object* v_toCold_1946_; lean_object* v_options_1947_; uint8_t v_hasTrace_1948_; 
lean_dec(v___x_1898_);
lean_dec(v___x_1896_);
v_toCold_1946_ = lean_ctor_get(v_a_1881_, 0);
v_options_1947_ = lean_ctor_get(v_toCold_1946_, 2);
v_hasTrace_1948_ = lean_ctor_get_uint8(v_options_1947_, sizeof(void*)*1);
if (v_hasTrace_1948_ == 0)
{
v___y_1885_ = v_a_1875_;
v___y_1886_ = v_a_1876_;
v___y_1887_ = v_a_1877_;
v___y_1888_ = v_a_1878_;
v___y_1889_ = v_a_1879_;
v___y_1890_ = v_a_1880_;
v___y_1891_ = v_a_1881_;
v___y_1892_ = v_a_1882_;
goto v___jp_1884_;
}
else
{
lean_object* v_inheritedTraceOptions_1949_; lean_object* v_cls_1950_; lean_object* v___x_1951_; uint8_t v___x_1952_; 
v_inheritedTraceOptions_1949_ = lean_ctor_get(v_toCold_1946_, 11);
v_cls_1950_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_1951_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_1952_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1949_, v_options_1947_, v___x_1951_);
if (v___x_1952_ == 0)
{
v___y_1885_ = v_a_1875_;
v___y_1886_ = v_a_1876_;
v___y_1887_ = v_a_1877_;
v___y_1888_ = v_a_1878_;
v___y_1889_ = v_a_1879_;
v___y_1890_ = v_a_1880_;
v___y_1891_ = v_a_1881_;
v___y_1892_ = v_a_1882_;
goto v___jp_1884_;
}
else
{
lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1953_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6);
lean_inc_ref(v_e_1874_);
v___x_1954_ = l_Lean_indentExpr(v_e_1874_);
v___x_1955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1953_);
lean_ctor_set(v___x_1955_, 1, v___x_1954_);
v___x_1956_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(v_cls_1950_, v___x_1955_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_dec_ref_known(v___x_1956_, 1);
v___y_1885_ = v_a_1875_;
v___y_1886_ = v_a_1876_;
v___y_1887_ = v_a_1877_;
v___y_1888_ = v_a_1878_;
v___y_1889_ = v_a_1879_;
v___y_1890_ = v_a_1880_;
v___y_1891_ = v_a_1881_;
v___y_1892_ = v_a_1882_;
goto v___jp_1884_;
}
else
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
lean_dec_ref(v_e_1874_);
lean_dec_ref(v_F_1873_);
lean_dec(v_fixedPrefixSize_1872_);
lean_dec(v_recFnName_1871_);
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1959_ = v___x_1956_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1956_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1957_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
}
}
v___jp_1884_:
{
lean_object* v___x_1893_; 
v___x_1893_ = l_Lean_Meta_etaExpand(v_e_1874_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v_a_1894_; lean_object* v___x_1895_; 
v_a_1894_ = lean_ctor_get(v___x_1893_, 0);
lean_inc(v_a_1894_);
lean_dec_ref_known(v___x_1893_, 1);
v___x_1895_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1871_, v_fixedPrefixSize_1872_, v_F_1873_, v_a_1894_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
return v___x_1895_;
}
else
{
lean_dec_ref(v_F_1873_);
lean_dec(v_fixedPrefixSize_1872_);
lean_dec(v_recFnName_1871_);
return v___x_1893_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(lean_object* v_recFnName_1965_, lean_object* v_fixedPrefixSize_1966_, lean_object* v_F_1967_, lean_object* v_x_1968_, lean_object* v_x_1969_, lean_object* v_x_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
if (lean_obj_tag(v_x_1968_) == 5)
{
lean_object* v_fn_1980_; lean_object* v_arg_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v_fn_1980_ = lean_ctor_get(v_x_1968_, 0);
lean_inc_ref(v_fn_1980_);
v_arg_1981_ = lean_ctor_get(v_x_1968_, 1);
lean_inc_ref(v_arg_1981_);
lean_dec_ref_known(v_x_1968_, 2);
v___x_1982_ = lean_array_set(v_x_1969_, v_x_1970_, v_arg_1981_);
v___x_1983_ = lean_unsigned_to_nat(1u);
v___x_1984_ = lean_nat_sub(v_x_1970_, v___x_1983_);
lean_dec(v_x_1970_);
v_x_1968_ = v_fn_1980_;
v_x_1969_ = v___x_1982_;
v_x_1970_ = v___x_1984_;
goto _start;
}
else
{
lean_object* v___x_1986_; 
lean_dec(v_x_1970_);
lean_inc_ref(v_F_1967_);
lean_inc(v_fixedPrefixSize_1966_);
lean_inc(v_recFnName_1965_);
v___x_1986_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1965_, v_fixedPrefixSize_1966_, v_F_1967_, v_x_1968_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v_a_1987_; size_t v_sz_1988_; size_t v___x_1989_; lean_object* v___x_1990_; 
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_a_1987_);
lean_dec_ref_known(v___x_1986_, 1);
v_sz_1988_ = lean_array_size(v_x_1969_);
v___x_1989_ = ((size_t)0ULL);
v___x_1990_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_1965_, v_fixedPrefixSize_1966_, v_F_1967_, v_sz_1988_, v___x_1989_, v_x_1969_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_1999_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1993_ = v___x_1990_;
v_isShared_1994_ = v_isSharedCheck_1999_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1990_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_1999_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1995_; lean_object* v___x_1997_; 
v___x_1995_ = l_Lean_mkAppN(v_a_1987_, v_a_1991_);
lean_dec(v_a_1991_);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 0, v___x_1995_);
v___x_1997_ = v___x_1993_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1995_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
else
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
lean_dec(v_a_1987_);
v_a_2000_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1990_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1990_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2000_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
}
else
{
lean_dec_ref(v_x_1969_);
lean_dec_ref(v_F_1967_);
lean_dec(v_fixedPrefixSize_1966_);
lean_dec(v_recFnName_1965_);
return v___x_1986_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(lean_object* v_recFnName_2008_, lean_object* v_fixedPrefixSize_2009_, lean_object* v_F_2010_, lean_object* v_e_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_){
_start:
{
uint8_t v___x_2021_; 
v___x_2021_ = l_Lean_Expr_isAppOf(v_e_2011_, v_recFnName_2008_);
if (v___x_2021_ == 0)
{
lean_object* v_dummy_2022_; lean_object* v_nargs_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v_dummy_2022_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
v_nargs_2023_ = l_Lean_Expr_getAppNumArgs(v_e_2011_);
lean_inc(v_nargs_2023_);
v___x_2024_ = lean_mk_array(v_nargs_2023_, v_dummy_2022_);
v___x_2025_ = lean_unsigned_to_nat(1u);
v___x_2026_ = lean_nat_sub(v_nargs_2023_, v___x_2025_);
lean_dec(v_nargs_2023_);
v___x_2027_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(v_recFnName_2008_, v_fixedPrefixSize_2009_, v_F_2010_, v_e_2011_, v___x_2024_, v___x_2026_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
return v___x_2027_;
}
else
{
lean_object* v___x_2028_; 
v___x_2028_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2008_, v_fixedPrefixSize_2009_, v_F_2010_, v_e_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
return v___x_2028_;
}
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__0));
v___x_2031_ = l_Lean_stringToMessageData(v___x_2030_);
return v___x_2031_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2033_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__2));
v___x_2034_ = l_Lean_stringToMessageData(v___x_2033_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0(lean_object* v___x_2035_, lean_object* v_b_2036_, lean_object* v_recFnName_2037_, lean_object* v_fixedPrefixSize_2038_, uint8_t v___x_2039_, lean_object* v___x_2040_, lean_object* v_a_2041_, lean_object* v_e_2042_, lean_object* v_xs_2043_, lean_object* v_altBody_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v___x_2061_; uint8_t v___x_2062_; 
v___x_2061_ = lean_array_get_size(v_xs_2043_);
v___x_2062_ = lean_nat_dec_eq(v___x_2061_, v___x_2040_);
if (v___x_2062_ == 0)
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
lean_dec_ref(v_altBody_2044_);
lean_dec(v_fixedPrefixSize_2038_);
lean_dec(v_recFnName_2037_);
v___x_2063_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1);
v___x_2064_ = l_Lean_indentExpr(v_a_2041_);
v___x_2065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2063_);
lean_ctor_set(v___x_2065_, 1, v___x_2064_);
v___x_2066_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3);
v___x_2067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2065_);
lean_ctor_set(v___x_2067_, 1, v___x_2066_);
v___x_2068_ = l_Lean_indentExpr(v_e_2042_);
v___x_2069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2067_);
lean_ctor_set(v___x_2069_, 1, v___x_2068_);
v___x_2070_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v___x_2069_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2073_ = v___x_2070_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2070_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2076_; 
if (v_isShared_2074_ == 0)
{
v___x_2076_ = v___x_2073_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_a_2071_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
else
{
lean_dec_ref(v_e_2042_);
lean_dec_ref(v_a_2041_);
goto v___jp_2054_;
}
v___jp_2054_:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2055_ = lean_array_get_borrowed(v___x_2035_, v_xs_2043_, v_b_2036_);
lean_inc(v___x_2055_);
v___x_2056_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2037_, v_fixedPrefixSize_2038_, v___x_2055_, v_altBody_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v_a_2057_; uint8_t v___x_2058_; uint8_t v___x_2059_; lean_object* v___x_2060_; 
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
lean_inc(v_a_2057_);
lean_dec_ref_known(v___x_2056_, 1);
v___x_2058_ = 0;
v___x_2059_ = 1;
v___x_2060_ = l_Lean_Meta_mkLambdaFVars(v_xs_2043_, v_a_2057_, v___x_2058_, v___x_2039_, v___x_2058_, v___x_2039_, v___x_2059_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
return v___x_2060_;
}
else
{
return v___x_2056_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___boxed(lean_object** _args){
lean_object* v___x_2079_ = _args[0];
lean_object* v_b_2080_ = _args[1];
lean_object* v_recFnName_2081_ = _args[2];
lean_object* v_fixedPrefixSize_2082_ = _args[3];
lean_object* v___x_2083_ = _args[4];
lean_object* v___x_2084_ = _args[5];
lean_object* v_a_2085_ = _args[6];
lean_object* v_e_2086_ = _args[7];
lean_object* v_xs_2087_ = _args[8];
lean_object* v_altBody_2088_ = _args[9];
lean_object* v___y_2089_ = _args[10];
lean_object* v___y_2090_ = _args[11];
lean_object* v___y_2091_ = _args[12];
lean_object* v___y_2092_ = _args[13];
lean_object* v___y_2093_ = _args[14];
lean_object* v___y_2094_ = _args[15];
lean_object* v___y_2095_ = _args[16];
lean_object* v___y_2096_ = _args[17];
lean_object* v___y_2097_ = _args[18];
_start:
{
uint8_t v___x_57604__boxed_2098_; lean_object* v_res_2099_; 
v___x_57604__boxed_2098_ = lean_unbox(v___x_2083_);
v_res_2099_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0(v___x_2079_, v_b_2080_, v_recFnName_2081_, v_fixedPrefixSize_2082_, v___x_57604__boxed_2098_, v___x_2084_, v_a_2085_, v_e_2086_, v_xs_2087_, v_altBody_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec_ref(v_xs_2087_);
lean_dec(v___x_2084_);
lean_dec(v_b_2080_);
lean_dec_ref(v___x_2079_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(lean_object* v_recFnName_2100_, lean_object* v_fixedPrefixSize_2101_, lean_object* v_e_2102_, lean_object* v_as_2103_, lean_object* v_bs_2104_, lean_object* v_i_2105_, lean_object* v_cs_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_){
_start:
{
lean_object* v___x_2116_; uint8_t v___x_2117_; 
v___x_2116_ = lean_array_get_size(v_as_2103_);
v___x_2117_ = lean_nat_dec_lt(v_i_2105_, v___x_2116_);
if (v___x_2117_ == 0)
{
lean_object* v___x_2118_; 
lean_dec(v_i_2105_);
lean_dec_ref(v_e_2102_);
lean_dec(v_fixedPrefixSize_2101_);
lean_dec(v_recFnName_2100_);
v___x_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2118_, 0, v_cs_2106_);
return v___x_2118_;
}
else
{
lean_object* v___x_2119_; uint8_t v___x_2120_; 
v___x_2119_ = lean_array_get_size(v_bs_2104_);
v___x_2120_ = lean_nat_dec_lt(v_i_2105_, v___x_2119_);
if (v___x_2120_ == 0)
{
lean_object* v___x_2121_; 
lean_dec(v_i_2105_);
lean_dec_ref(v_e_2102_);
lean_dec(v_fixedPrefixSize_2101_);
lean_dec(v_recFnName_2100_);
v___x_2121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2121_, 0, v_cs_2106_);
return v___x_2121_;
}
else
{
lean_object* v___x_2122_; lean_object* v_a_2123_; lean_object* v_b_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___f_2128_; uint8_t v___x_2129_; lean_object* v___x_2130_; 
v___x_2122_ = l_Lean_instInhabitedExpr;
v_a_2123_ = lean_array_fget_borrowed(v_as_2103_, v_i_2105_);
v_b_2124_ = lean_array_fget_borrowed(v_bs_2104_, v_i_2105_);
v___x_2125_ = lean_unsigned_to_nat(1u);
v___x_2126_ = lean_nat_add(v_b_2124_, v___x_2125_);
v___x_2127_ = lean_box(v___x_2120_);
lean_inc_ref(v_e_2102_);
lean_inc_n(v_a_2123_, 2);
lean_inc(v___x_2126_);
lean_inc(v_fixedPrefixSize_2101_);
lean_inc(v_recFnName_2100_);
lean_inc(v_b_2124_);
v___f_2128_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___boxed), 19, 8);
lean_closure_set(v___f_2128_, 0, v___x_2122_);
lean_closure_set(v___f_2128_, 1, v_b_2124_);
lean_closure_set(v___f_2128_, 2, v_recFnName_2100_);
lean_closure_set(v___f_2128_, 3, v_fixedPrefixSize_2101_);
lean_closure_set(v___f_2128_, 4, v___x_2127_);
lean_closure_set(v___f_2128_, 5, v___x_2126_);
lean_closure_set(v___f_2128_, 6, v_a_2123_);
lean_closure_set(v___f_2128_, 7, v_e_2102_);
v___x_2129_ = 0;
v___x_2130_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(v_a_2123_, v___x_2126_, v___f_2128_, v___x_2129_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref_known(v___x_2130_, 1);
v___x_2132_ = lean_nat_add(v_i_2105_, v___x_2125_);
lean_dec(v_i_2105_);
v___x_2133_ = lean_array_push(v_cs_2106_, v_a_2131_);
v_i_2105_ = v___x_2132_;
v_cs_2106_ = v___x_2133_;
goto _start;
}
else
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
lean_dec_ref(v_cs_2106_);
lean_dec(v_i_2105_);
lean_dec_ref(v_e_2102_);
lean_dec(v_fixedPrefixSize_2101_);
lean_dec(v_recFnName_2100_);
v_a_2135_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2137_ = v___x_2130_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2130_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2140_; 
if (v_isShared_2138_ == 0)
{
v___x_2140_ = v___x_2137_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_a_2135_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(lean_object* v_recFnName_2143_, lean_object* v_fixedPrefixSize_2144_, lean_object* v_F_2145_, lean_object* v_e_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_){
_start:
{
switch(lean_obj_tag(v_e_2146_))
{
case 6:
{
lean_object* v_binderName_2156_; lean_object* v_binderType_2157_; lean_object* v_body_2158_; uint8_t v_binderInfo_2159_; lean_object* v___f_2160_; lean_object* v___x_2161_; 
v_binderName_2156_ = lean_ctor_get(v_e_2146_, 0);
lean_inc(v_binderName_2156_);
v_binderType_2157_ = lean_ctor_get(v_e_2146_, 1);
lean_inc_ref(v_binderType_2157_);
v_body_2158_ = lean_ctor_get(v_e_2146_, 2);
lean_inc_ref(v_body_2158_);
v_binderInfo_2159_ = lean_ctor_get_uint8(v_e_2146_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2146_, 3);
lean_inc_ref(v_F_2145_);
lean_inc(v_fixedPrefixSize_2144_);
lean_inc(v_recFnName_2143_);
v___f_2160_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0___boxed), 14, 4);
lean_closure_set(v___f_2160_, 0, v_body_2158_);
lean_closure_set(v___f_2160_, 1, v_recFnName_2143_);
lean_closure_set(v___f_2160_, 2, v_fixedPrefixSize_2144_);
lean_closure_set(v___f_2160_, 3, v_F_2145_);
v___x_2161_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2143_, v_fixedPrefixSize_2144_, v_F_2145_, v_binderType_2157_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_object* v_a_2162_; uint8_t v___x_2163_; lean_object* v___x_2164_; 
v_a_2162_ = lean_ctor_get(v___x_2161_, 0);
lean_inc(v_a_2162_);
lean_dec_ref_known(v___x_2161_, 1);
v___x_2163_ = 0;
v___x_2164_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_binderName_2156_, v_binderInfo_2159_, v_a_2162_, v___f_2160_, v___x_2163_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_);
return v___x_2164_;
}
else
{
lean_dec_ref(v___f_2160_);
lean_dec(v_binderName_2156_);
return v___x_2161_;
}
}
case 7:
{
lean_object* v_binderName_2165_; lean_object* v_binderType_2166_; lean_object* v_body_2167_; uint8_t v_binderInfo_2168_; lean_object* v___f_2169_; lean_object* v___x_2170_; 
v_binderName_2165_ = lean_ctor_get(v_e_2146_, 0);
lean_inc(v_binderName_2165_);
v_binderType_2166_ = lean_ctor_get(v_e_2146_, 1);
lean_inc_ref(v_binderType_2166_);
v_body_2167_ = lean_ctor_get(v_e_2146_, 2);
lean_inc_ref(v_body_2167_);
v_binderInfo_2168_ = lean_ctor_get_uint8(v_e_2146_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2146_, 3);
lean_inc_ref(v_F_2145_);
lean_inc(v_fixedPrefixSize_2144_);
lean_inc(v_recFnName_2143_);
v___f_2169_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1___boxed), 14, 4);
lean_closure_set(v___f_2169_, 0, v_body_2167_);
lean_closure_set(v___f_2169_, 1, v_recFnName_2143_);
lean_closure_set(v___f_2169_, 2, v_fixedPrefixSize_2144_);
lean_closure_set(v___f_2169_, 3, v_F_2145_);
v___x_2170_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2143_, v_fixedPrefixSize_2144_, v_F_2145_, v_binderType_2166_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; uint8_t v___x_2172_; lean_object* v___x_2173_; 
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_a_2171_);
lean_dec_ref_known(v___x_2170_, 1);
v___x_2172_ = 0;
v___x_2173_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_binderName_2165_, v_binderInfo_2168_, v_a_2171_, v___f_2169_, v___x_2172_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_);
return v___x_2173_;
}
else
{
lean_dec_ref(v___f_2169_);
lean_dec(v_binderName_2165_);
return v___x_2170_;
}
}
case 8:
{
lean_object* v_declName_2174_; lean_object* v_type_2175_; lean_object* v_value_2176_; lean_object* v_body_2177_; uint8_t v_nondep_2178_; lean_object* v___f_2179_; lean_object* v___x_2180_; 
v_declName_2174_ = lean_ctor_get(v_e_2146_, 0);
lean_inc(v_declName_2174_);
v_type_2175_ = lean_ctor_get(v_e_2146_, 1);
lean_inc_ref(v_type_2175_);
v_value_2176_ = lean_ctor_get(v_e_2146_, 2);
lean_inc_ref(v_value_2176_);
v_body_2177_ = lean_ctor_get(v_e_2146_, 3);
lean_inc_ref(v_body_2177_);
v_nondep_2178_ = lean_ctor_get_uint8(v_e_2146_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2146_, 4);
lean_inc_ref_n(v_F_2145_, 2);
lean_inc_n(v_fixedPrefixSize_2144_, 2);
lean_inc_n(v_recFnName_2143_, 2);
v___f_2179_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2___boxed), 14, 4);
lean_closure_set(v___f_2179_, 0, v_body_2177_);
lean_closure_set(v___f_2179_, 1, v_recFnName_2143_);
lean_closure_set(v___f_2179_, 2, v_fixedPrefixSize_2144_);
lean_closure_set(v___f_2179_, 3, v_F_2145_);
v___x_2180_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2143_, v_fixedPrefixSize_2144_, v_F_2145_, v_type_2175_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; lean_object* v___x_2182_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_a_2181_);
lean_dec_ref_known(v___x_2180_, 1);
v___x_2182_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2143_, v_fixedPrefixSize_2144_, v_F_2145_, v_value_2176_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v_a_2183_; uint8_t v___x_2184_; uint8_t v___x_2185_; lean_object* v___x_2186_; 
v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
lean_inc(v_a_2183_);
lean_dec_ref_known(v___x_2182_, 1);
v___x_2184_ = 0;
v___x_2185_ = 0;
v___x_2186_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(v_declName_2174_, v_a_2181_, v_a_2183_, v___f_2179_, v_nondep_2178_, v___x_2184_, v___x_2185_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_);
return v___x_2186_;
}
else
{
lean_dec(v_a_2181_);
lean_dec_ref(v___f_2179_);
lean_dec(v_declName_2174_);
return v___x_2182_;
}
}
else
{
lean_dec_ref(v___f_2179_);
lean_dec_ref(v_value_2176_);
lean_dec(v_declName_2174_);
lean_dec_ref(v_F_2145_);
lean_dec(v_fixedPrefixSize_2144_);
lean_dec(v_recFnName_2143_);
return v___x_2180_;
}
}
case 10:
{
lean_object* v_data_2187_; lean_object* v_expr_2188_; lean_object* v___x_2189_; 
v_data_2187_ = lean_ctor_get(v_e_2146_, 0);
lean_inc(v_data_2187_);
v_expr_2188_ = lean_ctor_get(v_e_2146_, 1);
lean_inc_ref(v_expr_2188_);
v___x_2189_ = l_Lean_getRecAppSyntax_x3f(v_e_2146_);
lean_dec_ref_known(v_e_2146_, 2);
if (lean_obj_tag(v___x_2189_) == 1)
{
lean_object* v_val_2190_; lean_object* v_toCold_2191_; lean_object* v_currRecDepth_2192_; lean_object* v_ref_2193_; uint8_t v_diag_2194_; uint8_t v_suppressElabErrors_2195_; lean_object* v_ref_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
lean_dec(v_data_2187_);
v_val_2190_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_val_2190_);
lean_dec_ref_known(v___x_2189_, 1);
v_toCold_2191_ = lean_ctor_get(v_a_2153_, 0);
v_currRecDepth_2192_ = lean_ctor_get(v_a_2153_, 1);
v_ref_2193_ = lean_ctor_get(v_a_2153_, 2);
v_diag_2194_ = lean_ctor_get_uint8(v_a_2153_, sizeof(void*)*3);
v_suppressElabErrors_2195_ = lean_ctor_get_uint8(v_a_2153_, sizeof(void*)*3 + 1);
v_ref_2196_ = l_Lean_replaceRef(v_val_2190_, v_ref_2193_);
lean_dec(v_val_2190_);
lean_inc(v_currRecDepth_2192_);
lean_inc_ref(v_toCold_2191_);
v___x_2197_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2197_, 0, v_toCold_2191_);
lean_ctor_set(v___x_2197_, 1, v_currRecDepth_2192_);
lean_ctor_set(v___x_2197_, 2, v_ref_2196_);
lean_ctor_set_uint8(v___x_2197_, sizeof(void*)*3, v_diag_2194_);
lean_ctor_set_uint8(v___x_2197_, sizeof(void*)*3 + 1, v_suppressElabErrors_2195_);
v___x_2198_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2143_, v_fixedPrefixSize_2144_, v_F_2145_, v_expr_2188_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v___x_2197_, v_a_2154_);
lean_dec_ref_known(v___x_2197_, 3);
return v___x_2198_;
}
else
{
lean_object* v___x_2199_; 
lean_dec(v___x_2189_);
v___x_2199_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2143_, v_fixedPrefixSize_2144_, v_F_2145_, v_expr_2188_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2208_; 
v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2202_ = v___x_2199_;
v_isShared_2203_ = v_isSharedCheck_2208_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2199_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2208_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2204_; lean_object* v___x_2206_; 
v___x_2204_ = l_Lean_mkMData(v_data_2187_, v_a_2200_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 0, v___x_2204_);
v___x_2206_ = v___x_2202_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v___x_2204_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
else
{
lean_dec(v_data_2187_);
return v___x_2199_;
}
}
}
case 11:
{
lean_object* v_typeName_2209_; lean_object* v_idx_2210_; lean_object* v_struct_2211_; lean_object* v___x_2212_; 
v_typeName_2209_ = lean_ctor_get(v_e_2146_, 0);
lean_inc(v_typeName_2209_);
v_idx_2210_ = lean_ctor_get(v_e_2146_, 1);
lean_inc(v_idx_2210_);
v_struct_2211_ = lean_ctor_get(v_e_2146_, 2);
lean_inc_ref(v_struct_2211_);
lean_dec_ref_known(v_e_2146_, 3);
v___x_2212_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2143_, v_fixedPrefixSize_2144_, v_F_2145_, v_struct_2211_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_);
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2221_; 
v_a_2213_ = lean_ctor_get(v___x_2212_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2215_ = v___x_2212_;
v_isShared_2216_ = v_isSharedCheck_2221_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2212_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2221_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2217_; lean_object* v___x_2219_; 
v___x_2217_ = l_Lean_mkProj(v_typeName_2209_, v_idx_2210_, v_a_2213_);
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 0, v___x_2217_);
v___x_2219_ = v___x_2215_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v___x_2217_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
else
{
lean_dec(v_idx_2210_);
lean_dec(v_typeName_2209_);
return v___x_2212_;
}
}
case 4:
{
uint8_t v___x_2222_; 
v___x_2222_ = l_Lean_Expr_isConstOf(v_e_2146_, v_recFnName_2143_);
if (v___x_2222_ == 0)
{
lean_object* v___x_2223_; 
lean_dec_ref(v_F_2145_);
lean_dec(v_fixedPrefixSize_2144_);
lean_dec(v_recFnName_2143_);
v___x_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2223_, 0, v_e_2146_);
return v___x_2223_;
}
else
{
lean_object* v___x_2224_; 
v___x_2224_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2143_, v_fixedPrefixSize_2144_, v_F_2145_, v_e_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_);
return v___x_2224_;
}
}
case 5:
{
uint8_t v___x_2225_; lean_object* v___x_2226_; 
v___x_2225_ = 1;
lean_inc_ref(v_e_2146_);
v___x_2226_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(v_e_2146_, v___x_2225_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
lean_inc(v_a_2227_);
lean_dec_ref_known(v___x_2226_, 1);
if (lean_obj_tag(v_a_2227_) == 0)
{
lean_object* v___x_2228_; 
v___x_2228_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2143_, v_fixedPrefixSize_2144_, v_F_2145_, v_e_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_);
return v___x_2228_;
}
else
{
lean_object* v_val_2229_; lean_object* v___x_2230_; 
v_val_2229_ = lean_ctor_get(v_a_2227_, 0);
lean_inc(v_val_2229_);
lean_dec_ref_known(v_a_2227_, 1);
lean_inc_ref(v_F_2145_);
v___x_2230_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_val_2229_, v_F_2145_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v_a_2231_; 
v_a_2231_ = lean_ctor_get(v___x_2230_, 0);
lean_inc(v_a_2231_);
lean_dec_ref_known(v___x_2230_, 1);
if (lean_obj_tag(v_a_2231_) == 1)
{
lean_object* v_val_2232_; lean_object* v_toMatcherInfo_2233_; lean_object* v_matcherName_2234_; lean_object* v_matcherLevels_2235_; lean_object* v_params_2236_; lean_object* v_motive_2237_; lean_object* v_discrs_2238_; lean_object* v_alts_2239_; lean_object* v_remaining_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v_val_2232_ = lean_ctor_get(v_a_2231_, 0);
lean_inc(v_val_2232_);
lean_dec_ref_known(v_a_2231_, 1);
v_toMatcherInfo_2233_ = lean_ctor_get(v_val_2232_, 0);
lean_inc_ref(v_toMatcherInfo_2233_);
v_matcherName_2234_ = lean_ctor_get(v_val_2232_, 1);
lean_inc(v_matcherName_2234_);
v_matcherLevels_2235_ = lean_ctor_get(v_val_2232_, 2);
lean_inc_ref(v_matcherLevels_2235_);
v_params_2236_ = lean_ctor_get(v_val_2232_, 3);
lean_inc_ref(v_params_2236_);
v_motive_2237_ = lean_ctor_get(v_val_2232_, 4);
lean_inc_ref(v_motive_2237_);
v_discrs_2238_ = lean_ctor_get(v_val_2232_, 5);
lean_inc_ref(v_discrs_2238_);
v_alts_2239_ = lean_ctor_get(v_val_2232_, 6);
lean_inc_ref(v_alts_2239_);
v_remaining_2240_ = lean_ctor_get(v_val_2232_, 7);
lean_inc_ref(v_remaining_2240_);
v___x_2241_ = l_Lean_Meta_MatcherApp_altNumParams(v_val_2232_);
v___x_2242_ = lean_unsigned_to_nat(0u);
v___x_2243_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
lean_inc(v_fixedPrefixSize_2144_);
lean_inc(v_recFnName_2143_);
v___x_2244_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(v_recFnName_2143_, v_fixedPrefixSize_2144_, v_e_2146_, v_alts_2239_, v___x_2241_, v___x_2242_, v___x_2243_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_);
lean_dec_ref(v___x_2241_);
lean_dec_ref(v_alts_2239_);
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_object* v_a_2245_; size_t v_sz_2246_; size_t v___x_2247_; lean_object* v___x_2248_; 
v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
lean_inc(v_a_2245_);
lean_dec_ref_known(v___x_2244_, 1);
v_sz_2246_ = lean_array_size(v_discrs_2238_);
v___x_2247_ = ((size_t)0ULL);
v___x_2248_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_2143_, v_fixedPrefixSize_2144_, v_F_2145_, v_sz_2246_, v___x_2247_, v_discrs_2238_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_);
if (lean_obj_tag(v___x_2248_) == 0)
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2258_; 
v_a_2249_ = lean_ctor_get(v___x_2248_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2251_ = v___x_2248_;
v_isShared_2252_ = v_isSharedCheck_2258_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2248_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2258_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2256_; 
v___x_2253_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2253_, 0, v_toMatcherInfo_2233_);
lean_ctor_set(v___x_2253_, 1, v_matcherName_2234_);
lean_ctor_set(v___x_2253_, 2, v_matcherLevels_2235_);
lean_ctor_set(v___x_2253_, 3, v_params_2236_);
lean_ctor_set(v___x_2253_, 4, v_motive_2237_);
lean_ctor_set(v___x_2253_, 5, v_a_2249_);
lean_ctor_set(v___x_2253_, 6, v_a_2245_);
lean_ctor_set(v___x_2253_, 7, v_remaining_2240_);
v___x_2254_ = l_Lean_Meta_MatcherApp_toExpr(v___x_2253_);
if (v_isShared_2252_ == 0)
{
lean_ctor_set(v___x_2251_, 0, v___x_2254_);
v___x_2256_ = v___x_2251_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v___x_2254_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
else
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
lean_dec(v_a_2245_);
lean_dec_ref(v_remaining_2240_);
lean_dec_ref(v_motive_2237_);
lean_dec_ref(v_params_2236_);
lean_dec_ref(v_matcherLevels_2235_);
lean_dec(v_matcherName_2234_);
lean_dec_ref(v_toMatcherInfo_2233_);
v_a_2259_ = lean_ctor_get(v___x_2248_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2261_ = v___x_2248_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2248_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2264_; 
if (v_isShared_2262_ == 0)
{
v___x_2264_ = v___x_2261_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_a_2259_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
else
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2274_; 
lean_dec_ref(v_remaining_2240_);
lean_dec_ref(v_discrs_2238_);
lean_dec_ref(v_motive_2237_);
lean_dec_ref(v_params_2236_);
lean_dec_ref(v_matcherLevels_2235_);
lean_dec(v_matcherName_2234_);
lean_dec_ref(v_toMatcherInfo_2233_);
lean_dec_ref(v_F_2145_);
lean_dec(v_fixedPrefixSize_2144_);
lean_dec(v_recFnName_2143_);
v_a_2267_ = lean_ctor_get(v___x_2244_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2269_ = v___x_2244_;
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2244_);
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
else
{
lean_object* v___x_2275_; 
lean_dec(v_a_2231_);
v___x_2275_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2143_, v_fixedPrefixSize_2144_, v_F_2145_, v_e_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_);
return v___x_2275_;
}
}
else
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2283_; 
lean_dec_ref_known(v_e_2146_, 2);
lean_dec_ref(v_F_2145_);
lean_dec(v_fixedPrefixSize_2144_);
lean_dec(v_recFnName_2143_);
v_a_2276_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2230_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2230_);
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
lean_dec_ref_known(v_e_2146_, 2);
lean_dec_ref(v_F_2145_);
lean_dec(v_fixedPrefixSize_2144_);
lean_dec(v_recFnName_2143_);
v_a_2284_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2286_ = v___x_2226_;
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2226_);
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
lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
lean_dec_ref(v_F_2145_);
lean_dec(v_fixedPrefixSize_2144_);
v___x_2292_ = lean_unsigned_to_nat(1u);
v___x_2293_ = lean_mk_empty_array_with_capacity(v___x_2292_);
v___x_2294_ = lean_array_push(v___x_2293_, v_recFnName_2143_);
lean_inc_ref(v_e_2146_);
v___x_2295_ = l_Lean_Elab_ensureNoRecFn(v___x_2294_, v_e_2146_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2302_; 
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2302_ == 0)
{
lean_object* v_unused_2303_; 
v_unused_2303_ = lean_ctor_get(v___x_2295_, 0);
lean_dec(v_unused_2303_);
v___x_2297_ = v___x_2295_;
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
else
{
lean_dec(v___x_2295_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2300_; 
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 0, v_e_2146_);
v___x_2300_ = v___x_2297_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_e_2146_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
else
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2311_; 
lean_dec_ref(v_e_2146_);
v_a_2304_ = lean_ctor_get(v___x_2295_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2306_ = v___x_2295_;
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2295_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2309_; 
if (v_isShared_2307_ == 0)
{
v___x_2309_ = v___x_2306_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2304_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(lean_object* v_recFnName_2312_, lean_object* v_fixedPrefixSize_2313_, lean_object* v_F_2314_, lean_object* v_e_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_){
_start:
{
lean_object* v___y_2326_; lean_object* v___y_2327_; lean_object* v___x_2344_; 
lean_inc_ref(v_e_2315_);
lean_inc(v_recFnName_2312_);
v___x_2344_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___redArg(v_recFnName_2312_, v_e_2315_, v_a_2316_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2433_; 
v_a_2345_ = lean_ctor_get(v___x_2344_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2347_ = v___x_2344_;
v_isShared_2348_ = v_isSharedCheck_2433_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2344_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2433_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
uint8_t v___x_2349_; 
v___x_2349_ = lean_unbox(v_a_2345_);
lean_dec(v_a_2345_);
if (v___x_2349_ == 0)
{
lean_object* v___x_2351_; 
lean_dec_ref(v_F_2314_);
lean_dec(v_fixedPrefixSize_2313_);
lean_dec(v_recFnName_2312_);
if (v_isShared_2348_ == 0)
{
lean_ctor_set(v___x_2347_, 0, v_e_2315_);
v___x_2351_ = v___x_2347_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_e_2315_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
else
{
uint8_t v___x_2353_; lean_object* v___y_2355_; lean_object* v___y_2356_; lean_object* v___y_2357_; lean_object* v___y_2358_; lean_object* v___y_2359_; lean_object* v___y_2360_; lean_object* v___y_2361_; lean_object* v___y_2362_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
lean_del_object(v___x_2347_);
v___x_2353_ = 0;
v___x_2410_ = lean_st_ref_get(v_a_2317_);
v___x_2411_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v___x_2410_, v_e_2315_);
lean_dec(v___x_2410_);
if (lean_obj_tag(v___x_2411_) == 1)
{
lean_object* v_val_2412_; lean_object* v_fst_2413_; lean_object* v_snd_2414_; lean_object* v___x_2415_; 
v_val_2412_ = lean_ctor_get(v___x_2411_, 0);
lean_inc(v_val_2412_);
lean_dec_ref_known(v___x_2411_, 1);
v_fst_2413_ = lean_ctor_get(v_val_2412_, 0);
lean_inc(v_fst_2413_);
v_snd_2414_ = lean_ctor_get(v_val_2412_, 1);
lean_inc(v_snd_2414_);
lean_dec(v_val_2412_);
v___x_2415_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___redArg(v_snd_2414_, v_a_2320_);
lean_dec(v_snd_2414_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2424_; 
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2418_ = v___x_2415_;
v_isShared_2419_ = v_isSharedCheck_2424_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2415_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2424_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
uint8_t v___x_2420_; 
v___x_2420_ = lean_unbox(v_a_2416_);
lean_dec(v_a_2416_);
if (v___x_2420_ == 0)
{
lean_del_object(v___x_2418_);
lean_dec(v_fst_2413_);
v___y_2355_ = v_a_2316_;
v___y_2356_ = v_a_2317_;
v___y_2357_ = v_a_2318_;
v___y_2358_ = v_a_2319_;
v___y_2359_ = v_a_2320_;
v___y_2360_ = v_a_2321_;
v___y_2361_ = v_a_2322_;
v___y_2362_ = v_a_2323_;
goto v___jp_2354_;
}
else
{
lean_object* v___x_2422_; 
lean_dec_ref(v_e_2315_);
lean_dec_ref(v_F_2314_);
lean_dec(v_fixedPrefixSize_2313_);
lean_dec(v_recFnName_2312_);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 0, v_fst_2413_);
v___x_2422_ = v___x_2418_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_fst_2413_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
}
else
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2432_; 
lean_dec(v_fst_2413_);
lean_dec_ref(v_e_2315_);
lean_dec_ref(v_F_2314_);
lean_dec(v_fixedPrefixSize_2313_);
lean_dec(v_recFnName_2312_);
v_a_2425_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2427_ = v___x_2415_;
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2415_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2430_; 
if (v_isShared_2428_ == 0)
{
v___x_2430_ = v___x_2427_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_a_2425_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
}
else
{
lean_dec(v___x_2411_);
v___y_2355_ = v_a_2316_;
v___y_2356_ = v_a_2317_;
v___y_2357_ = v_a_2318_;
v___y_2358_ = v_a_2319_;
v___y_2359_ = v_a_2320_;
v___y_2360_ = v_a_2321_;
v___y_2361_ = v_a_2322_;
v___y_2362_ = v_a_2323_;
goto v___jp_2354_;
}
v___jp_2354_:
{
lean_object* v___x_2363_; 
lean_inc_ref(v_e_2315_);
v___x_2363_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(v_recFnName_2312_, v_fixedPrefixSize_2313_, v_F_2314_, v_e_2315_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v_a_2364_; lean_object* v___f_2365_; lean_object* v___x_2366_; 
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
lean_inc_n(v_a_2364_, 2);
lean_dec_ref_known(v___x_2363_, 1);
lean_inc_ref(v_e_2315_);
v___f_2365_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___boxed), 11, 2);
lean_closure_set(v___f_2365_, 0, v_e_2315_);
lean_closure_set(v___f_2365_, 1, v_a_2364_);
v___x_2366_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId(v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2401_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2369_ = v___x_2366_;
v_isShared_2370_ = v_isSharedCheck_2401_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2366_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2401_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v_toCold_2375_; lean_object* v_options_2376_; lean_object* v___x_2377_; uint8_t v___x_2378_; 
v___x_2371_ = lean_st_ref_take(v___y_2356_);
lean_inc(v_a_2364_);
v___x_2372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2372_, 0, v_a_2364_);
lean_ctor_set(v___x_2372_, 1, v_a_2367_);
v___x_2373_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4___redArg(v___x_2371_, v_e_2315_, v___x_2372_);
v___x_2374_ = lean_st_ref_put(v___y_2356_, v___x_2373_);
v_toCold_2375_ = lean_ctor_get(v___y_2361_, 0);
v_options_2376_ = lean_ctor_get(v_toCold_2375_, 2);
v___x_2377_ = l_Lean_Elab_WF_debug_definition_wf_replaceRecApps;
v___x_2378_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v_options_2376_, v___x_2377_);
if (v___x_2378_ == 0)
{
lean_object* v___x_2380_; 
lean_dec_ref(v___f_2365_);
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 0, v_a_2364_);
v___x_2380_ = v___x_2369_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_a_2364_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
else
{
lean_object* v___x_2382_; uint8_t v_transparency_2383_; uint8_t v___x_2384_; uint8_t v___x_2385_; 
lean_del_object(v___x_2369_);
v___x_2382_ = l_Lean_Meta_Context_config(v___y_2359_);
v_transparency_2383_ = lean_ctor_get_uint8(v___x_2382_, 9);
lean_dec_ref(v___x_2382_);
v___x_2384_ = 0;
v___x_2385_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2383_, v___x_2384_);
if (v___x_2385_ == 0)
{
lean_object* v_keyedConfig_2386_; uint8_t v_trackZetaDelta_2387_; lean_object* v_zetaDeltaSet_2388_; lean_object* v_lctx_2389_; lean_object* v_localInstances_2390_; lean_object* v_defEqCtx_x3f_2391_; lean_object* v_synthPendingDepth_2392_; lean_object* v_customCanUnfoldPredicate_x3f_2393_; uint8_t v_univApprox_2394_; uint8_t v_inTypeClassResolution_2395_; uint8_t v_cacheInferType_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
v_keyedConfig_2386_ = lean_ctor_get(v___y_2359_, 0);
v_trackZetaDelta_2387_ = lean_ctor_get_uint8(v___y_2359_, sizeof(void*)*7);
v_zetaDeltaSet_2388_ = lean_ctor_get(v___y_2359_, 1);
v_lctx_2389_ = lean_ctor_get(v___y_2359_, 2);
v_localInstances_2390_ = lean_ctor_get(v___y_2359_, 3);
v_defEqCtx_x3f_2391_ = lean_ctor_get(v___y_2359_, 4);
v_synthPendingDepth_2392_ = lean_ctor_get(v___y_2359_, 5);
v_customCanUnfoldPredicate_x3f_2393_ = lean_ctor_get(v___y_2359_, 6);
v_univApprox_2394_ = lean_ctor_get_uint8(v___y_2359_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2395_ = lean_ctor_get_uint8(v___y_2359_, sizeof(void*)*7 + 2);
v_cacheInferType_2396_ = lean_ctor_get_uint8(v___y_2359_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2386_);
v___x_2397_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2384_, v_keyedConfig_2386_);
lean_inc(v_customCanUnfoldPredicate_x3f_2393_);
lean_inc(v_synthPendingDepth_2392_);
lean_inc(v_defEqCtx_x3f_2391_);
lean_inc_ref(v_localInstances_2390_);
lean_inc_ref(v_lctx_2389_);
lean_inc(v_zetaDeltaSet_2388_);
v___x_2398_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2398_, 0, v___x_2397_);
lean_ctor_set(v___x_2398_, 1, v_zetaDeltaSet_2388_);
lean_ctor_set(v___x_2398_, 2, v_lctx_2389_);
lean_ctor_set(v___x_2398_, 3, v_localInstances_2390_);
lean_ctor_set(v___x_2398_, 4, v_defEqCtx_x3f_2391_);
lean_ctor_set(v___x_2398_, 5, v_synthPendingDepth_2392_);
lean_ctor_set(v___x_2398_, 6, v_customCanUnfoldPredicate_x3f_2393_);
lean_ctor_set_uint8(v___x_2398_, sizeof(void*)*7, v_trackZetaDelta_2387_);
lean_ctor_set_uint8(v___x_2398_, sizeof(void*)*7 + 1, v_univApprox_2394_);
lean_ctor_set_uint8(v___x_2398_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2395_);
lean_ctor_set_uint8(v___x_2398_, sizeof(void*)*7 + 3, v_cacheInferType_2396_);
v___x_2399_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v___f_2365_, v___x_2353_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___x_2398_, v___y_2360_, v___y_2361_, v___y_2362_);
lean_dec_ref_known(v___x_2398_, 7);
v___y_2326_ = v_a_2364_;
v___y_2327_ = v___x_2399_;
goto v___jp_2325_;
}
else
{
lean_object* v___x_2400_; 
v___x_2400_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v___f_2365_, v___x_2353_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
v___y_2326_ = v_a_2364_;
v___y_2327_ = v___x_2400_;
goto v___jp_2325_;
}
}
}
}
else
{
lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2409_; 
lean_dec_ref(v___f_2365_);
lean_dec(v_a_2364_);
lean_dec_ref(v_e_2315_);
v_a_2402_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2404_ = v___x_2366_;
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2366_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2407_; 
if (v_isShared_2405_ == 0)
{
v___x_2407_ = v___x_2404_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_a_2402_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
return v___x_2407_;
}
}
}
}
else
{
lean_dec_ref(v_e_2315_);
return v___x_2363_;
}
}
}
}
}
else
{
lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2441_; 
lean_dec_ref(v_e_2315_);
lean_dec_ref(v_F_2314_);
lean_dec(v_fixedPrefixSize_2313_);
lean_dec(v_recFnName_2312_);
v_a_2434_ = lean_ctor_get(v___x_2344_, 0);
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2436_ = v___x_2344_;
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v___x_2344_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2439_; 
if (v_isShared_2437_ == 0)
{
v___x_2439_ = v___x_2436_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_a_2434_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
}
v___jp_2325_:
{
if (lean_obj_tag(v___y_2327_) == 0)
{
lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2334_; 
v_isSharedCheck_2334_ = !lean_is_exclusive(v___y_2327_);
if (v_isSharedCheck_2334_ == 0)
{
lean_object* v_unused_2335_; 
v_unused_2335_ = lean_ctor_get(v___y_2327_, 0);
lean_dec(v_unused_2335_);
v___x_2329_ = v___y_2327_;
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
else
{
lean_dec(v___y_2327_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2332_; 
if (v_isShared_2330_ == 0)
{
lean_ctor_set(v___x_2329_, 0, v___y_2326_);
v___x_2332_ = v___x_2329_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v___y_2326_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
else
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2343_; 
lean_dec_ref(v___y_2326_);
v_a_2336_ = lean_ctor_get(v___y_2327_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___y_2327_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2338_ = v___y_2327_;
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___y_2327_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2341_; 
if (v_isShared_2339_ == 0)
{
v___x_2341_ = v___x_2338_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_a_2336_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2(lean_object* v_body_2442_, lean_object* v_recFnName_2443_, lean_object* v_fixedPrefixSize_2444_, lean_object* v_F_2445_, lean_object* v_x_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_){
_start:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2456_ = lean_expr_instantiate1(v_body_2442_, v_x_2446_);
v___x_2457_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2443_, v_fixedPrefixSize_2444_, v_F_2445_, v___x_2456_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp___boxed(lean_object* v_recFnName_2458_, lean_object* v_fixedPrefixSize_2459_, lean_object* v_F_2460_, lean_object* v_e_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_){
_start:
{
lean_object* v_res_2471_; 
v_res_2471_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2458_, v_fixedPrefixSize_2459_, v_F_2460_, v_e_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_);
lean_dec(v_a_2469_);
lean_dec_ref(v_a_2468_);
lean_dec(v_a_2467_);
lean_dec_ref(v_a_2466_);
lean_dec(v_a_2465_);
lean_dec_ref(v_a_2464_);
lean_dec(v_a_2463_);
lean_dec(v_a_2462_);
return v_res_2471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1___boxed(lean_object* v_recFnName_2472_, lean_object* v_fixedPrefixSize_2473_, lean_object* v_F_2474_, lean_object* v_sz_2475_, lean_object* v_i_2476_, lean_object* v_bs_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_){
_start:
{
size_t v_sz_boxed_2487_; size_t v_i_boxed_2488_; lean_object* v_res_2489_; 
v_sz_boxed_2487_ = lean_unbox_usize(v_sz_2475_);
lean_dec(v_sz_2475_);
v_i_boxed_2488_ = lean_unbox_usize(v_i_2476_);
lean_dec(v_i_2476_);
v_res_2489_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_2472_, v_fixedPrefixSize_2473_, v_F_2474_, v_sz_boxed_2487_, v_i_boxed_2488_, v_bs_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec(v___y_2479_);
lean_dec(v___y_2478_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16___boxed(lean_object* v_recFnName_2490_, lean_object* v_fixedPrefixSize_2491_, lean_object* v_F_2492_, lean_object* v_x_2493_, lean_object* v_x_2494_, lean_object* v_x_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
lean_object* v_res_2505_; 
v_res_2505_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(v_recFnName_2490_, v_fixedPrefixSize_2491_, v_F_2492_, v_x_2493_, v_x_2494_, v_x_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
lean_dec(v___y_2497_);
lean_dec(v___y_2496_);
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___boxed(lean_object* v_recFnName_2506_, lean_object* v_fixedPrefixSize_2507_, lean_object* v_e_2508_, lean_object* v_as_2509_, lean_object* v_bs_2510_, lean_object* v_i_2511_, lean_object* v_cs_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(v_recFnName_2506_, v_fixedPrefixSize_2507_, v_e_2508_, v_as_2509_, v_bs_2510_, v_i_2511_, v_cs_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
lean_dec(v___y_2516_);
lean_dec_ref(v___y_2515_);
lean_dec(v___y_2514_);
lean_dec(v___y_2513_);
lean_dec_ref(v_bs_2510_);
lean_dec_ref(v_as_2509_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___boxed(lean_object* v_recFnName_2523_, lean_object* v_fixedPrefixSize_2524_, lean_object* v_F_2525_, lean_object* v_e_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2523_, v_fixedPrefixSize_2524_, v_F_2525_, v_e_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_);
lean_dec(v_a_2534_);
lean_dec_ref(v_a_2533_);
lean_dec(v_a_2532_);
lean_dec_ref(v_a_2531_);
lean_dec(v_a_2530_);
lean_dec_ref(v_a_2529_);
lean_dec(v_a_2528_);
lean_dec(v_a_2527_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___boxed(lean_object* v_recFnName_2537_, lean_object* v_fixedPrefixSize_2538_, lean_object* v_F_2539_, lean_object* v_e_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_){
_start:
{
lean_object* v_res_2550_; 
v_res_2550_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2537_, v_fixedPrefixSize_2538_, v_F_2539_, v_e_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_);
lean_dec(v_a_2548_);
lean_dec_ref(v_a_2547_);
lean_dec(v_a_2546_);
lean_dec_ref(v_a_2545_);
lean_dec(v_a_2544_);
lean_dec_ref(v_a_2543_);
lean_dec(v_a_2542_);
lean_dec(v_a_2541_);
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___boxed(lean_object* v_recFnName_2551_, lean_object* v_fixedPrefixSize_2552_, lean_object* v_F_2553_, lean_object* v_e_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_){
_start:
{
lean_object* v_res_2564_; 
v_res_2564_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(v_recFnName_2551_, v_fixedPrefixSize_2552_, v_F_2553_, v_e_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_);
lean_dec(v_a_2562_);
lean_dec_ref(v_a_2561_);
lean_dec(v_a_2560_);
lean_dec_ref(v_a_2559_);
lean_dec(v_a_2558_);
lean_dec_ref(v_a_2557_);
lean_dec(v_a_2556_);
lean_dec(v_a_2555_);
return v_res_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7(lean_object* v_00_u03b1_2565_, lean_object* v_k_2566_, uint8_t v_allowLevelAssignments_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_){
_start:
{
lean_object* v___x_2577_; 
v___x_2577_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v_k_2566_, v_allowLevelAssignments_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___boxed(lean_object* v_00_u03b1_2578_, lean_object* v_k_2579_, lean_object* v_allowLevelAssignments_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2590_; lean_object* v_res_2591_; 
v_allowLevelAssignments_boxed_2590_ = lean_unbox(v_allowLevelAssignments_2580_);
v_res_2591_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7(v_00_u03b1_2578_, v_k_2579_, v_allowLevelAssignments_boxed_2590_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2583_);
lean_dec(v___y_2582_);
lean_dec(v___y_2581_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10(lean_object* v_00_u03b1_2592_, lean_object* v_name_2593_, uint8_t v_bi_2594_, lean_object* v_type_2595_, lean_object* v_k_2596_, uint8_t v_kind_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_){
_start:
{
lean_object* v___x_2607_; 
v___x_2607_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_name_2593_, v_bi_2594_, v_type_2595_, v_k_2596_, v_kind_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___boxed(lean_object* v_00_u03b1_2608_, lean_object* v_name_2609_, lean_object* v_bi_2610_, lean_object* v_type_2611_, lean_object* v_k_2612_, lean_object* v_kind_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_){
_start:
{
uint8_t v_bi_boxed_2623_; uint8_t v_kind_boxed_2624_; lean_object* v_res_2625_; 
v_bi_boxed_2623_ = lean_unbox(v_bi_2610_);
v_kind_boxed_2624_ = lean_unbox(v_kind_2613_);
v_res_2625_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10(v_00_u03b1_2608_, v_name_2609_, v_bi_boxed_2623_, v_type_2611_, v_k_2612_, v_kind_boxed_2624_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
lean_dec(v___y_2619_);
lean_dec_ref(v___y_2618_);
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
lean_dec(v___y_2615_);
lean_dec(v___y_2614_);
return v_res_2625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(lean_object* v_00_u03b1_2626_, lean_object* v_e_2627_, lean_object* v_maxFVars_2628_, lean_object* v_k_2629_, uint8_t v_cleanupAnnotations_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_){
_start:
{
lean_object* v___x_2640_; 
v___x_2640_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(v_e_2627_, v_maxFVars_2628_, v_k_2629_, v_cleanupAnnotations_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
return v___x_2640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___boxed(lean_object* v_00_u03b1_2641_, lean_object* v_e_2642_, lean_object* v_maxFVars_2643_, lean_object* v_k_2644_, lean_object* v_cleanupAnnotations_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2655_; lean_object* v_res_2656_; 
v_cleanupAnnotations_boxed_2655_ = lean_unbox(v_cleanupAnnotations_2645_);
v_res_2656_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(v_00_u03b1_2641_, v_e_2642_, v_maxFVars_2643_, v_k_2644_, v_cleanupAnnotations_boxed_2655_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec(v___y_2646_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0(lean_object* v_inst_2657_, lean_object* v_R_2658_, lean_object* v_a_2659_, lean_object* v_b_2660_){
_start:
{
lean_object* v___x_2661_; 
v___x_2661_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(v_a_2659_, v_b_2660_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2(lean_object* v_cls_2662_, lean_object* v_msg_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
lean_object* v___x_2673_; 
v___x_2673_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(v_cls_2662_, v_msg_2663_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
return v___x_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___boxed(lean_object* v_cls_2674_, lean_object* v_msg_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2(v_cls_2674_, v_msg_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
lean_dec(v___y_2677_);
lean_dec(v___y_2676_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4(lean_object* v_00_u03b2_2686_, lean_object* v_m_2687_, lean_object* v_a_2688_, lean_object* v_b_2689_){
_start:
{
lean_object* v___x_2690_; 
v___x_2690_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4___redArg(v_m_2687_, v_a_2688_, v_b_2689_);
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(lean_object* v_00_u03b1_2691_, lean_object* v_msg_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
lean_object* v___x_2702_; 
v___x_2702_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v_msg_2692_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___boxed(lean_object* v_00_u03b1_2703_, lean_object* v_msg_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_){
_start:
{
lean_object* v_res_2714_; 
v_res_2714_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(v_00_u03b1_2703_, v_msg_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v___y_2706_);
lean_dec(v___y_2705_);
return v_res_2714_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8(lean_object* v_00_u03b2_2715_, lean_object* v_m_2716_, lean_object* v_a_2717_){
_start:
{
lean_object* v___x_2718_; 
v___x_2718_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v_m_2716_, v_a_2717_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___boxed(lean_object* v_00_u03b2_2719_, lean_object* v_m_2720_, lean_object* v_a_2721_){
_start:
{
lean_object* v_res_2722_; 
v_res_2722_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8(v_00_u03b2_2719_, v_m_2720_, v_a_2721_);
lean_dec_ref(v_a_2721_);
lean_dec_ref(v_m_2720_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15(lean_object* v_00_u03b1_2723_, lean_object* v_name_2724_, lean_object* v_type_2725_, lean_object* v_val_2726_, lean_object* v_k_2727_, uint8_t v_nondep_2728_, uint8_t v_kind_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
lean_object* v___x_2739_; 
v___x_2739_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(v_name_2724_, v_type_2725_, v_val_2726_, v_k_2727_, v_nondep_2728_, v_kind_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___boxed(lean_object* v_00_u03b1_2740_, lean_object* v_name_2741_, lean_object* v_type_2742_, lean_object* v_val_2743_, lean_object* v_k_2744_, lean_object* v_nondep_2745_, lean_object* v_kind_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_){
_start:
{
uint8_t v_nondep_boxed_2756_; uint8_t v_kind_boxed_2757_; lean_object* v_res_2758_; 
v_nondep_boxed_2756_ = lean_unbox(v_nondep_2745_);
v_kind_boxed_2757_ = lean_unbox(v_kind_2746_);
v_res_2758_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15(v_00_u03b1_2740_, v_name_2741_, v_type_2742_, v_val_2743_, v_k_2744_, v_nondep_boxed_2756_, v_kind_boxed_2757_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2753_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec(v___y_2747_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20(lean_object* v_declName_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v___x_2769_; 
v___x_2769_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(v_declName_2759_, v___y_2767_);
return v___x_2769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___boxed(lean_object* v_declName_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
lean_object* v_res_2780_; 
v_res_2780_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20(v_declName_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec(v___y_2772_);
lean_dec(v___y_2771_);
return v_res_2780_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4(lean_object* v_00_u03b2_2781_, lean_object* v_a_2782_, lean_object* v_x_2783_){
_start:
{
uint8_t v___x_2784_; 
v___x_2784_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg(v_a_2782_, v_x_2783_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___boxed(lean_object* v_00_u03b2_2785_, lean_object* v_a_2786_, lean_object* v_x_2787_){
_start:
{
uint8_t v_res_2788_; lean_object* v_r_2789_; 
v_res_2788_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4(v_00_u03b2_2785_, v_a_2786_, v_x_2787_);
lean_dec(v_x_2787_);
lean_dec_ref(v_a_2786_);
v_r_2789_ = lean_box(v_res_2788_);
return v_r_2789_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5(lean_object* v_00_u03b2_2790_, lean_object* v_data_2791_){
_start:
{
lean_object* v___x_2792_; 
v___x_2792_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5___redArg(v_data_2791_);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6(lean_object* v_00_u03b2_2793_, lean_object* v_a_2794_, lean_object* v_b_2795_, lean_object* v_x_2796_){
_start:
{
lean_object* v___x_2797_; 
v___x_2797_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6___redArg(v_a_2794_, v_b_2795_, v_x_2796_);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11(lean_object* v_00_u03b2_2798_, lean_object* v_a_2799_, lean_object* v_x_2800_){
_start:
{
lean_object* v___x_2801_; 
v___x_2801_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(v_a_2799_, v_x_2800_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___boxed(lean_object* v_00_u03b2_2802_, lean_object* v_a_2803_, lean_object* v_x_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11(v_00_u03b2_2802_, v_a_2803_, v_x_2804_);
lean_dec(v_x_2804_);
lean_dec_ref(v_a_2803_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12(lean_object* v_00_u03b2_2806_, lean_object* v_i_2807_, lean_object* v_source_2808_, lean_object* v_target_2809_){
_start:
{
lean_object* v___x_2810_; 
v___x_2810_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12___redArg(v_i_2807_, v_source_2808_, v_target_2809_);
return v___x_2810_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21(lean_object* v_00_u03b1_2811_, lean_object* v_constName_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
lean_object* v___x_2822_; 
v___x_2822_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(v_constName_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___boxed(lean_object* v_00_u03b1_2823_, lean_object* v_constName_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21(v_00_u03b1_2823_, v_constName_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_);
lean_dec(v___y_2832_);
lean_dec_ref(v___y_2831_);
lean_dec(v___y_2830_);
lean_dec_ref(v___y_2829_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec(v___y_2825_);
return v_res_2834_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12_spec__22(lean_object* v_00_u03b2_2835_, lean_object* v_x_2836_, lean_object* v_x_2837_){
_start:
{
lean_object* v___x_2838_; 
v___x_2838_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12_spec__22___redArg(v_x_2836_, v_x_2837_);
return v___x_2838_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27(lean_object* v_00_u03b1_2839_, lean_object* v_ref_2840_, lean_object* v_constName_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_){
_start:
{
lean_object* v___x_2851_; 
v___x_2851_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(v_ref_2840_, v_constName_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_);
return v___x_2851_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___boxed(lean_object* v_00_u03b1_2852_, lean_object* v_ref_2853_, lean_object* v_constName_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27(v_00_u03b1_2852_, v_ref_2853_, v_constName_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
lean_dec(v___y_2858_);
lean_dec_ref(v___y_2857_);
lean_dec(v___y_2856_);
lean_dec(v___y_2855_);
lean_dec(v_ref_2853_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29(lean_object* v_00_u03b1_2865_, lean_object* v_ref_2866_, lean_object* v_msg_2867_, lean_object* v_declHint_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
lean_object* v___x_2878_; 
v___x_2878_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(v_ref_2866_, v_msg_2867_, v_declHint_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
return v___x_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___boxed(lean_object* v_00_u03b1_2879_, lean_object* v_ref_2880_, lean_object* v_msg_2881_, lean_object* v_declHint_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29(v_00_u03b1_2879_, v_ref_2880_, v_msg_2881_, v_declHint_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec_ref(v___y_2885_);
lean_dec(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec(v_ref_2880_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31(lean_object* v_msg_2893_, lean_object* v_declHint_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_){
_start:
{
lean_object* v___x_2904_; 
v___x_2904_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(v_msg_2893_, v_declHint_2894_, v___y_2902_);
return v___x_2904_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___boxed(lean_object* v_msg_2905_, lean_object* v_declHint_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31(v_msg_2905_, v_declHint_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
lean_dec(v___y_2908_);
lean_dec(v___y_2907_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31(lean_object* v_00_u03b1_2917_, lean_object* v_ref_2918_, lean_object* v_msg_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v___x_2929_; 
v___x_2929_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(v_ref_2918_, v_msg_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___boxed(lean_object* v_00_u03b1_2930_, lean_object* v_ref_2931_, lean_object* v_msg_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
lean_object* v_res_2942_; 
v_res_2942_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31(v_00_u03b1_2930_, v_ref_2931_, v_msg_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2939_);
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec(v_ref_2931_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(lean_object* v_cls_2943_, lean_object* v_msg_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_){
_start:
{
lean_object* v_ref_2950_; lean_object* v___x_2951_; lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2996_; 
v_ref_2950_ = lean_ctor_get(v___y_2947_, 2);
v___x_2951_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_);
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2954_ = v___x_2951_;
v_isShared_2955_ = v_isSharedCheck_2996_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v___x_2951_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2996_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2956_; lean_object* v_traceState_2957_; lean_object* v_env_2958_; lean_object* v_nextMacroScope_2959_; lean_object* v_ngen_2960_; lean_object* v_auxDeclNGen_2961_; lean_object* v_cache_2962_; lean_object* v_messages_2963_; lean_object* v_infoState_2964_; lean_object* v_snapshotTasks_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2995_; 
v___x_2956_ = lean_st_ref_take(v___y_2948_);
v_traceState_2957_ = lean_ctor_get(v___x_2956_, 4);
v_env_2958_ = lean_ctor_get(v___x_2956_, 0);
v_nextMacroScope_2959_ = lean_ctor_get(v___x_2956_, 1);
v_ngen_2960_ = lean_ctor_get(v___x_2956_, 2);
v_auxDeclNGen_2961_ = lean_ctor_get(v___x_2956_, 3);
v_cache_2962_ = lean_ctor_get(v___x_2956_, 5);
v_messages_2963_ = lean_ctor_get(v___x_2956_, 6);
v_infoState_2964_ = lean_ctor_get(v___x_2956_, 7);
v_snapshotTasks_2965_ = lean_ctor_get(v___x_2956_, 8);
v_isSharedCheck_2995_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2967_ = v___x_2956_;
v_isShared_2968_ = v_isSharedCheck_2995_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_snapshotTasks_2965_);
lean_inc(v_infoState_2964_);
lean_inc(v_messages_2963_);
lean_inc(v_cache_2962_);
lean_inc(v_traceState_2957_);
lean_inc(v_auxDeclNGen_2961_);
lean_inc(v_ngen_2960_);
lean_inc(v_nextMacroScope_2959_);
lean_inc(v_env_2958_);
lean_dec(v___x_2956_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2995_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
uint64_t v_tid_2969_; lean_object* v_traces_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2994_; 
v_tid_2969_ = lean_ctor_get_uint64(v_traceState_2957_, sizeof(void*)*1);
v_traces_2970_ = lean_ctor_get(v_traceState_2957_, 0);
v_isSharedCheck_2994_ = !lean_is_exclusive(v_traceState_2957_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2972_ = v_traceState_2957_;
v_isShared_2973_ = v_isSharedCheck_2994_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_traces_2970_);
lean_dec(v_traceState_2957_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2994_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2974_; lean_object* v___x_2975_; double v___x_2976_; uint8_t v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2985_; 
v___x_2974_ = lean_box(0);
v___x_2975_ = lean_box(0);
v___x_2976_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0);
v___x_2977_ = 0;
v___x_2978_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__1));
v___x_2979_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2979_, 0, v_cls_2943_);
lean_ctor_set(v___x_2979_, 1, v___x_2975_);
lean_ctor_set(v___x_2979_, 2, v___x_2978_);
lean_ctor_set_float(v___x_2979_, sizeof(void*)*3, v___x_2976_);
lean_ctor_set_float(v___x_2979_, sizeof(void*)*3 + 8, v___x_2976_);
lean_ctor_set_uint8(v___x_2979_, sizeof(void*)*3 + 16, v___x_2977_);
v___x_2980_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__2));
v___x_2981_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2981_, 0, v___x_2979_);
lean_ctor_set(v___x_2981_, 1, v_a_2952_);
lean_ctor_set(v___x_2981_, 2, v___x_2980_);
lean_inc(v_ref_2950_);
v___x_2982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2982_, 0, v_ref_2950_);
lean_ctor_set(v___x_2982_, 1, v___x_2981_);
v___x_2983_ = l_Lean_PersistentArray_push___redArg(v_traces_2970_, v___x_2982_);
if (v_isShared_2973_ == 0)
{
lean_ctor_set(v___x_2972_, 0, v___x_2983_);
v___x_2985_ = v___x_2972_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v___x_2983_);
lean_ctor_set_uint64(v_reuseFailAlloc_2993_, sizeof(void*)*1, v_tid_2969_);
v___x_2985_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
lean_object* v___x_2987_; 
if (v_isShared_2968_ == 0)
{
lean_ctor_set(v___x_2967_, 4, v___x_2985_);
v___x_2987_ = v___x_2967_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_env_2958_);
lean_ctor_set(v_reuseFailAlloc_2992_, 1, v_nextMacroScope_2959_);
lean_ctor_set(v_reuseFailAlloc_2992_, 2, v_ngen_2960_);
lean_ctor_set(v_reuseFailAlloc_2992_, 3, v_auxDeclNGen_2961_);
lean_ctor_set(v_reuseFailAlloc_2992_, 4, v___x_2985_);
lean_ctor_set(v_reuseFailAlloc_2992_, 5, v_cache_2962_);
lean_ctor_set(v_reuseFailAlloc_2992_, 6, v_messages_2963_);
lean_ctor_set(v_reuseFailAlloc_2992_, 7, v_infoState_2964_);
lean_ctor_set(v_reuseFailAlloc_2992_, 8, v_snapshotTasks_2965_);
v___x_2987_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
lean_object* v___x_2988_; lean_object* v___x_2990_; 
v___x_2988_ = lean_st_ref_put(v___y_2948_, v___x_2987_);
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 0, v___x_2974_);
v___x_2990_ = v___x_2954_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v___x_2974_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg___boxed(lean_object* v_cls_2997_, lean_object* v_msg_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_){
_start:
{
lean_object* v_res_3004_; 
v_res_3004_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_2997_, v_msg_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_);
lean_dec(v___y_3002_);
lean_dec_ref(v___y_3001_);
lean_dec(v___y_3000_);
lean_dec_ref(v___y_2999_);
return v_res_3004_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0(void){
_start:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3005_ = lean_box(0);
v___x_3006_ = lean_unsigned_to_nat(16u);
v___x_3007_ = lean_mk_array(v___x_3006_, v___x_3005_);
return v___x_3007_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1(void){
_start:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3008_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0);
v___x_3009_ = lean_unsigned_to_nat(0u);
v___x_3010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3010_, 0, v___x_3009_);
lean_ctor_set(v___x_3010_, 1, v___x_3008_);
return v___x_3010_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3(void){
_start:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; 
v___x_3012_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__2));
v___x_3013_ = l_Lean_stringToMessageData(v___x_3012_);
return v___x_3013_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5(void){
_start:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3015_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__4));
v___x_3016_ = l_Lean_stringToMessageData(v___x_3015_);
return v___x_3016_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7(void){
_start:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3018_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__6));
v___x_3019_ = l_Lean_stringToMessageData(v___x_3018_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(lean_object* v_recFnName_3020_, lean_object* v_fixedPrefixSize_3021_, lean_object* v_F_3022_, lean_object* v_e_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_){
_start:
{
lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v_toCold_3052_; lean_object* v_options_3053_; uint8_t v_hasTrace_3054_; 
v_toCold_3052_ = lean_ctor_get(v_a_3028_, 0);
v_options_3053_ = lean_ctor_get(v_toCold_3052_, 2);
v_hasTrace_3054_ = lean_ctor_get_uint8(v_options_3053_, sizeof(void*)*1);
if (v_hasTrace_3054_ == 0)
{
v___y_3032_ = v_a_3024_;
v___y_3033_ = v_a_3025_;
v___y_3034_ = v_a_3026_;
v___y_3035_ = v_a_3027_;
v___y_3036_ = v_a_3028_;
v___y_3037_ = v_a_3029_;
goto v___jp_3031_;
}
else
{
lean_object* v_inheritedTraceOptions_3055_; lean_object* v_cls_3056_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v_options_3063_; lean_object* v_inheritedTraceOptions_3064_; lean_object* v___y_3065_; lean_object* v___x_3086_; uint8_t v___x_3087_; 
v_inheritedTraceOptions_3055_ = lean_ctor_get(v_toCold_3052_, 11);
v_cls_3056_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_3086_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_3087_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3055_, v_options_3053_, v___x_3086_);
if (v___x_3087_ == 0)
{
v___y_3058_ = v_a_3024_;
v___y_3059_ = v_a_3025_;
v___y_3060_ = v_a_3026_;
v___y_3061_ = v_a_3027_;
v___y_3062_ = v_a_3028_;
v_options_3063_ = v_options_3053_;
v_inheritedTraceOptions_3064_ = v_inheritedTraceOptions_3055_;
v___y_3065_ = v_a_3029_;
goto v___jp_3057_;
}
else
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3088_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7);
lean_inc_ref(v_e_3023_);
v___x_3089_ = l_Lean_indentExpr(v_e_3023_);
v___x_3090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3090_, 0, v___x_3088_);
lean_ctor_set(v___x_3090_, 1, v___x_3089_);
v___x_3091_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3056_, v___x_3090_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_);
if (lean_obj_tag(v___x_3091_) == 0)
{
lean_dec_ref_known(v___x_3091_, 1);
v___y_3058_ = v_a_3024_;
v___y_3059_ = v_a_3025_;
v___y_3060_ = v_a_3026_;
v___y_3061_ = v_a_3027_;
v___y_3062_ = v_a_3028_;
v_options_3063_ = v_options_3053_;
v_inheritedTraceOptions_3064_ = v_inheritedTraceOptions_3055_;
v___y_3065_ = v_a_3029_;
goto v___jp_3057_;
}
else
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3099_; 
lean_dec_ref(v_e_3023_);
lean_dec_ref(v_F_3022_);
lean_dec(v_fixedPrefixSize_3021_);
lean_dec(v_recFnName_3020_);
v_a_3092_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3094_ = v___x_3091_;
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_3091_);
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
v___jp_3057_:
{
lean_object* v___x_3066_; uint8_t v___x_3067_; 
v___x_3066_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_3067_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3064_, v_options_3063_, v___x_3066_);
if (v___x_3067_ == 0)
{
v___y_3032_ = v___y_3058_;
v___y_3033_ = v___y_3059_;
v___y_3034_ = v___y_3060_;
v___y_3035_ = v___y_3061_;
v___y_3036_ = v___y_3062_;
v___y_3037_ = v___y_3065_;
goto v___jp_3031_;
}
else
{
lean_object* v___x_3068_; 
lean_inc(v___y_3065_);
lean_inc_ref(v___y_3062_);
lean_inc(v___y_3061_);
lean_inc_ref(v___y_3060_);
lean_inc_ref(v_F_3022_);
v___x_3068_ = lean_infer_type(v_F_3022_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3065_);
if (lean_obj_tag(v___x_3068_) == 0)
{
lean_object* v_a_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v_a_3069_ = lean_ctor_get(v___x_3068_, 0);
lean_inc(v_a_3069_);
lean_dec_ref_known(v___x_3068_, 1);
v___x_3070_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3);
lean_inc_ref(v_F_3022_);
v___x_3071_ = l_Lean_MessageData_ofExpr(v_F_3022_);
v___x_3072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3070_);
lean_ctor_set(v___x_3072_, 1, v___x_3071_);
v___x_3073_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5);
v___x_3074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3074_, 0, v___x_3072_);
lean_ctor_set(v___x_3074_, 1, v___x_3073_);
v___x_3075_ = l_Lean_indentExpr(v_a_3069_);
v___x_3076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3074_);
lean_ctor_set(v___x_3076_, 1, v___x_3075_);
v___x_3077_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3056_, v___x_3076_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3065_);
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_dec_ref_known(v___x_3077_, 1);
v___y_3032_ = v___y_3058_;
v___y_3033_ = v___y_3059_;
v___y_3034_ = v___y_3060_;
v___y_3035_ = v___y_3061_;
v___y_3036_ = v___y_3062_;
v___y_3037_ = v___y_3065_;
goto v___jp_3031_;
}
else
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3085_; 
lean_dec_ref(v_e_3023_);
lean_dec_ref(v_F_3022_);
lean_dec(v_fixedPrefixSize_3021_);
lean_dec(v_recFnName_3020_);
v_a_3078_ = lean_ctor_get(v___x_3077_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3080_ = v___x_3077_;
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_3077_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3083_; 
if (v_isShared_3081_ == 0)
{
v___x_3083_ = v___x_3080_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_a_3078_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
}
}
else
{
lean_dec_ref(v_e_3023_);
lean_dec_ref(v_F_3022_);
lean_dec(v_fixedPrefixSize_3021_);
lean_dec(v_recFnName_3020_);
return v___x_3068_;
}
}
}
}
v___jp_3031_:
{
lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
v___x_3038_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1);
v___x_3039_ = lean_st_mk_ref(v___x_3038_);
v___x_3040_ = lean_st_mk_ref(v___x_3038_);
v___x_3041_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_3020_, v_fixedPrefixSize_3021_, v_F_3022_, v_e_3023_, v___x_3040_, v___x_3039_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_);
if (lean_obj_tag(v___x_3041_) == 0)
{
lean_object* v_a_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3051_; 
v_a_3042_ = lean_ctor_get(v___x_3041_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3041_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3044_ = v___x_3041_;
v_isShared_3045_ = v_isSharedCheck_3051_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_a_3042_);
lean_dec(v___x_3041_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3051_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3049_; 
v___x_3046_ = lean_st_ref_get(v___x_3040_);
lean_dec(v___x_3040_);
lean_dec(v___x_3046_);
v___x_3047_ = lean_st_ref_get(v___x_3039_);
lean_dec(v___x_3039_);
lean_dec(v___x_3047_);
if (v_isShared_3045_ == 0)
{
v___x_3049_ = v___x_3044_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_a_3042_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
else
{
lean_dec(v___x_3040_);
lean_dec(v___x_3039_);
return v___x_3041_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___boxed(lean_object* v_recFnName_3100_, lean_object* v_fixedPrefixSize_3101_, lean_object* v_F_3102_, lean_object* v_e_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_, lean_object* v_a_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_){
_start:
{
lean_object* v_res_3111_; 
v_res_3111_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(v_recFnName_3100_, v_fixedPrefixSize_3101_, v_F_3102_, v_e_3103_, v_a_3104_, v_a_3105_, v_a_3106_, v_a_3107_, v_a_3108_, v_a_3109_);
lean_dec(v_a_3109_);
lean_dec_ref(v_a_3108_);
lean_dec(v_a_3107_);
lean_dec_ref(v_a_3106_);
lean_dec(v_a_3105_);
lean_dec_ref(v_a_3104_);
return v_res_3111_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0(lean_object* v_cls_3112_, lean_object* v_msg_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_){
_start:
{
lean_object* v___x_3121_; 
v___x_3121_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3112_, v_msg_3113_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_);
return v___x_3121_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___boxed(lean_object* v_cls_3122_, lean_object* v_msg_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_){
_start:
{
lean_object* v_res_3131_; 
v_res_3131_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0(v_cls_3122_, v_msg_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_);
lean_dec(v___y_3129_);
lean_dec_ref(v___y_3128_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
lean_dec(v___y_3125_);
lean_dec_ref(v___y_3124_);
return v_res_3131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0(lean_object* v_k_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v_b_3135_, lean_object* v_c_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_){
_start:
{
lean_object* v___x_3142_; 
lean_inc(v___y_3140_);
lean_inc_ref(v___y_3139_);
lean_inc(v___y_3138_);
lean_inc_ref(v___y_3137_);
lean_inc(v___y_3134_);
lean_inc_ref(v___y_3133_);
v___x_3142_ = lean_apply_9(v_k_3132_, v_b_3135_, v_c_3136_, v___y_3133_, v___y_3134_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, lean_box(0));
return v___x_3142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0___boxed(lean_object* v_k_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v_b_3146_, lean_object* v_c_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_){
_start:
{
lean_object* v_res_3153_; 
v_res_3153_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0(v_k_3143_, v___y_3144_, v___y_3145_, v_b_3146_, v_c_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3145_);
lean_dec_ref(v___y_3144_);
return v_res_3153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(lean_object* v_e_3154_, lean_object* v_maxFVars_3155_, lean_object* v_k_3156_, uint8_t v_cleanupAnnotations_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
lean_object* v___f_3165_; uint8_t v___x_3166_; uint8_t v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
lean_inc(v___y_3159_);
lean_inc_ref(v___y_3158_);
v___f_3165_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3165_, 0, v_k_3156_);
lean_closure_set(v___f_3165_, 1, v___y_3158_);
lean_closure_set(v___f_3165_, 2, v___y_3159_);
v___x_3166_ = 1;
v___x_3167_ = 0;
v___x_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3168_, 0, v_maxFVars_3155_);
v___x_3169_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3154_, v___x_3166_, v___x_3167_, v___x_3166_, v___x_3167_, v___x_3168_, v___f_3165_, v_cleanupAnnotations_3157_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_);
lean_dec_ref_known(v___x_3168_, 1);
if (lean_obj_tag(v___x_3169_) == 0)
{
return v___x_3169_;
}
else
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3177_; 
v_a_3170_ = lean_ctor_get(v___x_3169_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3172_ = v___x_3169_;
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3169_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3175_; 
if (v_isShared_3173_ == 0)
{
v___x_3175_ = v___x_3172_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_a_3170_);
v___x_3175_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
return v___x_3175_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___boxed(lean_object* v_e_3178_, lean_object* v_maxFVars_3179_, lean_object* v_k_3180_, lean_object* v_cleanupAnnotations_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3189_; lean_object* v_res_3190_; 
v_cleanupAnnotations_boxed_3189_ = lean_unbox(v_cleanupAnnotations_3181_);
v_res_3190_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_e_3178_, v_maxFVars_3179_, v_k_3180_, v_cleanupAnnotations_boxed_3189_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1(lean_object* v_00_u03b1_3191_, lean_object* v_e_3192_, lean_object* v_maxFVars_3193_, lean_object* v_k_3194_, uint8_t v_cleanupAnnotations_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_){
_start:
{
lean_object* v___x_3203_; 
v___x_3203_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_e_3192_, v_maxFVars_3193_, v_k_3194_, v_cleanupAnnotations_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_);
return v___x_3203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___boxed(lean_object* v_00_u03b1_3204_, lean_object* v_e_3205_, lean_object* v_maxFVars_3206_, lean_object* v_k_3207_, lean_object* v_cleanupAnnotations_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3216_; lean_object* v_res_3217_; 
v_cleanupAnnotations_boxed_3216_ = lean_unbox(v_cleanupAnnotations_3208_);
v_res_3217_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1(v_00_u03b1_3204_, v_e_3205_, v_maxFVars_3206_, v_k_3207_, v_cleanupAnnotations_boxed_3216_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
lean_dec(v___y_3214_);
lean_dec_ref(v___y_3213_);
lean_dec(v___y_3212_);
lean_dec_ref(v___y_3211_);
lean_dec(v___y_3210_);
lean_dec_ref(v___y_3209_);
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(lean_object* v_e_3218_, lean_object* v_k_3219_, uint8_t v_cleanupAnnotations_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_){
_start:
{
lean_object* v___f_3228_; uint8_t v___x_3229_; uint8_t v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; 
lean_inc(v___y_3222_);
lean_inc_ref(v___y_3221_);
v___f_3228_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3228_, 0, v_k_3219_);
lean_closure_set(v___f_3228_, 1, v___y_3221_);
lean_closure_set(v___f_3228_, 2, v___y_3222_);
v___x_3229_ = 1;
v___x_3230_ = 0;
v___x_3231_ = lean_box(0);
v___x_3232_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3218_, v___x_3229_, v___x_3230_, v___x_3229_, v___x_3230_, v___x_3231_, v___f_3228_, v_cleanupAnnotations_3220_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
if (lean_obj_tag(v___x_3232_) == 0)
{
return v___x_3232_;
}
else
{
lean_object* v_a_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3240_; 
v_a_3233_ = lean_ctor_get(v___x_3232_, 0);
v_isSharedCheck_3240_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3240_ == 0)
{
v___x_3235_ = v___x_3232_;
v_isShared_3236_ = v_isSharedCheck_3240_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_a_3233_);
lean_dec(v___x_3232_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3240_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
lean_object* v___x_3238_; 
if (v_isShared_3236_ == 0)
{
v___x_3238_ = v___x_3235_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v_a_3233_);
v___x_3238_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
return v___x_3238_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg___boxed(lean_object* v_e_3241_, lean_object* v_k_3242_, lean_object* v_cleanupAnnotations_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3251_; lean_object* v_res_3252_; 
v_cleanupAnnotations_boxed_3251_ = lean_unbox(v_cleanupAnnotations_3243_);
v_res_3252_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_e_3241_, v_k_3242_, v_cleanupAnnotations_boxed_3251_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
return v_res_3252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2(lean_object* v_00_u03b1_3253_, lean_object* v_e_3254_, lean_object* v_k_3255_, uint8_t v_cleanupAnnotations_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_){
_start:
{
lean_object* v___x_3264_; 
v___x_3264_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_e_3254_, v_k_3255_, v_cleanupAnnotations_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___boxed(lean_object* v_00_u03b1_3265_, lean_object* v_e_3266_, lean_object* v_k_3267_, lean_object* v_cleanupAnnotations_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3276_; lean_object* v_res_3277_; 
v_cleanupAnnotations_boxed_3276_ = lean_unbox(v_cleanupAnnotations_3268_);
v_res_3277_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2(v_00_u03b1_3265_, v_e_3266_, v_k_3267_, v_cleanupAnnotations_boxed_3276_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
return v_res_3277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0(lean_object* v_a_3278_, lean_object* v___x_3279_, lean_object* v___x_3280_, lean_object* v_x_3281_, uint8_t v___x_3282_, lean_object* v_xs_3283_, lean_object* v_type_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_){
_start:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; 
v___x_3292_ = l_Lean_LocalDecl_type(v_a_3278_);
v___x_3293_ = lean_array_get_borrowed(v___x_3279_, v_xs_3283_, v___x_3280_);
v___x_3294_ = l_Lean_Expr_replaceFVar(v___x_3292_, v_x_3281_, v___x_3293_);
lean_dec_ref(v___x_3292_);
v___x_3295_ = l_Lean_mkArrow(v___x_3294_, v_type_3284_, v___y_3289_, v___y_3290_);
if (lean_obj_tag(v___x_3295_) == 0)
{
lean_object* v_a_3296_; uint8_t v___x_3297_; uint8_t v___x_3298_; lean_object* v___x_3299_; 
v_a_3296_ = lean_ctor_get(v___x_3295_, 0);
lean_inc_n(v_a_3296_, 2);
lean_dec_ref_known(v___x_3295_, 1);
v___x_3297_ = 0;
v___x_3298_ = 1;
v___x_3299_ = l_Lean_Meta_mkLambdaFVars(v_xs_3283_, v_a_3296_, v___x_3297_, v___x_3282_, v___x_3297_, v___x_3282_, v___x_3298_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_);
if (lean_obj_tag(v___x_3299_) == 0)
{
lean_object* v_a_3300_; lean_object* v___x_3301_; 
v_a_3300_ = lean_ctor_get(v___x_3299_, 0);
lean_inc(v_a_3300_);
lean_dec_ref_known(v___x_3299_, 1);
v___x_3301_ = l_Lean_Meta_getLevel(v_a_3296_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_);
if (lean_obj_tag(v___x_3301_) == 0)
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3310_; 
v_a_3302_ = lean_ctor_get(v___x_3301_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3304_ = v___x_3301_;
v_isShared_3305_ = v_isSharedCheck_3310_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3301_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3310_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3306_; lean_object* v___x_3308_; 
v___x_3306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3306_, 0, v_a_3300_);
lean_ctor_set(v___x_3306_, 1, v_a_3302_);
if (v_isShared_3305_ == 0)
{
lean_ctor_set(v___x_3304_, 0, v___x_3306_);
v___x_3308_ = v___x_3304_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v___x_3306_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
}
else
{
lean_object* v_a_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3318_; 
lean_dec(v_a_3300_);
v_a_3311_ = lean_ctor_get(v___x_3301_, 0);
v_isSharedCheck_3318_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3313_ = v___x_3301_;
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_a_3311_);
lean_dec(v___x_3301_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v___x_3316_; 
if (v_isShared_3314_ == 0)
{
v___x_3316_ = v___x_3313_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_a_3311_);
v___x_3316_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
return v___x_3316_;
}
}
}
}
else
{
lean_object* v_a_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3326_; 
lean_dec(v_a_3296_);
v_a_3319_ = lean_ctor_get(v___x_3299_, 0);
v_isSharedCheck_3326_ = !lean_is_exclusive(v___x_3299_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3321_ = v___x_3299_;
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_a_3319_);
lean_dec(v___x_3299_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v___x_3324_; 
if (v_isShared_3322_ == 0)
{
v___x_3324_ = v___x_3321_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v_a_3319_);
v___x_3324_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
return v___x_3324_;
}
}
}
}
else
{
lean_object* v_a_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3334_; 
v_a_3327_ = lean_ctor_get(v___x_3295_, 0);
v_isSharedCheck_3334_ = !lean_is_exclusive(v___x_3295_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3329_ = v___x_3295_;
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_a_3327_);
lean_dec(v___x_3295_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v___x_3332_; 
if (v_isShared_3330_ == 0)
{
v___x_3332_ = v___x_3329_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v_a_3327_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
return v___x_3332_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed(lean_object* v_a_3335_, lean_object* v___x_3336_, lean_object* v___x_3337_, lean_object* v_x_3338_, lean_object* v___x_3339_, lean_object* v_xs_3340_, lean_object* v_type_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_){
_start:
{
uint8_t v___x_6245__boxed_3349_; lean_object* v_res_3350_; 
v___x_6245__boxed_3349_ = lean_unbox(v___x_3339_);
v_res_3350_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0(v_a_3335_, v___x_3336_, v___x_3337_, v_x_3338_, v___x_6245__boxed_3349_, v_xs_3340_, v_type_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_);
lean_dec(v___y_3347_);
lean_dec_ref(v___y_3346_);
lean_dec(v___y_3345_);
lean_dec_ref(v___y_3344_);
lean_dec(v___y_3343_);
lean_dec_ref(v___y_3342_);
lean_dec_ref(v_xs_3340_);
lean_dec(v___x_3337_);
lean_dec_ref(v___x_3336_);
lean_dec_ref(v_a_3335_);
return v_res_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg___lam__0(lean_object* v_k_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v_b_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_){
_start:
{
lean_object* v___x_3360_; 
lean_inc(v___y_3358_);
lean_inc_ref(v___y_3357_);
lean_inc(v___y_3356_);
lean_inc_ref(v___y_3355_);
lean_inc(v___y_3353_);
lean_inc_ref(v___y_3352_);
v___x_3360_ = lean_apply_8(v_k_3351_, v_b_3354_, v___y_3352_, v___y_3353_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, lean_box(0));
return v___x_3360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v_b_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg___lam__0(v_k_3361_, v___y_3362_, v___y_3363_, v_b_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_);
lean_dec(v___y_3368_);
lean_dec_ref(v___y_3367_);
lean_dec(v___y_3366_);
lean_dec_ref(v___y_3365_);
lean_dec(v___y_3363_);
lean_dec_ref(v___y_3362_);
return v_res_3370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg(lean_object* v_name_3371_, uint8_t v_bi_3372_, lean_object* v_type_3373_, lean_object* v_k_3374_, uint8_t v_kind_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
lean_object* v___f_3383_; lean_object* v___x_3384_; 
lean_inc(v___y_3377_);
lean_inc_ref(v___y_3376_);
v___f_3383_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3383_, 0, v_k_3374_);
lean_closure_set(v___f_3383_, 1, v___y_3376_);
lean_closure_set(v___f_3383_, 2, v___y_3377_);
v___x_3384_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3371_, v_bi_3372_, v_type_3373_, v___f_3383_, v_kind_3375_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
if (lean_obj_tag(v___x_3384_) == 0)
{
return v___x_3384_;
}
else
{
lean_object* v_a_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3392_; 
v_a_3385_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3387_ = v___x_3384_;
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_a_3385_);
lean_dec(v___x_3384_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___x_3390_; 
if (v_isShared_3388_ == 0)
{
v___x_3390_ = v___x_3387_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v_a_3385_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
return v___x_3390_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg___boxed(lean_object* v_name_3393_, lean_object* v_bi_3394_, lean_object* v_type_3395_, lean_object* v_k_3396_, lean_object* v_kind_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_){
_start:
{
uint8_t v_bi_boxed_3405_; uint8_t v_kind_boxed_3406_; lean_object* v_res_3407_; 
v_bi_boxed_3405_ = lean_unbox(v_bi_3394_);
v_kind_boxed_3406_ = lean_unbox(v_kind_3397_);
v_res_3407_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg(v_name_3393_, v_bi_boxed_3405_, v_type_3395_, v_k_3396_, v_kind_boxed_3406_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
lean_dec(v___y_3403_);
lean_dec_ref(v___y_3402_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(lean_object* v_name_3408_, lean_object* v_type_3409_, lean_object* v_k_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_){
_start:
{
uint8_t v___x_3418_; uint8_t v___x_3419_; lean_object* v___x_3420_; 
v___x_3418_ = 0;
v___x_3419_ = 0;
v___x_3420_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg(v_name_3408_, v___x_3418_, v_type_3409_, v_k_3410_, v___x_3419_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_);
return v___x_3420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___boxed(lean_object* v_name_3421_, lean_object* v_type_3422_, lean_object* v_k_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_){
_start:
{
lean_object* v_res_3431_; 
v_res_3431_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v_name_3421_, v_type_3422_, v_k_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
return v_res_3431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(lean_object* v_x_3445_, lean_object* v_F_3446_, lean_object* v_val_3447_, lean_object* v_k_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_){
_start:
{
lean_object* v___x_3456_; uint8_t v___y_3458_; uint8_t v___x_3572_; 
v___x_3456_ = l_Lean_instInhabitedExpr;
v___x_3572_ = l_Lean_Expr_isFVar(v_x_3445_);
if (v___x_3572_ == 0)
{
v___y_3458_ = v___x_3572_;
goto v___jp_3457_;
}
else
{
lean_object* v___x_3573_; lean_object* v___x_3574_; uint8_t v___x_3575_; 
v___x_3573_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6));
v___x_3574_ = lean_unsigned_to_nat(6u);
v___x_3575_ = l_Lean_Expr_isAppOfArity(v_val_3447_, v___x_3573_, v___x_3574_);
v___y_3458_ = v___x_3575_;
goto v___jp_3457_;
}
v___jp_3457_:
{
if (v___y_3458_ == 0)
{
lean_object* v___x_3459_; 
lean_inc(v_a_3454_);
lean_inc_ref(v_a_3453_);
lean_inc(v_a_3452_);
lean_inc_ref(v_a_3451_);
lean_inc(v_a_3450_);
lean_inc_ref(v_a_3449_);
v___x_3459_ = lean_apply_10(v_k_3448_, v_x_3445_, v_F_3446_, v_val_3447_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_, lean_box(0));
return v___x_3459_;
}
else
{
lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; uint8_t v___x_3466_; 
v___x_3460_ = lean_unsigned_to_nat(3u);
v___x_3461_ = l_Lean_Expr_getAppNumArgs(v_val_3447_);
v___x_3462_ = lean_nat_sub(v___x_3461_, v___x_3460_);
v___x_3463_ = lean_unsigned_to_nat(1u);
v___x_3464_ = lean_nat_sub(v___x_3462_, v___x_3463_);
lean_dec(v___x_3462_);
v___x_3465_ = l_Lean_Expr_getRevArg_x21(v_val_3447_, v___x_3464_);
v___x_3466_ = lean_expr_eqv(v___x_3465_, v_x_3445_);
lean_dec_ref(v___x_3465_);
if (v___x_3466_ == 0)
{
lean_object* v___x_3467_; 
lean_dec(v___x_3461_);
lean_inc(v_a_3454_);
lean_inc_ref(v_a_3453_);
lean_inc(v_a_3452_);
lean_inc_ref(v_a_3451_);
lean_inc(v_a_3450_);
lean_inc_ref(v_a_3449_);
v___x_3467_ = lean_apply_10(v_k_3448_, v_x_3445_, v_F_3446_, v_val_3447_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_, lean_box(0));
return v___x_3467_;
}
else
{
lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; uint8_t v___x_3472_; 
v___x_3468_ = lean_unsigned_to_nat(4u);
v___x_3469_ = lean_nat_sub(v___x_3461_, v___x_3468_);
v___x_3470_ = lean_nat_sub(v___x_3469_, v___x_3463_);
lean_dec(v___x_3469_);
v___x_3471_ = l_Lean_Expr_getRevArg_x21(v_val_3447_, v___x_3470_);
v___x_3472_ = l_Lean_Expr_isLambda(v___x_3471_);
lean_dec_ref(v___x_3471_);
if (v___x_3472_ == 0)
{
lean_object* v___x_3473_; 
lean_dec(v___x_3461_);
lean_inc(v_a_3454_);
lean_inc_ref(v_a_3453_);
lean_inc(v_a_3452_);
lean_inc_ref(v_a_3451_);
lean_inc(v_a_3450_);
lean_inc_ref(v_a_3449_);
v___x_3473_ = lean_apply_10(v_k_3448_, v_x_3445_, v_F_3446_, v_val_3447_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_, lean_box(0));
return v___x_3473_;
}
else
{
lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; uint8_t v___x_3478_; 
v___x_3474_ = lean_unsigned_to_nat(5u);
v___x_3475_ = lean_nat_sub(v___x_3461_, v___x_3474_);
v___x_3476_ = lean_nat_sub(v___x_3475_, v___x_3463_);
lean_dec(v___x_3475_);
v___x_3477_ = l_Lean_Expr_getRevArg_x21(v_val_3447_, v___x_3476_);
v___x_3478_ = l_Lean_Expr_isLambda(v___x_3477_);
lean_dec_ref(v___x_3477_);
if (v___x_3478_ == 0)
{
lean_object* v___x_3479_; 
lean_dec(v___x_3461_);
lean_inc(v_a_3454_);
lean_inc_ref(v_a_3453_);
lean_inc(v_a_3452_);
lean_inc_ref(v_a_3451_);
lean_inc(v_a_3450_);
lean_inc_ref(v_a_3449_);
v___x_3479_ = lean_apply_10(v_k_3448_, v_x_3445_, v_F_3446_, v_val_3447_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_, lean_box(0));
return v___x_3479_;
}
else
{
lean_object* v_dummy_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v_args_3483_; lean_object* v___x_3484_; lean_object* v_00_u03b1_3485_; lean_object* v_00_u03b2_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
v_dummy_3480_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_3461_);
v___x_3481_ = lean_mk_array(v___x_3461_, v_dummy_3480_);
v___x_3482_ = lean_nat_sub(v___x_3461_, v___x_3463_);
lean_dec(v___x_3461_);
v_args_3483_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_3447_, v___x_3481_, v___x_3482_);
v___x_3484_ = lean_unsigned_to_nat(0u);
v_00_u03b1_3485_ = lean_array_get(v___x_3456_, v_args_3483_, v___x_3484_);
v_00_u03b2_3486_ = lean_array_get(v___x_3456_, v_args_3483_, v___x_3463_);
v___x_3487_ = l_Lean_Expr_fvarId_x21(v_F_3446_);
v___x_3488_ = l_Lean_FVarId_getDecl___redArg(v___x_3487_, v_a_3451_, v_a_3453_, v_a_3454_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v_a_3489_; lean_object* v___x_3490_; lean_object* v___f_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; uint8_t v___x_3494_; lean_object* v___x_3495_; 
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
lean_inc_n(v_a_3489_, 2);
lean_dec_ref_known(v___x_3488_, 1);
v___x_3490_ = lean_box(v___x_3472_);
lean_inc_ref(v_x_3445_);
v___f_3491_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed), 14, 5);
lean_closure_set(v___f_3491_, 0, v_a_3489_);
lean_closure_set(v___f_3491_, 1, v___x_3456_);
lean_closure_set(v___f_3491_, 2, v___x_3484_);
lean_closure_set(v___f_3491_, 3, v_x_3445_);
lean_closure_set(v___f_3491_, 4, v___x_3490_);
v___x_3492_ = lean_unsigned_to_nat(2u);
v___x_3493_ = lean_array_get(v___x_3456_, v_args_3483_, v___x_3492_);
v___x_3494_ = 0;
v___x_3495_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v___x_3493_, v___f_3491_, v___x_3494_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; lean_object* v_fst_3497_; lean_object* v_snd_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3555_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_a_3496_);
lean_dec_ref_known(v___x_3495_, 1);
v_fst_3497_ = lean_ctor_get(v_a_3496_, 0);
v_snd_3498_ = lean_ctor_get(v_a_3496_, 1);
v_isSharedCheck_3555_ = !lean_is_exclusive(v_a_3496_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3500_ = v_a_3496_;
v_isShared_3501_ = v_isSharedCheck_3555_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_snd_3498_);
lean_inc(v_fst_3497_);
lean_dec(v_a_3496_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3555_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___x_3502_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__2));
v___x_3503_ = lean_array_get(v___x_3456_, v_args_3483_, v___x_3468_);
lean_inc_ref(v_x_3445_);
lean_inc(v_a_3489_);
lean_inc(v_00_u03b2_3486_);
lean_inc(v_00_u03b1_3485_);
lean_inc_ref(v_k_3448_);
v___x_3504_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3456_, v___x_3484_, v_k_3448_, v___x_3492_, v___x_3494_, v___x_3472_, v_00_u03b1_3485_, v_00_u03b2_3486_, v___x_3460_, v_a_3489_, v_x_3445_, v___x_3463_, v___x_3502_, v___x_3503_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_);
if (lean_obj_tag(v___x_3504_) == 0)
{
lean_object* v_a_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; 
v_a_3505_ = lean_ctor_get(v___x_3504_, 0);
lean_inc(v_a_3505_);
lean_dec_ref_known(v___x_3504_, 1);
v___x_3506_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__4));
v___x_3507_ = lean_array_get(v___x_3456_, v_args_3483_, v___x_3474_);
lean_dec_ref(v_args_3483_);
lean_inc_ref(v_x_3445_);
lean_inc(v_00_u03b2_3486_);
lean_inc(v_00_u03b1_3485_);
v___x_3508_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3456_, v___x_3484_, v_k_3448_, v___x_3492_, v___x_3494_, v___x_3472_, v_00_u03b1_3485_, v_00_u03b2_3486_, v___x_3460_, v_a_3489_, v_x_3445_, v___x_3463_, v___x_3506_, v___x_3507_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_);
if (lean_obj_tag(v___x_3508_) == 0)
{
lean_object* v_a_3509_; lean_object* v___x_3510_; 
v_a_3509_ = lean_ctor_get(v___x_3508_, 0);
lean_inc(v_a_3509_);
lean_dec_ref_known(v___x_3508_, 1);
lean_inc(v_00_u03b1_3485_);
v___x_3510_ = l_Lean_Meta_getLevel(v_00_u03b1_3485_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_);
if (lean_obj_tag(v___x_3510_) == 0)
{
lean_object* v_a_3511_; lean_object* v___x_3512_; 
v_a_3511_ = lean_ctor_get(v___x_3510_, 0);
lean_inc(v_a_3511_);
lean_dec_ref_known(v___x_3510_, 1);
lean_inc(v_00_u03b2_3486_);
v___x_3512_ = l_Lean_Meta_getLevel(v_00_u03b2_3486_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_);
if (lean_obj_tag(v___x_3512_) == 0)
{
lean_object* v_a_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3538_; 
v_a_3513_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3515_ = v___x_3512_;
v_isShared_3516_ = v_isSharedCheck_3538_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_a_3513_);
lean_dec(v___x_3512_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3538_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3520_; 
v___x_3517_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6));
v___x_3518_ = lean_box(0);
if (v_isShared_3501_ == 0)
{
lean_ctor_set_tag(v___x_3500_, 1);
lean_ctor_set(v___x_3500_, 1, v___x_3518_);
lean_ctor_set(v___x_3500_, 0, v_a_3513_);
v___x_3520_ = v___x_3500_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_a_3513_);
lean_ctor_set(v_reuseFailAlloc_3537_, 1, v___x_3518_);
v___x_3520_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3535_; 
v___x_3521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3521_, 0, v_a_3511_);
lean_ctor_set(v___x_3521_, 1, v___x_3520_);
v___x_3522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3522_, 0, v_snd_3498_);
lean_ctor_set(v___x_3522_, 1, v___x_3521_);
v___x_3523_ = l_Lean_mkConst(v___x_3517_, v___x_3522_);
v___x_3524_ = lean_unsigned_to_nat(7u);
v___x_3525_ = lean_mk_empty_array_with_capacity(v___x_3524_);
v___x_3526_ = lean_array_push(v___x_3525_, v_00_u03b1_3485_);
v___x_3527_ = lean_array_push(v___x_3526_, v_00_u03b2_3486_);
v___x_3528_ = lean_array_push(v___x_3527_, v_fst_3497_);
v___x_3529_ = lean_array_push(v___x_3528_, v_x_3445_);
v___x_3530_ = lean_array_push(v___x_3529_, v_a_3505_);
v___x_3531_ = lean_array_push(v___x_3530_, v_a_3509_);
v___x_3532_ = lean_array_push(v___x_3531_, v_F_3446_);
v___x_3533_ = l_Lean_mkAppN(v___x_3523_, v___x_3532_);
lean_dec_ref(v___x_3532_);
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 0, v___x_3533_);
v___x_3535_ = v___x_3515_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v___x_3533_);
v___x_3535_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
return v___x_3535_;
}
}
}
}
else
{
lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3546_; 
lean_dec(v_a_3511_);
lean_dec(v_a_3509_);
lean_dec(v_a_3505_);
lean_del_object(v___x_3500_);
lean_dec(v_snd_3498_);
lean_dec(v_fst_3497_);
lean_dec(v_00_u03b2_3486_);
lean_dec(v_00_u03b1_3485_);
lean_dec_ref(v_F_3446_);
lean_dec_ref(v_x_3445_);
v_a_3539_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3541_ = v___x_3512_;
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___x_3512_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3544_; 
if (v_isShared_3542_ == 0)
{
v___x_3544_ = v___x_3541_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_a_3539_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
}
}
}
}
else
{
lean_object* v_a_3547_; lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3554_; 
lean_dec(v_a_3509_);
lean_dec(v_a_3505_);
lean_del_object(v___x_3500_);
lean_dec(v_snd_3498_);
lean_dec(v_fst_3497_);
lean_dec(v_00_u03b2_3486_);
lean_dec(v_00_u03b1_3485_);
lean_dec_ref(v_F_3446_);
lean_dec_ref(v_x_3445_);
v_a_3547_ = lean_ctor_get(v___x_3510_, 0);
v_isSharedCheck_3554_ = !lean_is_exclusive(v___x_3510_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3549_ = v___x_3510_;
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
else
{
lean_inc(v_a_3547_);
lean_dec(v___x_3510_);
v___x_3549_ = lean_box(0);
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
v_resetjp_3548_:
{
lean_object* v___x_3552_; 
if (v_isShared_3550_ == 0)
{
v___x_3552_ = v___x_3549_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v_a_3547_);
v___x_3552_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
return v___x_3552_;
}
}
}
}
else
{
lean_dec(v_a_3505_);
lean_del_object(v___x_3500_);
lean_dec(v_snd_3498_);
lean_dec(v_fst_3497_);
lean_dec(v_00_u03b2_3486_);
lean_dec(v_00_u03b1_3485_);
lean_dec_ref(v_F_3446_);
lean_dec_ref(v_x_3445_);
return v___x_3508_;
}
}
else
{
lean_del_object(v___x_3500_);
lean_dec(v_snd_3498_);
lean_dec(v_fst_3497_);
lean_dec(v_a_3489_);
lean_dec(v_00_u03b2_3486_);
lean_dec(v_00_u03b1_3485_);
lean_dec_ref(v_args_3483_);
lean_dec_ref(v_k_3448_);
lean_dec_ref(v_F_3446_);
lean_dec_ref(v_x_3445_);
return v___x_3504_;
}
}
}
else
{
lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3563_; 
lean_dec(v_a_3489_);
lean_dec(v_00_u03b2_3486_);
lean_dec(v_00_u03b1_3485_);
lean_dec_ref(v_args_3483_);
lean_dec_ref(v_k_3448_);
lean_dec_ref(v_F_3446_);
lean_dec_ref(v_x_3445_);
v_a_3556_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3563_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3558_ = v___x_3495_;
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_dec(v___x_3495_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v___x_3561_; 
if (v_isShared_3559_ == 0)
{
v___x_3561_ = v___x_3558_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_a_3556_);
v___x_3561_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
return v___x_3561_;
}
}
}
}
else
{
lean_object* v_a_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3571_; 
lean_dec(v_00_u03b2_3486_);
lean_dec(v_00_u03b1_3485_);
lean_dec_ref(v_args_3483_);
lean_dec_ref(v_k_3448_);
lean_dec_ref(v_F_3446_);
lean_dec_ref(v_x_3445_);
v_a_3564_ = lean_ctor_get(v___x_3488_, 0);
v_isSharedCheck_3571_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3571_ == 0)
{
v___x_3566_ = v___x_3488_;
v_isShared_3567_ = v_isSharedCheck_3571_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_a_3564_);
lean_dec(v___x_3488_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3571_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v___x_3569_; 
if (v_isShared_3567_ == 0)
{
v___x_3569_ = v___x_3566_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v_a_3564_);
v___x_3569_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
return v___x_3569_;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1(lean_object* v___x_3576_, lean_object* v_body_3577_, lean_object* v_k_3578_, lean_object* v___x_3579_, uint8_t v___x_3580_, uint8_t v___x_3581_, lean_object* v_FNew_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_){
_start:
{
lean_object* v___x_3590_; 
lean_inc_ref(v_FNew_3582_);
lean_inc_ref(v___x_3576_);
v___x_3590_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v___x_3576_, v_FNew_3582_, v_body_3577_, v_k_3578_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_);
if (lean_obj_tag(v___x_3590_) == 0)
{
lean_object* v_a_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; uint8_t v___x_3595_; lean_object* v___x_3596_; 
v_a_3591_ = lean_ctor_get(v___x_3590_, 0);
lean_inc(v_a_3591_);
lean_dec_ref_known(v___x_3590_, 1);
v___x_3592_ = lean_mk_empty_array_with_capacity(v___x_3579_);
v___x_3593_ = lean_array_push(v___x_3592_, v___x_3576_);
v___x_3594_ = lean_array_push(v___x_3593_, v_FNew_3582_);
v___x_3595_ = 1;
v___x_3596_ = l_Lean_Meta_mkLambdaFVars(v___x_3594_, v_a_3591_, v___x_3580_, v___x_3581_, v___x_3580_, v___x_3581_, v___x_3595_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_);
lean_dec_ref(v___x_3594_);
return v___x_3596_;
}
else
{
lean_dec_ref(v_FNew_3582_);
lean_dec_ref(v___x_3576_);
return v___x_3590_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1___boxed(lean_object* v___x_3597_, lean_object* v_body_3598_, lean_object* v_k_3599_, lean_object* v___x_3600_, lean_object* v___x_3601_, lean_object* v___x_3602_, lean_object* v_FNew_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_){
_start:
{
uint8_t v___x_6491__boxed_3611_; uint8_t v___x_6492__boxed_3612_; lean_object* v_res_3613_; 
v___x_6491__boxed_3611_ = lean_unbox(v___x_3601_);
v___x_6492__boxed_3612_ = lean_unbox(v___x_3602_);
v_res_3613_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1(v___x_3597_, v_body_3598_, v_k_3599_, v___x_3600_, v___x_6491__boxed_3611_, v___x_6492__boxed_3612_, v_FNew_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_);
lean_dec(v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec(v___y_3607_);
lean_dec_ref(v___y_3606_);
lean_dec(v___y_3605_);
lean_dec_ref(v___y_3604_);
lean_dec(v___x_3600_);
return v_res_3613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2(lean_object* v___x_3614_, lean_object* v___x_3615_, lean_object* v_k_3616_, lean_object* v___x_3617_, uint8_t v___x_3618_, uint8_t v___x_3619_, lean_object* v_00_u03b1_3620_, lean_object* v_00_u03b2_3621_, lean_object* v___x_3622_, lean_object* v_ctorName_3623_, lean_object* v_a_3624_, lean_object* v_x_3625_, lean_object* v_xs_3626_, lean_object* v_body_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_){
_start:
{
lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___f_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3635_ = lean_array_get_borrowed(v___x_3614_, v_xs_3626_, v___x_3615_);
v___x_3636_ = lean_box(v___x_3618_);
v___x_3637_ = lean_box(v___x_3619_);
lean_inc_n(v___x_3635_, 2);
v___f_3638_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1___boxed), 14, 6);
lean_closure_set(v___f_3638_, 0, v___x_3635_);
lean_closure_set(v___f_3638_, 1, v_body_3627_);
lean_closure_set(v___f_3638_, 2, v_k_3616_);
lean_closure_set(v___f_3638_, 3, v___x_3617_);
lean_closure_set(v___f_3638_, 4, v___x_3636_);
lean_closure_set(v___f_3638_, 5, v___x_3637_);
v___x_3639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3639_, 0, v_00_u03b1_3620_);
v___x_3640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3640_, 0, v_00_u03b2_3621_);
v___x_3641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3641_, 0, v___x_3635_);
v___x_3642_ = lean_mk_empty_array_with_capacity(v___x_3622_);
v___x_3643_ = lean_array_push(v___x_3642_, v___x_3639_);
v___x_3644_ = lean_array_push(v___x_3643_, v___x_3640_);
v___x_3645_ = lean_array_push(v___x_3644_, v___x_3641_);
v___x_3646_ = l_Lean_Meta_mkAppOptM(v_ctorName_3623_, v___x_3645_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_);
if (lean_obj_tag(v___x_3646_) == 0)
{
lean_object* v_a_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; 
v_a_3647_ = lean_ctor_get(v___x_3646_, 0);
lean_inc(v_a_3647_);
lean_dec_ref_known(v___x_3646_, 1);
v___x_3648_ = l_Lean_LocalDecl_type(v_a_3624_);
v___x_3649_ = l_Lean_Expr_replaceFVar(v___x_3648_, v_x_3625_, v_a_3647_);
lean_dec(v_a_3647_);
lean_dec_ref(v___x_3648_);
v___x_3650_ = l_Lean_LocalDecl_userName(v_a_3624_);
v___x_3651_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_3650_, v___x_3649_, v___f_3638_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_);
return v___x_3651_;
}
else
{
lean_dec_ref(v___f_3638_);
lean_dec_ref(v_x_3625_);
return v___x_3646_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2___boxed(lean_object** _args){
lean_object* v___x_3652_ = _args[0];
lean_object* v___x_3653_ = _args[1];
lean_object* v_k_3654_ = _args[2];
lean_object* v___x_3655_ = _args[3];
lean_object* v___x_3656_ = _args[4];
lean_object* v___x_3657_ = _args[5];
lean_object* v_00_u03b1_3658_ = _args[6];
lean_object* v_00_u03b2_3659_ = _args[7];
lean_object* v___x_3660_ = _args[8];
lean_object* v_ctorName_3661_ = _args[9];
lean_object* v_a_3662_ = _args[10];
lean_object* v_x_3663_ = _args[11];
lean_object* v_xs_3664_ = _args[12];
lean_object* v_body_3665_ = _args[13];
lean_object* v___y_3666_ = _args[14];
lean_object* v___y_3667_ = _args[15];
lean_object* v___y_3668_ = _args[16];
lean_object* v___y_3669_ = _args[17];
lean_object* v___y_3670_ = _args[18];
lean_object* v___y_3671_ = _args[19];
lean_object* v___y_3672_ = _args[20];
_start:
{
uint8_t v___x_6511__boxed_3673_; uint8_t v___x_6512__boxed_3674_; lean_object* v_res_3675_; 
v___x_6511__boxed_3673_ = lean_unbox(v___x_3656_);
v___x_6512__boxed_3674_ = lean_unbox(v___x_3657_);
v_res_3675_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2(v___x_3652_, v___x_3653_, v_k_3654_, v___x_3655_, v___x_6511__boxed_3673_, v___x_6512__boxed_3674_, v_00_u03b1_3658_, v_00_u03b2_3659_, v___x_3660_, v_ctorName_3661_, v_a_3662_, v_x_3663_, v_xs_3664_, v_body_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_);
lean_dec(v___y_3671_);
lean_dec_ref(v___y_3670_);
lean_dec(v___y_3669_);
lean_dec_ref(v___y_3668_);
lean_dec(v___y_3667_);
lean_dec_ref(v___y_3666_);
lean_dec_ref(v_xs_3664_);
lean_dec_ref(v_a_3662_);
lean_dec(v___x_3660_);
lean_dec(v___x_3653_);
lean_dec_ref(v___x_3652_);
return v_res_3675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(lean_object* v___x_3676_, lean_object* v___x_3677_, lean_object* v_k_3678_, lean_object* v___x_3679_, uint8_t v___x_3680_, uint8_t v___x_3681_, lean_object* v_00_u03b1_3682_, lean_object* v_00_u03b2_3683_, lean_object* v___x_3684_, lean_object* v_a_3685_, lean_object* v_x_3686_, lean_object* v___x_3687_, lean_object* v_ctorName_3688_, lean_object* v_minor_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_){
_start:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___f_3699_; lean_object* v___x_3700_; 
v___x_3697_ = lean_box(v___x_3680_);
v___x_3698_ = lean_box(v___x_3681_);
v___f_3699_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2___boxed), 21, 12);
lean_closure_set(v___f_3699_, 0, v___x_3676_);
lean_closure_set(v___f_3699_, 1, v___x_3677_);
lean_closure_set(v___f_3699_, 2, v_k_3678_);
lean_closure_set(v___f_3699_, 3, v___x_3679_);
lean_closure_set(v___f_3699_, 4, v___x_3697_);
lean_closure_set(v___f_3699_, 5, v___x_3698_);
lean_closure_set(v___f_3699_, 6, v_00_u03b1_3682_);
lean_closure_set(v___f_3699_, 7, v_00_u03b2_3683_);
lean_closure_set(v___f_3699_, 8, v___x_3684_);
lean_closure_set(v___f_3699_, 9, v_ctorName_3688_);
lean_closure_set(v___f_3699_, 10, v_a_3685_);
lean_closure_set(v___f_3699_, 11, v_x_3686_);
v___x_3700_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_minor_3689_, v___x_3687_, v___f_3699_, v___x_3680_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_);
return v___x_3700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3___boxed(lean_object** _args){
lean_object* v___x_3701_ = _args[0];
lean_object* v___x_3702_ = _args[1];
lean_object* v_k_3703_ = _args[2];
lean_object* v___x_3704_ = _args[3];
lean_object* v___x_3705_ = _args[4];
lean_object* v___x_3706_ = _args[5];
lean_object* v_00_u03b1_3707_ = _args[6];
lean_object* v_00_u03b2_3708_ = _args[7];
lean_object* v___x_3709_ = _args[8];
lean_object* v_a_3710_ = _args[9];
lean_object* v_x_3711_ = _args[10];
lean_object* v___x_3712_ = _args[11];
lean_object* v_ctorName_3713_ = _args[12];
lean_object* v_minor_3714_ = _args[13];
lean_object* v___y_3715_ = _args[14];
lean_object* v___y_3716_ = _args[15];
lean_object* v___y_3717_ = _args[16];
lean_object* v___y_3718_ = _args[17];
lean_object* v___y_3719_ = _args[18];
lean_object* v___y_3720_ = _args[19];
lean_object* v___y_3721_ = _args[20];
_start:
{
uint8_t v___x_6475__boxed_3722_; uint8_t v___x_6476__boxed_3723_; lean_object* v_res_3724_; 
v___x_6475__boxed_3722_ = lean_unbox(v___x_3705_);
v___x_6476__boxed_3723_ = lean_unbox(v___x_3706_);
v_res_3724_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3701_, v___x_3702_, v_k_3703_, v___x_3704_, v___x_6475__boxed_3722_, v___x_6476__boxed_3723_, v_00_u03b1_3707_, v_00_u03b2_3708_, v___x_3709_, v_a_3710_, v_x_3711_, v___x_3712_, v_ctorName_3713_, v_minor_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_);
lean_dec(v___y_3720_);
lean_dec_ref(v___y_3719_);
lean_dec(v___y_3718_);
lean_dec_ref(v___y_3717_);
lean_dec(v___y_3716_);
lean_dec_ref(v___y_3715_);
return v_res_3724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___boxed(lean_object* v_x_3725_, lean_object* v_F_3726_, lean_object* v_val_3727_, lean_object* v_k_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_, lean_object* v_a_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_){
_start:
{
lean_object* v_res_3736_; 
v_res_3736_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v_x_3725_, v_F_3726_, v_val_3727_, v_k_3728_, v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_, v_a_3733_, v_a_3734_);
lean_dec(v_a_3734_);
lean_dec_ref(v_a_3733_);
lean_dec(v_a_3732_);
lean_dec_ref(v_a_3731_);
lean_dec(v_a_3730_);
lean_dec_ref(v_a_3729_);
return v_res_3736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0(lean_object* v_00_u03b1_3737_, lean_object* v_name_3738_, uint8_t v_bi_3739_, lean_object* v_type_3740_, lean_object* v_k_3741_, uint8_t v_kind_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_){
_start:
{
lean_object* v___x_3750_; 
v___x_3750_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___redArg(v_name_3738_, v_bi_3739_, v_type_3740_, v_k_3741_, v_kind_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_);
return v___x_3750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3751_, lean_object* v_name_3752_, lean_object* v_bi_3753_, lean_object* v_type_3754_, lean_object* v_k_3755_, lean_object* v_kind_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_){
_start:
{
uint8_t v_bi_boxed_3764_; uint8_t v_kind_boxed_3765_; lean_object* v_res_3766_; 
v_bi_boxed_3764_ = lean_unbox(v_bi_3753_);
v_kind_boxed_3765_ = lean_unbox(v_kind_3756_);
v_res_3766_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0_spec__0(v_00_u03b1_3751_, v_name_3752_, v_bi_boxed_3764_, v_type_3754_, v_k_3755_, v_kind_boxed_3765_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_);
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
return v_res_3766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0(lean_object* v_00_u03b1_3767_, lean_object* v_name_3768_, lean_object* v_type_3769_, lean_object* v_k_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_){
_start:
{
lean_object* v___x_3778_; 
v___x_3778_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v_name_3768_, v_type_3769_, v_k_3770_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_);
return v___x_3778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___boxed(lean_object* v_00_u03b1_3779_, lean_object* v_name_3780_, lean_object* v_type_3781_, lean_object* v_k_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_){
_start:
{
lean_object* v_res_3790_; 
v_res_3790_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0(v_00_u03b1_3779_, v_name_3780_, v_type_3781_, v_k_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_);
lean_dec(v___y_3788_);
lean_dec_ref(v___y_3787_);
lean_dec(v___y_3786_);
lean_dec_ref(v___y_3785_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3783_);
return v_res_3790_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3791_; 
v___x_3791_ = l_Lean_Elab_Term_instInhabitedTermElabM___redArg();
return v___x_3791_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(lean_object* v_msg_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_){
_start:
{
lean_object* v___x_3800_; lean_object* v___x_3331__overap_3801_; lean_object* v___x_3802_; 
v___x_3800_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0, &l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0);
v___x_3331__overap_3801_ = lean_panic_fn_borrowed(v___x_3800_, v_msg_3792_);
lean_inc(v___y_3798_);
lean_inc_ref(v___y_3797_);
lean_inc(v___y_3796_);
lean_inc_ref(v___y_3795_);
lean_inc(v___y_3794_);
lean_inc_ref(v___y_3793_);
v___x_3802_ = lean_apply_7(v___x_3331__overap_3801_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, lean_box(0));
return v___x_3802_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___boxed(lean_object* v_msg_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_){
_start:
{
lean_object* v_res_3811_; 
v_res_3811_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(v_msg_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_);
lean_dec(v___y_3809_);
lean_dec_ref(v___y_3808_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
return v_res_3811_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3(void){
_start:
{
lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; 
v___x_3815_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__2));
v___x_3816_ = lean_unsigned_to_nat(49u);
v___x_3817_ = lean_unsigned_to_nat(186u);
v___x_3818_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__1));
v___x_3819_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__0));
v___x_3820_ = l_mkPanicMessageWithDecl(v___x_3819_, v___x_3818_, v___x_3817_, v___x_3816_, v___x_3815_);
return v___x_3820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1___boxed(lean_object* v___x_3821_, lean_object* v_a_3822_, lean_object* v_k_3823_, lean_object* v___x_3824_, lean_object* v___x_3825_, lean_object* v___x_3826_, lean_object* v___x_3827_, lean_object* v___x_3828_, lean_object* v_FNew_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_){
_start:
{
uint8_t v___x_3506__boxed_3837_; uint8_t v___x_3507__boxed_3838_; uint8_t v___x_3508__boxed_3839_; lean_object* v_res_3840_; 
v___x_3506__boxed_3837_ = lean_unbox(v___x_3826_);
v___x_3507__boxed_3838_ = lean_unbox(v___x_3827_);
v___x_3508__boxed_3839_ = lean_unbox(v___x_3828_);
v_res_3840_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1(v___x_3821_, v_a_3822_, v_k_3823_, v___x_3824_, v___x_3825_, v___x_3506__boxed_3837_, v___x_3507__boxed_3838_, v___x_3508__boxed_3839_, v_FNew_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
lean_dec(v___x_3824_);
return v_res_3840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0(lean_object* v___x_3846_, lean_object* v___x_3847_, lean_object* v___x_3848_, lean_object* v___x_3849_, uint8_t v___x_3850_, uint8_t v___x_3851_, lean_object* v_k_3852_, lean_object* v___x_3853_, lean_object* v_00_u03b1_3854_, lean_object* v_00_u03b2_3855_, lean_object* v___x_3856_, lean_object* v_a_3857_, lean_object* v_x_3858_, lean_object* v_xs_3859_, lean_object* v_body_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_){
_start:
{
lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; uint8_t v___x_3873_; lean_object* v___x_3874_; 
v___x_3868_ = lean_array_get(v___x_3846_, v_xs_3859_, v___x_3847_);
v___x_3869_ = lean_array_get(v___x_3846_, v_xs_3859_, v___x_3848_);
v___x_3870_ = lean_array_get_size(v_xs_3859_);
v___x_3871_ = l_Array_toSubarray___redArg(v_xs_3859_, v___x_3849_, v___x_3870_);
v___x_3872_ = l_Subarray_copy___redArg(v___x_3871_);
v___x_3873_ = 1;
v___x_3874_ = l_Lean_Meta_mkLambdaFVars(v___x_3872_, v_body_3860_, v___x_3850_, v___x_3851_, v___x_3850_, v___x_3851_, v___x_3873_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_);
lean_dec_ref(v___x_3872_);
if (lean_obj_tag(v___x_3874_) == 0)
{
lean_object* v_a_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3901_; 
v_a_3875_ = lean_ctor_get(v___x_3874_, 0);
v_isSharedCheck_3901_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3901_ == 0)
{
v___x_3877_ = v___x_3874_;
v_isShared_3878_ = v_isSharedCheck_3901_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_a_3875_);
lean_dec(v___x_3874_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3901_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___f_3882_; lean_object* v___x_3883_; lean_object* v___x_3885_; 
v___x_3879_ = lean_box(v___x_3850_);
v___x_3880_ = lean_box(v___x_3851_);
v___x_3881_ = lean_box(v___x_3873_);
lean_inc(v___x_3868_);
lean_inc(v___x_3869_);
v___f_3882_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1___boxed), 16, 8);
lean_closure_set(v___f_3882_, 0, v___x_3869_);
lean_closure_set(v___f_3882_, 1, v_a_3875_);
lean_closure_set(v___f_3882_, 2, v_k_3852_);
lean_closure_set(v___f_3882_, 3, v___x_3853_);
lean_closure_set(v___f_3882_, 4, v___x_3868_);
lean_closure_set(v___f_3882_, 5, v___x_3879_);
lean_closure_set(v___f_3882_, 6, v___x_3880_);
lean_closure_set(v___f_3882_, 7, v___x_3881_);
v___x_3883_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__2));
if (v_isShared_3878_ == 0)
{
lean_ctor_set_tag(v___x_3877_, 1);
lean_ctor_set(v___x_3877_, 0, v_00_u03b1_3854_);
v___x_3885_ = v___x_3877_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v_00_u03b1_3854_);
v___x_3885_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; 
v___x_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3886_, 0, v_00_u03b2_3855_);
v___x_3887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3887_, 0, v___x_3868_);
v___x_3888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3888_, 0, v___x_3869_);
v___x_3889_ = lean_mk_empty_array_with_capacity(v___x_3856_);
v___x_3890_ = lean_array_push(v___x_3889_, v___x_3885_);
v___x_3891_ = lean_array_push(v___x_3890_, v___x_3886_);
v___x_3892_ = lean_array_push(v___x_3891_, v___x_3887_);
v___x_3893_ = lean_array_push(v___x_3892_, v___x_3888_);
v___x_3894_ = l_Lean_Meta_mkAppOptM(v___x_3883_, v___x_3893_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_);
if (lean_obj_tag(v___x_3894_) == 0)
{
lean_object* v_a_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; 
v_a_3895_ = lean_ctor_get(v___x_3894_, 0);
lean_inc(v_a_3895_);
lean_dec_ref_known(v___x_3894_, 1);
v___x_3896_ = l_Lean_LocalDecl_type(v_a_3857_);
v___x_3897_ = l_Lean_Expr_replaceFVar(v___x_3896_, v_x_3858_, v_a_3895_);
lean_dec(v_a_3895_);
lean_dec_ref(v___x_3896_);
v___x_3898_ = l_Lean_LocalDecl_userName(v_a_3857_);
v___x_3899_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_3898_, v___x_3897_, v___f_3882_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_);
return v___x_3899_;
}
else
{
lean_dec_ref(v___f_3882_);
lean_dec_ref(v_x_3858_);
return v___x_3894_;
}
}
}
}
else
{
lean_dec(v___x_3869_);
lean_dec(v___x_3868_);
lean_dec_ref(v_x_3858_);
lean_dec_ref(v_00_u03b2_3855_);
lean_dec_ref(v_00_u03b1_3854_);
lean_dec(v___x_3853_);
lean_dec_ref(v_k_3852_);
return v___x_3874_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___boxed(lean_object** _args){
lean_object* v___x_3902_ = _args[0];
lean_object* v___x_3903_ = _args[1];
lean_object* v___x_3904_ = _args[2];
lean_object* v___x_3905_ = _args[3];
lean_object* v___x_3906_ = _args[4];
lean_object* v___x_3907_ = _args[5];
lean_object* v_k_3908_ = _args[6];
lean_object* v___x_3909_ = _args[7];
lean_object* v_00_u03b1_3910_ = _args[8];
lean_object* v_00_u03b2_3911_ = _args[9];
lean_object* v___x_3912_ = _args[10];
lean_object* v_a_3913_ = _args[11];
lean_object* v_x_3914_ = _args[12];
lean_object* v_xs_3915_ = _args[13];
lean_object* v_body_3916_ = _args[14];
lean_object* v___y_3917_ = _args[15];
lean_object* v___y_3918_ = _args[16];
lean_object* v___y_3919_ = _args[17];
lean_object* v___y_3920_ = _args[18];
lean_object* v___y_3921_ = _args[19];
lean_object* v___y_3922_ = _args[20];
lean_object* v___y_3923_ = _args[21];
_start:
{
uint8_t v___x_3533__boxed_3924_; uint8_t v___x_3534__boxed_3925_; lean_object* v_res_3926_; 
v___x_3533__boxed_3924_ = lean_unbox(v___x_3906_);
v___x_3534__boxed_3925_ = lean_unbox(v___x_3907_);
v_res_3926_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0(v___x_3902_, v___x_3903_, v___x_3904_, v___x_3905_, v___x_3533__boxed_3924_, v___x_3534__boxed_3925_, v_k_3908_, v___x_3909_, v_00_u03b1_3910_, v_00_u03b2_3911_, v___x_3912_, v_a_3913_, v_x_3914_, v_xs_3915_, v_body_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_);
lean_dec(v___y_3922_);
lean_dec_ref(v___y_3921_);
lean_dec(v___y_3920_);
lean_dec_ref(v___y_3919_);
lean_dec(v___y_3918_);
lean_dec_ref(v___y_3917_);
lean_dec_ref(v_a_3913_);
lean_dec(v___x_3912_);
lean_dec(v___x_3904_);
lean_dec(v___x_3903_);
lean_dec_ref(v___x_3902_);
return v_res_3926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(lean_object* v_x_3930_, lean_object* v_F_3931_, lean_object* v_val_3932_, lean_object* v_k_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_){
_start:
{
lean_object* v___y_3942_; lean_object* v___y_3943_; lean_object* v___y_3944_; lean_object* v___y_3945_; lean_object* v___y_3946_; lean_object* v___y_3947_; lean_object* v___x_3950_; uint8_t v___y_3952_; uint8_t v___x_4043_; 
v___x_3950_ = l_Lean_instInhabitedExpr;
v___x_4043_ = l_Lean_Expr_isFVar(v_x_3930_);
if (v___x_4043_ == 0)
{
v___y_3952_ = v___x_4043_;
goto v___jp_3951_;
}
else
{
lean_object* v___x_4044_; lean_object* v___x_4045_; uint8_t v___x_4046_; 
v___x_4044_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4));
v___x_4045_ = lean_unsigned_to_nat(5u);
v___x_4046_ = l_Lean_Expr_isAppOfArity(v_val_3932_, v___x_4044_, v___x_4045_);
v___y_3952_ = v___x_4046_;
goto v___jp_3951_;
}
v___jp_3941_:
{
lean_object* v___x_3948_; lean_object* v___x_3949_; 
v___x_3948_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3);
v___x_3949_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(v___x_3948_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_);
return v___x_3949_;
}
v___jp_3951_:
{
if (v___y_3952_ == 0)
{
lean_object* v___x_3953_; 
lean_dec_ref(v_x_3930_);
lean_inc(v_a_3939_);
lean_inc_ref(v_a_3938_);
lean_inc(v_a_3937_);
lean_inc_ref(v_a_3936_);
lean_inc(v_a_3935_);
lean_inc_ref(v_a_3934_);
v___x_3953_ = lean_apply_9(v_k_3933_, v_F_3931_, v_val_3932_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_, lean_box(0));
return v___x_3953_;
}
else
{
lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; uint8_t v___x_3960_; 
v___x_3954_ = lean_unsigned_to_nat(3u);
v___x_3955_ = l_Lean_Expr_getAppNumArgs(v_val_3932_);
v___x_3956_ = lean_nat_sub(v___x_3955_, v___x_3954_);
v___x_3957_ = lean_unsigned_to_nat(1u);
v___x_3958_ = lean_nat_sub(v___x_3956_, v___x_3957_);
lean_dec(v___x_3956_);
v___x_3959_ = l_Lean_Expr_getRevArg_x21(v_val_3932_, v___x_3958_);
v___x_3960_ = lean_expr_eqv(v___x_3959_, v_x_3930_);
lean_dec_ref(v___x_3959_);
if (v___x_3960_ == 0)
{
lean_object* v___x_3961_; 
lean_dec(v___x_3955_);
lean_dec_ref(v_x_3930_);
lean_inc(v_a_3939_);
lean_inc_ref(v_a_3938_);
lean_inc(v_a_3937_);
lean_inc_ref(v_a_3936_);
lean_inc(v_a_3935_);
lean_inc_ref(v_a_3934_);
v___x_3961_ = lean_apply_9(v_k_3933_, v_F_3931_, v_val_3932_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_, lean_box(0));
return v___x_3961_;
}
else
{
lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; uint8_t v___x_3966_; 
v___x_3962_ = lean_unsigned_to_nat(4u);
v___x_3963_ = lean_nat_sub(v___x_3955_, v___x_3962_);
v___x_3964_ = lean_nat_sub(v___x_3963_, v___x_3957_);
lean_dec(v___x_3963_);
v___x_3965_ = l_Lean_Expr_getRevArg_x21(v_val_3932_, v___x_3964_);
v___x_3966_ = l_Lean_Expr_isLambda(v___x_3965_);
if (v___x_3966_ == 0)
{
lean_object* v___x_3967_; 
lean_dec_ref(v___x_3965_);
lean_dec(v___x_3955_);
lean_dec_ref(v_x_3930_);
lean_inc(v_a_3939_);
lean_inc_ref(v_a_3938_);
lean_inc(v_a_3937_);
lean_inc_ref(v_a_3936_);
lean_inc(v_a_3935_);
lean_inc_ref(v_a_3934_);
v___x_3967_ = lean_apply_9(v_k_3933_, v_F_3931_, v_val_3932_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_, lean_box(0));
return v___x_3967_;
}
else
{
lean_object* v___x_3968_; uint8_t v___x_3969_; 
v___x_3968_ = l_Lean_Expr_bindingBody_x21(v___x_3965_);
lean_dec_ref(v___x_3965_);
v___x_3969_ = l_Lean_Expr_isLambda(v___x_3968_);
lean_dec_ref(v___x_3968_);
if (v___x_3969_ == 0)
{
lean_object* v___x_3970_; 
lean_dec(v___x_3955_);
lean_dec_ref(v_x_3930_);
lean_inc(v_a_3939_);
lean_inc_ref(v_a_3938_);
lean_inc(v_a_3937_);
lean_inc_ref(v_a_3936_);
lean_inc(v_a_3935_);
lean_inc_ref(v_a_3934_);
v___x_3970_ = lean_apply_9(v_k_3933_, v_F_3931_, v_val_3932_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_, lean_box(0));
return v___x_3970_;
}
else
{
lean_object* v___x_3971_; lean_object* v___x_3972_; 
v___x_3971_ = l_Lean_Expr_getAppFn(v_val_3932_);
v___x_3972_ = l_Lean_Expr_constLevels_x21(v___x_3971_);
lean_dec_ref(v___x_3971_);
if (lean_obj_tag(v___x_3972_) == 1)
{
lean_object* v_tail_3973_; 
v_tail_3973_ = lean_ctor_get(v___x_3972_, 1);
lean_inc(v_tail_3973_);
lean_dec_ref_known(v___x_3972_, 2);
if (lean_obj_tag(v_tail_3973_) == 1)
{
lean_object* v_tail_3974_; 
v_tail_3974_ = lean_ctor_get(v_tail_3973_, 1);
lean_inc(v_tail_3974_);
if (lean_obj_tag(v_tail_3974_) == 1)
{
lean_object* v_tail_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_4041_; 
v_tail_3975_ = lean_ctor_get(v_tail_3974_, 1);
v_isSharedCheck_4041_ = !lean_is_exclusive(v_tail_3974_);
if (v_isSharedCheck_4041_ == 0)
{
lean_object* v_unused_4042_; 
v_unused_4042_ = lean_ctor_get(v_tail_3974_, 0);
lean_dec(v_unused_4042_);
v___x_3977_ = v_tail_3974_;
v_isShared_3978_ = v_isSharedCheck_4041_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_tail_3975_);
lean_dec(v_tail_3974_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_4041_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
if (lean_obj_tag(v_tail_3975_) == 0)
{
lean_object* v_dummy_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v_args_3982_; lean_object* v___x_3983_; lean_object* v_00_u03b1_3984_; lean_object* v_00_u03b2_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; 
v_dummy_3979_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_3955_);
v___x_3980_ = lean_mk_array(v___x_3955_, v_dummy_3979_);
v___x_3981_ = lean_nat_sub(v___x_3955_, v___x_3957_);
lean_dec(v___x_3955_);
v_args_3982_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_3932_, v___x_3980_, v___x_3981_);
v___x_3983_ = lean_unsigned_to_nat(0u);
v_00_u03b1_3984_ = lean_array_get(v___x_3950_, v_args_3982_, v___x_3983_);
v_00_u03b2_3985_ = lean_array_get(v___x_3950_, v_args_3982_, v___x_3957_);
v___x_3986_ = l_Lean_Expr_fvarId_x21(v_F_3931_);
v___x_3987_ = l_Lean_FVarId_getDecl___redArg(v___x_3986_, v_a_3936_, v_a_3938_, v_a_3939_);
if (lean_obj_tag(v___x_3987_) == 0)
{
lean_object* v_a_3988_; lean_object* v___x_3989_; lean_object* v___f_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; uint8_t v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___f_3996_; lean_object* v___x_3997_; 
v_a_3988_ = lean_ctor_get(v___x_3987_, 0);
lean_inc_n(v_a_3988_, 2);
lean_dec_ref_known(v___x_3987_, 1);
v___x_3989_ = lean_box(v___x_3966_);
lean_inc_ref_n(v_x_3930_, 2);
v___f_3990_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed), 14, 5);
lean_closure_set(v___f_3990_, 0, v_a_3988_);
lean_closure_set(v___f_3990_, 1, v___x_3950_);
lean_closure_set(v___f_3990_, 2, v___x_3983_);
lean_closure_set(v___f_3990_, 3, v_x_3930_);
lean_closure_set(v___f_3990_, 4, v___x_3989_);
v___x_3991_ = lean_unsigned_to_nat(2u);
v___x_3992_ = lean_array_get(v___x_3950_, v_args_3982_, v___x_3991_);
v___x_3993_ = 0;
v___x_3994_ = lean_box(v___x_3993_);
v___x_3995_ = lean_box(v___x_3966_);
lean_inc(v_00_u03b2_3985_);
lean_inc(v_00_u03b1_3984_);
v___f_3996_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___boxed), 22, 13);
lean_closure_set(v___f_3996_, 0, v___x_3950_);
lean_closure_set(v___f_3996_, 1, v___x_3983_);
lean_closure_set(v___f_3996_, 2, v___x_3957_);
lean_closure_set(v___f_3996_, 3, v___x_3991_);
lean_closure_set(v___f_3996_, 4, v___x_3994_);
lean_closure_set(v___f_3996_, 5, v___x_3995_);
lean_closure_set(v___f_3996_, 6, v_k_3933_);
lean_closure_set(v___f_3996_, 7, v___x_3954_);
lean_closure_set(v___f_3996_, 8, v_00_u03b1_3984_);
lean_closure_set(v___f_3996_, 9, v_00_u03b2_3985_);
lean_closure_set(v___f_3996_, 10, v___x_3962_);
lean_closure_set(v___f_3996_, 11, v_a_3988_);
lean_closure_set(v___f_3996_, 12, v_x_3930_);
v___x_3997_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v___x_3992_, v___f_3990_, v___x_3993_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_);
if (lean_obj_tag(v___x_3997_) == 0)
{
lean_object* v_a_3998_; lean_object* v_fst_3999_; lean_object* v_snd_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; 
v_a_3998_ = lean_ctor_get(v___x_3997_, 0);
lean_inc(v_a_3998_);
lean_dec_ref_known(v___x_3997_, 1);
v_fst_3999_ = lean_ctor_get(v_a_3998_, 0);
lean_inc(v_fst_3999_);
v_snd_4000_ = lean_ctor_get(v_a_3998_, 1);
lean_inc(v_snd_4000_);
lean_dec(v_a_3998_);
v___x_4001_ = lean_array_get(v___x_3950_, v_args_3982_, v___x_3962_);
lean_dec_ref(v_args_3982_);
v___x_4002_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v___x_4001_, v___f_3996_, v___x_3993_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_);
if (lean_obj_tag(v___x_4002_) == 0)
{
lean_object* v_a_4003_; lean_object* v___x_4005_; uint8_t v_isShared_4006_; uint8_t v_isSharedCheck_4024_; 
v_a_4003_ = lean_ctor_get(v___x_4002_, 0);
v_isSharedCheck_4024_ = !lean_is_exclusive(v___x_4002_);
if (v_isSharedCheck_4024_ == 0)
{
v___x_4005_ = v___x_4002_;
v_isShared_4006_ = v_isSharedCheck_4024_;
goto v_resetjp_4004_;
}
else
{
lean_inc(v_a_4003_);
lean_dec(v___x_4002_);
v___x_4005_ = lean_box(0);
v_isShared_4006_ = v_isSharedCheck_4024_;
goto v_resetjp_4004_;
}
v_resetjp_4004_:
{
lean_object* v___x_4007_; lean_object* v___x_4009_; 
v___x_4007_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4));
if (v_isShared_3978_ == 0)
{
lean_ctor_set(v___x_3977_, 1, v_tail_3973_);
lean_ctor_set(v___x_3977_, 0, v_snd_4000_);
v___x_4009_ = v___x_3977_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v_snd_4000_);
lean_ctor_set(v_reuseFailAlloc_4023_, 1, v_tail_3973_);
v___x_4009_ = v_reuseFailAlloc_4023_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4021_; 
v___x_4010_ = l_Lean_mkConst(v___x_4007_, v___x_4009_);
v___x_4011_ = lean_unsigned_to_nat(6u);
v___x_4012_ = lean_mk_empty_array_with_capacity(v___x_4011_);
v___x_4013_ = lean_array_push(v___x_4012_, v_00_u03b1_3984_);
v___x_4014_ = lean_array_push(v___x_4013_, v_00_u03b2_3985_);
v___x_4015_ = lean_array_push(v___x_4014_, v_fst_3999_);
v___x_4016_ = lean_array_push(v___x_4015_, v_x_3930_);
v___x_4017_ = lean_array_push(v___x_4016_, v_a_4003_);
v___x_4018_ = lean_array_push(v___x_4017_, v_F_3931_);
v___x_4019_ = l_Lean_mkAppN(v___x_4010_, v___x_4018_);
lean_dec_ref(v___x_4018_);
if (v_isShared_4006_ == 0)
{
lean_ctor_set(v___x_4005_, 0, v___x_4019_);
v___x_4021_ = v___x_4005_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v___x_4019_);
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
else
{
lean_dec(v_snd_4000_);
lean_dec(v_fst_3999_);
lean_dec(v_00_u03b2_3985_);
lean_dec(v_00_u03b1_3984_);
lean_del_object(v___x_3977_);
lean_dec_ref_known(v_tail_3973_, 2);
lean_dec_ref(v_F_3931_);
lean_dec_ref(v_x_3930_);
return v___x_4002_;
}
}
else
{
lean_object* v_a_4025_; lean_object* v___x_4027_; uint8_t v_isShared_4028_; uint8_t v_isSharedCheck_4032_; 
lean_dec_ref(v___f_3996_);
lean_dec(v_00_u03b2_3985_);
lean_dec(v_00_u03b1_3984_);
lean_dec_ref(v_args_3982_);
lean_del_object(v___x_3977_);
lean_dec_ref_known(v_tail_3973_, 2);
lean_dec_ref(v_F_3931_);
lean_dec_ref(v_x_3930_);
v_a_4025_ = lean_ctor_get(v___x_3997_, 0);
v_isSharedCheck_4032_ = !lean_is_exclusive(v___x_3997_);
if (v_isSharedCheck_4032_ == 0)
{
v___x_4027_ = v___x_3997_;
v_isShared_4028_ = v_isSharedCheck_4032_;
goto v_resetjp_4026_;
}
else
{
lean_inc(v_a_4025_);
lean_dec(v___x_3997_);
v___x_4027_ = lean_box(0);
v_isShared_4028_ = v_isSharedCheck_4032_;
goto v_resetjp_4026_;
}
v_resetjp_4026_:
{
lean_object* v___x_4030_; 
if (v_isShared_4028_ == 0)
{
v___x_4030_ = v___x_4027_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v_a_4025_);
v___x_4030_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
return v___x_4030_;
}
}
}
}
else
{
lean_object* v_a_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4040_; 
lean_dec(v_00_u03b2_3985_);
lean_dec(v_00_u03b1_3984_);
lean_dec_ref(v_args_3982_);
lean_del_object(v___x_3977_);
lean_dec_ref_known(v_tail_3973_, 2);
lean_dec_ref(v_k_3933_);
lean_dec_ref(v_F_3931_);
lean_dec_ref(v_x_3930_);
v_a_4033_ = lean_ctor_get(v___x_3987_, 0);
v_isSharedCheck_4040_ = !lean_is_exclusive(v___x_3987_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_4035_ = v___x_3987_;
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_a_4033_);
lean_dec(v___x_3987_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v___x_4038_; 
if (v_isShared_4036_ == 0)
{
v___x_4038_ = v___x_4035_;
goto v_reusejp_4037_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v_a_4033_);
v___x_4038_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4037_;
}
v_reusejp_4037_:
{
return v___x_4038_;
}
}
}
}
else
{
lean_del_object(v___x_3977_);
lean_dec(v_tail_3975_);
lean_dec_ref_known(v_tail_3973_, 2);
lean_dec(v___x_3955_);
lean_dec_ref(v_k_3933_);
lean_dec_ref(v_val_3932_);
lean_dec_ref(v_F_3931_);
lean_dec_ref(v_x_3930_);
v___y_3942_ = v_a_3934_;
v___y_3943_ = v_a_3935_;
v___y_3944_ = v_a_3936_;
v___y_3945_ = v_a_3937_;
v___y_3946_ = v_a_3938_;
v___y_3947_ = v_a_3939_;
goto v___jp_3941_;
}
}
}
else
{
lean_dec_ref_known(v_tail_3973_, 2);
lean_dec(v_tail_3974_);
lean_dec(v___x_3955_);
lean_dec_ref(v_k_3933_);
lean_dec_ref(v_val_3932_);
lean_dec_ref(v_F_3931_);
lean_dec_ref(v_x_3930_);
v___y_3942_ = v_a_3934_;
v___y_3943_ = v_a_3935_;
v___y_3944_ = v_a_3936_;
v___y_3945_ = v_a_3937_;
v___y_3946_ = v_a_3938_;
v___y_3947_ = v_a_3939_;
goto v___jp_3941_;
}
}
else
{
lean_dec(v_tail_3973_);
lean_dec(v___x_3955_);
lean_dec_ref(v_k_3933_);
lean_dec_ref(v_val_3932_);
lean_dec_ref(v_F_3931_);
lean_dec_ref(v_x_3930_);
v___y_3942_ = v_a_3934_;
v___y_3943_ = v_a_3935_;
v___y_3944_ = v_a_3936_;
v___y_3945_ = v_a_3937_;
v___y_3946_ = v_a_3938_;
v___y_3947_ = v_a_3939_;
goto v___jp_3941_;
}
}
else
{
lean_dec(v___x_3972_);
lean_dec(v___x_3955_);
lean_dec_ref(v_k_3933_);
lean_dec_ref(v_val_3932_);
lean_dec_ref(v_F_3931_);
lean_dec_ref(v_x_3930_);
v___y_3942_ = v_a_3934_;
v___y_3943_ = v_a_3935_;
v___y_3944_ = v_a_3936_;
v___y_3945_ = v_a_3937_;
v___y_3946_ = v_a_3938_;
v___y_3947_ = v_a_3939_;
goto v___jp_3941_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1(lean_object* v___x_4047_, lean_object* v_a_4048_, lean_object* v_k_4049_, lean_object* v___x_4050_, lean_object* v___x_4051_, uint8_t v___x_4052_, uint8_t v___x_4053_, uint8_t v___x_4054_, lean_object* v_FNew_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_){
_start:
{
lean_object* v___x_4063_; 
lean_inc_ref(v_FNew_4055_);
lean_inc_ref(v___x_4047_);
v___x_4063_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v___x_4047_, v_FNew_4055_, v_a_4048_, v_k_4049_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_);
if (lean_obj_tag(v___x_4063_) == 0)
{
lean_object* v_a_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; 
v_a_4064_ = lean_ctor_get(v___x_4063_, 0);
lean_inc(v_a_4064_);
lean_dec_ref_known(v___x_4063_, 1);
v___x_4065_ = lean_mk_empty_array_with_capacity(v___x_4050_);
v___x_4066_ = lean_array_push(v___x_4065_, v___x_4051_);
v___x_4067_ = lean_array_push(v___x_4066_, v___x_4047_);
v___x_4068_ = lean_array_push(v___x_4067_, v_FNew_4055_);
v___x_4069_ = l_Lean_Meta_mkLambdaFVars(v___x_4068_, v_a_4064_, v___x_4052_, v___x_4053_, v___x_4052_, v___x_4053_, v___x_4054_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_);
lean_dec_ref(v___x_4068_);
return v___x_4069_;
}
else
{
lean_dec_ref(v_FNew_4055_);
lean_dec_ref(v___x_4051_);
lean_dec_ref(v___x_4047_);
return v___x_4063_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___boxed(lean_object* v_x_4070_, lean_object* v_F_4071_, lean_object* v_val_4072_, lean_object* v_k_4073_, lean_object* v_a_4074_, lean_object* v_a_4075_, lean_object* v_a_4076_, lean_object* v_a_4077_, lean_object* v_a_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_){
_start:
{
lean_object* v_res_4081_; 
v_res_4081_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v_x_4070_, v_F_4071_, v_val_4072_, v_k_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_, v_a_4078_, v_a_4079_);
lean_dec(v_a_4079_);
lean_dec_ref(v_a_4078_);
lean_dec(v_a_4077_);
lean_dec_ref(v_a_4076_);
lean_dec(v_a_4075_);
lean_dec_ref(v_a_4074_);
return v_res_4081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0(lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_){
_start:
{
lean_object* v___x_4095_; 
v___x_4095_ = l_Lean_Elab_WF_applyCleanWfTactic(v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_);
if (lean_obj_tag(v___x_4095_) == 0)
{
lean_object* v_ref_4096_; uint8_t v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; 
lean_dec_ref_known(v___x_4095_, 1);
v_ref_4096_ = lean_ctor_get(v___y_4092_, 2);
v___x_4097_ = 0;
v___x_4098_ = l_Lean_SourceInfo_fromRef(v_ref_4096_, v___x_4097_);
v___x_4099_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__1));
v___x_4100_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__2));
lean_inc(v___x_4098_);
v___x_4101_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4101_, 0, v___x_4098_);
lean_ctor_set(v___x_4101_, 1, v___x_4100_);
v___x_4102_ = l_Lean_Syntax_node1(v___x_4098_, v___x_4099_, v___x_4101_);
v___x_4103_ = l_Lean_Elab_Tactic_evalTactic(v___x_4102_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_);
return v___x_4103_;
}
else
{
return v___x_4095_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___boxed(lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_){
_start:
{
lean_object* v_res_4113_; 
v_res_4113_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0(v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_);
lean_dec(v___y_4111_);
lean_dec_ref(v___y_4110_);
lean_dec(v___y_4109_);
lean_dec_ref(v___y_4108_);
lean_dec(v___y_4107_);
lean_dec_ref(v___y_4106_);
lean_dec(v___y_4105_);
lean_dec_ref(v___y_4104_);
return v_res_4113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(lean_object* v_mvarId_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_){
_start:
{
lean_object* v___f_4123_; lean_object* v___x_4124_; 
v___f_4123_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___closed__0));
v___x_4124_ = l_Lean_Elab_Tactic_run(v_mvarId_4115_, v___f_4123_, v_a_4116_, v_a_4117_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_);
if (lean_obj_tag(v___x_4124_) == 0)
{
lean_object* v_a_4125_; lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4135_; 
v_a_4125_ = lean_ctor_get(v___x_4124_, 0);
v_isSharedCheck_4135_ = !lean_is_exclusive(v___x_4124_);
if (v_isSharedCheck_4135_ == 0)
{
v___x_4127_ = v___x_4124_;
v_isShared_4128_ = v_isSharedCheck_4135_;
goto v_resetjp_4126_;
}
else
{
lean_inc(v_a_4125_);
lean_dec(v___x_4124_);
v___x_4127_ = lean_box(0);
v_isShared_4128_ = v_isSharedCheck_4135_;
goto v_resetjp_4126_;
}
v_resetjp_4126_:
{
uint8_t v___x_4129_; 
v___x_4129_ = l_List_isEmpty___redArg(v_a_4125_);
if (v___x_4129_ == 0)
{
lean_object* v___x_4130_; 
lean_del_object(v___x_4127_);
v___x_4130_ = l_Lean_Elab_Term_reportUnsolvedGoals(v_a_4125_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_);
return v___x_4130_;
}
else
{
lean_object* v___x_4131_; lean_object* v___x_4133_; 
lean_dec(v_a_4125_);
v___x_4131_ = lean_box(0);
if (v_isShared_4128_ == 0)
{
lean_ctor_set(v___x_4127_, 0, v___x_4131_);
v___x_4133_ = v___x_4127_;
goto v_reusejp_4132_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v___x_4131_);
v___x_4133_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4132_;
}
v_reusejp_4132_:
{
return v___x_4133_;
}
}
}
}
else
{
lean_object* v_a_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4143_; 
v_a_4136_ = lean_ctor_get(v___x_4124_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v___x_4124_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4138_ = v___x_4124_;
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_a_4136_);
lean_dec(v___x_4124_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v___x_4141_; 
if (v_isShared_4139_ == 0)
{
v___x_4141_ = v___x_4138_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v_a_4136_);
v___x_4141_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
return v___x_4141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___boxed(lean_object* v_mvarId_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_){
_start:
{
lean_object* v_res_4152_; 
v_res_4152_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(v_mvarId_4144_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_, v_a_4149_, v_a_4150_);
lean_dec(v_a_4150_);
lean_dec_ref(v_a_4149_);
lean_dec(v_a_4148_);
lean_dec_ref(v_a_4147_);
lean_dec(v_a_4146_);
lean_dec_ref(v_a_4145_);
return v_res_4152_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(lean_object* v_x_4153_, lean_object* v_x_4154_, lean_object* v_x_4155_, lean_object* v_x_4156_){
_start:
{
lean_object* v_ks_4157_; lean_object* v_vs_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4182_; 
v_ks_4157_ = lean_ctor_get(v_x_4153_, 0);
v_vs_4158_ = lean_ctor_get(v_x_4153_, 1);
v_isSharedCheck_4182_ = !lean_is_exclusive(v_x_4153_);
if (v_isSharedCheck_4182_ == 0)
{
v___x_4160_ = v_x_4153_;
v_isShared_4161_ = v_isSharedCheck_4182_;
goto v_resetjp_4159_;
}
else
{
lean_inc(v_vs_4158_);
lean_inc(v_ks_4157_);
lean_dec(v_x_4153_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4182_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
lean_object* v___x_4162_; uint8_t v___x_4163_; 
v___x_4162_ = lean_array_get_size(v_ks_4157_);
v___x_4163_ = lean_nat_dec_lt(v_x_4154_, v___x_4162_);
if (v___x_4163_ == 0)
{
lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4167_; 
lean_dec(v_x_4154_);
v___x_4164_ = lean_array_push(v_ks_4157_, v_x_4155_);
v___x_4165_ = lean_array_push(v_vs_4158_, v_x_4156_);
if (v_isShared_4161_ == 0)
{
lean_ctor_set(v___x_4160_, 1, v___x_4165_);
lean_ctor_set(v___x_4160_, 0, v___x_4164_);
v___x_4167_ = v___x_4160_;
goto v_reusejp_4166_;
}
else
{
lean_object* v_reuseFailAlloc_4168_; 
v_reuseFailAlloc_4168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4168_, 0, v___x_4164_);
lean_ctor_set(v_reuseFailAlloc_4168_, 1, v___x_4165_);
v___x_4167_ = v_reuseFailAlloc_4168_;
goto v_reusejp_4166_;
}
v_reusejp_4166_:
{
return v___x_4167_;
}
}
else
{
lean_object* v_k_x27_4169_; uint8_t v___x_4170_; 
v_k_x27_4169_ = lean_array_fget_borrowed(v_ks_4157_, v_x_4154_);
v___x_4170_ = l_Lean_instBEqMVarId_beq(v_x_4155_, v_k_x27_4169_);
if (v___x_4170_ == 0)
{
lean_object* v___x_4172_; 
if (v_isShared_4161_ == 0)
{
v___x_4172_ = v___x_4160_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v_ks_4157_);
lean_ctor_set(v_reuseFailAlloc_4176_, 1, v_vs_4158_);
v___x_4172_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
lean_object* v___x_4173_; lean_object* v___x_4174_; 
v___x_4173_ = lean_unsigned_to_nat(1u);
v___x_4174_ = lean_nat_add(v_x_4154_, v___x_4173_);
lean_dec(v_x_4154_);
v_x_4153_ = v___x_4172_;
v_x_4154_ = v___x_4174_;
goto _start;
}
}
else
{
lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4180_; 
v___x_4177_ = lean_array_fset(v_ks_4157_, v_x_4154_, v_x_4155_);
v___x_4178_ = lean_array_fset(v_vs_4158_, v_x_4154_, v_x_4156_);
lean_dec(v_x_4154_);
if (v_isShared_4161_ == 0)
{
lean_ctor_set(v___x_4160_, 1, v___x_4178_);
lean_ctor_set(v___x_4160_, 0, v___x_4177_);
v___x_4180_ = v___x_4160_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v___x_4177_);
lean_ctor_set(v_reuseFailAlloc_4181_, 1, v___x_4178_);
v___x_4180_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
return v___x_4180_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_4183_, lean_object* v_k_4184_, lean_object* v_v_4185_){
_start:
{
lean_object* v___x_4186_; lean_object* v___x_4187_; 
v___x_4186_ = lean_unsigned_to_nat(0u);
v___x_4187_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_n_4183_, v___x_4186_, v_k_4184_, v_v_4185_);
return v___x_4187_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4188_; 
v___x_4188_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_4188_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(lean_object* v_x_4189_, size_t v_x_4190_, size_t v_x_4191_, lean_object* v_x_4192_, lean_object* v_x_4193_){
_start:
{
if (lean_obj_tag(v_x_4189_) == 0)
{
lean_object* v_es_4194_; size_t v___x_4195_; size_t v___x_4196_; lean_object* v_j_4197_; lean_object* v___x_4198_; uint8_t v___x_4199_; 
v_es_4194_ = lean_ctor_get(v_x_4189_, 0);
v___x_4195_ = ((size_t)31ULL);
v___x_4196_ = lean_usize_land(v_x_4190_, v___x_4195_);
v_j_4197_ = lean_usize_to_nat(v___x_4196_);
v___x_4198_ = lean_array_get_size(v_es_4194_);
v___x_4199_ = lean_nat_dec_lt(v_j_4197_, v___x_4198_);
if (v___x_4199_ == 0)
{
lean_dec(v_j_4197_);
lean_dec(v_x_4193_);
lean_dec(v_x_4192_);
return v_x_4189_;
}
else
{
lean_object* v___x_4201_; uint8_t v_isShared_4202_; uint8_t v_isSharedCheck_4238_; 
lean_inc_ref(v_es_4194_);
v_isSharedCheck_4238_ = !lean_is_exclusive(v_x_4189_);
if (v_isSharedCheck_4238_ == 0)
{
lean_object* v_unused_4239_; 
v_unused_4239_ = lean_ctor_get(v_x_4189_, 0);
lean_dec(v_unused_4239_);
v___x_4201_ = v_x_4189_;
v_isShared_4202_ = v_isSharedCheck_4238_;
goto v_resetjp_4200_;
}
else
{
lean_dec(v_x_4189_);
v___x_4201_ = lean_box(0);
v_isShared_4202_ = v_isSharedCheck_4238_;
goto v_resetjp_4200_;
}
v_resetjp_4200_:
{
lean_object* v_v_4203_; lean_object* v___x_4204_; lean_object* v_xs_x27_4205_; lean_object* v___y_4207_; 
v_v_4203_ = lean_array_fget(v_es_4194_, v_j_4197_);
v___x_4204_ = lean_box(0);
v_xs_x27_4205_ = lean_array_fset(v_es_4194_, v_j_4197_, v___x_4204_);
switch(lean_obj_tag(v_v_4203_))
{
case 0:
{
lean_object* v_key_4212_; lean_object* v_val_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4223_; 
v_key_4212_ = lean_ctor_get(v_v_4203_, 0);
v_val_4213_ = lean_ctor_get(v_v_4203_, 1);
v_isSharedCheck_4223_ = !lean_is_exclusive(v_v_4203_);
if (v_isSharedCheck_4223_ == 0)
{
v___x_4215_ = v_v_4203_;
v_isShared_4216_ = v_isSharedCheck_4223_;
goto v_resetjp_4214_;
}
else
{
lean_inc(v_val_4213_);
lean_inc(v_key_4212_);
lean_dec(v_v_4203_);
v___x_4215_ = lean_box(0);
v_isShared_4216_ = v_isSharedCheck_4223_;
goto v_resetjp_4214_;
}
v_resetjp_4214_:
{
uint8_t v___x_4217_; 
v___x_4217_ = l_Lean_instBEqMVarId_beq(v_x_4192_, v_key_4212_);
if (v___x_4217_ == 0)
{
lean_object* v___x_4218_; lean_object* v___x_4219_; 
lean_del_object(v___x_4215_);
v___x_4218_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4212_, v_val_4213_, v_x_4192_, v_x_4193_);
v___x_4219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4219_, 0, v___x_4218_);
v___y_4207_ = v___x_4219_;
goto v___jp_4206_;
}
else
{
lean_object* v___x_4221_; 
lean_dec(v_val_4213_);
lean_dec(v_key_4212_);
if (v_isShared_4216_ == 0)
{
lean_ctor_set(v___x_4215_, 1, v_x_4193_);
lean_ctor_set(v___x_4215_, 0, v_x_4192_);
v___x_4221_ = v___x_4215_;
goto v_reusejp_4220_;
}
else
{
lean_object* v_reuseFailAlloc_4222_; 
v_reuseFailAlloc_4222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4222_, 0, v_x_4192_);
lean_ctor_set(v_reuseFailAlloc_4222_, 1, v_x_4193_);
v___x_4221_ = v_reuseFailAlloc_4222_;
goto v_reusejp_4220_;
}
v_reusejp_4220_:
{
v___y_4207_ = v___x_4221_;
goto v___jp_4206_;
}
}
}
}
case 1:
{
lean_object* v_node_4224_; lean_object* v___x_4226_; uint8_t v_isShared_4227_; uint8_t v_isSharedCheck_4236_; 
v_node_4224_ = lean_ctor_get(v_v_4203_, 0);
v_isSharedCheck_4236_ = !lean_is_exclusive(v_v_4203_);
if (v_isSharedCheck_4236_ == 0)
{
v___x_4226_ = v_v_4203_;
v_isShared_4227_ = v_isSharedCheck_4236_;
goto v_resetjp_4225_;
}
else
{
lean_inc(v_node_4224_);
lean_dec(v_v_4203_);
v___x_4226_ = lean_box(0);
v_isShared_4227_ = v_isSharedCheck_4236_;
goto v_resetjp_4225_;
}
v_resetjp_4225_:
{
size_t v___x_4228_; size_t v___x_4229_; size_t v___x_4230_; size_t v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4234_; 
v___x_4228_ = ((size_t)5ULL);
v___x_4229_ = lean_usize_shift_right(v_x_4190_, v___x_4228_);
v___x_4230_ = ((size_t)1ULL);
v___x_4231_ = lean_usize_add(v_x_4191_, v___x_4230_);
v___x_4232_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_node_4224_, v___x_4229_, v___x_4231_, v_x_4192_, v_x_4193_);
if (v_isShared_4227_ == 0)
{
lean_ctor_set(v___x_4226_, 0, v___x_4232_);
v___x_4234_ = v___x_4226_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v___x_4232_);
v___x_4234_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
v___y_4207_ = v___x_4234_;
goto v___jp_4206_;
}
}
}
default: 
{
lean_object* v___x_4237_; 
v___x_4237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4237_, 0, v_x_4192_);
lean_ctor_set(v___x_4237_, 1, v_x_4193_);
v___y_4207_ = v___x_4237_;
goto v___jp_4206_;
}
}
v___jp_4206_:
{
lean_object* v___x_4208_; lean_object* v___x_4210_; 
v___x_4208_ = lean_array_fset(v_xs_x27_4205_, v_j_4197_, v___y_4207_);
lean_dec(v_j_4197_);
if (v_isShared_4202_ == 0)
{
lean_ctor_set(v___x_4201_, 0, v___x_4208_);
v___x_4210_ = v___x_4201_;
goto v_reusejp_4209_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v___x_4208_);
v___x_4210_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4209_;
}
v_reusejp_4209_:
{
return v___x_4210_;
}
}
}
}
}
else
{
lean_object* v_ks_4240_; lean_object* v_vs_4241_; lean_object* v___x_4243_; uint8_t v_isShared_4244_; uint8_t v_isSharedCheck_4259_; 
v_ks_4240_ = lean_ctor_get(v_x_4189_, 0);
v_vs_4241_ = lean_ctor_get(v_x_4189_, 1);
v_isSharedCheck_4259_ = !lean_is_exclusive(v_x_4189_);
if (v_isSharedCheck_4259_ == 0)
{
v___x_4243_ = v_x_4189_;
v_isShared_4244_ = v_isSharedCheck_4259_;
goto v_resetjp_4242_;
}
else
{
lean_inc(v_vs_4241_);
lean_inc(v_ks_4240_);
lean_dec(v_x_4189_);
v___x_4243_ = lean_box(0);
v_isShared_4244_ = v_isSharedCheck_4259_;
goto v_resetjp_4242_;
}
v_resetjp_4242_:
{
lean_object* v___x_4246_; 
if (v_isShared_4244_ == 0)
{
v___x_4246_ = v___x_4243_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_ks_4240_);
lean_ctor_set(v_reuseFailAlloc_4258_, 1, v_vs_4241_);
v___x_4246_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4245_;
}
v_reusejp_4245_:
{
lean_object* v_newNode_4247_; size_t v___x_4248_; uint8_t v___x_4249_; 
v_newNode_4247_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(v___x_4246_, v_x_4192_, v_x_4193_);
v___x_4248_ = ((size_t)7ULL);
v___x_4249_ = lean_usize_dec_le(v___x_4248_, v_x_4191_);
if (v___x_4249_ == 0)
{
lean_object* v___x_4250_; lean_object* v___x_4251_; uint8_t v___x_4252_; 
v___x_4250_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4247_);
v___x_4251_ = lean_unsigned_to_nat(4u);
v___x_4252_ = lean_nat_dec_lt(v___x_4250_, v___x_4251_);
lean_dec(v___x_4250_);
if (v___x_4252_ == 0)
{
lean_object* v_ks_4253_; lean_object* v_vs_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; 
v_ks_4253_ = lean_ctor_get(v_newNode_4247_, 0);
lean_inc_ref(v_ks_4253_);
v_vs_4254_ = lean_ctor_get(v_newNode_4247_, 1);
lean_inc_ref(v_vs_4254_);
lean_dec_ref(v_newNode_4247_);
v___x_4255_ = lean_unsigned_to_nat(0u);
v___x_4256_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_4257_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_x_4191_, v_ks_4253_, v_vs_4254_, v___x_4255_, v___x_4256_);
lean_dec_ref(v_vs_4254_);
lean_dec_ref(v_ks_4253_);
return v___x_4257_;
}
else
{
return v_newNode_4247_;
}
}
else
{
return v_newNode_4247_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_4260_, lean_object* v_keys_4261_, lean_object* v_vals_4262_, lean_object* v_i_4263_, lean_object* v_entries_4264_){
_start:
{
lean_object* v___x_4265_; uint8_t v___x_4266_; 
v___x_4265_ = lean_array_get_size(v_keys_4261_);
v___x_4266_ = lean_nat_dec_lt(v_i_4263_, v___x_4265_);
if (v___x_4266_ == 0)
{
lean_dec(v_i_4263_);
return v_entries_4264_;
}
else
{
lean_object* v_k_4267_; lean_object* v_v_4268_; uint64_t v___x_4269_; size_t v_h_4270_; size_t v___x_4271_; lean_object* v___x_4272_; size_t v___x_4273_; size_t v___x_4274_; size_t v___x_4275_; size_t v_h_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; 
v_k_4267_ = lean_array_fget_borrowed(v_keys_4261_, v_i_4263_);
v_v_4268_ = lean_array_fget_borrowed(v_vals_4262_, v_i_4263_);
v___x_4269_ = l_Lean_instHashableMVarId_hash(v_k_4267_);
v_h_4270_ = lean_uint64_to_usize(v___x_4269_);
v___x_4271_ = ((size_t)5ULL);
v___x_4272_ = lean_unsigned_to_nat(1u);
v___x_4273_ = ((size_t)1ULL);
v___x_4274_ = lean_usize_sub(v_depth_4260_, v___x_4273_);
v___x_4275_ = lean_usize_mul(v___x_4271_, v___x_4274_);
v_h_4276_ = lean_usize_shift_right(v_h_4270_, v___x_4275_);
v___x_4277_ = lean_nat_add(v_i_4263_, v___x_4272_);
lean_dec(v_i_4263_);
lean_inc(v_v_4268_);
lean_inc(v_k_4267_);
v___x_4278_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_entries_4264_, v_h_4276_, v_depth_4260_, v_k_4267_, v_v_4268_);
v_i_4263_ = v___x_4277_;
v_entries_4264_ = v___x_4278_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_4280_, lean_object* v_keys_4281_, lean_object* v_vals_4282_, lean_object* v_i_4283_, lean_object* v_entries_4284_){
_start:
{
size_t v_depth_boxed_4285_; lean_object* v_res_4286_; 
v_depth_boxed_4285_ = lean_unbox_usize(v_depth_4280_);
lean_dec(v_depth_4280_);
v_res_4286_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_4285_, v_keys_4281_, v_vals_4282_, v_i_4283_, v_entries_4284_);
lean_dec_ref(v_vals_4282_);
lean_dec_ref(v_keys_4281_);
return v_res_4286_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_4287_, lean_object* v_x_4288_, lean_object* v_x_4289_, lean_object* v_x_4290_, lean_object* v_x_4291_){
_start:
{
size_t v_x_3985__boxed_4292_; size_t v_x_3986__boxed_4293_; lean_object* v_res_4294_; 
v_x_3985__boxed_4292_ = lean_unbox_usize(v_x_4288_);
lean_dec(v_x_4288_);
v_x_3986__boxed_4293_ = lean_unbox_usize(v_x_4289_);
lean_dec(v_x_4289_);
v_res_4294_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4287_, v_x_3985__boxed_4292_, v_x_3986__boxed_4293_, v_x_4290_, v_x_4291_);
return v_res_4294_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(lean_object* v_x_4295_, lean_object* v_x_4296_, lean_object* v_x_4297_){
_start:
{
uint64_t v___x_4298_; size_t v___x_4299_; size_t v___x_4300_; lean_object* v___x_4301_; 
v___x_4298_ = l_Lean_instHashableMVarId_hash(v_x_4296_);
v___x_4299_ = lean_uint64_to_usize(v___x_4298_);
v___x_4300_ = ((size_t)1ULL);
v___x_4301_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4295_, v___x_4299_, v___x_4300_, v_x_4296_, v_x_4297_);
return v___x_4301_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(lean_object* v_mvarId_4302_, lean_object* v_val_4303_, lean_object* v___y_4304_){
_start:
{
lean_object* v___x_4306_; lean_object* v_mctx_4307_; lean_object* v_cache_4308_; lean_object* v_zetaDeltaFVarIds_4309_; lean_object* v_postponed_4310_; lean_object* v_diag_4311_; lean_object* v___x_4313_; uint8_t v_isShared_4314_; uint8_t v_isSharedCheck_4340_; 
v___x_4306_ = lean_st_ref_take(v___y_4304_);
v_mctx_4307_ = lean_ctor_get(v___x_4306_, 0);
v_cache_4308_ = lean_ctor_get(v___x_4306_, 1);
v_zetaDeltaFVarIds_4309_ = lean_ctor_get(v___x_4306_, 2);
v_postponed_4310_ = lean_ctor_get(v___x_4306_, 3);
v_diag_4311_ = lean_ctor_get(v___x_4306_, 4);
v_isSharedCheck_4340_ = !lean_is_exclusive(v___x_4306_);
if (v_isSharedCheck_4340_ == 0)
{
v___x_4313_ = v___x_4306_;
v_isShared_4314_ = v_isSharedCheck_4340_;
goto v_resetjp_4312_;
}
else
{
lean_inc(v_diag_4311_);
lean_inc(v_postponed_4310_);
lean_inc(v_zetaDeltaFVarIds_4309_);
lean_inc(v_cache_4308_);
lean_inc(v_mctx_4307_);
lean_dec(v___x_4306_);
v___x_4313_ = lean_box(0);
v_isShared_4314_ = v_isSharedCheck_4340_;
goto v_resetjp_4312_;
}
v_resetjp_4312_:
{
lean_object* v_depth_4315_; lean_object* v_levelAssignDepth_4316_; lean_object* v_lmvarCounter_4317_; lean_object* v_mvarCounter_4318_; lean_object* v_lDecls_4319_; lean_object* v_decls_4320_; lean_object* v_userNames_4321_; lean_object* v_lAssignment_4322_; lean_object* v_eAssignment_4323_; lean_object* v_dAssignment_4324_; lean_object* v_instanceTypedMVars_4325_; lean_object* v___x_4327_; uint8_t v_isShared_4328_; uint8_t v_isSharedCheck_4339_; 
v_depth_4315_ = lean_ctor_get(v_mctx_4307_, 0);
v_levelAssignDepth_4316_ = lean_ctor_get(v_mctx_4307_, 1);
v_lmvarCounter_4317_ = lean_ctor_get(v_mctx_4307_, 2);
v_mvarCounter_4318_ = lean_ctor_get(v_mctx_4307_, 3);
v_lDecls_4319_ = lean_ctor_get(v_mctx_4307_, 4);
v_decls_4320_ = lean_ctor_get(v_mctx_4307_, 5);
v_userNames_4321_ = lean_ctor_get(v_mctx_4307_, 6);
v_lAssignment_4322_ = lean_ctor_get(v_mctx_4307_, 7);
v_eAssignment_4323_ = lean_ctor_get(v_mctx_4307_, 8);
v_dAssignment_4324_ = lean_ctor_get(v_mctx_4307_, 9);
v_instanceTypedMVars_4325_ = lean_ctor_get(v_mctx_4307_, 10);
v_isSharedCheck_4339_ = !lean_is_exclusive(v_mctx_4307_);
if (v_isSharedCheck_4339_ == 0)
{
v___x_4327_ = v_mctx_4307_;
v_isShared_4328_ = v_isSharedCheck_4339_;
goto v_resetjp_4326_;
}
else
{
lean_inc(v_instanceTypedMVars_4325_);
lean_inc(v_dAssignment_4324_);
lean_inc(v_eAssignment_4323_);
lean_inc(v_lAssignment_4322_);
lean_inc(v_userNames_4321_);
lean_inc(v_decls_4320_);
lean_inc(v_lDecls_4319_);
lean_inc(v_mvarCounter_4318_);
lean_inc(v_lmvarCounter_4317_);
lean_inc(v_levelAssignDepth_4316_);
lean_inc(v_depth_4315_);
lean_dec(v_mctx_4307_);
v___x_4327_ = lean_box(0);
v_isShared_4328_ = v_isSharedCheck_4339_;
goto v_resetjp_4326_;
}
v_resetjp_4326_:
{
lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4332_; 
v___x_4329_ = lean_box(0);
v___x_4330_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(v_eAssignment_4323_, v_mvarId_4302_, v_val_4303_);
if (v_isShared_4328_ == 0)
{
lean_ctor_set(v___x_4327_, 8, v___x_4330_);
v___x_4332_ = v___x_4327_;
goto v_reusejp_4331_;
}
else
{
lean_object* v_reuseFailAlloc_4338_; 
v_reuseFailAlloc_4338_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_4338_, 0, v_depth_4315_);
lean_ctor_set(v_reuseFailAlloc_4338_, 1, v_levelAssignDepth_4316_);
lean_ctor_set(v_reuseFailAlloc_4338_, 2, v_lmvarCounter_4317_);
lean_ctor_set(v_reuseFailAlloc_4338_, 3, v_mvarCounter_4318_);
lean_ctor_set(v_reuseFailAlloc_4338_, 4, v_lDecls_4319_);
lean_ctor_set(v_reuseFailAlloc_4338_, 5, v_decls_4320_);
lean_ctor_set(v_reuseFailAlloc_4338_, 6, v_userNames_4321_);
lean_ctor_set(v_reuseFailAlloc_4338_, 7, v_lAssignment_4322_);
lean_ctor_set(v_reuseFailAlloc_4338_, 8, v___x_4330_);
lean_ctor_set(v_reuseFailAlloc_4338_, 9, v_dAssignment_4324_);
lean_ctor_set(v_reuseFailAlloc_4338_, 10, v_instanceTypedMVars_4325_);
v___x_4332_ = v_reuseFailAlloc_4338_;
goto v_reusejp_4331_;
}
v_reusejp_4331_:
{
lean_object* v___x_4334_; 
if (v_isShared_4314_ == 0)
{
lean_ctor_set(v___x_4313_, 0, v___x_4332_);
v___x_4334_ = v___x_4313_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v___x_4332_);
lean_ctor_set(v_reuseFailAlloc_4337_, 1, v_cache_4308_);
lean_ctor_set(v_reuseFailAlloc_4337_, 2, v_zetaDeltaFVarIds_4309_);
lean_ctor_set(v_reuseFailAlloc_4337_, 3, v_postponed_4310_);
lean_ctor_set(v_reuseFailAlloc_4337_, 4, v_diag_4311_);
v___x_4334_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
lean_object* v___x_4335_; lean_object* v___x_4336_; 
v___x_4335_ = lean_st_ref_put(v___y_4304_, v___x_4334_);
v___x_4336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4336_, 0, v___x_4329_);
return v___x_4336_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg___boxed(lean_object* v_mvarId_4341_, lean_object* v_val_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_){
_start:
{
lean_object* v_res_4345_; 
v_res_4345_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mvarId_4341_, v_val_4342_, v___y_4343_);
lean_dec(v___y_4343_);
return v_res_4345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___lam__0(lean_object* v_mv_u2081_4350_, lean_object* v_mv_u2082_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_){
_start:
{
lean_object* v___x_4360_; 
lean_inc(v_mv_u2081_4350_);
v___x_4360_ = l_Lean_MVarId_getDecl(v_mv_u2081_4350_, v___y_4352_, v___y_4353_, v___y_4354_, v___y_4355_);
if (lean_obj_tag(v___x_4360_) == 0)
{
lean_object* v_a_4361_; lean_object* v___x_4362_; 
v_a_4361_ = lean_ctor_get(v___x_4360_, 0);
lean_inc(v_a_4361_);
lean_dec_ref_known(v___x_4360_, 1);
lean_inc(v_mv_u2082_4351_);
v___x_4362_ = l_Lean_MVarId_getDecl(v_mv_u2082_4351_, v___y_4352_, v___y_4353_, v___y_4354_, v___y_4355_);
if (lean_obj_tag(v___x_4362_) == 0)
{
lean_object* v_a_4363_; lean_object* v_lctx_4364_; lean_object* v_type_4365_; lean_object* v_lctx_4366_; lean_object* v_type_4367_; uint8_t v___x_4368_; 
v_a_4363_ = lean_ctor_get(v___x_4362_, 0);
lean_inc(v_a_4363_);
lean_dec_ref_known(v___x_4362_, 1);
v_lctx_4364_ = lean_ctor_get(v_a_4361_, 1);
lean_inc_ref(v_lctx_4364_);
v_type_4365_ = lean_ctor_get(v_a_4361_, 2);
lean_inc_ref(v_type_4365_);
lean_dec(v_a_4361_);
v_lctx_4366_ = lean_ctor_get(v_a_4363_, 1);
lean_inc_ref(v_lctx_4366_);
v_type_4367_ = lean_ctor_get(v_a_4363_, 2);
lean_inc_ref(v_type_4367_);
lean_dec(v_a_4363_);
v___x_4368_ = lean_expr_eqv(v_type_4365_, v_type_4367_);
lean_dec_ref(v_type_4367_);
lean_dec_ref(v_type_4365_);
if (v___x_4368_ == 0)
{
lean_dec_ref(v_lctx_4366_);
lean_dec_ref(v_lctx_4364_);
lean_dec(v_mv_u2082_4351_);
lean_dec(v_mv_u2081_4350_);
goto v___jp_4357_;
}
else
{
lean_object* v___x_4369_; uint8_t v___x_4370_; 
v___x_4369_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
v___x_4370_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_4364_, v_lctx_4366_, v___x_4369_);
if (v___x_4370_ == 0)
{
uint8_t v___x_4371_; 
v___x_4371_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_4366_, v_lctx_4364_, v___x_4369_);
lean_dec_ref(v_lctx_4364_);
lean_dec_ref(v_lctx_4366_);
if (v___x_4371_ == 0)
{
lean_dec(v_mv_u2082_4351_);
lean_dec(v_mv_u2081_4350_);
goto v___jp_4357_;
}
else
{
lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4383_; 
v___x_4372_ = l_Lean_Expr_mvar___override(v_mv_u2082_4351_);
v___x_4373_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mv_u2081_4350_, v___x_4372_, v___y_4353_);
v_isSharedCheck_4383_ = !lean_is_exclusive(v___x_4373_);
if (v_isSharedCheck_4383_ == 0)
{
lean_object* v_unused_4384_; 
v_unused_4384_ = lean_ctor_get(v___x_4373_, 0);
lean_dec(v_unused_4384_);
v___x_4375_ = v___x_4373_;
v_isShared_4376_ = v_isSharedCheck_4383_;
goto v_resetjp_4374_;
}
else
{
lean_dec(v___x_4373_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4383_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4381_; 
v___x_4377_ = lean_box(v___x_4370_);
v___x_4378_ = lean_box(v___x_4368_);
v___x_4379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4379_, 0, v___x_4377_);
lean_ctor_set(v___x_4379_, 1, v___x_4378_);
if (v_isShared_4376_ == 0)
{
lean_ctor_set(v___x_4375_, 0, v___x_4379_);
v___x_4381_ = v___x_4375_;
goto v_reusejp_4380_;
}
else
{
lean_object* v_reuseFailAlloc_4382_; 
v_reuseFailAlloc_4382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4382_, 0, v___x_4379_);
v___x_4381_ = v_reuseFailAlloc_4382_;
goto v_reusejp_4380_;
}
v_reusejp_4380_:
{
return v___x_4381_;
}
}
}
}
else
{
lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4388_; uint8_t v_isShared_4389_; uint8_t v_isSharedCheck_4397_; 
lean_dec_ref(v_lctx_4366_);
lean_dec_ref(v_lctx_4364_);
v___x_4385_ = l_Lean_Expr_mvar___override(v_mv_u2081_4350_);
v___x_4386_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mv_u2082_4351_, v___x_4385_, v___y_4353_);
v_isSharedCheck_4397_ = !lean_is_exclusive(v___x_4386_);
if (v_isSharedCheck_4397_ == 0)
{
lean_object* v_unused_4398_; 
v_unused_4398_ = lean_ctor_get(v___x_4386_, 0);
lean_dec(v_unused_4398_);
v___x_4388_ = v___x_4386_;
v_isShared_4389_ = v_isSharedCheck_4397_;
goto v_resetjp_4387_;
}
else
{
lean_dec(v___x_4386_);
v___x_4388_ = lean_box(0);
v_isShared_4389_ = v_isSharedCheck_4397_;
goto v_resetjp_4387_;
}
v_resetjp_4387_:
{
uint8_t v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4395_; 
v___x_4390_ = 0;
v___x_4391_ = lean_box(v___x_4368_);
v___x_4392_ = lean_box(v___x_4390_);
v___x_4393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4393_, 0, v___x_4391_);
lean_ctor_set(v___x_4393_, 1, v___x_4392_);
if (v_isShared_4389_ == 0)
{
lean_ctor_set(v___x_4388_, 0, v___x_4393_);
v___x_4395_ = v___x_4388_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v___x_4393_);
v___x_4395_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
return v___x_4395_;
}
}
}
}
}
else
{
lean_object* v_a_4399_; lean_object* v___x_4401_; uint8_t v_isShared_4402_; uint8_t v_isSharedCheck_4406_; 
lean_dec(v_a_4361_);
lean_dec(v_mv_u2082_4351_);
lean_dec(v_mv_u2081_4350_);
v_a_4399_ = lean_ctor_get(v___x_4362_, 0);
v_isSharedCheck_4406_ = !lean_is_exclusive(v___x_4362_);
if (v_isSharedCheck_4406_ == 0)
{
v___x_4401_ = v___x_4362_;
v_isShared_4402_ = v_isSharedCheck_4406_;
goto v_resetjp_4400_;
}
else
{
lean_inc(v_a_4399_);
lean_dec(v___x_4362_);
v___x_4401_ = lean_box(0);
v_isShared_4402_ = v_isSharedCheck_4406_;
goto v_resetjp_4400_;
}
v_resetjp_4400_:
{
lean_object* v___x_4404_; 
if (v_isShared_4402_ == 0)
{
v___x_4404_ = v___x_4401_;
goto v_reusejp_4403_;
}
else
{
lean_object* v_reuseFailAlloc_4405_; 
v_reuseFailAlloc_4405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4405_, 0, v_a_4399_);
v___x_4404_ = v_reuseFailAlloc_4405_;
goto v_reusejp_4403_;
}
v_reusejp_4403_:
{
return v___x_4404_;
}
}
}
}
else
{
lean_object* v_a_4407_; lean_object* v___x_4409_; uint8_t v_isShared_4410_; uint8_t v_isSharedCheck_4414_; 
lean_dec(v_mv_u2082_4351_);
lean_dec(v_mv_u2081_4350_);
v_a_4407_ = lean_ctor_get(v___x_4360_, 0);
v_isSharedCheck_4414_ = !lean_is_exclusive(v___x_4360_);
if (v_isSharedCheck_4414_ == 0)
{
v___x_4409_ = v___x_4360_;
v_isShared_4410_ = v_isSharedCheck_4414_;
goto v_resetjp_4408_;
}
else
{
lean_inc(v_a_4407_);
lean_dec(v___x_4360_);
v___x_4409_ = lean_box(0);
v_isShared_4410_ = v_isSharedCheck_4414_;
goto v_resetjp_4408_;
}
v_resetjp_4408_:
{
lean_object* v___x_4412_; 
if (v_isShared_4410_ == 0)
{
v___x_4412_ = v___x_4409_;
goto v_reusejp_4411_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v_a_4407_);
v___x_4412_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4411_;
}
v_reusejp_4411_:
{
return v___x_4412_;
}
}
}
v___jp_4357_:
{
lean_object* v___x_4358_; lean_object* v___x_4359_; 
v___x_4358_ = ((lean_object*)(l_Lean_Elab_WF_assignSubsumed___lam__0___closed__0));
v___x_4359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4359_, 0, v___x_4358_);
return v___x_4359_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___lam__0___boxed(lean_object* v_mv_u2081_4415_, lean_object* v_mv_u2082_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_){
_start:
{
lean_object* v_res_4422_; 
v_res_4422_ = l_Lean_Elab_WF_assignSubsumed___lam__0(v_mv_u2081_4415_, v_mv_u2082_4416_, v___y_4417_, v___y_4418_, v___y_4419_, v___y_4420_);
lean_dec(v___y_4420_);
lean_dec_ref(v___y_4419_);
lean_dec(v___y_4418_);
lean_dec_ref(v___y_4417_);
return v_res_4422_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1(lean_object* v___x_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_){
_start:
{
lean_object* v___x_4429_; 
v___x_4429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4429_, 0, v___x_4423_);
return v___x_4429_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1___boxed(lean_object* v___x_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_){
_start:
{
lean_object* v_res_4436_; 
v_res_4436_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1(v___x_4430_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_);
lean_dec(v___y_4434_);
lean_dec_ref(v___y_4433_);
lean_dec(v___y_4432_);
lean_dec_ref(v___y_4431_);
return v_res_4436_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0(lean_object* v_f_4437_, lean_object* v___x_4438_, lean_object* v___x_4439_, lean_object* v___x_4440_, lean_object* v_a_4441_, uint8_t v___x_4442_, lean_object* v_snd_4443_, lean_object* v_fst_4444_, lean_object* v_next_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_){
_start:
{
lean_object* v___x_4451_; 
v___x_4451_ = lean_apply_7(v_f_4437_, v___x_4438_, v___x_4439_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_, lean_box(0));
if (lean_obj_tag(v___x_4451_) == 0)
{
lean_object* v_a_4452_; lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4487_; 
v_a_4452_ = lean_ctor_get(v___x_4451_, 0);
v_isSharedCheck_4487_ = !lean_is_exclusive(v___x_4451_);
if (v_isSharedCheck_4487_ == 0)
{
v___x_4454_ = v___x_4451_;
v_isShared_4455_ = v_isSharedCheck_4487_;
goto v_resetjp_4453_;
}
else
{
lean_inc(v_a_4452_);
lean_dec(v___x_4451_);
v___x_4454_ = lean_box(0);
v_isShared_4455_ = v_isSharedCheck_4487_;
goto v_resetjp_4453_;
}
v_resetjp_4453_:
{
lean_object* v_fst_4456_; lean_object* v_snd_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4486_; 
v_fst_4456_ = lean_ctor_get(v_a_4452_, 0);
v_snd_4457_ = lean_ctor_get(v_a_4452_, 1);
v_isSharedCheck_4486_ = !lean_is_exclusive(v_a_4452_);
if (v_isSharedCheck_4486_ == 0)
{
v___x_4459_ = v_a_4452_;
v_isShared_4460_ = v_isSharedCheck_4486_;
goto v_resetjp_4458_;
}
else
{
lean_inc(v_snd_4457_);
lean_inc(v_fst_4456_);
lean_dec(v_a_4452_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4486_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
lean_object* v_removed_4462_; lean_object* v_numRemoved_4463_; uint8_t v___x_4482_; 
v___x_4482_ = lean_unbox(v_fst_4456_);
lean_dec(v_fst_4456_);
if (v___x_4482_ == 0)
{
lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; 
v___x_4483_ = lean_nat_add(v_snd_4443_, v___x_4440_);
lean_dec(v_snd_4443_);
v___x_4484_ = lean_box(v___x_4442_);
v___x_4485_ = lean_array_set(v_fst_4444_, v_next_4445_, v___x_4484_);
v_removed_4462_ = v___x_4485_;
v_numRemoved_4463_ = v___x_4483_;
goto v___jp_4461_;
}
else
{
v_removed_4462_ = v_fst_4444_;
v_numRemoved_4463_ = v_snd_4443_;
goto v___jp_4461_;
}
v___jp_4461_:
{
uint8_t v___x_4464_; 
v___x_4464_ = lean_unbox(v_snd_4457_);
lean_dec(v_snd_4457_);
if (v___x_4464_ == 0)
{
lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4469_; 
v___x_4465_ = lean_nat_add(v_numRemoved_4463_, v___x_4440_);
lean_dec(v_numRemoved_4463_);
v___x_4466_ = lean_box(v___x_4442_);
v___x_4467_ = lean_array_set(v_removed_4462_, v_a_4441_, v___x_4466_);
if (v_isShared_4460_ == 0)
{
lean_ctor_set(v___x_4459_, 1, v___x_4465_);
lean_ctor_set(v___x_4459_, 0, v___x_4467_);
v___x_4469_ = v___x_4459_;
goto v_reusejp_4468_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v___x_4467_);
lean_ctor_set(v_reuseFailAlloc_4474_, 1, v___x_4465_);
v___x_4469_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4468_;
}
v_reusejp_4468_:
{
lean_object* v___x_4470_; lean_object* v___x_4472_; 
v___x_4470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4470_, 0, v___x_4469_);
if (v_isShared_4455_ == 0)
{
lean_ctor_set(v___x_4454_, 0, v___x_4470_);
v___x_4472_ = v___x_4454_;
goto v_reusejp_4471_;
}
else
{
lean_object* v_reuseFailAlloc_4473_; 
v_reuseFailAlloc_4473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4473_, 0, v___x_4470_);
v___x_4472_ = v_reuseFailAlloc_4473_;
goto v_reusejp_4471_;
}
v_reusejp_4471_:
{
return v___x_4472_;
}
}
}
else
{
lean_object* v___x_4476_; 
if (v_isShared_4460_ == 0)
{
lean_ctor_set(v___x_4459_, 1, v_numRemoved_4463_);
lean_ctor_set(v___x_4459_, 0, v_removed_4462_);
v___x_4476_ = v___x_4459_;
goto v_reusejp_4475_;
}
else
{
lean_object* v_reuseFailAlloc_4481_; 
v_reuseFailAlloc_4481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4481_, 0, v_removed_4462_);
lean_ctor_set(v_reuseFailAlloc_4481_, 1, v_numRemoved_4463_);
v___x_4476_ = v_reuseFailAlloc_4481_;
goto v_reusejp_4475_;
}
v_reusejp_4475_:
{
lean_object* v___x_4477_; lean_object* v___x_4479_; 
v___x_4477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4477_, 0, v___x_4476_);
if (v_isShared_4455_ == 0)
{
lean_ctor_set(v___x_4454_, 0, v___x_4477_);
v___x_4479_ = v___x_4454_;
goto v_reusejp_4478_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v___x_4477_);
v___x_4479_ = v_reuseFailAlloc_4480_;
goto v_reusejp_4478_;
}
v_reusejp_4478_:
{
return v___x_4479_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4488_; lean_object* v___x_4490_; uint8_t v_isShared_4491_; uint8_t v_isSharedCheck_4495_; 
lean_dec(v_fst_4444_);
lean_dec(v_snd_4443_);
v_a_4488_ = lean_ctor_get(v___x_4451_, 0);
v_isSharedCheck_4495_ = !lean_is_exclusive(v___x_4451_);
if (v_isSharedCheck_4495_ == 0)
{
v___x_4490_ = v___x_4451_;
v_isShared_4491_ = v_isSharedCheck_4495_;
goto v_resetjp_4489_;
}
else
{
lean_inc(v_a_4488_);
lean_dec(v___x_4451_);
v___x_4490_ = lean_box(0);
v_isShared_4491_ = v_isSharedCheck_4495_;
goto v_resetjp_4489_;
}
v_resetjp_4489_:
{
lean_object* v___x_4493_; 
if (v_isShared_4491_ == 0)
{
v___x_4493_ = v___x_4490_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4494_; 
v_reuseFailAlloc_4494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4494_, 0, v_a_4488_);
v___x_4493_ = v_reuseFailAlloc_4494_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
return v___x_4493_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_f_4496_, lean_object* v___x_4497_, lean_object* v___x_4498_, lean_object* v___x_4499_, lean_object* v_a_4500_, lean_object* v___x_4501_, lean_object* v_snd_4502_, lean_object* v_fst_4503_, lean_object* v_next_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_){
_start:
{
uint8_t v___x_4358__boxed_4510_; lean_object* v_res_4511_; 
v___x_4358__boxed_4510_ = lean_unbox(v___x_4501_);
v_res_4511_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0(v_f_4496_, v___x_4497_, v___x_4498_, v___x_4499_, v_a_4500_, v___x_4358__boxed_4510_, v_snd_4502_, v_fst_4503_, v_next_4504_, v___y_4505_, v___y_4506_, v___y_4507_, v___y_4508_);
lean_dec(v_next_4504_);
lean_dec(v_a_4500_);
lean_dec(v___x_4499_);
return v_res_4511_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(lean_object* v_upperBound_4512_, lean_object* v_a_4513_, lean_object* v_next_4514_, lean_object* v_f_4515_, lean_object* v_a_4516_, lean_object* v_b_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_){
_start:
{
uint8_t v___x_4523_; 
v___x_4523_ = lean_nat_dec_lt(v_a_4516_, v_upperBound_4512_);
if (v___x_4523_ == 0)
{
lean_object* v___x_4524_; 
lean_dec(v_a_4516_);
lean_dec_ref(v_f_4515_);
lean_dec(v_next_4514_);
v___x_4524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4524_, 0, v_b_4517_);
return v___x_4524_;
}
else
{
lean_object* v_fst_4525_; lean_object* v_snd_4526_; lean_object* v___x_4528_; uint8_t v_isShared_4529_; uint8_t v_isSharedCheck_4573_; 
v_fst_4525_ = lean_ctor_get(v_b_4517_, 0);
v_snd_4526_ = lean_ctor_get(v_b_4517_, 1);
v_isSharedCheck_4573_ = !lean_is_exclusive(v_b_4517_);
if (v_isSharedCheck_4573_ == 0)
{
v___x_4528_ = v_b_4517_;
v_isShared_4529_ = v_isSharedCheck_4573_;
goto v_resetjp_4527_;
}
else
{
lean_inc(v_snd_4526_);
lean_inc(v_fst_4525_);
lean_dec(v_b_4517_);
v___x_4528_ = lean_box(0);
v_isShared_4529_ = v_isSharedCheck_4573_;
goto v_resetjp_4527_;
}
v_resetjp_4527_:
{
lean_object* v___x_4530_; lean_object* v___y_4532_; uint8_t v___y_4555_; uint8_t v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; uint8_t v___x_4568_; 
v___x_4530_ = lean_unsigned_to_nat(1u);
v___x_4565_ = 0;
v___x_4566_ = lean_box(v___x_4565_);
v___x_4567_ = lean_array_get(v___x_4566_, v_fst_4525_, v_next_4514_);
lean_dec(v___x_4566_);
v___x_4568_ = lean_unbox(v___x_4567_);
if (v___x_4568_ == 0)
{
lean_object* v___x_4569_; lean_object* v___x_4570_; uint8_t v___x_4571_; 
lean_dec(v___x_4567_);
v___x_4569_ = lean_box(v___x_4565_);
v___x_4570_ = lean_array_get(v___x_4569_, v_fst_4525_, v_a_4516_);
lean_dec(v___x_4569_);
v___x_4571_ = lean_unbox(v___x_4570_);
lean_dec(v___x_4570_);
v___y_4555_ = v___x_4571_;
goto v___jp_4554_;
}
else
{
uint8_t v___x_4572_; 
v___x_4572_ = lean_unbox(v___x_4567_);
lean_dec(v___x_4567_);
v___y_4555_ = v___x_4572_;
goto v___jp_4554_;
}
v___jp_4531_:
{
lean_object* v___x_4533_; 
lean_inc(v___y_4521_);
lean_inc_ref(v___y_4520_);
lean_inc(v___y_4519_);
lean_inc_ref(v___y_4518_);
v___x_4533_ = lean_apply_5(v___y_4532_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_, lean_box(0));
if (lean_obj_tag(v___x_4533_) == 0)
{
lean_object* v_a_4534_; lean_object* v___x_4536_; uint8_t v_isShared_4537_; uint8_t v_isSharedCheck_4545_; 
v_a_4534_ = lean_ctor_get(v___x_4533_, 0);
v_isSharedCheck_4545_ = !lean_is_exclusive(v___x_4533_);
if (v_isSharedCheck_4545_ == 0)
{
v___x_4536_ = v___x_4533_;
v_isShared_4537_ = v_isSharedCheck_4545_;
goto v_resetjp_4535_;
}
else
{
lean_inc(v_a_4534_);
lean_dec(v___x_4533_);
v___x_4536_ = lean_box(0);
v_isShared_4537_ = v_isSharedCheck_4545_;
goto v_resetjp_4535_;
}
v_resetjp_4535_:
{
if (lean_obj_tag(v_a_4534_) == 0)
{
lean_object* v_a_4538_; lean_object* v___x_4540_; 
lean_dec(v_a_4516_);
lean_dec_ref(v_f_4515_);
lean_dec(v_next_4514_);
v_a_4538_ = lean_ctor_get(v_a_4534_, 0);
lean_inc(v_a_4538_);
lean_dec_ref_known(v_a_4534_, 1);
if (v_isShared_4537_ == 0)
{
lean_ctor_set(v___x_4536_, 0, v_a_4538_);
v___x_4540_ = v___x_4536_;
goto v_reusejp_4539_;
}
else
{
lean_object* v_reuseFailAlloc_4541_; 
v_reuseFailAlloc_4541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4541_, 0, v_a_4538_);
v___x_4540_ = v_reuseFailAlloc_4541_;
goto v_reusejp_4539_;
}
v_reusejp_4539_:
{
return v___x_4540_;
}
}
else
{
lean_object* v_a_4542_; lean_object* v___x_4543_; 
lean_del_object(v___x_4536_);
v_a_4542_ = lean_ctor_get(v_a_4534_, 0);
lean_inc(v_a_4542_);
lean_dec_ref_known(v_a_4534_, 1);
v___x_4543_ = lean_nat_add(v_a_4516_, v___x_4530_);
lean_dec(v_a_4516_);
v_a_4516_ = v___x_4543_;
v_b_4517_ = v_a_4542_;
goto _start;
}
}
}
else
{
lean_object* v_a_4546_; lean_object* v___x_4548_; uint8_t v_isShared_4549_; uint8_t v_isSharedCheck_4553_; 
lean_dec(v_a_4516_);
lean_dec_ref(v_f_4515_);
lean_dec(v_next_4514_);
v_a_4546_ = lean_ctor_get(v___x_4533_, 0);
v_isSharedCheck_4553_ = !lean_is_exclusive(v___x_4533_);
if (v_isSharedCheck_4553_ == 0)
{
v___x_4548_ = v___x_4533_;
v_isShared_4549_ = v_isSharedCheck_4553_;
goto v_resetjp_4547_;
}
else
{
lean_inc(v_a_4546_);
lean_dec(v___x_4533_);
v___x_4548_ = lean_box(0);
v_isShared_4549_ = v_isSharedCheck_4553_;
goto v_resetjp_4547_;
}
v_resetjp_4547_:
{
lean_object* v___x_4551_; 
if (v_isShared_4549_ == 0)
{
v___x_4551_ = v___x_4548_;
goto v_reusejp_4550_;
}
else
{
lean_object* v_reuseFailAlloc_4552_; 
v_reuseFailAlloc_4552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4552_, 0, v_a_4546_);
v___x_4551_ = v_reuseFailAlloc_4552_;
goto v_reusejp_4550_;
}
v_reusejp_4550_:
{
return v___x_4551_;
}
}
}
}
v___jp_4554_:
{
if (v___y_4555_ == 0)
{
lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___f_4559_; 
lean_del_object(v___x_4528_);
v___x_4556_ = lean_array_fget_borrowed(v_a_4513_, v_next_4514_);
v___x_4557_ = lean_array_fget_borrowed(v_a_4513_, v_a_4516_);
v___x_4558_ = lean_box(v___x_4523_);
lean_inc(v_next_4514_);
lean_inc(v_a_4516_);
lean_inc(v___x_4557_);
lean_inc(v___x_4556_);
lean_inc_ref(v_f_4515_);
v___f_4559_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4559_, 0, v_f_4515_);
lean_closure_set(v___f_4559_, 1, v___x_4556_);
lean_closure_set(v___f_4559_, 2, v___x_4557_);
lean_closure_set(v___f_4559_, 3, v___x_4530_);
lean_closure_set(v___f_4559_, 4, v_a_4516_);
lean_closure_set(v___f_4559_, 5, v___x_4558_);
lean_closure_set(v___f_4559_, 6, v_snd_4526_);
lean_closure_set(v___f_4559_, 7, v_fst_4525_);
lean_closure_set(v___f_4559_, 8, v_next_4514_);
v___y_4532_ = v___f_4559_;
goto v___jp_4531_;
}
else
{
lean_object* v___x_4561_; 
if (v_isShared_4529_ == 0)
{
v___x_4561_ = v___x_4528_;
goto v_reusejp_4560_;
}
else
{
lean_object* v_reuseFailAlloc_4564_; 
v_reuseFailAlloc_4564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4564_, 0, v_fst_4525_);
lean_ctor_set(v_reuseFailAlloc_4564_, 1, v_snd_4526_);
v___x_4561_ = v_reuseFailAlloc_4564_;
goto v_reusejp_4560_;
}
v_reusejp_4560_:
{
lean_object* v___x_4562_; lean_object* v___f_4563_; 
v___x_4562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4562_, 0, v___x_4561_);
v___f_4563_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1___boxed), 6, 1);
lean_closure_set(v___f_4563_, 0, v___x_4562_);
v___y_4532_ = v___f_4563_;
goto v___jp_4531_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___boxed(lean_object* v_upperBound_4574_, lean_object* v_a_4575_, lean_object* v_next_4576_, lean_object* v_f_4577_, lean_object* v_a_4578_, lean_object* v_b_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_){
_start:
{
lean_object* v_res_4585_; 
v_res_4585_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v_upperBound_4574_, v_a_4575_, v_next_4576_, v_f_4577_, v_a_4578_, v_b_4579_, v___y_4580_, v___y_4581_, v___y_4582_, v___y_4583_);
lean_dec(v___y_4583_);
lean_dec_ref(v___y_4582_);
lean_dec(v___y_4581_);
lean_dec_ref(v___y_4580_);
lean_dec_ref(v_a_4575_);
lean_dec(v_upperBound_4574_);
return v_res_4585_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(lean_object* v_upperBound_4586_, lean_object* v___x_4587_, lean_object* v_a_4588_, lean_object* v_f_4589_, lean_object* v_a_4590_, lean_object* v_b_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_){
_start:
{
uint8_t v___x_4597_; 
v___x_4597_ = lean_nat_dec_lt(v_a_4590_, v_upperBound_4586_);
if (v___x_4597_ == 0)
{
lean_object* v___x_4598_; 
lean_dec(v_a_4590_);
lean_dec_ref(v_f_4589_);
v___x_4598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4598_, 0, v_b_4591_);
return v___x_4598_;
}
else
{
lean_object* v_fst_4599_; lean_object* v_snd_4600_; lean_object* v___x_4602_; uint8_t v_isShared_4603_; uint8_t v_isSharedCheck_4621_; 
v_fst_4599_ = lean_ctor_get(v_b_4591_, 0);
v_snd_4600_ = lean_ctor_get(v_b_4591_, 1);
v_isSharedCheck_4621_ = !lean_is_exclusive(v_b_4591_);
if (v_isSharedCheck_4621_ == 0)
{
v___x_4602_ = v_b_4591_;
v_isShared_4603_ = v_isSharedCheck_4621_;
goto v_resetjp_4601_;
}
else
{
lean_inc(v_snd_4600_);
lean_inc(v_fst_4599_);
lean_dec(v_b_4591_);
v___x_4602_ = lean_box(0);
v_isShared_4603_ = v_isSharedCheck_4621_;
goto v_resetjp_4601_;
}
v_resetjp_4601_:
{
lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4607_; 
v___x_4604_ = lean_unsigned_to_nat(1u);
v___x_4605_ = lean_nat_add(v_a_4590_, v___x_4604_);
if (v_isShared_4603_ == 0)
{
v___x_4607_ = v___x_4602_;
goto v_reusejp_4606_;
}
else
{
lean_object* v_reuseFailAlloc_4620_; 
v_reuseFailAlloc_4620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4620_, 0, v_fst_4599_);
lean_ctor_set(v_reuseFailAlloc_4620_, 1, v_snd_4600_);
v___x_4607_ = v_reuseFailAlloc_4620_;
goto v_reusejp_4606_;
}
v_reusejp_4606_:
{
lean_object* v___x_4608_; 
lean_inc(v___x_4605_);
lean_inc_ref(v_f_4589_);
v___x_4608_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v___x_4587_, v_a_4588_, v_a_4590_, v_f_4589_, v___x_4605_, v___x_4607_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_);
if (lean_obj_tag(v___x_4608_) == 0)
{
lean_object* v_a_4609_; lean_object* v_fst_4610_; lean_object* v_snd_4611_; lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4619_; 
v_a_4609_ = lean_ctor_get(v___x_4608_, 0);
lean_inc(v_a_4609_);
lean_dec_ref_known(v___x_4608_, 1);
v_fst_4610_ = lean_ctor_get(v_a_4609_, 0);
v_snd_4611_ = lean_ctor_get(v_a_4609_, 1);
v_isSharedCheck_4619_ = !lean_is_exclusive(v_a_4609_);
if (v_isSharedCheck_4619_ == 0)
{
v___x_4613_ = v_a_4609_;
v_isShared_4614_ = v_isSharedCheck_4619_;
goto v_resetjp_4612_;
}
else
{
lean_inc(v_snd_4611_);
lean_inc(v_fst_4610_);
lean_dec(v_a_4609_);
v___x_4613_ = lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4619_;
goto v_resetjp_4612_;
}
v_resetjp_4612_:
{
lean_object* v___x_4616_; 
if (v_isShared_4614_ == 0)
{
v___x_4616_ = v___x_4613_;
goto v_reusejp_4615_;
}
else
{
lean_object* v_reuseFailAlloc_4618_; 
v_reuseFailAlloc_4618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4618_, 0, v_fst_4610_);
lean_ctor_set(v_reuseFailAlloc_4618_, 1, v_snd_4611_);
v___x_4616_ = v_reuseFailAlloc_4618_;
goto v_reusejp_4615_;
}
v_reusejp_4615_:
{
v_a_4590_ = v___x_4605_;
v_b_4591_ = v___x_4616_;
goto _start;
}
}
}
else
{
lean_dec(v___x_4605_);
lean_dec_ref(v_f_4589_);
return v___x_4608_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_4622_, lean_object* v___x_4623_, lean_object* v_a_4624_, lean_object* v_f_4625_, lean_object* v_a_4626_, lean_object* v_b_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_){
_start:
{
lean_object* v_res_4633_; 
v_res_4633_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v_upperBound_4622_, v___x_4623_, v_a_4624_, v_f_4625_, v_a_4626_, v_b_4627_, v___y_4628_, v___y_4629_, v___y_4630_, v___y_4631_);
lean_dec(v___y_4631_);
lean_dec_ref(v___y_4630_);
lean_dec(v___y_4629_);
lean_dec_ref(v___y_4628_);
lean_dec_ref(v_a_4624_);
lean_dec(v___x_4623_);
lean_dec(v_upperBound_4622_);
return v_res_4633_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0(lean_object* v___x_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_){
_start:
{
lean_object* v___x_4640_; 
v___x_4640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4640_, 0, v___x_4634_);
return v___x_4640_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed(lean_object* v___x_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_){
_start:
{
lean_object* v_res_4647_; 
v_res_4647_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0(v___x_4641_, v___y_4642_, v___y_4643_, v___y_4644_, v___y_4645_);
lean_dec(v___y_4645_);
lean_dec_ref(v___y_4644_);
lean_dec(v___y_4643_);
lean_dec_ref(v___y_4642_);
return v_res_4647_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(lean_object* v_upperBound_4648_, lean_object* v_removed_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_b_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_){
_start:
{
lean_object* v___y_4659_; uint8_t v___x_4682_; 
v___x_4682_ = lean_nat_dec_lt(v_a_4651_, v_upperBound_4648_);
if (v___x_4682_ == 0)
{
lean_object* v___x_4683_; 
lean_dec(v_a_4651_);
v___x_4683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4683_, 0, v_b_4652_);
return v___x_4683_;
}
else
{
uint8_t v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; uint8_t v___x_4687_; 
v___x_4684_ = 0;
v___x_4685_ = lean_box(v___x_4684_);
v___x_4686_ = lean_array_get(v___x_4685_, v_removed_4649_, v_a_4651_);
lean_dec(v___x_4685_);
v___x_4687_ = lean_unbox(v___x_4686_);
lean_dec(v___x_4686_);
if (v___x_4687_ == 0)
{
lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___f_4691_; 
v___x_4688_ = lean_array_fget_borrowed(v_a_4650_, v_a_4651_);
lean_inc(v___x_4688_);
v___x_4689_ = lean_array_push(v_b_4652_, v___x_4688_);
v___x_4690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4690_, 0, v___x_4689_);
v___f_4691_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4691_, 0, v___x_4690_);
v___y_4659_ = v___f_4691_;
goto v___jp_4658_;
}
else
{
lean_object* v___x_4692_; lean_object* v___f_4693_; 
v___x_4692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4692_, 0, v_b_4652_);
v___f_4693_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4693_, 0, v___x_4692_);
v___y_4659_ = v___f_4693_;
goto v___jp_4658_;
}
}
v___jp_4658_:
{
lean_object* v___x_4660_; 
lean_inc(v___y_4656_);
lean_inc_ref(v___y_4655_);
lean_inc(v___y_4654_);
lean_inc_ref(v___y_4653_);
v___x_4660_ = lean_apply_5(v___y_4659_, v___y_4653_, v___y_4654_, v___y_4655_, v___y_4656_, lean_box(0));
if (lean_obj_tag(v___x_4660_) == 0)
{
lean_object* v_a_4661_; lean_object* v___x_4663_; uint8_t v_isShared_4664_; uint8_t v_isSharedCheck_4673_; 
v_a_4661_ = lean_ctor_get(v___x_4660_, 0);
v_isSharedCheck_4673_ = !lean_is_exclusive(v___x_4660_);
if (v_isSharedCheck_4673_ == 0)
{
v___x_4663_ = v___x_4660_;
v_isShared_4664_ = v_isSharedCheck_4673_;
goto v_resetjp_4662_;
}
else
{
lean_inc(v_a_4661_);
lean_dec(v___x_4660_);
v___x_4663_ = lean_box(0);
v_isShared_4664_ = v_isSharedCheck_4673_;
goto v_resetjp_4662_;
}
v_resetjp_4662_:
{
if (lean_obj_tag(v_a_4661_) == 0)
{
lean_object* v_a_4665_; lean_object* v___x_4667_; 
lean_dec(v_a_4651_);
v_a_4665_ = lean_ctor_get(v_a_4661_, 0);
lean_inc(v_a_4665_);
lean_dec_ref_known(v_a_4661_, 1);
if (v_isShared_4664_ == 0)
{
lean_ctor_set(v___x_4663_, 0, v_a_4665_);
v___x_4667_ = v___x_4663_;
goto v_reusejp_4666_;
}
else
{
lean_object* v_reuseFailAlloc_4668_; 
v_reuseFailAlloc_4668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4668_, 0, v_a_4665_);
v___x_4667_ = v_reuseFailAlloc_4668_;
goto v_reusejp_4666_;
}
v_reusejp_4666_:
{
return v___x_4667_;
}
}
else
{
lean_object* v_a_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; 
lean_del_object(v___x_4663_);
v_a_4669_ = lean_ctor_get(v_a_4661_, 0);
lean_inc(v_a_4669_);
lean_dec_ref_known(v_a_4661_, 1);
v___x_4670_ = lean_unsigned_to_nat(1u);
v___x_4671_ = lean_nat_add(v_a_4651_, v___x_4670_);
lean_dec(v_a_4651_);
v_a_4651_ = v___x_4671_;
v_b_4652_ = v_a_4669_;
goto _start;
}
}
}
else
{
lean_object* v_a_4674_; lean_object* v___x_4676_; uint8_t v_isShared_4677_; uint8_t v_isSharedCheck_4681_; 
lean_dec(v_a_4651_);
v_a_4674_ = lean_ctor_get(v___x_4660_, 0);
v_isSharedCheck_4681_ = !lean_is_exclusive(v___x_4660_);
if (v_isSharedCheck_4681_ == 0)
{
v___x_4676_ = v___x_4660_;
v_isShared_4677_ = v_isSharedCheck_4681_;
goto v_resetjp_4675_;
}
else
{
lean_inc(v_a_4674_);
lean_dec(v___x_4660_);
v___x_4676_ = lean_box(0);
v_isShared_4677_ = v_isSharedCheck_4681_;
goto v_resetjp_4675_;
}
v_resetjp_4675_:
{
lean_object* v___x_4679_; 
if (v_isShared_4677_ == 0)
{
v___x_4679_ = v___x_4676_;
goto v_reusejp_4678_;
}
else
{
lean_object* v_reuseFailAlloc_4680_; 
v_reuseFailAlloc_4680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4680_, 0, v_a_4674_);
v___x_4679_ = v_reuseFailAlloc_4680_;
goto v_reusejp_4678_;
}
v_reusejp_4678_:
{
return v___x_4679_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___boxed(lean_object* v_upperBound_4694_, lean_object* v_removed_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_b_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_){
_start:
{
lean_object* v_res_4704_; 
v_res_4704_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v_upperBound_4694_, v_removed_4695_, v_a_4696_, v_a_4697_, v_b_4698_, v___y_4699_, v___y_4700_, v___y_4701_, v___y_4702_);
lean_dec(v___y_4702_);
lean_dec_ref(v___y_4701_);
lean_dec(v___y_4700_);
lean_dec_ref(v___y_4699_);
lean_dec_ref(v_a_4696_);
lean_dec_ref(v_removed_4695_);
lean_dec(v_upperBound_4694_);
return v_res_4704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(lean_object* v_a_4705_, lean_object* v_f_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_){
_start:
{
lean_object* v___x_4712_; uint8_t v___x_4713_; lean_object* v___x_4714_; lean_object* v_removed_4715_; lean_object* v_numRemoved_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; 
v___x_4712_ = lean_array_get_size(v_a_4705_);
v___x_4713_ = 0;
v___x_4714_ = lean_box(v___x_4713_);
v_removed_4715_ = lean_mk_array(v___x_4712_, v___x_4714_);
v_numRemoved_4716_ = lean_unsigned_to_nat(0u);
v___x_4717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4717_, 0, v_removed_4715_);
lean_ctor_set(v___x_4717_, 1, v_numRemoved_4716_);
v___x_4718_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v___x_4712_, v___x_4712_, v_a_4705_, v_f_4706_, v_numRemoved_4716_, v___x_4717_, v___y_4707_, v___y_4708_, v___y_4709_, v___y_4710_);
if (lean_obj_tag(v___x_4718_) == 0)
{
lean_object* v_a_4719_; lean_object* v_fst_4720_; lean_object* v_snd_4721_; lean_object* v_a_x27_4722_; lean_object* v___x_4723_; 
v_a_4719_ = lean_ctor_get(v___x_4718_, 0);
lean_inc(v_a_4719_);
lean_dec_ref_known(v___x_4718_, 1);
v_fst_4720_ = lean_ctor_get(v_a_4719_, 0);
lean_inc(v_fst_4720_);
v_snd_4721_ = lean_ctor_get(v_a_4719_, 1);
lean_inc(v_snd_4721_);
lean_dec(v_a_4719_);
v_a_x27_4722_ = lean_mk_empty_array_with_capacity(v_snd_4721_);
lean_dec(v_snd_4721_);
v___x_4723_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v___x_4712_, v_fst_4720_, v_a_4705_, v_numRemoved_4716_, v_a_x27_4722_, v___y_4707_, v___y_4708_, v___y_4709_, v___y_4710_);
lean_dec(v_fst_4720_);
return v___x_4723_;
}
else
{
lean_object* v_a_4724_; lean_object* v___x_4726_; uint8_t v_isShared_4727_; uint8_t v_isSharedCheck_4731_; 
v_a_4724_ = lean_ctor_get(v___x_4718_, 0);
v_isSharedCheck_4731_ = !lean_is_exclusive(v___x_4718_);
if (v_isSharedCheck_4731_ == 0)
{
v___x_4726_ = v___x_4718_;
v_isShared_4727_ = v_isSharedCheck_4731_;
goto v_resetjp_4725_;
}
else
{
lean_inc(v_a_4724_);
lean_dec(v___x_4718_);
v___x_4726_ = lean_box(0);
v_isShared_4727_ = v_isSharedCheck_4731_;
goto v_resetjp_4725_;
}
v_resetjp_4725_:
{
lean_object* v___x_4729_; 
if (v_isShared_4727_ == 0)
{
v___x_4729_ = v___x_4726_;
goto v_reusejp_4728_;
}
else
{
lean_object* v_reuseFailAlloc_4730_; 
v_reuseFailAlloc_4730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4730_, 0, v_a_4724_);
v___x_4729_ = v_reuseFailAlloc_4730_;
goto v_reusejp_4728_;
}
v_reusejp_4728_:
{
return v___x_4729_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg___boxed(lean_object* v_a_4732_, lean_object* v_f_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_){
_start:
{
lean_object* v_res_4739_; 
v_res_4739_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_a_4732_, v_f_4733_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_);
lean_dec(v___y_4737_);
lean_dec_ref(v___y_4736_);
lean_dec(v___y_4735_);
lean_dec_ref(v___y_4734_);
lean_dec_ref(v_a_4732_);
return v_res_4739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed(lean_object* v_mvars_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_){
_start:
{
lean_object* v___f_4747_; lean_object* v___x_4748_; 
v___f_4747_ = ((lean_object*)(l_Lean_Elab_WF_assignSubsumed___closed__0));
v___x_4748_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_mvars_4741_, v___f_4747_, v_a_4742_, v_a_4743_, v_a_4744_, v_a_4745_);
return v___x_4748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___boxed(lean_object* v_mvars_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_){
_start:
{
lean_object* v_res_4755_; 
v_res_4755_ = l_Lean_Elab_WF_assignSubsumed(v_mvars_4749_, v_a_4750_, v_a_4751_, v_a_4752_, v_a_4753_);
lean_dec(v_a_4753_);
lean_dec_ref(v_a_4752_);
lean_dec(v_a_4751_);
lean_dec_ref(v_a_4750_);
lean_dec_ref(v_mvars_4749_);
return v_res_4755_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0(lean_object* v_mvarId_4756_, lean_object* v_val_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_){
_start:
{
lean_object* v___x_4763_; 
v___x_4763_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mvarId_4756_, v_val_4757_, v___y_4759_);
return v___x_4763_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___boxed(lean_object* v_mvarId_4764_, lean_object* v_val_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_, lean_object* v___y_4768_, lean_object* v___y_4769_, lean_object* v___y_4770_){
_start:
{
lean_object* v_res_4771_; 
v_res_4771_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0(v_mvarId_4764_, v_val_4765_, v___y_4766_, v___y_4767_, v___y_4768_, v___y_4769_);
lean_dec(v___y_4769_);
lean_dec_ref(v___y_4768_);
lean_dec(v___y_4767_);
lean_dec_ref(v___y_4766_);
return v_res_4771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1(lean_object* v_00_u03b1_4772_, lean_object* v_a_4773_, lean_object* v_f_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_){
_start:
{
lean_object* v___x_4780_; 
v___x_4780_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_a_4773_, v_f_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_);
return v___x_4780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___boxed(lean_object* v_00_u03b1_4781_, lean_object* v_a_4782_, lean_object* v_f_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_){
_start:
{
lean_object* v_res_4789_; 
v_res_4789_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1(v_00_u03b1_4781_, v_a_4782_, v_f_4783_, v___y_4784_, v___y_4785_, v___y_4786_, v___y_4787_);
lean_dec(v___y_4787_);
lean_dec_ref(v___y_4786_);
lean_dec(v___y_4785_);
lean_dec_ref(v___y_4784_);
lean_dec_ref(v_a_4782_);
return v_res_4789_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0(lean_object* v_00_u03b2_4790_, lean_object* v_x_4791_, lean_object* v_x_4792_, lean_object* v_x_4793_){
_start:
{
lean_object* v___x_4794_; 
v___x_4794_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(v_x_4791_, v_x_4792_, v_x_4793_);
return v___x_4794_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2(lean_object* v_upperBound_4795_, lean_object* v_00_u03b1_4796_, lean_object* v_a_4797_, lean_object* v_next_4798_, lean_object* v_f_4799_, lean_object* v_inst_4800_, lean_object* v_R_4801_, lean_object* v_a_4802_, lean_object* v_b_4803_, lean_object* v_c_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_){
_start:
{
lean_object* v___x_4810_; 
v___x_4810_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v_upperBound_4795_, v_a_4797_, v_next_4798_, v_f_4799_, v_a_4802_, v_b_4803_, v___y_4805_, v___y_4806_, v___y_4807_, v___y_4808_);
return v___x_4810_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___boxed(lean_object* v_upperBound_4811_, lean_object* v_00_u03b1_4812_, lean_object* v_a_4813_, lean_object* v_next_4814_, lean_object* v_f_4815_, lean_object* v_inst_4816_, lean_object* v_R_4817_, lean_object* v_a_4818_, lean_object* v_b_4819_, lean_object* v_c_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_){
_start:
{
lean_object* v_res_4826_; 
v_res_4826_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2(v_upperBound_4811_, v_00_u03b1_4812_, v_a_4813_, v_next_4814_, v_f_4815_, v_inst_4816_, v_R_4817_, v_a_4818_, v_b_4819_, v_c_4820_, v___y_4821_, v___y_4822_, v___y_4823_, v___y_4824_);
lean_dec(v___y_4824_);
lean_dec_ref(v___y_4823_);
lean_dec(v___y_4822_);
lean_dec_ref(v___y_4821_);
lean_dec_ref(v_a_4813_);
lean_dec(v_upperBound_4811_);
return v_res_4826_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3(lean_object* v_00_u03b1_4827_, lean_object* v_upperBound_4828_, lean_object* v_removed_4829_, lean_object* v_a_4830_, lean_object* v_inst_4831_, lean_object* v_R_4832_, lean_object* v_a_4833_, lean_object* v_b_4834_, lean_object* v_c_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_){
_start:
{
lean_object* v___x_4841_; 
v___x_4841_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v_upperBound_4828_, v_removed_4829_, v_a_4830_, v_a_4833_, v_b_4834_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_);
return v___x_4841_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___boxed(lean_object* v_00_u03b1_4842_, lean_object* v_upperBound_4843_, lean_object* v_removed_4844_, lean_object* v_a_4845_, lean_object* v_inst_4846_, lean_object* v_R_4847_, lean_object* v_a_4848_, lean_object* v_b_4849_, lean_object* v_c_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_){
_start:
{
lean_object* v_res_4856_; 
v_res_4856_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3(v_00_u03b1_4842_, v_upperBound_4843_, v_removed_4844_, v_a_4845_, v_inst_4846_, v_R_4847_, v_a_4848_, v_b_4849_, v_c_4850_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_);
lean_dec(v___y_4854_);
lean_dec_ref(v___y_4853_);
lean_dec(v___y_4852_);
lean_dec_ref(v___y_4851_);
lean_dec_ref(v_a_4845_);
lean_dec_ref(v_removed_4844_);
lean_dec(v_upperBound_4843_);
return v_res_4856_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4(lean_object* v_upperBound_4857_, lean_object* v___x_4858_, lean_object* v_00_u03b1_4859_, lean_object* v_a_4860_, lean_object* v_f_4861_, lean_object* v_inst_4862_, lean_object* v_R_4863_, lean_object* v_a_4864_, lean_object* v_b_4865_, lean_object* v_c_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_){
_start:
{
lean_object* v___x_4872_; 
v___x_4872_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v_upperBound_4857_, v___x_4858_, v_a_4860_, v_f_4861_, v_a_4864_, v_b_4865_, v___y_4867_, v___y_4868_, v___y_4869_, v___y_4870_);
return v___x_4872_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___boxed(lean_object* v_upperBound_4873_, lean_object* v___x_4874_, lean_object* v_00_u03b1_4875_, lean_object* v_a_4876_, lean_object* v_f_4877_, lean_object* v_inst_4878_, lean_object* v_R_4879_, lean_object* v_a_4880_, lean_object* v_b_4881_, lean_object* v_c_4882_, lean_object* v___y_4883_, lean_object* v___y_4884_, lean_object* v___y_4885_, lean_object* v___y_4886_, lean_object* v___y_4887_){
_start:
{
lean_object* v_res_4888_; 
v_res_4888_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4(v_upperBound_4873_, v___x_4874_, v_00_u03b1_4875_, v_a_4876_, v_f_4877_, v_inst_4878_, v_R_4879_, v_a_4880_, v_b_4881_, v_c_4882_, v___y_4883_, v___y_4884_, v___y_4885_, v___y_4886_);
lean_dec(v___y_4886_);
lean_dec_ref(v___y_4885_);
lean_dec(v___y_4884_);
lean_dec_ref(v___y_4883_);
lean_dec_ref(v_a_4876_);
lean_dec(v___x_4874_);
lean_dec(v_upperBound_4873_);
return v_res_4888_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4889_, lean_object* v_x_4890_, size_t v_x_4891_, size_t v_x_4892_, lean_object* v_x_4893_, lean_object* v_x_4894_){
_start:
{
lean_object* v___x_4895_; 
v___x_4895_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4890_, v_x_4891_, v_x_4892_, v_x_4893_, v_x_4894_);
return v___x_4895_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4896_, lean_object* v_x_4897_, lean_object* v_x_4898_, lean_object* v_x_4899_, lean_object* v_x_4900_, lean_object* v_x_4901_){
_start:
{
size_t v_x_4928__boxed_4902_; size_t v_x_4929__boxed_4903_; lean_object* v_res_4904_; 
v_x_4928__boxed_4902_ = lean_unbox_usize(v_x_4898_);
lean_dec(v_x_4898_);
v_x_4929__boxed_4903_ = lean_unbox_usize(v_x_4899_);
lean_dec(v_x_4899_);
v_res_4904_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1(v_00_u03b2_4896_, v_x_4897_, v_x_4928__boxed_4902_, v_x_4929__boxed_4903_, v_x_4900_, v_x_4901_);
return v_res_4904_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_4905_, lean_object* v_n_4906_, lean_object* v_k_4907_, lean_object* v_v_4908_){
_start:
{
lean_object* v___x_4909_; 
v___x_4909_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(v_n_4906_, v_k_4907_, v_v_4908_);
return v___x_4909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_4910_, size_t v_depth_4911_, lean_object* v_keys_4912_, lean_object* v_vals_4913_, lean_object* v_heq_4914_, lean_object* v_i_4915_, lean_object* v_entries_4916_){
_start:
{
lean_object* v___x_4917_; 
v___x_4917_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_4911_, v_keys_4912_, v_vals_4913_, v_i_4915_, v_entries_4916_);
return v___x_4917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_4918_, lean_object* v_depth_4919_, lean_object* v_keys_4920_, lean_object* v_vals_4921_, lean_object* v_heq_4922_, lean_object* v_i_4923_, lean_object* v_entries_4924_){
_start:
{
size_t v_depth_boxed_4925_; lean_object* v_res_4926_; 
v_depth_boxed_4925_ = lean_unbox_usize(v_depth_4919_);
lean_dec(v_depth_4919_);
v_res_4926_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_4918_, v_depth_boxed_4925_, v_keys_4920_, v_vals_4921_, v_heq_4922_, v_i_4923_, v_entries_4924_);
lean_dec_ref(v_vals_4921_);
lean_dec_ref(v_keys_4920_);
return v_res_4926_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_4927_, lean_object* v_x_4928_, lean_object* v_x_4929_, lean_object* v_x_4930_, lean_object* v_x_4931_){
_start:
{
lean_object* v___x_4932_; 
v___x_4932_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_x_4928_, v_x_4929_, v_x_4930_, v_x_4931_);
return v___x_4932_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4934_; lean_object* v___x_4935_; 
v___x_4934_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__0));
v___x_4935_ = l_Lean_stringToMessageData(v___x_4934_);
return v___x_4935_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4937_; lean_object* v___x_4938_; 
v___x_4937_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__2));
v___x_4938_ = l_Lean_stringToMessageData(v___x_4937_);
return v___x_4938_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(lean_object* v_argsPacker_4939_, lean_object* v_as_4940_, size_t v_sz_4941_, size_t v_i_4942_, lean_object* v_b_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_){
_start:
{
lean_object* v_a_4950_; uint8_t v___x_4954_; 
v___x_4954_ = lean_usize_dec_lt(v_i_4942_, v_sz_4941_);
if (v___x_4954_ == 0)
{
lean_object* v___x_4955_; 
v___x_4955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4955_, 0, v_b_4943_);
return v___x_4955_;
}
else
{
lean_object* v_a_4956_; lean_object* v___x_4957_; 
v_a_4956_ = lean_array_uget_borrowed(v_as_4940_, v_i_4942_);
lean_inc(v_a_4956_);
v___x_4957_ = l_Lean_MVarId_getType(v_a_4956_, v___y_4944_, v___y_4945_, v___y_4946_, v___y_4947_);
if (lean_obj_tag(v___x_4957_) == 0)
{
lean_object* v_a_4958_; lean_object* v___y_4960_; lean_object* v___y_4961_; lean_object* v___y_4962_; lean_object* v___y_4963_; 
v_a_4958_ = lean_ctor_get(v___x_4957_, 0);
lean_inc(v_a_4958_);
lean_dec_ref_known(v___x_4957_, 1);
if (lean_obj_tag(v_a_4958_) == 10)
{
lean_object* v_expr_4976_; 
v_expr_4976_ = lean_ctor_get(v_a_4958_, 1);
if (lean_obj_tag(v_expr_4976_) == 5)
{
lean_object* v_arg_4977_; lean_object* v___x_4978_; 
lean_inc_ref(v_expr_4976_);
lean_dec_ref_known(v_a_4958_, 2);
v_arg_4977_ = lean_ctor_get(v_expr_4976_, 1);
lean_inc_ref_n(v_arg_4977_, 2);
lean_dec_ref_known(v_expr_4976_, 2);
v___x_4978_ = l_Lean_Meta_ArgsPacker_unpack(v_argsPacker_4939_, v_arg_4977_);
if (lean_obj_tag(v___x_4978_) == 1)
{
lean_object* v_val_4979_; lean_object* v_fst_4980_; lean_object* v___x_4981_; uint8_t v___x_4982_; 
lean_dec_ref(v_arg_4977_);
v_val_4979_ = lean_ctor_get(v___x_4978_, 0);
lean_inc(v_val_4979_);
lean_dec_ref_known(v___x_4978_, 1);
v_fst_4980_ = lean_ctor_get(v_val_4979_, 0);
lean_inc(v_fst_4980_);
lean_dec(v_val_4979_);
v___x_4981_ = lean_array_get_size(v_b_4943_);
v___x_4982_ = lean_nat_dec_lt(v_fst_4980_, v___x_4981_);
if (v___x_4982_ == 0)
{
lean_dec(v_fst_4980_);
v_a_4950_ = v_b_4943_;
goto v___jp_4949_;
}
else
{
lean_object* v_v_4983_; lean_object* v___x_4984_; lean_object* v_xs_x27_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; 
v_v_4983_ = lean_array_fget(v_b_4943_, v_fst_4980_);
v___x_4984_ = lean_box(0);
v_xs_x27_4985_ = lean_array_fset(v_b_4943_, v_fst_4980_, v___x_4984_);
lean_inc(v_a_4956_);
v___x_4986_ = lean_array_push(v_v_4983_, v_a_4956_);
v___x_4987_ = lean_array_fset(v_xs_x27_4985_, v_fst_4980_, v___x_4986_);
lean_dec(v_fst_4980_);
v_a_4950_ = v___x_4987_;
goto v___jp_4949_;
}
}
else
{
lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; 
lean_dec(v___x_4978_);
v___x_4988_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3);
v___x_4989_ = l_Lean_indentExpr(v_arg_4977_);
v___x_4990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4990_, 0, v___x_4988_);
lean_ctor_set(v___x_4990_, 1, v___x_4989_);
v___x_4991_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v___x_4990_, v___y_4944_, v___y_4945_, v___y_4946_, v___y_4947_);
if (lean_obj_tag(v___x_4991_) == 0)
{
lean_dec_ref_known(v___x_4991_, 1);
v_a_4950_ = v_b_4943_;
goto v___jp_4949_;
}
else
{
lean_object* v_a_4992_; lean_object* v___x_4994_; uint8_t v_isShared_4995_; uint8_t v_isSharedCheck_4999_; 
lean_dec_ref(v_b_4943_);
v_a_4992_ = lean_ctor_get(v___x_4991_, 0);
v_isSharedCheck_4999_ = !lean_is_exclusive(v___x_4991_);
if (v_isSharedCheck_4999_ == 0)
{
v___x_4994_ = v___x_4991_;
v_isShared_4995_ = v_isSharedCheck_4999_;
goto v_resetjp_4993_;
}
else
{
lean_inc(v_a_4992_);
lean_dec(v___x_4991_);
v___x_4994_ = lean_box(0);
v_isShared_4995_ = v_isSharedCheck_4999_;
goto v_resetjp_4993_;
}
v_resetjp_4993_:
{
lean_object* v___x_4997_; 
if (v_isShared_4995_ == 0)
{
v___x_4997_ = v___x_4994_;
goto v_reusejp_4996_;
}
else
{
lean_object* v_reuseFailAlloc_4998_; 
v_reuseFailAlloc_4998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4998_, 0, v_a_4992_);
v___x_4997_ = v_reuseFailAlloc_4998_;
goto v_reusejp_4996_;
}
v_reusejp_4996_:
{
return v___x_4997_;
}
}
}
}
}
else
{
v___y_4960_ = v___y_4944_;
v___y_4961_ = v___y_4945_;
v___y_4962_ = v___y_4946_;
v___y_4963_ = v___y_4947_;
goto v___jp_4959_;
}
}
else
{
v___y_4960_ = v___y_4944_;
v___y_4961_ = v___y_4945_;
v___y_4962_ = v___y_4946_;
v___y_4963_ = v___y_4947_;
goto v___jp_4959_;
}
v___jp_4959_:
{
lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; 
v___x_4964_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1);
v___x_4965_ = l_Lean_indentExpr(v_a_4958_);
v___x_4966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4966_, 0, v___x_4964_);
lean_ctor_set(v___x_4966_, 1, v___x_4965_);
v___x_4967_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v___x_4966_, v___y_4960_, v___y_4961_, v___y_4962_, v___y_4963_);
if (lean_obj_tag(v___x_4967_) == 0)
{
lean_dec_ref_known(v___x_4967_, 1);
v_a_4950_ = v_b_4943_;
goto v___jp_4949_;
}
else
{
lean_object* v_a_4968_; lean_object* v___x_4970_; uint8_t v_isShared_4971_; uint8_t v_isSharedCheck_4975_; 
lean_dec_ref(v_b_4943_);
v_a_4968_ = lean_ctor_get(v___x_4967_, 0);
v_isSharedCheck_4975_ = !lean_is_exclusive(v___x_4967_);
if (v_isSharedCheck_4975_ == 0)
{
v___x_4970_ = v___x_4967_;
v_isShared_4971_ = v_isSharedCheck_4975_;
goto v_resetjp_4969_;
}
else
{
lean_inc(v_a_4968_);
lean_dec(v___x_4967_);
v___x_4970_ = lean_box(0);
v_isShared_4971_ = v_isSharedCheck_4975_;
goto v_resetjp_4969_;
}
v_resetjp_4969_:
{
lean_object* v___x_4973_; 
if (v_isShared_4971_ == 0)
{
v___x_4973_ = v___x_4970_;
goto v_reusejp_4972_;
}
else
{
lean_object* v_reuseFailAlloc_4974_; 
v_reuseFailAlloc_4974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4974_, 0, v_a_4968_);
v___x_4973_ = v_reuseFailAlloc_4974_;
goto v_reusejp_4972_;
}
v_reusejp_4972_:
{
return v___x_4973_;
}
}
}
}
}
else
{
lean_object* v_a_5000_; lean_object* v___x_5002_; uint8_t v_isShared_5003_; uint8_t v_isSharedCheck_5007_; 
lean_dec_ref(v_b_4943_);
v_a_5000_ = lean_ctor_get(v___x_4957_, 0);
v_isSharedCheck_5007_ = !lean_is_exclusive(v___x_4957_);
if (v_isSharedCheck_5007_ == 0)
{
v___x_5002_ = v___x_4957_;
v_isShared_5003_ = v_isSharedCheck_5007_;
goto v_resetjp_5001_;
}
else
{
lean_inc(v_a_5000_);
lean_dec(v___x_4957_);
v___x_5002_ = lean_box(0);
v_isShared_5003_ = v_isSharedCheck_5007_;
goto v_resetjp_5001_;
}
v_resetjp_5001_:
{
lean_object* v___x_5005_; 
if (v_isShared_5003_ == 0)
{
v___x_5005_ = v___x_5002_;
goto v_reusejp_5004_;
}
else
{
lean_object* v_reuseFailAlloc_5006_; 
v_reuseFailAlloc_5006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5006_, 0, v_a_5000_);
v___x_5005_ = v_reuseFailAlloc_5006_;
goto v_reusejp_5004_;
}
v_reusejp_5004_:
{
return v___x_5005_;
}
}
}
}
v___jp_4949_:
{
size_t v___x_4951_; size_t v___x_4952_; 
v___x_4951_ = ((size_t)1ULL);
v___x_4952_ = lean_usize_add(v_i_4942_, v___x_4951_);
v_i_4942_ = v___x_4952_;
v_b_4943_ = v_a_4950_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___boxed(lean_object* v_argsPacker_5008_, lean_object* v_as_5009_, lean_object* v_sz_5010_, lean_object* v_i_5011_, lean_object* v_b_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_){
_start:
{
size_t v_sz_boxed_5018_; size_t v_i_boxed_5019_; lean_object* v_res_5020_; 
v_sz_boxed_5018_ = lean_unbox_usize(v_sz_5010_);
lean_dec(v_sz_5010_);
v_i_boxed_5019_ = lean_unbox_usize(v_i_5011_);
lean_dec(v_i_5011_);
v_res_5020_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(v_argsPacker_5008_, v_as_5009_, v_sz_boxed_5018_, v_i_boxed_5019_, v_b_5012_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_);
lean_dec(v___y_5016_);
lean_dec_ref(v___y_5015_);
lean_dec(v___y_5014_);
lean_dec_ref(v___y_5013_);
lean_dec_ref(v_as_5009_);
lean_dec_ref(v_argsPacker_5008_);
return v_res_5020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_groupGoalsByFunction(lean_object* v_argsPacker_5021_, lean_object* v_numFuncs_5022_, lean_object* v_goals_5023_, lean_object* v_a_5024_, lean_object* v_a_5025_, lean_object* v_a_5026_, lean_object* v_a_5027_){
_start:
{
lean_object* v___x_5029_; lean_object* v_r_5030_; size_t v_sz_5031_; size_t v___x_5032_; lean_object* v___x_5033_; 
v___x_5029_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg___closed__0));
v_r_5030_ = lean_mk_array(v_numFuncs_5022_, v___x_5029_);
v_sz_5031_ = lean_array_size(v_goals_5023_);
v___x_5032_ = ((size_t)0ULL);
v___x_5033_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(v_argsPacker_5021_, v_goals_5023_, v_sz_5031_, v___x_5032_, v_r_5030_, v_a_5024_, v_a_5025_, v_a_5026_, v_a_5027_);
return v___x_5033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_groupGoalsByFunction___boxed(lean_object* v_argsPacker_5034_, lean_object* v_numFuncs_5035_, lean_object* v_goals_5036_, lean_object* v_a_5037_, lean_object* v_a_5038_, lean_object* v_a_5039_, lean_object* v_a_5040_, lean_object* v_a_5041_){
_start:
{
lean_object* v_res_5042_; 
v_res_5042_ = l_Lean_Elab_WF_groupGoalsByFunction(v_argsPacker_5034_, v_numFuncs_5035_, v_goals_5036_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_);
lean_dec(v_a_5040_);
lean_dec_ref(v_a_5039_);
lean_dec(v_a_5038_);
lean_dec_ref(v_a_5037_);
lean_dec_ref(v_goals_5036_);
lean_dec_ref(v_argsPacker_5034_);
return v_res_5042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(lean_object* v_t_5043_, lean_object* v___y_5044_){
_start:
{
lean_object* v___x_5046_; lean_object* v_infoState_5047_; uint8_t v_enabled_5048_; 
v___x_5046_ = lean_st_ref_get(v___y_5044_);
v_infoState_5047_ = lean_ctor_get(v___x_5046_, 7);
lean_inc_ref(v_infoState_5047_);
lean_dec(v___x_5046_);
v_enabled_5048_ = lean_ctor_get_uint8(v_infoState_5047_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5047_);
if (v_enabled_5048_ == 0)
{
lean_object* v___x_5049_; lean_object* v___x_5050_; 
lean_dec_ref(v_t_5043_);
v___x_5049_ = lean_box(0);
v___x_5050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5050_, 0, v___x_5049_);
return v___x_5050_;
}
else
{
lean_object* v___x_5051_; lean_object* v_infoState_5052_; lean_object* v_env_5053_; lean_object* v_nextMacroScope_5054_; lean_object* v_ngen_5055_; lean_object* v_auxDeclNGen_5056_; lean_object* v_traceState_5057_; lean_object* v_cache_5058_; lean_object* v_messages_5059_; lean_object* v_snapshotTasks_5060_; lean_object* v___x_5062_; uint8_t v_isShared_5063_; uint8_t v_isSharedCheck_5082_; 
v___x_5051_ = lean_st_ref_take(v___y_5044_);
v_infoState_5052_ = lean_ctor_get(v___x_5051_, 7);
v_env_5053_ = lean_ctor_get(v___x_5051_, 0);
v_nextMacroScope_5054_ = lean_ctor_get(v___x_5051_, 1);
v_ngen_5055_ = lean_ctor_get(v___x_5051_, 2);
v_auxDeclNGen_5056_ = lean_ctor_get(v___x_5051_, 3);
v_traceState_5057_ = lean_ctor_get(v___x_5051_, 4);
v_cache_5058_ = lean_ctor_get(v___x_5051_, 5);
v_messages_5059_ = lean_ctor_get(v___x_5051_, 6);
v_snapshotTasks_5060_ = lean_ctor_get(v___x_5051_, 8);
v_isSharedCheck_5082_ = !lean_is_exclusive(v___x_5051_);
if (v_isSharedCheck_5082_ == 0)
{
v___x_5062_ = v___x_5051_;
v_isShared_5063_ = v_isSharedCheck_5082_;
goto v_resetjp_5061_;
}
else
{
lean_inc(v_snapshotTasks_5060_);
lean_inc(v_infoState_5052_);
lean_inc(v_messages_5059_);
lean_inc(v_cache_5058_);
lean_inc(v_traceState_5057_);
lean_inc(v_auxDeclNGen_5056_);
lean_inc(v_ngen_5055_);
lean_inc(v_nextMacroScope_5054_);
lean_inc(v_env_5053_);
lean_dec(v___x_5051_);
v___x_5062_ = lean_box(0);
v_isShared_5063_ = v_isSharedCheck_5082_;
goto v_resetjp_5061_;
}
v_resetjp_5061_:
{
uint8_t v_enabled_5064_; lean_object* v_assignment_5065_; lean_object* v_lazyAssignment_5066_; lean_object* v_trees_5067_; lean_object* v___x_5069_; uint8_t v_isShared_5070_; uint8_t v_isSharedCheck_5081_; 
v_enabled_5064_ = lean_ctor_get_uint8(v_infoState_5052_, sizeof(void*)*3);
v_assignment_5065_ = lean_ctor_get(v_infoState_5052_, 0);
v_lazyAssignment_5066_ = lean_ctor_get(v_infoState_5052_, 1);
v_trees_5067_ = lean_ctor_get(v_infoState_5052_, 2);
v_isSharedCheck_5081_ = !lean_is_exclusive(v_infoState_5052_);
if (v_isSharedCheck_5081_ == 0)
{
v___x_5069_ = v_infoState_5052_;
v_isShared_5070_ = v_isSharedCheck_5081_;
goto v_resetjp_5068_;
}
else
{
lean_inc(v_trees_5067_);
lean_inc(v_lazyAssignment_5066_);
lean_inc(v_assignment_5065_);
lean_dec(v_infoState_5052_);
v___x_5069_ = lean_box(0);
v_isShared_5070_ = v_isSharedCheck_5081_;
goto v_resetjp_5068_;
}
v_resetjp_5068_:
{
lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5074_; 
v___x_5071_ = lean_box(0);
v___x_5072_ = l_Lean_PersistentArray_push___redArg(v_trees_5067_, v_t_5043_);
if (v_isShared_5070_ == 0)
{
lean_ctor_set(v___x_5069_, 2, v___x_5072_);
v___x_5074_ = v___x_5069_;
goto v_reusejp_5073_;
}
else
{
lean_object* v_reuseFailAlloc_5080_; 
v_reuseFailAlloc_5080_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5080_, 0, v_assignment_5065_);
lean_ctor_set(v_reuseFailAlloc_5080_, 1, v_lazyAssignment_5066_);
lean_ctor_set(v_reuseFailAlloc_5080_, 2, v___x_5072_);
lean_ctor_set_uint8(v_reuseFailAlloc_5080_, sizeof(void*)*3, v_enabled_5064_);
v___x_5074_ = v_reuseFailAlloc_5080_;
goto v_reusejp_5073_;
}
v_reusejp_5073_:
{
lean_object* v___x_5076_; 
if (v_isShared_5063_ == 0)
{
lean_ctor_set(v___x_5062_, 7, v___x_5074_);
v___x_5076_ = v___x_5062_;
goto v_reusejp_5075_;
}
else
{
lean_object* v_reuseFailAlloc_5079_; 
v_reuseFailAlloc_5079_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5079_, 0, v_env_5053_);
lean_ctor_set(v_reuseFailAlloc_5079_, 1, v_nextMacroScope_5054_);
lean_ctor_set(v_reuseFailAlloc_5079_, 2, v_ngen_5055_);
lean_ctor_set(v_reuseFailAlloc_5079_, 3, v_auxDeclNGen_5056_);
lean_ctor_set(v_reuseFailAlloc_5079_, 4, v_traceState_5057_);
lean_ctor_set(v_reuseFailAlloc_5079_, 5, v_cache_5058_);
lean_ctor_set(v_reuseFailAlloc_5079_, 6, v_messages_5059_);
lean_ctor_set(v_reuseFailAlloc_5079_, 7, v___x_5074_);
lean_ctor_set(v_reuseFailAlloc_5079_, 8, v_snapshotTasks_5060_);
v___x_5076_ = v_reuseFailAlloc_5079_;
goto v_reusejp_5075_;
}
v_reusejp_5075_:
{
lean_object* v___x_5077_; lean_object* v___x_5078_; 
v___x_5077_ = lean_st_ref_put(v___y_5044_, v___x_5076_);
v___x_5078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5078_, 0, v___x_5071_);
return v___x_5078_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg___boxed(lean_object* v_t_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_){
_start:
{
lean_object* v_res_5086_; 
v_res_5086_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v_t_5083_, v___y_5084_);
lean_dec(v___y_5084_);
return v_res_5086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0(lean_object* v_t_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_){
_start:
{
lean_object* v___x_5095_; 
v___x_5095_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v_t_5087_, v___y_5093_);
return v___x_5095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___boxed(lean_object* v_t_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_, lean_object* v___y_5101_, lean_object* v___y_5102_, lean_object* v___y_5103_){
_start:
{
lean_object* v_res_5104_; 
v_res_5104_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0(v_t_5096_, v___y_5097_, v___y_5098_, v___y_5099_, v___y_5100_, v___y_5101_, v___y_5102_);
lean_dec(v___y_5102_);
lean_dec_ref(v___y_5101_);
lean_dec(v___y_5100_);
lean_dec_ref(v___y_5099_);
lean_dec(v___y_5098_);
lean_dec_ref(v___y_5097_);
return v_res_5104_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(lean_object* v_e_5105_, lean_object* v___y_5106_){
_start:
{
uint8_t v___x_5108_; 
v___x_5108_ = l_Lean_Expr_hasMVar(v_e_5105_);
if (v___x_5108_ == 0)
{
lean_object* v___x_5109_; 
v___x_5109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5109_, 0, v_e_5105_);
return v___x_5109_;
}
else
{
lean_object* v___x_5110_; lean_object* v_mctx_5111_; lean_object* v___x_5112_; lean_object* v_fst_5113_; lean_object* v_snd_5114_; lean_object* v___x_5115_; lean_object* v_cache_5116_; lean_object* v_zetaDeltaFVarIds_5117_; lean_object* v_postponed_5118_; lean_object* v_diag_5119_; lean_object* v___x_5121_; uint8_t v_isShared_5122_; uint8_t v_isSharedCheck_5128_; 
v___x_5110_ = lean_st_ref_get(v___y_5106_);
v_mctx_5111_ = lean_ctor_get(v___x_5110_, 0);
lean_inc_ref(v_mctx_5111_);
lean_dec(v___x_5110_);
v___x_5112_ = l_Lean_instantiateMVarsCore(v_mctx_5111_, v_e_5105_);
v_fst_5113_ = lean_ctor_get(v___x_5112_, 0);
lean_inc(v_fst_5113_);
v_snd_5114_ = lean_ctor_get(v___x_5112_, 1);
lean_inc(v_snd_5114_);
lean_dec_ref(v___x_5112_);
v___x_5115_ = lean_st_ref_take(v___y_5106_);
v_cache_5116_ = lean_ctor_get(v___x_5115_, 1);
v_zetaDeltaFVarIds_5117_ = lean_ctor_get(v___x_5115_, 2);
v_postponed_5118_ = lean_ctor_get(v___x_5115_, 3);
v_diag_5119_ = lean_ctor_get(v___x_5115_, 4);
v_isSharedCheck_5128_ = !lean_is_exclusive(v___x_5115_);
if (v_isSharedCheck_5128_ == 0)
{
lean_object* v_unused_5129_; 
v_unused_5129_ = lean_ctor_get(v___x_5115_, 0);
lean_dec(v_unused_5129_);
v___x_5121_ = v___x_5115_;
v_isShared_5122_ = v_isSharedCheck_5128_;
goto v_resetjp_5120_;
}
else
{
lean_inc(v_diag_5119_);
lean_inc(v_postponed_5118_);
lean_inc(v_zetaDeltaFVarIds_5117_);
lean_inc(v_cache_5116_);
lean_dec(v___x_5115_);
v___x_5121_ = lean_box(0);
v_isShared_5122_ = v_isSharedCheck_5128_;
goto v_resetjp_5120_;
}
v_resetjp_5120_:
{
lean_object* v___x_5124_; 
if (v_isShared_5122_ == 0)
{
lean_ctor_set(v___x_5121_, 0, v_snd_5114_);
v___x_5124_ = v___x_5121_;
goto v_reusejp_5123_;
}
else
{
lean_object* v_reuseFailAlloc_5127_; 
v_reuseFailAlloc_5127_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5127_, 0, v_snd_5114_);
lean_ctor_set(v_reuseFailAlloc_5127_, 1, v_cache_5116_);
lean_ctor_set(v_reuseFailAlloc_5127_, 2, v_zetaDeltaFVarIds_5117_);
lean_ctor_set(v_reuseFailAlloc_5127_, 3, v_postponed_5118_);
lean_ctor_set(v_reuseFailAlloc_5127_, 4, v_diag_5119_);
v___x_5124_ = v_reuseFailAlloc_5127_;
goto v_reusejp_5123_;
}
v_reusejp_5123_:
{
lean_object* v___x_5125_; lean_object* v___x_5126_; 
v___x_5125_ = lean_st_ref_put(v___y_5106_, v___x_5124_);
v___x_5126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5126_, 0, v_fst_5113_);
return v___x_5126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg___boxed(lean_object* v_e_5130_, lean_object* v___y_5131_, lean_object* v___y_5132_){
_start:
{
lean_object* v_res_5133_; 
v_res_5133_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_e_5130_, v___y_5131_);
lean_dec(v___y_5131_);
return v_res_5133_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7(lean_object* v_e_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_){
_start:
{
lean_object* v___x_5140_; 
v___x_5140_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_e_5134_, v___y_5136_);
return v___x_5140_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___boxed(lean_object* v_e_5141_, lean_object* v___y_5142_, lean_object* v___y_5143_, lean_object* v___y_5144_, lean_object* v___y_5145_, lean_object* v___y_5146_){
_start:
{
lean_object* v_res_5147_; 
v_res_5147_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7(v_e_5141_, v___y_5142_, v___y_5143_, v___y_5144_, v___y_5145_);
lean_dec(v___y_5145_);
lean_dec_ref(v___y_5144_);
lean_dec(v___y_5143_);
lean_dec_ref(v___y_5142_);
return v_res_5147_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(lean_object* v_as_5148_, size_t v_i_5149_, size_t v_stop_5150_, lean_object* v_b_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_){
_start:
{
uint8_t v___x_5159_; 
v___x_5159_ = lean_usize_dec_eq(v_i_5149_, v_stop_5150_);
if (v___x_5159_ == 0)
{
lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; 
v___x_5160_ = lean_array_uget_borrowed(v_as_5148_, v_i_5149_);
lean_inc(v___x_5160_);
v___x_5161_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_5161_, 0, v___x_5160_);
v___x_5162_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v___x_5161_, v___y_5157_);
if (lean_obj_tag(v___x_5162_) == 0)
{
lean_object* v_a_5163_; size_t v___x_5164_; size_t v___x_5165_; 
v_a_5163_ = lean_ctor_get(v___x_5162_, 0);
lean_inc(v_a_5163_);
lean_dec_ref_known(v___x_5162_, 1);
v___x_5164_ = ((size_t)1ULL);
v___x_5165_ = lean_usize_add(v_i_5149_, v___x_5164_);
v_i_5149_ = v___x_5165_;
v_b_5151_ = v_a_5163_;
goto _start;
}
else
{
return v___x_5162_;
}
}
else
{
lean_object* v___x_5167_; 
v___x_5167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5167_, 0, v_b_5151_);
return v___x_5167_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4___boxed(lean_object* v_as_5168_, lean_object* v_i_5169_, lean_object* v_stop_5170_, lean_object* v_b_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_, lean_object* v___y_5174_, lean_object* v___y_5175_, lean_object* v___y_5176_, lean_object* v___y_5177_, lean_object* v___y_5178_){
_start:
{
size_t v_i_boxed_5179_; size_t v_stop_boxed_5180_; lean_object* v_res_5181_; 
v_i_boxed_5179_ = lean_unbox_usize(v_i_5169_);
lean_dec(v_i_5169_);
v_stop_boxed_5180_ = lean_unbox_usize(v_stop_5170_);
lean_dec(v_stop_5170_);
v_res_5181_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v_as_5168_, v_i_boxed_5179_, v_stop_boxed_5180_, v_b_5171_, v___y_5172_, v___y_5173_, v___y_5174_, v___y_5175_, v___y_5176_, v___y_5177_);
lean_dec(v___y_5177_);
lean_dec_ref(v___y_5176_);
lean_dec(v___y_5175_);
lean_dec_ref(v___y_5174_);
lean_dec(v___y_5173_);
lean_dec_ref(v___y_5172_);
lean_dec_ref(v_as_5168_);
return v_res_5181_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; 
v___x_5182_ = lean_unsigned_to_nat(32u);
v___x_5183_ = lean_mk_empty_array_with_capacity(v___x_5182_);
v___x_5184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5184_, 0, v___x_5183_);
return v___x_5184_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; 
v___x_5185_ = ((size_t)5ULL);
v___x_5186_ = lean_unsigned_to_nat(0u);
v___x_5187_ = lean_unsigned_to_nat(32u);
v___x_5188_ = lean_mk_empty_array_with_capacity(v___x_5187_);
v___x_5189_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0);
v___x_5190_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5190_, 0, v___x_5189_);
lean_ctor_set(v___x_5190_, 1, v___x_5188_);
lean_ctor_set(v___x_5190_, 2, v___x_5186_);
lean_ctor_set(v___x_5190_, 3, v___x_5186_);
lean_ctor_set_usize(v___x_5190_, 4, v___x_5185_);
return v___x_5190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(lean_object* v___y_5191_){
_start:
{
lean_object* v___x_5193_; lean_object* v_infoState_5194_; lean_object* v_trees_5195_; lean_object* v___x_5196_; lean_object* v_infoState_5197_; lean_object* v_env_5198_; lean_object* v_nextMacroScope_5199_; lean_object* v_ngen_5200_; lean_object* v_auxDeclNGen_5201_; lean_object* v_traceState_5202_; lean_object* v_cache_5203_; lean_object* v_messages_5204_; lean_object* v_snapshotTasks_5205_; lean_object* v___x_5207_; uint8_t v_isShared_5208_; uint8_t v_isSharedCheck_5226_; 
v___x_5193_ = lean_st_ref_get(v___y_5191_);
v_infoState_5194_ = lean_ctor_get(v___x_5193_, 7);
lean_inc_ref(v_infoState_5194_);
lean_dec(v___x_5193_);
v_trees_5195_ = lean_ctor_get(v_infoState_5194_, 2);
lean_inc_ref(v_trees_5195_);
lean_dec_ref(v_infoState_5194_);
v___x_5196_ = lean_st_ref_take(v___y_5191_);
v_infoState_5197_ = lean_ctor_get(v___x_5196_, 7);
v_env_5198_ = lean_ctor_get(v___x_5196_, 0);
v_nextMacroScope_5199_ = lean_ctor_get(v___x_5196_, 1);
v_ngen_5200_ = lean_ctor_get(v___x_5196_, 2);
v_auxDeclNGen_5201_ = lean_ctor_get(v___x_5196_, 3);
v_traceState_5202_ = lean_ctor_get(v___x_5196_, 4);
v_cache_5203_ = lean_ctor_get(v___x_5196_, 5);
v_messages_5204_ = lean_ctor_get(v___x_5196_, 6);
v_snapshotTasks_5205_ = lean_ctor_get(v___x_5196_, 8);
v_isSharedCheck_5226_ = !lean_is_exclusive(v___x_5196_);
if (v_isSharedCheck_5226_ == 0)
{
v___x_5207_ = v___x_5196_;
v_isShared_5208_ = v_isSharedCheck_5226_;
goto v_resetjp_5206_;
}
else
{
lean_inc(v_snapshotTasks_5205_);
lean_inc(v_infoState_5197_);
lean_inc(v_messages_5204_);
lean_inc(v_cache_5203_);
lean_inc(v_traceState_5202_);
lean_inc(v_auxDeclNGen_5201_);
lean_inc(v_ngen_5200_);
lean_inc(v_nextMacroScope_5199_);
lean_inc(v_env_5198_);
lean_dec(v___x_5196_);
v___x_5207_ = lean_box(0);
v_isShared_5208_ = v_isSharedCheck_5226_;
goto v_resetjp_5206_;
}
v_resetjp_5206_:
{
uint8_t v_enabled_5209_; lean_object* v_assignment_5210_; lean_object* v_lazyAssignment_5211_; lean_object* v___x_5213_; uint8_t v_isShared_5214_; uint8_t v_isSharedCheck_5224_; 
v_enabled_5209_ = lean_ctor_get_uint8(v_infoState_5197_, sizeof(void*)*3);
v_assignment_5210_ = lean_ctor_get(v_infoState_5197_, 0);
v_lazyAssignment_5211_ = lean_ctor_get(v_infoState_5197_, 1);
v_isSharedCheck_5224_ = !lean_is_exclusive(v_infoState_5197_);
if (v_isSharedCheck_5224_ == 0)
{
lean_object* v_unused_5225_; 
v_unused_5225_ = lean_ctor_get(v_infoState_5197_, 2);
lean_dec(v_unused_5225_);
v___x_5213_ = v_infoState_5197_;
v_isShared_5214_ = v_isSharedCheck_5224_;
goto v_resetjp_5212_;
}
else
{
lean_inc(v_lazyAssignment_5211_);
lean_inc(v_assignment_5210_);
lean_dec(v_infoState_5197_);
v___x_5213_ = lean_box(0);
v_isShared_5214_ = v_isSharedCheck_5224_;
goto v_resetjp_5212_;
}
v_resetjp_5212_:
{
lean_object* v___x_5215_; lean_object* v___x_5217_; 
v___x_5215_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1);
if (v_isShared_5214_ == 0)
{
lean_ctor_set(v___x_5213_, 2, v___x_5215_);
v___x_5217_ = v___x_5213_;
goto v_reusejp_5216_;
}
else
{
lean_object* v_reuseFailAlloc_5223_; 
v_reuseFailAlloc_5223_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5223_, 0, v_assignment_5210_);
lean_ctor_set(v_reuseFailAlloc_5223_, 1, v_lazyAssignment_5211_);
lean_ctor_set(v_reuseFailAlloc_5223_, 2, v___x_5215_);
lean_ctor_set_uint8(v_reuseFailAlloc_5223_, sizeof(void*)*3, v_enabled_5209_);
v___x_5217_ = v_reuseFailAlloc_5223_;
goto v_reusejp_5216_;
}
v_reusejp_5216_:
{
lean_object* v___x_5219_; 
if (v_isShared_5208_ == 0)
{
lean_ctor_set(v___x_5207_, 7, v___x_5217_);
v___x_5219_ = v___x_5207_;
goto v_reusejp_5218_;
}
else
{
lean_object* v_reuseFailAlloc_5222_; 
v_reuseFailAlloc_5222_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5222_, 0, v_env_5198_);
lean_ctor_set(v_reuseFailAlloc_5222_, 1, v_nextMacroScope_5199_);
lean_ctor_set(v_reuseFailAlloc_5222_, 2, v_ngen_5200_);
lean_ctor_set(v_reuseFailAlloc_5222_, 3, v_auxDeclNGen_5201_);
lean_ctor_set(v_reuseFailAlloc_5222_, 4, v_traceState_5202_);
lean_ctor_set(v_reuseFailAlloc_5222_, 5, v_cache_5203_);
lean_ctor_set(v_reuseFailAlloc_5222_, 6, v_messages_5204_);
lean_ctor_set(v_reuseFailAlloc_5222_, 7, v___x_5217_);
lean_ctor_set(v_reuseFailAlloc_5222_, 8, v_snapshotTasks_5205_);
v___x_5219_ = v_reuseFailAlloc_5222_;
goto v_reusejp_5218_;
}
v_reusejp_5218_:
{
lean_object* v___x_5220_; lean_object* v___x_5221_; 
v___x_5220_ = lean_st_ref_put(v___y_5191_, v___x_5219_);
v___x_5221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5221_, 0, v_trees_5195_);
return v___x_5221_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___boxed(lean_object* v___y_5227_, lean_object* v___y_5228_){
_start:
{
lean_object* v_res_5229_; 
v_res_5229_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_5227_);
lean_dec(v___y_5227_);
return v_res_5229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(lean_object* v___y_5230_, lean_object* v_mkInfoTree_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_, lean_object* v_a_5239_, lean_object* v_a_x3f_5240_){
_start:
{
lean_object* v___x_5242_; lean_object* v_infoState_5243_; lean_object* v_trees_5244_; lean_object* v___x_5245_; 
v___x_5242_ = lean_st_ref_get(v___y_5230_);
v_infoState_5243_ = lean_ctor_get(v___x_5242_, 7);
lean_inc_ref(v_infoState_5243_);
lean_dec(v___x_5242_);
v_trees_5244_ = lean_ctor_get(v_infoState_5243_, 2);
lean_inc_ref(v_trees_5244_);
lean_dec_ref(v_infoState_5243_);
lean_inc(v___y_5230_);
lean_inc_ref(v___y_5238_);
lean_inc(v___y_5237_);
lean_inc_ref(v___y_5236_);
lean_inc(v___y_5235_);
lean_inc_ref(v___y_5234_);
lean_inc(v___y_5233_);
lean_inc_ref(v___y_5232_);
v___x_5245_ = lean_apply_10(v_mkInfoTree_5231_, v_trees_5244_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_, v___y_5236_, v___y_5237_, v___y_5238_, v___y_5230_, lean_box(0));
if (lean_obj_tag(v___x_5245_) == 0)
{
lean_object* v_a_5246_; lean_object* v___x_5248_; uint8_t v_isShared_5249_; uint8_t v_isSharedCheck_5284_; 
v_a_5246_ = lean_ctor_get(v___x_5245_, 0);
v_isSharedCheck_5284_ = !lean_is_exclusive(v___x_5245_);
if (v_isSharedCheck_5284_ == 0)
{
v___x_5248_ = v___x_5245_;
v_isShared_5249_ = v_isSharedCheck_5284_;
goto v_resetjp_5247_;
}
else
{
lean_inc(v_a_5246_);
lean_dec(v___x_5245_);
v___x_5248_ = lean_box(0);
v_isShared_5249_ = v_isSharedCheck_5284_;
goto v_resetjp_5247_;
}
v_resetjp_5247_:
{
lean_object* v___x_5250_; lean_object* v_infoState_5251_; lean_object* v_env_5252_; lean_object* v_nextMacroScope_5253_; lean_object* v_ngen_5254_; lean_object* v_auxDeclNGen_5255_; lean_object* v_traceState_5256_; lean_object* v_cache_5257_; lean_object* v_messages_5258_; lean_object* v_snapshotTasks_5259_; lean_object* v___x_5261_; uint8_t v_isShared_5262_; uint8_t v_isSharedCheck_5283_; 
v___x_5250_ = lean_st_ref_take(v___y_5230_);
v_infoState_5251_ = lean_ctor_get(v___x_5250_, 7);
v_env_5252_ = lean_ctor_get(v___x_5250_, 0);
v_nextMacroScope_5253_ = lean_ctor_get(v___x_5250_, 1);
v_ngen_5254_ = lean_ctor_get(v___x_5250_, 2);
v_auxDeclNGen_5255_ = lean_ctor_get(v___x_5250_, 3);
v_traceState_5256_ = lean_ctor_get(v___x_5250_, 4);
v_cache_5257_ = lean_ctor_get(v___x_5250_, 5);
v_messages_5258_ = lean_ctor_get(v___x_5250_, 6);
v_snapshotTasks_5259_ = lean_ctor_get(v___x_5250_, 8);
v_isSharedCheck_5283_ = !lean_is_exclusive(v___x_5250_);
if (v_isSharedCheck_5283_ == 0)
{
v___x_5261_ = v___x_5250_;
v_isShared_5262_ = v_isSharedCheck_5283_;
goto v_resetjp_5260_;
}
else
{
lean_inc(v_snapshotTasks_5259_);
lean_inc(v_infoState_5251_);
lean_inc(v_messages_5258_);
lean_inc(v_cache_5257_);
lean_inc(v_traceState_5256_);
lean_inc(v_auxDeclNGen_5255_);
lean_inc(v_ngen_5254_);
lean_inc(v_nextMacroScope_5253_);
lean_inc(v_env_5252_);
lean_dec(v___x_5250_);
v___x_5261_ = lean_box(0);
v_isShared_5262_ = v_isSharedCheck_5283_;
goto v_resetjp_5260_;
}
v_resetjp_5260_:
{
uint8_t v_enabled_5263_; lean_object* v_assignment_5264_; lean_object* v_lazyAssignment_5265_; lean_object* v___x_5267_; uint8_t v_isShared_5268_; uint8_t v_isSharedCheck_5281_; 
v_enabled_5263_ = lean_ctor_get_uint8(v_infoState_5251_, sizeof(void*)*3);
v_assignment_5264_ = lean_ctor_get(v_infoState_5251_, 0);
v_lazyAssignment_5265_ = lean_ctor_get(v_infoState_5251_, 1);
v_isSharedCheck_5281_ = !lean_is_exclusive(v_infoState_5251_);
if (v_isSharedCheck_5281_ == 0)
{
lean_object* v_unused_5282_; 
v_unused_5282_ = lean_ctor_get(v_infoState_5251_, 2);
lean_dec(v_unused_5282_);
v___x_5267_ = v_infoState_5251_;
v_isShared_5268_ = v_isSharedCheck_5281_;
goto v_resetjp_5266_;
}
else
{
lean_inc(v_lazyAssignment_5265_);
lean_inc(v_assignment_5264_);
lean_dec(v_infoState_5251_);
v___x_5267_ = lean_box(0);
v_isShared_5268_ = v_isSharedCheck_5281_;
goto v_resetjp_5266_;
}
v_resetjp_5266_:
{
lean_object* v___x_5269_; lean_object* v___x_5270_; lean_object* v___x_5272_; 
v___x_5269_ = lean_box(0);
v___x_5270_ = l_Lean_PersistentArray_push___redArg(v_a_5239_, v_a_5246_);
if (v_isShared_5268_ == 0)
{
lean_ctor_set(v___x_5267_, 2, v___x_5270_);
v___x_5272_ = v___x_5267_;
goto v_reusejp_5271_;
}
else
{
lean_object* v_reuseFailAlloc_5280_; 
v_reuseFailAlloc_5280_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5280_, 0, v_assignment_5264_);
lean_ctor_set(v_reuseFailAlloc_5280_, 1, v_lazyAssignment_5265_);
lean_ctor_set(v_reuseFailAlloc_5280_, 2, v___x_5270_);
lean_ctor_set_uint8(v_reuseFailAlloc_5280_, sizeof(void*)*3, v_enabled_5263_);
v___x_5272_ = v_reuseFailAlloc_5280_;
goto v_reusejp_5271_;
}
v_reusejp_5271_:
{
lean_object* v___x_5274_; 
if (v_isShared_5262_ == 0)
{
lean_ctor_set(v___x_5261_, 7, v___x_5272_);
v___x_5274_ = v___x_5261_;
goto v_reusejp_5273_;
}
else
{
lean_object* v_reuseFailAlloc_5279_; 
v_reuseFailAlloc_5279_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5279_, 0, v_env_5252_);
lean_ctor_set(v_reuseFailAlloc_5279_, 1, v_nextMacroScope_5253_);
lean_ctor_set(v_reuseFailAlloc_5279_, 2, v_ngen_5254_);
lean_ctor_set(v_reuseFailAlloc_5279_, 3, v_auxDeclNGen_5255_);
lean_ctor_set(v_reuseFailAlloc_5279_, 4, v_traceState_5256_);
lean_ctor_set(v_reuseFailAlloc_5279_, 5, v_cache_5257_);
lean_ctor_set(v_reuseFailAlloc_5279_, 6, v_messages_5258_);
lean_ctor_set(v_reuseFailAlloc_5279_, 7, v___x_5272_);
lean_ctor_set(v_reuseFailAlloc_5279_, 8, v_snapshotTasks_5259_);
v___x_5274_ = v_reuseFailAlloc_5279_;
goto v_reusejp_5273_;
}
v_reusejp_5273_:
{
lean_object* v___x_5275_; lean_object* v___x_5277_; 
v___x_5275_ = lean_st_ref_put(v___y_5230_, v___x_5274_);
if (v_isShared_5249_ == 0)
{
lean_ctor_set(v___x_5248_, 0, v___x_5269_);
v___x_5277_ = v___x_5248_;
goto v_reusejp_5276_;
}
else
{
lean_object* v_reuseFailAlloc_5278_; 
v_reuseFailAlloc_5278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5278_, 0, v___x_5269_);
v___x_5277_ = v_reuseFailAlloc_5278_;
goto v_reusejp_5276_;
}
v_reusejp_5276_:
{
return v___x_5277_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5285_; lean_object* v___x_5287_; uint8_t v_isShared_5288_; uint8_t v_isSharedCheck_5292_; 
lean_dec_ref(v_a_5239_);
v_a_5285_ = lean_ctor_get(v___x_5245_, 0);
v_isSharedCheck_5292_ = !lean_is_exclusive(v___x_5245_);
if (v_isSharedCheck_5292_ == 0)
{
v___x_5287_ = v___x_5245_;
v_isShared_5288_ = v_isSharedCheck_5292_;
goto v_resetjp_5286_;
}
else
{
lean_inc(v_a_5285_);
lean_dec(v___x_5245_);
v___x_5287_ = lean_box(0);
v_isShared_5288_ = v_isSharedCheck_5292_;
goto v_resetjp_5286_;
}
v_resetjp_5286_:
{
lean_object* v___x_5290_; 
if (v_isShared_5288_ == 0)
{
v___x_5290_ = v___x_5287_;
goto v_reusejp_5289_;
}
else
{
lean_object* v_reuseFailAlloc_5291_; 
v_reuseFailAlloc_5291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5291_, 0, v_a_5285_);
v___x_5290_ = v_reuseFailAlloc_5291_;
goto v_reusejp_5289_;
}
v_reusejp_5289_:
{
return v___x_5290_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0___boxed(lean_object* v___y_5293_, lean_object* v_mkInfoTree_5294_, lean_object* v___y_5295_, lean_object* v___y_5296_, lean_object* v___y_5297_, lean_object* v___y_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v_a_5302_, lean_object* v_a_x3f_5303_, lean_object* v___y_5304_){
_start:
{
lean_object* v_res_5305_; 
v_res_5305_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5293_, v_mkInfoTree_5294_, v___y_5295_, v___y_5296_, v___y_5297_, v___y_5298_, v___y_5299_, v___y_5300_, v___y_5301_, v_a_5302_, v_a_x3f_5303_);
lean_dec(v_a_x3f_5303_);
lean_dec_ref(v___y_5301_);
lean_dec(v___y_5300_);
lean_dec_ref(v___y_5299_);
lean_dec(v___y_5298_);
lean_dec_ref(v___y_5297_);
lean_dec(v___y_5296_);
lean_dec_ref(v___y_5295_);
lean_dec(v___y_5293_);
return v_res_5305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(lean_object* v_x_5306_, lean_object* v_mkInfoTree_5307_, lean_object* v___y_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_){
_start:
{
lean_object* v___x_5317_; lean_object* v_infoState_5318_; uint8_t v_enabled_5319_; 
v___x_5317_ = lean_st_ref_get(v___y_5315_);
v_infoState_5318_ = lean_ctor_get(v___x_5317_, 7);
lean_inc_ref(v_infoState_5318_);
lean_dec(v___x_5317_);
v_enabled_5319_ = lean_ctor_get_uint8(v_infoState_5318_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5318_);
if (v_enabled_5319_ == 0)
{
lean_object* v___x_5320_; 
lean_dec_ref(v_mkInfoTree_5307_);
lean_inc(v___y_5315_);
lean_inc_ref(v___y_5314_);
lean_inc(v___y_5313_);
lean_inc_ref(v___y_5312_);
lean_inc(v___y_5311_);
lean_inc_ref(v___y_5310_);
lean_inc(v___y_5309_);
lean_inc_ref(v___y_5308_);
v___x_5320_ = lean_apply_9(v_x_5306_, v___y_5308_, v___y_5309_, v___y_5310_, v___y_5311_, v___y_5312_, v___y_5313_, v___y_5314_, v___y_5315_, lean_box(0));
return v___x_5320_;
}
else
{
lean_object* v___x_5321_; lean_object* v_a_5322_; lean_object* v_r_5323_; 
v___x_5321_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_5315_);
v_a_5322_ = lean_ctor_get(v___x_5321_, 0);
lean_inc(v_a_5322_);
lean_dec_ref(v___x_5321_);
lean_inc(v___y_5315_);
lean_inc_ref(v___y_5314_);
lean_inc(v___y_5313_);
lean_inc_ref(v___y_5312_);
lean_inc(v___y_5311_);
lean_inc_ref(v___y_5310_);
lean_inc(v___y_5309_);
lean_inc_ref(v___y_5308_);
v_r_5323_ = lean_apply_9(v_x_5306_, v___y_5308_, v___y_5309_, v___y_5310_, v___y_5311_, v___y_5312_, v___y_5313_, v___y_5314_, v___y_5315_, lean_box(0));
if (lean_obj_tag(v_r_5323_) == 0)
{
lean_object* v_a_5324_; lean_object* v___x_5326_; uint8_t v_isShared_5327_; uint8_t v_isSharedCheck_5348_; 
v_a_5324_ = lean_ctor_get(v_r_5323_, 0);
v_isSharedCheck_5348_ = !lean_is_exclusive(v_r_5323_);
if (v_isSharedCheck_5348_ == 0)
{
v___x_5326_ = v_r_5323_;
v_isShared_5327_ = v_isSharedCheck_5348_;
goto v_resetjp_5325_;
}
else
{
lean_inc(v_a_5324_);
lean_dec(v_r_5323_);
v___x_5326_ = lean_box(0);
v_isShared_5327_ = v_isSharedCheck_5348_;
goto v_resetjp_5325_;
}
v_resetjp_5325_:
{
lean_object* v___x_5329_; 
lean_inc(v_a_5324_);
if (v_isShared_5327_ == 0)
{
lean_ctor_set_tag(v___x_5326_, 1);
v___x_5329_ = v___x_5326_;
goto v_reusejp_5328_;
}
else
{
lean_object* v_reuseFailAlloc_5347_; 
v_reuseFailAlloc_5347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5347_, 0, v_a_5324_);
v___x_5329_ = v_reuseFailAlloc_5347_;
goto v_reusejp_5328_;
}
v_reusejp_5328_:
{
lean_object* v___x_5330_; 
v___x_5330_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5315_, v_mkInfoTree_5307_, v___y_5308_, v___y_5309_, v___y_5310_, v___y_5311_, v___y_5312_, v___y_5313_, v___y_5314_, v_a_5322_, v___x_5329_);
lean_dec_ref(v___x_5329_);
if (lean_obj_tag(v___x_5330_) == 0)
{
lean_object* v___x_5332_; uint8_t v_isShared_5333_; uint8_t v_isSharedCheck_5337_; 
v_isSharedCheck_5337_ = !lean_is_exclusive(v___x_5330_);
if (v_isSharedCheck_5337_ == 0)
{
lean_object* v_unused_5338_; 
v_unused_5338_ = lean_ctor_get(v___x_5330_, 0);
lean_dec(v_unused_5338_);
v___x_5332_ = v___x_5330_;
v_isShared_5333_ = v_isSharedCheck_5337_;
goto v_resetjp_5331_;
}
else
{
lean_dec(v___x_5330_);
v___x_5332_ = lean_box(0);
v_isShared_5333_ = v_isSharedCheck_5337_;
goto v_resetjp_5331_;
}
v_resetjp_5331_:
{
lean_object* v___x_5335_; 
if (v_isShared_5333_ == 0)
{
lean_ctor_set(v___x_5332_, 0, v_a_5324_);
v___x_5335_ = v___x_5332_;
goto v_reusejp_5334_;
}
else
{
lean_object* v_reuseFailAlloc_5336_; 
v_reuseFailAlloc_5336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5336_, 0, v_a_5324_);
v___x_5335_ = v_reuseFailAlloc_5336_;
goto v_reusejp_5334_;
}
v_reusejp_5334_:
{
return v___x_5335_;
}
}
}
else
{
lean_object* v_a_5339_; lean_object* v___x_5341_; uint8_t v_isShared_5342_; uint8_t v_isSharedCheck_5346_; 
lean_dec(v_a_5324_);
v_a_5339_ = lean_ctor_get(v___x_5330_, 0);
v_isSharedCheck_5346_ = !lean_is_exclusive(v___x_5330_);
if (v_isSharedCheck_5346_ == 0)
{
v___x_5341_ = v___x_5330_;
v_isShared_5342_ = v_isSharedCheck_5346_;
goto v_resetjp_5340_;
}
else
{
lean_inc(v_a_5339_);
lean_dec(v___x_5330_);
v___x_5341_ = lean_box(0);
v_isShared_5342_ = v_isSharedCheck_5346_;
goto v_resetjp_5340_;
}
v_resetjp_5340_:
{
lean_object* v___x_5344_; 
if (v_isShared_5342_ == 0)
{
v___x_5344_ = v___x_5341_;
goto v_reusejp_5343_;
}
else
{
lean_object* v_reuseFailAlloc_5345_; 
v_reuseFailAlloc_5345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5345_, 0, v_a_5339_);
v___x_5344_ = v_reuseFailAlloc_5345_;
goto v_reusejp_5343_;
}
v_reusejp_5343_:
{
return v___x_5344_;
}
}
}
}
}
}
else
{
lean_object* v_a_5349_; lean_object* v___x_5350_; lean_object* v___x_5351_; 
v_a_5349_ = lean_ctor_get(v_r_5323_, 0);
lean_inc(v_a_5349_);
lean_dec_ref_known(v_r_5323_, 1);
v___x_5350_ = lean_box(0);
v___x_5351_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5315_, v_mkInfoTree_5307_, v___y_5308_, v___y_5309_, v___y_5310_, v___y_5311_, v___y_5312_, v___y_5313_, v___y_5314_, v_a_5322_, v___x_5350_);
if (lean_obj_tag(v___x_5351_) == 0)
{
lean_object* v___x_5353_; uint8_t v_isShared_5354_; uint8_t v_isSharedCheck_5358_; 
v_isSharedCheck_5358_ = !lean_is_exclusive(v___x_5351_);
if (v_isSharedCheck_5358_ == 0)
{
lean_object* v_unused_5359_; 
v_unused_5359_ = lean_ctor_get(v___x_5351_, 0);
lean_dec(v_unused_5359_);
v___x_5353_ = v___x_5351_;
v_isShared_5354_ = v_isSharedCheck_5358_;
goto v_resetjp_5352_;
}
else
{
lean_dec(v___x_5351_);
v___x_5353_ = lean_box(0);
v_isShared_5354_ = v_isSharedCheck_5358_;
goto v_resetjp_5352_;
}
v_resetjp_5352_:
{
lean_object* v___x_5356_; 
if (v_isShared_5354_ == 0)
{
lean_ctor_set_tag(v___x_5353_, 1);
lean_ctor_set(v___x_5353_, 0, v_a_5349_);
v___x_5356_ = v___x_5353_;
goto v_reusejp_5355_;
}
else
{
lean_object* v_reuseFailAlloc_5357_; 
v_reuseFailAlloc_5357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5357_, 0, v_a_5349_);
v___x_5356_ = v_reuseFailAlloc_5357_;
goto v_reusejp_5355_;
}
v_reusejp_5355_:
{
return v___x_5356_;
}
}
}
else
{
lean_object* v_a_5360_; lean_object* v___x_5362_; uint8_t v_isShared_5363_; uint8_t v_isSharedCheck_5367_; 
lean_dec(v_a_5349_);
v_a_5360_ = lean_ctor_get(v___x_5351_, 0);
v_isSharedCheck_5367_ = !lean_is_exclusive(v___x_5351_);
if (v_isSharedCheck_5367_ == 0)
{
v___x_5362_ = v___x_5351_;
v_isShared_5363_ = v_isSharedCheck_5367_;
goto v_resetjp_5361_;
}
else
{
lean_inc(v_a_5360_);
lean_dec(v___x_5351_);
v___x_5362_ = lean_box(0);
v_isShared_5363_ = v_isSharedCheck_5367_;
goto v_resetjp_5361_;
}
v_resetjp_5361_:
{
lean_object* v___x_5365_; 
if (v_isShared_5363_ == 0)
{
v___x_5365_ = v___x_5362_;
goto v_reusejp_5364_;
}
else
{
lean_object* v_reuseFailAlloc_5366_; 
v_reuseFailAlloc_5366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5366_, 0, v_a_5360_);
v___x_5365_ = v_reuseFailAlloc_5366_;
goto v_reusejp_5364_;
}
v_reusejp_5364_:
{
return v___x_5365_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___boxed(lean_object* v_x_5368_, lean_object* v_mkInfoTree_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_, lean_object* v___y_5374_, lean_object* v___y_5375_, lean_object* v___y_5376_, lean_object* v___y_5377_, lean_object* v___y_5378_){
_start:
{
lean_object* v_res_5379_; 
v_res_5379_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v_x_5368_, v_mkInfoTree_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_);
lean_dec(v___y_5377_);
lean_dec_ref(v___y_5376_);
lean_dec(v___y_5375_);
lean_dec_ref(v___y_5374_);
lean_dec(v___y_5373_);
lean_dec_ref(v___y_5372_);
lean_dec(v___y_5371_);
lean_dec_ref(v___y_5370_);
return v_res_5379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1(lean_object* v_a_5380_, lean_object* v_trees_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_){
_start:
{
lean_object* v___x_5391_; 
lean_inc(v___y_5389_);
lean_inc_ref(v___y_5388_);
lean_inc(v___y_5387_);
lean_inc_ref(v___y_5386_);
lean_inc(v___y_5385_);
lean_inc_ref(v___y_5384_);
lean_inc(v___y_5383_);
lean_inc_ref(v___y_5382_);
v___x_5391_ = lean_apply_9(v_a_5380_, v___y_5382_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_, v___y_5389_, lean_box(0));
if (lean_obj_tag(v___x_5391_) == 0)
{
lean_object* v_a_5392_; lean_object* v___x_5394_; uint8_t v_isShared_5395_; uint8_t v_isSharedCheck_5400_; 
v_a_5392_ = lean_ctor_get(v___x_5391_, 0);
v_isSharedCheck_5400_ = !lean_is_exclusive(v___x_5391_);
if (v_isSharedCheck_5400_ == 0)
{
v___x_5394_ = v___x_5391_;
v_isShared_5395_ = v_isSharedCheck_5400_;
goto v_resetjp_5393_;
}
else
{
lean_inc(v_a_5392_);
lean_dec(v___x_5391_);
v___x_5394_ = lean_box(0);
v_isShared_5395_ = v_isSharedCheck_5400_;
goto v_resetjp_5393_;
}
v_resetjp_5393_:
{
lean_object* v___x_5396_; lean_object* v___x_5398_; 
v___x_5396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5396_, 0, v_a_5392_);
lean_ctor_set(v___x_5396_, 1, v_trees_5381_);
if (v_isShared_5395_ == 0)
{
lean_ctor_set(v___x_5394_, 0, v___x_5396_);
v___x_5398_ = v___x_5394_;
goto v_reusejp_5397_;
}
else
{
lean_object* v_reuseFailAlloc_5399_; 
v_reuseFailAlloc_5399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5399_, 0, v___x_5396_);
v___x_5398_ = v_reuseFailAlloc_5399_;
goto v_reusejp_5397_;
}
v_reusejp_5397_:
{
return v___x_5398_;
}
}
}
else
{
lean_object* v_a_5401_; lean_object* v___x_5403_; uint8_t v_isShared_5404_; uint8_t v_isSharedCheck_5408_; 
lean_dec_ref(v_trees_5381_);
v_a_5401_ = lean_ctor_get(v___x_5391_, 0);
v_isSharedCheck_5408_ = !lean_is_exclusive(v___x_5391_);
if (v_isSharedCheck_5408_ == 0)
{
v___x_5403_ = v___x_5391_;
v_isShared_5404_ = v_isSharedCheck_5408_;
goto v_resetjp_5402_;
}
else
{
lean_inc(v_a_5401_);
lean_dec(v___x_5391_);
v___x_5403_ = lean_box(0);
v_isShared_5404_ = v_isSharedCheck_5408_;
goto v_resetjp_5402_;
}
v_resetjp_5402_:
{
lean_object* v___x_5406_; 
if (v_isShared_5404_ == 0)
{
v___x_5406_ = v___x_5403_;
goto v_reusejp_5405_;
}
else
{
lean_object* v_reuseFailAlloc_5407_; 
v_reuseFailAlloc_5407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5407_, 0, v_a_5401_);
v___x_5406_ = v_reuseFailAlloc_5407_;
goto v_reusejp_5405_;
}
v_reusejp_5405_:
{
return v___x_5406_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1___boxed(lean_object* v_a_5409_, lean_object* v_trees_5410_, lean_object* v___y_5411_, lean_object* v___y_5412_, lean_object* v___y_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_){
_start:
{
lean_object* v_res_5420_; 
v_res_5420_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1(v_a_5409_, v_trees_5410_, v___y_5411_, v___y_5412_, v___y_5413_, v___y_5414_, v___y_5415_, v___y_5416_, v___y_5417_, v___y_5418_);
lean_dec(v___y_5418_);
lean_dec_ref(v___y_5417_);
lean_dec(v___y_5416_);
lean_dec_ref(v___y_5415_);
lean_dec(v___y_5414_);
lean_dec_ref(v___y_5413_);
lean_dec(v___y_5412_);
lean_dec_ref(v___y_5411_);
return v_res_5420_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2(lean_object* v___x_5421_, lean_object* v_tactic_5422_, lean_object* v_ref_5423_, lean_object* v___y_5424_, lean_object* v___y_5425_, lean_object* v___y_5426_, lean_object* v___y_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_){
_start:
{
lean_object* v___x_5433_; 
v___x_5433_ = l_Lean_Elab_Tactic_setGoals___redArg(v___x_5421_, v___y_5425_);
if (lean_obj_tag(v___x_5433_) == 0)
{
lean_object* v___x_5434_; 
lean_dec_ref_known(v___x_5433_, 1);
v___x_5434_ = l_Lean_Elab_WF_applyCleanWfTactic(v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_);
if (lean_obj_tag(v___x_5434_) == 0)
{
lean_object* v___x_5435_; lean_object* v___x_5436_; 
lean_dec_ref_known(v___x_5434_, 1);
v___x_5435_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_5435_, 0, v_tactic_5422_);
v___x_5436_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v_ref_5423_, v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_);
if (lean_obj_tag(v___x_5436_) == 0)
{
lean_object* v_a_5437_; lean_object* v___f_5438_; lean_object* v___x_5439_; 
v_a_5437_ = lean_ctor_get(v___x_5436_, 0);
lean_inc(v_a_5437_);
lean_dec_ref_known(v___x_5436_, 1);
v___f_5438_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1___boxed), 11, 1);
lean_closure_set(v___f_5438_, 0, v_a_5437_);
v___x_5439_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v___x_5435_, v___f_5438_, v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_);
return v___x_5439_;
}
else
{
lean_object* v_a_5440_; lean_object* v___x_5442_; uint8_t v_isShared_5443_; uint8_t v_isSharedCheck_5447_; 
lean_dec_ref(v___x_5435_);
v_a_5440_ = lean_ctor_get(v___x_5436_, 0);
v_isSharedCheck_5447_ = !lean_is_exclusive(v___x_5436_);
if (v_isSharedCheck_5447_ == 0)
{
v___x_5442_ = v___x_5436_;
v_isShared_5443_ = v_isSharedCheck_5447_;
goto v_resetjp_5441_;
}
else
{
lean_inc(v_a_5440_);
lean_dec(v___x_5436_);
v___x_5442_ = lean_box(0);
v_isShared_5443_ = v_isSharedCheck_5447_;
goto v_resetjp_5441_;
}
v_resetjp_5441_:
{
lean_object* v___x_5445_; 
if (v_isShared_5443_ == 0)
{
v___x_5445_ = v___x_5442_;
goto v_reusejp_5444_;
}
else
{
lean_object* v_reuseFailAlloc_5446_; 
v_reuseFailAlloc_5446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5446_, 0, v_a_5440_);
v___x_5445_ = v_reuseFailAlloc_5446_;
goto v_reusejp_5444_;
}
v_reusejp_5444_:
{
return v___x_5445_;
}
}
}
}
else
{
lean_dec(v_ref_5423_);
lean_dec(v_tactic_5422_);
return v___x_5434_;
}
}
else
{
lean_dec(v_ref_5423_);
lean_dec(v_tactic_5422_);
return v___x_5433_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2___boxed(lean_object* v___x_5448_, lean_object* v_tactic_5449_, lean_object* v_ref_5450_, lean_object* v___y_5451_, lean_object* v___y_5452_, lean_object* v___y_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_){
_start:
{
lean_object* v_res_5460_; 
v_res_5460_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2(v___x_5448_, v_tactic_5449_, v_ref_5450_, v___y_5451_, v___y_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_);
lean_dec(v___y_5458_);
lean_dec_ref(v___y_5457_);
lean_dec(v___y_5456_);
lean_dec_ref(v___y_5455_);
lean_dec(v___y_5454_);
lean_dec_ref(v___y_5453_);
lean_dec(v___y_5452_);
lean_dec_ref(v___y_5451_);
return v_res_5460_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5461_; lean_object* v___x_5462_; 
v___x_5461_ = lean_box(1);
v___x_5462_ = l_Lean_MessageData_ofFormat(v___x_5461_);
return v___x_5462_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5466_; lean_object* v___x_5467_; 
v___x_5466_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__2));
v___x_5467_ = l_Lean_MessageData_ofFormat(v___x_5466_);
return v___x_5467_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3(lean_object* v_x_5468_, lean_object* v_x_5469_){
_start:
{
if (lean_obj_tag(v_x_5469_) == 0)
{
return v_x_5468_;
}
else
{
lean_object* v_head_5470_; lean_object* v_tail_5471_; lean_object* v___x_5473_; uint8_t v_isShared_5474_; uint8_t v_isSharedCheck_5493_; 
v_head_5470_ = lean_ctor_get(v_x_5469_, 0);
v_tail_5471_ = lean_ctor_get(v_x_5469_, 1);
v_isSharedCheck_5493_ = !lean_is_exclusive(v_x_5469_);
if (v_isSharedCheck_5493_ == 0)
{
v___x_5473_ = v_x_5469_;
v_isShared_5474_ = v_isSharedCheck_5493_;
goto v_resetjp_5472_;
}
else
{
lean_inc(v_tail_5471_);
lean_inc(v_head_5470_);
lean_dec(v_x_5469_);
v___x_5473_ = lean_box(0);
v_isShared_5474_ = v_isSharedCheck_5493_;
goto v_resetjp_5472_;
}
v_resetjp_5472_:
{
lean_object* v_before_5475_; lean_object* v___x_5477_; uint8_t v_isShared_5478_; uint8_t v_isSharedCheck_5491_; 
v_before_5475_ = lean_ctor_get(v_head_5470_, 0);
v_isSharedCheck_5491_ = !lean_is_exclusive(v_head_5470_);
if (v_isSharedCheck_5491_ == 0)
{
lean_object* v_unused_5492_; 
v_unused_5492_ = lean_ctor_get(v_head_5470_, 1);
lean_dec(v_unused_5492_);
v___x_5477_ = v_head_5470_;
v_isShared_5478_ = v_isSharedCheck_5491_;
goto v_resetjp_5476_;
}
else
{
lean_inc(v_before_5475_);
lean_dec(v_head_5470_);
v___x_5477_ = lean_box(0);
v_isShared_5478_ = v_isSharedCheck_5491_;
goto v_resetjp_5476_;
}
v_resetjp_5476_:
{
lean_object* v___x_5479_; lean_object* v___x_5481_; 
v___x_5479_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_5478_ == 0)
{
lean_ctor_set_tag(v___x_5477_, 7);
lean_ctor_set(v___x_5477_, 1, v___x_5479_);
lean_ctor_set(v___x_5477_, 0, v_x_5468_);
v___x_5481_ = v___x_5477_;
goto v_reusejp_5480_;
}
else
{
lean_object* v_reuseFailAlloc_5490_; 
v_reuseFailAlloc_5490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5490_, 0, v_x_5468_);
lean_ctor_set(v_reuseFailAlloc_5490_, 1, v___x_5479_);
v___x_5481_ = v_reuseFailAlloc_5490_;
goto v_reusejp_5480_;
}
v_reusejp_5480_:
{
lean_object* v___x_5482_; lean_object* v___x_5484_; 
v___x_5482_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3);
if (v_isShared_5474_ == 0)
{
lean_ctor_set_tag(v___x_5473_, 7);
lean_ctor_set(v___x_5473_, 1, v___x_5482_);
lean_ctor_set(v___x_5473_, 0, v___x_5481_);
v___x_5484_ = v___x_5473_;
goto v_reusejp_5483_;
}
else
{
lean_object* v_reuseFailAlloc_5489_; 
v_reuseFailAlloc_5489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5489_, 0, v___x_5481_);
lean_ctor_set(v_reuseFailAlloc_5489_, 1, v___x_5482_);
v___x_5484_ = v_reuseFailAlloc_5489_;
goto v_reusejp_5483_;
}
v_reusejp_5483_:
{
lean_object* v___x_5485_; lean_object* v___x_5486_; lean_object* v___x_5487_; 
v___x_5485_ = l_Lean_MessageData_ofSyntax(v_before_5475_);
v___x_5486_ = l_Lean_indentD(v___x_5485_);
v___x_5487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5487_, 0, v___x_5484_);
lean_ctor_set(v___x_5487_, 1, v___x_5486_);
v_x_5468_ = v___x_5487_;
v_x_5469_ = v_tail_5471_;
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
lean_object* v___x_5497_; lean_object* v___x_5498_; 
v___x_5497_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__1));
v___x_5498_ = l_Lean_MessageData_ofFormat(v___x_5497_);
return v___x_5498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(lean_object* v_msgData_5499_, lean_object* v_macroStack_5500_, lean_object* v___y_5501_){
_start:
{
lean_object* v_toCold_5503_; lean_object* v_options_5504_; lean_object* v___x_5505_; uint8_t v___x_5506_; 
v_toCold_5503_ = lean_ctor_get(v___y_5501_, 0);
v_options_5504_ = lean_ctor_get(v_toCold_5503_, 2);
v___x_5505_ = l_Lean_Elab_pp_macroStack;
v___x_5506_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v_options_5504_, v___x_5505_);
if (v___x_5506_ == 0)
{
lean_object* v___x_5507_; 
lean_dec(v_macroStack_5500_);
v___x_5507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5507_, 0, v_msgData_5499_);
return v___x_5507_;
}
else
{
if (lean_obj_tag(v_macroStack_5500_) == 0)
{
lean_object* v___x_5508_; 
v___x_5508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5508_, 0, v_msgData_5499_);
return v___x_5508_;
}
else
{
lean_object* v_head_5509_; lean_object* v_after_5510_; lean_object* v___x_5512_; uint8_t v_isShared_5513_; uint8_t v_isSharedCheck_5525_; 
v_head_5509_ = lean_ctor_get(v_macroStack_5500_, 0);
lean_inc(v_head_5509_);
v_after_5510_ = lean_ctor_get(v_head_5509_, 1);
v_isSharedCheck_5525_ = !lean_is_exclusive(v_head_5509_);
if (v_isSharedCheck_5525_ == 0)
{
lean_object* v_unused_5526_; 
v_unused_5526_ = lean_ctor_get(v_head_5509_, 0);
lean_dec(v_unused_5526_);
v___x_5512_ = v_head_5509_;
v_isShared_5513_ = v_isSharedCheck_5525_;
goto v_resetjp_5511_;
}
else
{
lean_inc(v_after_5510_);
lean_dec(v_head_5509_);
v___x_5512_ = lean_box(0);
v_isShared_5513_ = v_isSharedCheck_5525_;
goto v_resetjp_5511_;
}
v_resetjp_5511_:
{
lean_object* v___x_5514_; lean_object* v___x_5516_; 
v___x_5514_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_5513_ == 0)
{
lean_ctor_set_tag(v___x_5512_, 7);
lean_ctor_set(v___x_5512_, 1, v___x_5514_);
lean_ctor_set(v___x_5512_, 0, v_msgData_5499_);
v___x_5516_ = v___x_5512_;
goto v_reusejp_5515_;
}
else
{
lean_object* v_reuseFailAlloc_5524_; 
v_reuseFailAlloc_5524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5524_, 0, v_msgData_5499_);
lean_ctor_set(v_reuseFailAlloc_5524_, 1, v___x_5514_);
v___x_5516_ = v_reuseFailAlloc_5524_;
goto v_reusejp_5515_;
}
v_reusejp_5515_:
{
lean_object* v___x_5517_; lean_object* v___x_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; lean_object* v_msgData_5521_; lean_object* v___x_5522_; lean_object* v___x_5523_; 
v___x_5517_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2);
v___x_5518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5518_, 0, v___x_5516_);
lean_ctor_set(v___x_5518_, 1, v___x_5517_);
v___x_5519_ = l_Lean_MessageData_ofSyntax(v_after_5510_);
v___x_5520_ = l_Lean_indentD(v___x_5519_);
v_msgData_5521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_5521_, 0, v___x_5518_);
lean_ctor_set(v_msgData_5521_, 1, v___x_5520_);
v___x_5522_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3(v_msgData_5521_, v_macroStack_5500_);
v___x_5523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5523_, 0, v___x_5522_);
return v___x_5523_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_5527_, lean_object* v_macroStack_5528_, lean_object* v___y_5529_, lean_object* v___y_5530_){
_start:
{
lean_object* v_res_5531_; 
v_res_5531_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_msgData_5527_, v_macroStack_5528_, v___y_5529_);
lean_dec_ref(v___y_5529_);
return v_res_5531_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(lean_object* v_msg_5532_, lean_object* v___y_5533_, lean_object* v___y_5534_, lean_object* v___y_5535_, lean_object* v___y_5536_, lean_object* v___y_5537_, lean_object* v___y_5538_){
_start:
{
lean_object* v_ref_5540_; lean_object* v_macroStack_5541_; lean_object* v___x_5542_; lean_object* v___x_5543_; lean_object* v_a_5544_; lean_object* v___x_5545_; lean_object* v_a_5546_; lean_object* v___x_5548_; uint8_t v_isShared_5549_; uint8_t v_isSharedCheck_5554_; 
v_ref_5540_ = lean_ctor_get(v___y_5537_, 2);
v_macroStack_5541_ = lean_ctor_get(v___y_5533_, 1);
v___x_5542_ = l_Lean_Elab_getBetterRef(v_ref_5540_, v_macroStack_5541_);
v___x_5543_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_5532_, v___y_5535_, v___y_5536_, v___y_5537_, v___y_5538_);
v_a_5544_ = lean_ctor_get(v___x_5543_, 0);
lean_inc(v_a_5544_);
lean_dec_ref(v___x_5543_);
lean_inc(v_macroStack_5541_);
v___x_5545_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_a_5544_, v_macroStack_5541_, v___y_5537_);
v_a_5546_ = lean_ctor_get(v___x_5545_, 0);
v_isSharedCheck_5554_ = !lean_is_exclusive(v___x_5545_);
if (v_isSharedCheck_5554_ == 0)
{
v___x_5548_ = v___x_5545_;
v_isShared_5549_ = v_isSharedCheck_5554_;
goto v_resetjp_5547_;
}
else
{
lean_inc(v_a_5546_);
lean_dec(v___x_5545_);
v___x_5548_ = lean_box(0);
v_isShared_5549_ = v_isSharedCheck_5554_;
goto v_resetjp_5547_;
}
v_resetjp_5547_:
{
lean_object* v___x_5550_; lean_object* v___x_5552_; 
v___x_5550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5550_, 0, v___x_5542_);
lean_ctor_set(v___x_5550_, 1, v_a_5546_);
if (v_isShared_5549_ == 0)
{
lean_ctor_set_tag(v___x_5548_, 1);
lean_ctor_set(v___x_5548_, 0, v___x_5550_);
v___x_5552_ = v___x_5548_;
goto v_reusejp_5551_;
}
else
{
lean_object* v_reuseFailAlloc_5553_; 
v_reuseFailAlloc_5553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5553_, 0, v___x_5550_);
v___x_5552_ = v_reuseFailAlloc_5553_;
goto v_reusejp_5551_;
}
v_reusejp_5551_:
{
return v___x_5552_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg___boxed(lean_object* v_msg_5555_, lean_object* v___y_5556_, lean_object* v___y_5557_, lean_object* v___y_5558_, lean_object* v___y_5559_, lean_object* v___y_5560_, lean_object* v___y_5561_, lean_object* v___y_5562_){
_start:
{
lean_object* v_res_5563_; 
v_res_5563_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v_msg_5555_, v___y_5556_, v___y_5557_, v___y_5558_, v___y_5559_, v___y_5560_, v___y_5561_);
lean_dec(v___y_5561_);
lean_dec_ref(v___y_5560_);
lean_dec(v___y_5559_);
lean_dec_ref(v___y_5558_);
lean_dec(v___y_5557_);
lean_dec_ref(v___y_5556_);
return v_res_5563_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1(void){
_start:
{
lean_object* v___x_5565_; lean_object* v___x_5566_; 
v___x_5565_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__0));
v___x_5566_ = l_Lean_stringToMessageData(v___x_5565_);
return v___x_5566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(lean_object* v_as_5567_, size_t v_sz_5568_, size_t v_i_5569_, lean_object* v_b_5570_, lean_object* v___y_5571_, lean_object* v___y_5572_, lean_object* v___y_5573_, lean_object* v___y_5574_, lean_object* v___y_5575_, lean_object* v___y_5576_){
_start:
{
lean_object* v_a_5579_; uint8_t v___x_5583_; 
v___x_5583_ = lean_usize_dec_lt(v_i_5569_, v_sz_5568_);
if (v___x_5583_ == 0)
{
lean_object* v___x_5584_; 
v___x_5584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5584_, 0, v_b_5570_);
return v___x_5584_;
}
else
{
lean_object* v___x_5585_; lean_object* v_a_5586_; lean_object* v___x_5587_; 
v___x_5585_ = lean_box(0);
v_a_5586_ = lean_array_uget_borrowed(v_as_5567_, v_i_5569_);
lean_inc(v_a_5586_);
v___x_5587_ = l_Lean_MVarId_getType(v_a_5586_, v___y_5573_, v___y_5574_, v___y_5575_, v___y_5576_);
if (lean_obj_tag(v___x_5587_) == 0)
{
lean_object* v_a_5588_; lean_object* v___x_5589_; 
v_a_5588_ = lean_ctor_get(v___x_5587_, 0);
lean_inc(v_a_5588_);
lean_dec_ref_known(v___x_5587_, 1);
lean_inc(v_a_5586_);
v___x_5589_ = l_Lean_MVarId_getType(v_a_5586_, v___y_5573_, v___y_5574_, v___y_5575_, v___y_5576_);
if (lean_obj_tag(v___x_5589_) == 0)
{
lean_object* v_a_5590_; lean_object* v___x_5591_; 
v_a_5590_ = lean_ctor_get(v___x_5589_, 0);
lean_inc(v_a_5590_);
lean_dec_ref_known(v___x_5589_, 1);
v___x_5591_ = l_Lean_getRecAppSyntax_x3f(v_a_5590_);
lean_dec(v_a_5590_);
if (lean_obj_tag(v___x_5591_) == 1)
{
lean_object* v_val_5592_; lean_object* v___x_5593_; lean_object* v___x_5594_; 
v_val_5592_ = lean_ctor_get(v___x_5591_, 0);
lean_inc(v_val_5592_);
lean_dec_ref_known(v___x_5591_, 1);
v___x_5593_ = l_Lean_Expr_mdataExpr_x21(v_a_5588_);
lean_dec(v_a_5588_);
lean_inc(v_a_5586_);
v___x_5594_ = l_Lean_MVarId_setType___redArg(v_a_5586_, v___x_5593_, v___y_5574_);
if (lean_obj_tag(v___x_5594_) == 0)
{
lean_object* v_toCold_5595_; lean_object* v_currRecDepth_5596_; lean_object* v_ref_5597_; uint8_t v_diag_5598_; uint8_t v_suppressElabErrors_5599_; lean_object* v_ref_5600_; lean_object* v___x_5601_; lean_object* v___x_5602_; 
lean_dec_ref_known(v___x_5594_, 1);
v_toCold_5595_ = lean_ctor_get(v___y_5575_, 0);
v_currRecDepth_5596_ = lean_ctor_get(v___y_5575_, 1);
v_ref_5597_ = lean_ctor_get(v___y_5575_, 2);
v_diag_5598_ = lean_ctor_get_uint8(v___y_5575_, sizeof(void*)*3);
v_suppressElabErrors_5599_ = lean_ctor_get_uint8(v___y_5575_, sizeof(void*)*3 + 1);
v_ref_5600_ = l_Lean_replaceRef(v_val_5592_, v_ref_5597_);
lean_dec(v_val_5592_);
lean_inc(v_currRecDepth_5596_);
lean_inc_ref(v_toCold_5595_);
v___x_5601_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5601_, 0, v_toCold_5595_);
lean_ctor_set(v___x_5601_, 1, v_currRecDepth_5596_);
lean_ctor_set(v___x_5601_, 2, v_ref_5600_);
lean_ctor_set_uint8(v___x_5601_, sizeof(void*)*3, v_diag_5598_);
lean_ctor_set_uint8(v___x_5601_, sizeof(void*)*3 + 1, v_suppressElabErrors_5599_);
lean_inc(v_a_5586_);
v___x_5602_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(v_a_5586_, v___y_5571_, v___y_5572_, v___y_5573_, v___y_5574_, v___x_5601_, v___y_5576_);
lean_dec_ref_known(v___x_5601_, 3);
if (lean_obj_tag(v___x_5602_) == 0)
{
lean_dec_ref_known(v___x_5602_, 1);
v_a_5579_ = v___x_5585_;
goto v___jp_5578_;
}
else
{
return v___x_5602_;
}
}
else
{
lean_dec(v_val_5592_);
return v___x_5594_;
}
}
else
{
lean_object* v___x_5603_; lean_object* v___x_5604_; lean_object* v___x_5605_; lean_object* v___x_5606_; 
lean_dec(v___x_5591_);
v___x_5603_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1);
v___x_5604_ = l_Lean_indentExpr(v_a_5588_);
v___x_5605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5605_, 0, v___x_5603_);
lean_ctor_set(v___x_5605_, 1, v___x_5604_);
v___x_5606_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v___x_5605_, v___y_5571_, v___y_5572_, v___y_5573_, v___y_5574_, v___y_5575_, v___y_5576_);
if (lean_obj_tag(v___x_5606_) == 0)
{
lean_dec_ref_known(v___x_5606_, 1);
v_a_5579_ = v___x_5585_;
goto v___jp_5578_;
}
else
{
return v___x_5606_;
}
}
}
else
{
lean_object* v_a_5607_; lean_object* v___x_5609_; uint8_t v_isShared_5610_; uint8_t v_isSharedCheck_5614_; 
lean_dec(v_a_5588_);
v_a_5607_ = lean_ctor_get(v___x_5589_, 0);
v_isSharedCheck_5614_ = !lean_is_exclusive(v___x_5589_);
if (v_isSharedCheck_5614_ == 0)
{
v___x_5609_ = v___x_5589_;
v_isShared_5610_ = v_isSharedCheck_5614_;
goto v_resetjp_5608_;
}
else
{
lean_inc(v_a_5607_);
lean_dec(v___x_5589_);
v___x_5609_ = lean_box(0);
v_isShared_5610_ = v_isSharedCheck_5614_;
goto v_resetjp_5608_;
}
v_resetjp_5608_:
{
lean_object* v___x_5612_; 
if (v_isShared_5610_ == 0)
{
v___x_5612_ = v___x_5609_;
goto v_reusejp_5611_;
}
else
{
lean_object* v_reuseFailAlloc_5613_; 
v_reuseFailAlloc_5613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5613_, 0, v_a_5607_);
v___x_5612_ = v_reuseFailAlloc_5613_;
goto v_reusejp_5611_;
}
v_reusejp_5611_:
{
return v___x_5612_;
}
}
}
}
else
{
lean_object* v_a_5615_; lean_object* v___x_5617_; uint8_t v_isShared_5618_; uint8_t v_isSharedCheck_5622_; 
v_a_5615_ = lean_ctor_get(v___x_5587_, 0);
v_isSharedCheck_5622_ = !lean_is_exclusive(v___x_5587_);
if (v_isSharedCheck_5622_ == 0)
{
v___x_5617_ = v___x_5587_;
v_isShared_5618_ = v_isSharedCheck_5622_;
goto v_resetjp_5616_;
}
else
{
lean_inc(v_a_5615_);
lean_dec(v___x_5587_);
v___x_5617_ = lean_box(0);
v_isShared_5618_ = v_isSharedCheck_5622_;
goto v_resetjp_5616_;
}
v_resetjp_5616_:
{
lean_object* v___x_5620_; 
if (v_isShared_5618_ == 0)
{
v___x_5620_ = v___x_5617_;
goto v_reusejp_5619_;
}
else
{
lean_object* v_reuseFailAlloc_5621_; 
v_reuseFailAlloc_5621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5621_, 0, v_a_5615_);
v___x_5620_ = v_reuseFailAlloc_5621_;
goto v_reusejp_5619_;
}
v_reusejp_5619_:
{
return v___x_5620_;
}
}
}
}
v___jp_5578_:
{
size_t v___x_5580_; size_t v___x_5581_; 
v___x_5580_ = ((size_t)1ULL);
v___x_5581_ = lean_usize_add(v_i_5569_, v___x_5580_);
v_i_5569_ = v___x_5581_;
v_b_5570_ = v_a_5579_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___boxed(lean_object* v_as_5623_, lean_object* v_sz_5624_, lean_object* v_i_5625_, lean_object* v_b_5626_, lean_object* v___y_5627_, lean_object* v___y_5628_, lean_object* v___y_5629_, lean_object* v___y_5630_, lean_object* v___y_5631_, lean_object* v___y_5632_, lean_object* v___y_5633_){
_start:
{
size_t v_sz_boxed_5634_; size_t v_i_boxed_5635_; lean_object* v_res_5636_; 
v_sz_boxed_5634_ = lean_unbox_usize(v_sz_5624_);
lean_dec(v_sz_5624_);
v_i_boxed_5635_ = lean_unbox_usize(v_i_5625_);
lean_dec(v_i_5625_);
v_res_5636_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(v_as_5623_, v_sz_boxed_5634_, v_i_boxed_5635_, v_b_5626_, v___y_5627_, v___y_5628_, v___y_5629_, v___y_5630_, v___y_5631_, v___y_5632_);
lean_dec(v___y_5632_);
lean_dec_ref(v___y_5631_);
lean_dec(v___y_5630_);
lean_dec_ref(v___y_5629_);
lean_dec(v___y_5628_);
lean_dec_ref(v___y_5627_);
lean_dec_ref(v_as_5623_);
return v_res_5636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(lean_object* v_as_5637_, size_t v_i_5638_, size_t v_stop_5639_, lean_object* v_b_5640_, lean_object* v___y_5641_, lean_object* v___y_5642_, lean_object* v___y_5643_, lean_object* v___y_5644_){
_start:
{
uint8_t v___x_5646_; 
v___x_5646_ = lean_usize_dec_eq(v_i_5638_, v_stop_5639_);
if (v___x_5646_ == 0)
{
lean_object* v___x_5647_; lean_object* v___x_5648_; 
v___x_5647_ = lean_array_uget_borrowed(v_as_5637_, v_i_5638_);
lean_inc(v___x_5647_);
v___x_5648_ = l_Lean_MVarId_getType(v___x_5647_, v___y_5641_, v___y_5642_, v___y_5643_, v___y_5644_);
if (lean_obj_tag(v___x_5648_) == 0)
{
lean_object* v_a_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; 
v_a_5649_ = lean_ctor_get(v___x_5648_, 0);
lean_inc(v_a_5649_);
lean_dec_ref_known(v___x_5648_, 1);
v___x_5650_ = l_Lean_Expr_mdataExpr_x21(v_a_5649_);
lean_dec(v_a_5649_);
lean_inc(v___x_5647_);
v___x_5651_ = l_Lean_MVarId_setType___redArg(v___x_5647_, v___x_5650_, v___y_5642_);
if (lean_obj_tag(v___x_5651_) == 0)
{
lean_object* v_a_5652_; size_t v___x_5653_; size_t v___x_5654_; 
v_a_5652_ = lean_ctor_get(v___x_5651_, 0);
lean_inc(v_a_5652_);
lean_dec_ref_known(v___x_5651_, 1);
v___x_5653_ = ((size_t)1ULL);
v___x_5654_ = lean_usize_add(v_i_5638_, v___x_5653_);
v_i_5638_ = v___x_5654_;
v_b_5640_ = v_a_5652_;
goto _start;
}
else
{
return v___x_5651_;
}
}
else
{
lean_object* v_a_5656_; lean_object* v___x_5658_; uint8_t v_isShared_5659_; uint8_t v_isSharedCheck_5663_; 
v_a_5656_ = lean_ctor_get(v___x_5648_, 0);
v_isSharedCheck_5663_ = !lean_is_exclusive(v___x_5648_);
if (v_isSharedCheck_5663_ == 0)
{
v___x_5658_ = v___x_5648_;
v_isShared_5659_ = v_isSharedCheck_5663_;
goto v_resetjp_5657_;
}
else
{
lean_inc(v_a_5656_);
lean_dec(v___x_5648_);
v___x_5658_ = lean_box(0);
v_isShared_5659_ = v_isSharedCheck_5663_;
goto v_resetjp_5657_;
}
v_resetjp_5657_:
{
lean_object* v___x_5661_; 
if (v_isShared_5659_ == 0)
{
v___x_5661_ = v___x_5658_;
goto v_reusejp_5660_;
}
else
{
lean_object* v_reuseFailAlloc_5662_; 
v_reuseFailAlloc_5662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5662_, 0, v_a_5656_);
v___x_5661_ = v_reuseFailAlloc_5662_;
goto v_reusejp_5660_;
}
v_reusejp_5660_:
{
return v___x_5661_;
}
}
}
}
else
{
lean_object* v___x_5664_; 
v___x_5664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5664_, 0, v_b_5640_);
return v___x_5664_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg___boxed(lean_object* v_as_5665_, lean_object* v_i_5666_, lean_object* v_stop_5667_, lean_object* v_b_5668_, lean_object* v___y_5669_, lean_object* v___y_5670_, lean_object* v___y_5671_, lean_object* v___y_5672_, lean_object* v___y_5673_){
_start:
{
size_t v_i_boxed_5674_; size_t v_stop_boxed_5675_; lean_object* v_res_5676_; 
v_i_boxed_5674_ = lean_unbox_usize(v_i_5666_);
lean_dec(v_i_5666_);
v_stop_boxed_5675_ = lean_unbox_usize(v_stop_5667_);
lean_dec(v_stop_5667_);
v_res_5676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v_as_5665_, v_i_boxed_5674_, v_stop_boxed_5675_, v_b_5668_, v___y_5669_, v___y_5670_, v___y_5671_, v___y_5672_);
lean_dec(v___y_5672_);
lean_dec_ref(v___y_5671_);
lean_dec(v___y_5670_);
lean_dec_ref(v___y_5669_);
lean_dec_ref(v_as_5665_);
return v_res_5676_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3(lean_object* v___x_5677_, lean_object* v___x_5678_, lean_object* v___x_5679_, lean_object* v___y_5680_, lean_object* v___y_5681_, lean_object* v___y_5682_, lean_object* v___y_5683_, lean_object* v___y_5684_, lean_object* v___y_5685_){
_start:
{
if (lean_obj_tag(v___x_5677_) == 0)
{
lean_object* v___x_5687_; size_t v_sz_5688_; size_t v___x_5689_; lean_object* v___x_5690_; 
v___x_5687_ = lean_box(0);
v_sz_5688_ = lean_array_size(v___x_5678_);
v___x_5689_ = ((size_t)0ULL);
v___x_5690_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(v___x_5678_, v_sz_5688_, v___x_5689_, v___x_5687_, v___y_5680_, v___y_5681_, v___y_5682_, v___y_5683_, v___y_5684_, v___y_5685_);
lean_dec_ref(v___x_5678_);
if (lean_obj_tag(v___x_5690_) == 0)
{
lean_object* v___x_5692_; uint8_t v_isShared_5693_; uint8_t v_isSharedCheck_5697_; 
v_isSharedCheck_5697_ = !lean_is_exclusive(v___x_5690_);
if (v_isSharedCheck_5697_ == 0)
{
lean_object* v_unused_5698_; 
v_unused_5698_ = lean_ctor_get(v___x_5690_, 0);
lean_dec(v_unused_5698_);
v___x_5692_ = v___x_5690_;
v_isShared_5693_ = v_isSharedCheck_5697_;
goto v_resetjp_5691_;
}
else
{
lean_dec(v___x_5690_);
v___x_5692_ = lean_box(0);
v_isShared_5693_ = v_isSharedCheck_5697_;
goto v_resetjp_5691_;
}
v_resetjp_5691_:
{
lean_object* v___x_5695_; 
if (v_isShared_5693_ == 0)
{
lean_ctor_set(v___x_5692_, 0, v___x_5687_);
v___x_5695_ = v___x_5692_;
goto v_reusejp_5694_;
}
else
{
lean_object* v_reuseFailAlloc_5696_; 
v_reuseFailAlloc_5696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5696_, 0, v___x_5687_);
v___x_5695_ = v_reuseFailAlloc_5696_;
goto v_reusejp_5694_;
}
v_reusejp_5694_:
{
return v___x_5695_;
}
}
}
else
{
return v___x_5690_;
}
}
else
{
lean_object* v_val_5699_; lean_object* v___x_5701_; uint8_t v_isShared_5702_; uint8_t v_isSharedCheck_5766_; 
v_val_5699_ = lean_ctor_get(v___x_5677_, 0);
v_isSharedCheck_5766_ = !lean_is_exclusive(v___x_5677_);
if (v_isSharedCheck_5766_ == 0)
{
v___x_5701_ = v___x_5677_;
v_isShared_5702_ = v_isSharedCheck_5766_;
goto v_resetjp_5700_;
}
else
{
lean_inc(v_val_5699_);
lean_dec(v___x_5677_);
v___x_5701_ = lean_box(0);
v_isShared_5702_ = v_isSharedCheck_5766_;
goto v_resetjp_5700_;
}
v_resetjp_5700_:
{
lean_object* v_ref_5703_; lean_object* v_tactic_5704_; lean_object* v_toCold_5705_; lean_object* v_currRecDepth_5706_; lean_object* v_ref_5707_; uint8_t v_diag_5708_; uint8_t v_suppressElabErrors_5709_; lean_object* v___x_5710_; lean_object* v___x_5711_; lean_object* v_ref_5712_; lean_object* v___x_5713_; lean_object* v___y_5739_; lean_object* v___y_5756_; uint8_t v___x_5757_; 
v_ref_5703_ = lean_ctor_get(v_val_5699_, 0);
lean_inc(v_ref_5703_);
v_tactic_5704_ = lean_ctor_get(v_val_5699_, 1);
lean_inc(v_tactic_5704_);
lean_dec(v_val_5699_);
v_toCold_5705_ = lean_ctor_get(v___y_5684_, 0);
v_currRecDepth_5706_ = lean_ctor_get(v___y_5684_, 1);
v_ref_5707_ = lean_ctor_get(v___y_5684_, 2);
v_diag_5708_ = lean_ctor_get_uint8(v___y_5684_, sizeof(void*)*3);
v_suppressElabErrors_5709_ = lean_ctor_get_uint8(v___y_5684_, sizeof(void*)*3 + 1);
v___x_5710_ = lean_unsigned_to_nat(0u);
v___x_5711_ = lean_array_get_size(v___x_5678_);
v_ref_5712_ = l_Lean_replaceRef(v_ref_5703_, v_ref_5707_);
lean_inc(v_currRecDepth_5706_);
lean_inc_ref(v_toCold_5705_);
v___x_5713_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5713_, 0, v_toCold_5705_);
lean_ctor_set(v___x_5713_, 1, v_currRecDepth_5706_);
lean_ctor_set(v___x_5713_, 2, v_ref_5712_);
lean_ctor_set_uint8(v___x_5713_, sizeof(void*)*3, v_diag_5708_);
lean_ctor_set_uint8(v___x_5713_, sizeof(void*)*3 + 1, v_suppressElabErrors_5709_);
v___x_5757_ = lean_nat_dec_lt(v___x_5710_, v___x_5711_);
if (v___x_5757_ == 0)
{
goto v___jp_5740_;
}
else
{
lean_object* v___x_5758_; uint8_t v___x_5759_; 
v___x_5758_ = lean_box(0);
v___x_5759_ = lean_nat_dec_le(v___x_5711_, v___x_5711_);
if (v___x_5759_ == 0)
{
if (v___x_5757_ == 0)
{
goto v___jp_5740_;
}
else
{
size_t v___x_5760_; size_t v___x_5761_; lean_object* v___x_5762_; 
v___x_5760_ = ((size_t)0ULL);
v___x_5761_ = lean_usize_of_nat(v___x_5711_);
v___x_5762_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v___x_5678_, v___x_5760_, v___x_5761_, v___x_5758_, v___y_5682_, v___y_5683_, v___x_5713_, v___y_5685_);
v___y_5756_ = v___x_5762_;
goto v___jp_5755_;
}
}
else
{
size_t v___x_5763_; size_t v___x_5764_; lean_object* v___x_5765_; 
v___x_5763_ = ((size_t)0ULL);
v___x_5764_ = lean_usize_of_nat(v___x_5711_);
v___x_5765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v___x_5678_, v___x_5763_, v___x_5764_, v___x_5758_, v___y_5682_, v___y_5683_, v___x_5713_, v___y_5685_);
v___y_5756_ = v___x_5765_;
goto v___jp_5755_;
}
}
v___jp_5714_:
{
lean_object* v___x_5715_; lean_object* v___x_5716_; lean_object* v___f_5717_; lean_object* v___x_5718_; 
v___x_5715_ = lean_array_get(v___x_5679_, v___x_5678_, v___x_5710_);
v___x_5716_ = lean_array_to_list(v___x_5678_);
v___f_5717_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2___boxed), 12, 3);
lean_closure_set(v___f_5717_, 0, v___x_5716_);
lean_closure_set(v___f_5717_, 1, v_tactic_5704_);
lean_closure_set(v___f_5717_, 2, v_ref_5703_);
v___x_5718_ = l_Lean_Elab_Tactic_run(v___x_5715_, v___f_5717_, v___y_5680_, v___y_5681_, v___y_5682_, v___y_5683_, v___x_5713_, v___y_5685_);
if (lean_obj_tag(v___x_5718_) == 0)
{
lean_object* v_a_5719_; lean_object* v___x_5721_; uint8_t v_isShared_5722_; uint8_t v_isSharedCheck_5729_; 
v_a_5719_ = lean_ctor_get(v___x_5718_, 0);
v_isSharedCheck_5729_ = !lean_is_exclusive(v___x_5718_);
if (v_isSharedCheck_5729_ == 0)
{
v___x_5721_ = v___x_5718_;
v_isShared_5722_ = v_isSharedCheck_5729_;
goto v_resetjp_5720_;
}
else
{
lean_inc(v_a_5719_);
lean_dec(v___x_5718_);
v___x_5721_ = lean_box(0);
v_isShared_5722_ = v_isSharedCheck_5729_;
goto v_resetjp_5720_;
}
v_resetjp_5720_:
{
uint8_t v___x_5723_; 
v___x_5723_ = l_List_isEmpty___redArg(v_a_5719_);
if (v___x_5723_ == 0)
{
lean_object* v___x_5724_; 
lean_del_object(v___x_5721_);
v___x_5724_ = l_Lean_Elab_Term_reportUnsolvedGoals(v_a_5719_, v___y_5682_, v___y_5683_, v___x_5713_, v___y_5685_);
lean_dec_ref_known(v___x_5713_, 3);
return v___x_5724_;
}
else
{
lean_object* v___x_5725_; lean_object* v___x_5727_; 
lean_dec(v_a_5719_);
lean_dec_ref_known(v___x_5713_, 3);
v___x_5725_ = lean_box(0);
if (v_isShared_5722_ == 0)
{
lean_ctor_set(v___x_5721_, 0, v___x_5725_);
v___x_5727_ = v___x_5721_;
goto v_reusejp_5726_;
}
else
{
lean_object* v_reuseFailAlloc_5728_; 
v_reuseFailAlloc_5728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5728_, 0, v___x_5725_);
v___x_5727_ = v_reuseFailAlloc_5728_;
goto v_reusejp_5726_;
}
v_reusejp_5726_:
{
return v___x_5727_;
}
}
}
}
else
{
lean_object* v_a_5730_; lean_object* v___x_5732_; uint8_t v_isShared_5733_; uint8_t v_isSharedCheck_5737_; 
lean_dec_ref_known(v___x_5713_, 3);
v_a_5730_ = lean_ctor_get(v___x_5718_, 0);
v_isSharedCheck_5737_ = !lean_is_exclusive(v___x_5718_);
if (v_isSharedCheck_5737_ == 0)
{
v___x_5732_ = v___x_5718_;
v_isShared_5733_ = v_isSharedCheck_5737_;
goto v_resetjp_5731_;
}
else
{
lean_inc(v_a_5730_);
lean_dec(v___x_5718_);
v___x_5732_ = lean_box(0);
v_isShared_5733_ = v_isSharedCheck_5737_;
goto v_resetjp_5731_;
}
v_resetjp_5731_:
{
lean_object* v___x_5735_; 
if (v_isShared_5733_ == 0)
{
v___x_5735_ = v___x_5732_;
goto v_reusejp_5734_;
}
else
{
lean_object* v_reuseFailAlloc_5736_; 
v_reuseFailAlloc_5736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5736_, 0, v_a_5730_);
v___x_5735_ = v_reuseFailAlloc_5736_;
goto v_reusejp_5734_;
}
v_reusejp_5734_:
{
return v___x_5735_;
}
}
}
}
v___jp_5738_:
{
if (lean_obj_tag(v___y_5739_) == 0)
{
lean_dec_ref_known(v___y_5739_, 1);
goto v___jp_5714_;
}
else
{
lean_dec_ref_known(v___x_5713_, 3);
lean_dec(v_tactic_5704_);
lean_dec(v_ref_5703_);
lean_dec_ref(v___x_5678_);
return v___y_5739_;
}
}
v___jp_5740_:
{
uint8_t v___x_5741_; 
v___x_5741_ = lean_nat_dec_eq(v___x_5711_, v___x_5710_);
if (v___x_5741_ == 0)
{
uint8_t v___x_5742_; 
lean_del_object(v___x_5701_);
v___x_5742_ = lean_nat_dec_lt(v___x_5710_, v___x_5711_);
if (v___x_5742_ == 0)
{
goto v___jp_5714_;
}
else
{
lean_object* v___x_5743_; uint8_t v___x_5744_; 
v___x_5743_ = lean_box(0);
v___x_5744_ = lean_nat_dec_le(v___x_5711_, v___x_5711_);
if (v___x_5744_ == 0)
{
if (v___x_5742_ == 0)
{
goto v___jp_5714_;
}
else
{
size_t v___x_5745_; size_t v___x_5746_; lean_object* v___x_5747_; 
v___x_5745_ = ((size_t)0ULL);
v___x_5746_ = lean_usize_of_nat(v___x_5711_);
v___x_5747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v___x_5678_, v___x_5745_, v___x_5746_, v___x_5743_, v___y_5680_, v___y_5681_, v___y_5682_, v___y_5683_, v___x_5713_, v___y_5685_);
v___y_5739_ = v___x_5747_;
goto v___jp_5738_;
}
}
else
{
size_t v___x_5748_; size_t v___x_5749_; lean_object* v___x_5750_; 
v___x_5748_ = ((size_t)0ULL);
v___x_5749_ = lean_usize_of_nat(v___x_5711_);
v___x_5750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v___x_5678_, v___x_5748_, v___x_5749_, v___x_5743_, v___y_5680_, v___y_5681_, v___y_5682_, v___y_5683_, v___x_5713_, v___y_5685_);
v___y_5739_ = v___x_5750_;
goto v___jp_5738_;
}
}
}
else
{
lean_object* v___x_5751_; lean_object* v___x_5753_; 
lean_dec_ref_known(v___x_5713_, 3);
lean_dec(v_tactic_5704_);
lean_dec(v_ref_5703_);
lean_dec_ref(v___x_5678_);
v___x_5751_ = lean_box(0);
if (v_isShared_5702_ == 0)
{
lean_ctor_set_tag(v___x_5701_, 0);
lean_ctor_set(v___x_5701_, 0, v___x_5751_);
v___x_5753_ = v___x_5701_;
goto v_reusejp_5752_;
}
else
{
lean_object* v_reuseFailAlloc_5754_; 
v_reuseFailAlloc_5754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5754_, 0, v___x_5751_);
v___x_5753_ = v_reuseFailAlloc_5754_;
goto v_reusejp_5752_;
}
v_reusejp_5752_:
{
return v___x_5753_;
}
}
}
v___jp_5755_:
{
if (lean_obj_tag(v___y_5756_) == 0)
{
lean_dec_ref_known(v___y_5756_, 1);
goto v___jp_5740_;
}
else
{
lean_dec_ref_known(v___x_5713_, 3);
lean_dec(v_tactic_5704_);
lean_dec(v_ref_5703_);
lean_del_object(v___x_5701_);
lean_dec_ref(v___x_5678_);
return v___y_5756_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3___boxed(lean_object* v___x_5767_, lean_object* v___x_5768_, lean_object* v___x_5769_, lean_object* v___y_5770_, lean_object* v___y_5771_, lean_object* v___y_5772_, lean_object* v___y_5773_, lean_object* v___y_5774_, lean_object* v___y_5775_, lean_object* v___y_5776_){
_start:
{
lean_object* v_res_5777_; 
v_res_5777_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3(v___x_5767_, v___x_5768_, v___x_5769_, v___y_5770_, v___y_5771_, v___y_5772_, v___y_5773_, v___y_5774_, v___y_5775_);
lean_dec(v___y_5775_);
lean_dec_ref(v___y_5774_);
lean_dec(v___y_5773_);
lean_dec_ref(v___y_5772_);
lean_dec(v___y_5771_);
lean_dec_ref(v___y_5770_);
lean_dec(v___x_5769_);
return v_res_5777_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0(lean_object* v_x_5778_){
_start:
{
uint8_t v___x_5779_; 
v___x_5779_ = 0;
return v___x_5779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0___boxed(lean_object* v_x_5780_){
_start:
{
uint8_t v_res_5781_; lean_object* v_r_5782_; 
v_res_5781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0(v_x_5780_);
lean_dec(v_x_5780_);
v_r_5782_ = lean_box(v_res_5781_);
return v_r_5782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(lean_object* v_as_5789_, size_t v_sz_5790_, size_t v_i_5791_, lean_object* v_b_5792_, lean_object* v___y_5793_, lean_object* v___y_5794_, lean_object* v___y_5795_, lean_object* v___y_5796_){
_start:
{
uint8_t v___x_5798_; 
v___x_5798_ = lean_usize_dec_lt(v_i_5791_, v_sz_5790_);
if (v___x_5798_ == 0)
{
lean_object* v___x_5799_; 
v___x_5799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5799_, 0, v_b_5792_);
return v___x_5799_;
}
else
{
lean_object* v_snd_5800_; lean_object* v_fst_5801_; lean_object* v___x_5803_; uint8_t v_isShared_5804_; uint8_t v_isSharedCheck_5873_; 
v_snd_5800_ = lean_ctor_get(v_b_5792_, 1);
v_fst_5801_ = lean_ctor_get(v_b_5792_, 0);
v_isSharedCheck_5873_ = !lean_is_exclusive(v_b_5792_);
if (v_isSharedCheck_5873_ == 0)
{
v___x_5803_ = v_b_5792_;
v_isShared_5804_ = v_isSharedCheck_5873_;
goto v_resetjp_5802_;
}
else
{
lean_inc(v_snd_5800_);
lean_inc(v_fst_5801_);
lean_dec(v_b_5792_);
v___x_5803_ = lean_box(0);
v_isShared_5804_ = v_isSharedCheck_5873_;
goto v_resetjp_5802_;
}
v_resetjp_5802_:
{
lean_object* v_array_5805_; lean_object* v_start_5806_; lean_object* v_stop_5807_; uint8_t v___x_5808_; 
v_array_5805_ = lean_ctor_get(v_snd_5800_, 0);
v_start_5806_ = lean_ctor_get(v_snd_5800_, 1);
v_stop_5807_ = lean_ctor_get(v_snd_5800_, 2);
v___x_5808_ = lean_nat_dec_lt(v_start_5806_, v_stop_5807_);
if (v___x_5808_ == 0)
{
lean_object* v___x_5810_; 
if (v_isShared_5804_ == 0)
{
v___x_5810_ = v___x_5803_;
goto v_reusejp_5809_;
}
else
{
lean_object* v_reuseFailAlloc_5812_; 
v_reuseFailAlloc_5812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5812_, 0, v_fst_5801_);
lean_ctor_set(v_reuseFailAlloc_5812_, 1, v_snd_5800_);
v___x_5810_ = v_reuseFailAlloc_5812_;
goto v_reusejp_5809_;
}
v_reusejp_5809_:
{
lean_object* v___x_5811_; 
v___x_5811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5811_, 0, v___x_5810_);
return v___x_5811_;
}
}
else
{
lean_object* v___x_5814_; uint8_t v_isShared_5815_; uint8_t v_isSharedCheck_5869_; 
lean_inc(v_stop_5807_);
lean_inc(v_start_5806_);
lean_inc_ref(v_array_5805_);
v_isSharedCheck_5869_ = !lean_is_exclusive(v_snd_5800_);
if (v_isSharedCheck_5869_ == 0)
{
lean_object* v_unused_5870_; lean_object* v_unused_5871_; lean_object* v_unused_5872_; 
v_unused_5870_ = lean_ctor_get(v_snd_5800_, 2);
lean_dec(v_unused_5870_);
v_unused_5871_ = lean_ctor_get(v_snd_5800_, 1);
lean_dec(v_unused_5871_);
v_unused_5872_ = lean_ctor_get(v_snd_5800_, 0);
lean_dec(v_unused_5872_);
v___x_5814_ = v_snd_5800_;
v_isShared_5815_ = v_isSharedCheck_5869_;
goto v_resetjp_5813_;
}
else
{
lean_dec(v_snd_5800_);
v___x_5814_ = lean_box(0);
v_isShared_5815_ = v_isSharedCheck_5869_;
goto v_resetjp_5813_;
}
v_resetjp_5813_:
{
lean_object* v_array_5816_; lean_object* v_start_5817_; lean_object* v_stop_5818_; lean_object* v___x_5819_; lean_object* v___x_5820_; lean_object* v___x_5821_; lean_object* v___x_5823_; 
v_array_5816_ = lean_ctor_get(v_fst_5801_, 0);
v_start_5817_ = lean_ctor_get(v_fst_5801_, 1);
v_stop_5818_ = lean_ctor_get(v_fst_5801_, 2);
v___x_5819_ = lean_array_fget(v_array_5805_, v_start_5806_);
v___x_5820_ = lean_unsigned_to_nat(1u);
v___x_5821_ = lean_nat_add(v_start_5806_, v___x_5820_);
lean_dec(v_start_5806_);
if (v_isShared_5815_ == 0)
{
lean_ctor_set(v___x_5814_, 1, v___x_5821_);
v___x_5823_ = v___x_5814_;
goto v_reusejp_5822_;
}
else
{
lean_object* v_reuseFailAlloc_5868_; 
v_reuseFailAlloc_5868_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5868_, 0, v_array_5805_);
lean_ctor_set(v_reuseFailAlloc_5868_, 1, v___x_5821_);
lean_ctor_set(v_reuseFailAlloc_5868_, 2, v_stop_5807_);
v___x_5823_ = v_reuseFailAlloc_5868_;
goto v_reusejp_5822_;
}
v_reusejp_5822_:
{
uint8_t v___x_5824_; 
v___x_5824_ = lean_nat_dec_lt(v_start_5817_, v_stop_5818_);
if (v___x_5824_ == 0)
{
lean_object* v___x_5826_; 
lean_dec(v___x_5819_);
if (v_isShared_5804_ == 0)
{
lean_ctor_set(v___x_5803_, 1, v___x_5823_);
v___x_5826_ = v___x_5803_;
goto v_reusejp_5825_;
}
else
{
lean_object* v_reuseFailAlloc_5828_; 
v_reuseFailAlloc_5828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5828_, 0, v_fst_5801_);
lean_ctor_set(v_reuseFailAlloc_5828_, 1, v___x_5823_);
v___x_5826_ = v_reuseFailAlloc_5828_;
goto v_reusejp_5825_;
}
v_reusejp_5825_:
{
lean_object* v___x_5827_; 
v___x_5827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5827_, 0, v___x_5826_);
return v___x_5827_;
}
}
else
{
lean_object* v___x_5830_; uint8_t v_isShared_5831_; uint8_t v_isSharedCheck_5864_; 
lean_inc(v_stop_5818_);
lean_inc(v_start_5817_);
lean_inc_ref(v_array_5816_);
v_isSharedCheck_5864_ = !lean_is_exclusive(v_fst_5801_);
if (v_isSharedCheck_5864_ == 0)
{
lean_object* v_unused_5865_; lean_object* v_unused_5866_; lean_object* v_unused_5867_; 
v_unused_5865_ = lean_ctor_get(v_fst_5801_, 2);
lean_dec(v_unused_5865_);
v_unused_5866_ = lean_ctor_get(v_fst_5801_, 1);
lean_dec(v_unused_5866_);
v_unused_5867_ = lean_ctor_get(v_fst_5801_, 0);
lean_dec(v_unused_5867_);
v___x_5830_ = v_fst_5801_;
v_isShared_5831_ = v_isSharedCheck_5864_;
goto v_resetjp_5829_;
}
else
{
lean_dec(v_fst_5801_);
v___x_5830_ = lean_box(0);
v_isShared_5831_ = v_isSharedCheck_5864_;
goto v_resetjp_5829_;
}
v_resetjp_5829_:
{
lean_object* v___f_5832_; lean_object* v___x_5833_; lean_object* v_a_5834_; lean_object* v___x_5835_; lean_object* v___y_5836_; lean_object* v___x_5837_; lean_object* v___x_5839_; 
v___f_5832_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__0));
v___x_5833_ = lean_box(0);
v_a_5834_ = lean_array_uget_borrowed(v_as_5789_, v_i_5791_);
v___x_5835_ = lean_array_fget_borrowed(v_array_5816_, v_start_5817_);
lean_inc(v___x_5835_);
v___y_5836_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3___boxed), 10, 3);
lean_closure_set(v___y_5836_, 0, v___x_5819_);
lean_closure_set(v___y_5836_, 1, v___x_5835_);
lean_closure_set(v___y_5836_, 2, v___x_5833_);
v___x_5837_ = lean_nat_add(v_start_5817_, v___x_5820_);
lean_dec(v_start_5817_);
if (v_isShared_5831_ == 0)
{
lean_ctor_set(v___x_5830_, 1, v___x_5837_);
v___x_5839_ = v___x_5830_;
goto v_reusejp_5838_;
}
else
{
lean_object* v_reuseFailAlloc_5863_; 
v_reuseFailAlloc_5863_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5863_, 0, v_array_5816_);
lean_ctor_set(v_reuseFailAlloc_5863_, 1, v___x_5837_);
lean_ctor_set(v_reuseFailAlloc_5863_, 2, v_stop_5818_);
v___x_5839_ = v_reuseFailAlloc_5863_;
goto v_reusejp_5838_;
}
v_reusejp_5838_:
{
lean_object* v___x_5840_; lean_object* v___x_5841_; lean_object* v___x_5842_; lean_object* v___x_5843_; uint8_t v___x_5844_; lean_object* v___x_5845_; lean_object* v___x_5846_; lean_object* v___x_5847_; lean_object* v___x_5848_; 
lean_inc(v_a_5834_);
v___x_5840_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withDeclName___boxed), 10, 3);
lean_closure_set(v___x_5840_, 0, lean_box(0));
lean_closure_set(v___x_5840_, 1, v_a_5834_);
lean_closure_set(v___x_5840_, 2, v___y_5836_);
v___x_5841_ = lean_box(0);
v___x_5842_ = lean_box(0);
v___x_5843_ = lean_box(1);
v___x_5844_ = 0;
v___x_5845_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__1));
v___x_5846_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_5846_, 0, v___x_5841_);
lean_ctor_set(v___x_5846_, 1, v___x_5842_);
lean_ctor_set(v___x_5846_, 2, v___x_5841_);
lean_ctor_set(v___x_5846_, 3, v___f_5832_);
lean_ctor_set(v___x_5846_, 4, v___x_5843_);
lean_ctor_set(v___x_5846_, 5, v___x_5843_);
lean_ctor_set(v___x_5846_, 6, v___x_5841_);
lean_ctor_set(v___x_5846_, 7, v___x_5845_);
lean_ctor_set_uint8(v___x_5846_, sizeof(void*)*8, v___x_5824_);
lean_ctor_set_uint8(v___x_5846_, sizeof(void*)*8 + 1, v___x_5824_);
lean_ctor_set_uint8(v___x_5846_, sizeof(void*)*8 + 2, v___x_5824_);
lean_ctor_set_uint8(v___x_5846_, sizeof(void*)*8 + 3, v___x_5824_);
lean_ctor_set_uint8(v___x_5846_, sizeof(void*)*8 + 4, v___x_5844_);
lean_ctor_set_uint8(v___x_5846_, sizeof(void*)*8 + 5, v___x_5844_);
lean_ctor_set_uint8(v___x_5846_, sizeof(void*)*8 + 6, v___x_5844_);
lean_ctor_set_uint8(v___x_5846_, sizeof(void*)*8 + 7, v___x_5844_);
lean_ctor_set_uint8(v___x_5846_, sizeof(void*)*8 + 8, v___x_5824_);
lean_ctor_set_uint8(v___x_5846_, sizeof(void*)*8 + 9, v___x_5844_);
lean_ctor_set_uint8(v___x_5846_, sizeof(void*)*8 + 10, v___x_5824_);
v___x_5847_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__2));
v___x_5848_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_5840_, v___x_5846_, v___x_5847_, v___y_5793_, v___y_5794_, v___y_5795_, v___y_5796_);
if (lean_obj_tag(v___x_5848_) == 0)
{
lean_object* v___x_5850_; 
lean_dec_ref_known(v___x_5848_, 1);
if (v_isShared_5804_ == 0)
{
lean_ctor_set(v___x_5803_, 1, v___x_5823_);
lean_ctor_set(v___x_5803_, 0, v___x_5839_);
v___x_5850_ = v___x_5803_;
goto v_reusejp_5849_;
}
else
{
lean_object* v_reuseFailAlloc_5854_; 
v_reuseFailAlloc_5854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5854_, 0, v___x_5839_);
lean_ctor_set(v_reuseFailAlloc_5854_, 1, v___x_5823_);
v___x_5850_ = v_reuseFailAlloc_5854_;
goto v_reusejp_5849_;
}
v_reusejp_5849_:
{
size_t v___x_5851_; size_t v___x_5852_; 
v___x_5851_ = ((size_t)1ULL);
v___x_5852_ = lean_usize_add(v_i_5791_, v___x_5851_);
v_i_5791_ = v___x_5852_;
v_b_5792_ = v___x_5850_;
goto _start;
}
}
else
{
lean_object* v_a_5855_; lean_object* v___x_5857_; uint8_t v_isShared_5858_; uint8_t v_isSharedCheck_5862_; 
lean_dec_ref(v___x_5839_);
lean_dec_ref(v___x_5823_);
lean_del_object(v___x_5803_);
v_a_5855_ = lean_ctor_get(v___x_5848_, 0);
v_isSharedCheck_5862_ = !lean_is_exclusive(v___x_5848_);
if (v_isSharedCheck_5862_ == 0)
{
v___x_5857_ = v___x_5848_;
v_isShared_5858_ = v_isSharedCheck_5862_;
goto v_resetjp_5856_;
}
else
{
lean_inc(v_a_5855_);
lean_dec(v___x_5848_);
v___x_5857_ = lean_box(0);
v_isShared_5858_ = v_isSharedCheck_5862_;
goto v_resetjp_5856_;
}
v_resetjp_5856_:
{
lean_object* v___x_5860_; 
if (v_isShared_5858_ == 0)
{
v___x_5860_ = v___x_5857_;
goto v_reusejp_5859_;
}
else
{
lean_object* v_reuseFailAlloc_5861_; 
v_reuseFailAlloc_5861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5861_, 0, v_a_5855_);
v___x_5860_ = v_reuseFailAlloc_5861_;
goto v_reusejp_5859_;
}
v_reusejp_5859_:
{
return v___x_5860_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___boxed(lean_object* v_as_5874_, lean_object* v_sz_5875_, lean_object* v_i_5876_, lean_object* v_b_5877_, lean_object* v___y_5878_, lean_object* v___y_5879_, lean_object* v___y_5880_, lean_object* v___y_5881_, lean_object* v___y_5882_){
_start:
{
size_t v_sz_boxed_5883_; size_t v_i_boxed_5884_; lean_object* v_res_5885_; 
v_sz_boxed_5883_ = lean_unbox_usize(v_sz_5875_);
lean_dec(v_sz_5875_);
v_i_boxed_5884_ = lean_unbox_usize(v_i_5876_);
lean_dec(v_i_5876_);
v_res_5885_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(v_as_5874_, v_sz_boxed_5883_, v_i_boxed_5884_, v_b_5877_, v___y_5878_, v___y_5879_, v___y_5880_, v___y_5881_);
lean_dec(v___y_5881_);
lean_dec_ref(v___y_5880_);
lean_dec(v___y_5879_);
lean_dec_ref(v___y_5878_);
lean_dec_ref(v_as_5874_);
return v_res_5885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___lam__0(lean_object* v_value_5886_, lean_object* v_decrTactics_5887_, lean_object* v_argsPacker_5888_, lean_object* v_funNames_5889_, lean_object* v___y_5890_, lean_object* v___y_5891_, lean_object* v___y_5892_, lean_object* v___y_5893_){
_start:
{
lean_object* v___x_5895_; 
lean_inc_ref(v_value_5886_);
v___x_5895_ = l_Lean_Meta_getMVarsNoDelayed(v_value_5886_, v___y_5890_, v___y_5891_, v___y_5892_, v___y_5893_);
if (lean_obj_tag(v___x_5895_) == 0)
{
lean_object* v_a_5896_; lean_object* v___x_5897_; 
v_a_5896_ = lean_ctor_get(v___x_5895_, 0);
lean_inc(v_a_5896_);
lean_dec_ref_known(v___x_5895_, 1);
v___x_5897_ = l_Lean_Elab_WF_assignSubsumed(v_a_5896_, v___y_5890_, v___y_5891_, v___y_5892_, v___y_5893_);
lean_dec(v_a_5896_);
if (lean_obj_tag(v___x_5897_) == 0)
{
lean_object* v_a_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; 
v_a_5898_ = lean_ctor_get(v___x_5897_, 0);
lean_inc(v_a_5898_);
lean_dec_ref_known(v___x_5897_, 1);
v___x_5899_ = lean_array_get_size(v_decrTactics_5887_);
v___x_5900_ = l_Lean_Elab_WF_groupGoalsByFunction(v_argsPacker_5888_, v___x_5899_, v_a_5898_, v___y_5890_, v___y_5891_, v___y_5892_, v___y_5893_);
lean_dec(v_a_5898_);
if (lean_obj_tag(v___x_5900_) == 0)
{
lean_object* v_a_5901_; lean_object* v___x_5902_; lean_object* v___x_5903_; lean_object* v___x_5904_; lean_object* v___x_5905_; lean_object* v___x_5906_; size_t v_sz_5907_; size_t v___x_5908_; lean_object* v___x_5909_; 
v_a_5901_ = lean_ctor_get(v___x_5900_, 0);
lean_inc(v_a_5901_);
lean_dec_ref_known(v___x_5900_, 1);
v___x_5902_ = lean_unsigned_to_nat(0u);
v___x_5903_ = lean_array_get_size(v_a_5901_);
v___x_5904_ = l_Array_toSubarray___redArg(v_a_5901_, v___x_5902_, v___x_5903_);
v___x_5905_ = l_Array_toSubarray___redArg(v_decrTactics_5887_, v___x_5902_, v___x_5899_);
v___x_5906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5906_, 0, v___x_5904_);
lean_ctor_set(v___x_5906_, 1, v___x_5905_);
v_sz_5907_ = lean_array_size(v_funNames_5889_);
v___x_5908_ = ((size_t)0ULL);
v___x_5909_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(v_funNames_5889_, v_sz_5907_, v___x_5908_, v___x_5906_, v___y_5890_, v___y_5891_, v___y_5892_, v___y_5893_);
if (lean_obj_tag(v___x_5909_) == 0)
{
lean_object* v___x_5910_; 
lean_dec_ref_known(v___x_5909_, 1);
v___x_5910_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_value_5886_, v___y_5891_);
return v___x_5910_;
}
else
{
lean_object* v_a_5911_; lean_object* v___x_5913_; uint8_t v_isShared_5914_; uint8_t v_isSharedCheck_5918_; 
lean_dec_ref(v_value_5886_);
v_a_5911_ = lean_ctor_get(v___x_5909_, 0);
v_isSharedCheck_5918_ = !lean_is_exclusive(v___x_5909_);
if (v_isSharedCheck_5918_ == 0)
{
v___x_5913_ = v___x_5909_;
v_isShared_5914_ = v_isSharedCheck_5918_;
goto v_resetjp_5912_;
}
else
{
lean_inc(v_a_5911_);
lean_dec(v___x_5909_);
v___x_5913_ = lean_box(0);
v_isShared_5914_ = v_isSharedCheck_5918_;
goto v_resetjp_5912_;
}
v_resetjp_5912_:
{
lean_object* v___x_5916_; 
if (v_isShared_5914_ == 0)
{
v___x_5916_ = v___x_5913_;
goto v_reusejp_5915_;
}
else
{
lean_object* v_reuseFailAlloc_5917_; 
v_reuseFailAlloc_5917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5917_, 0, v_a_5911_);
v___x_5916_ = v_reuseFailAlloc_5917_;
goto v_reusejp_5915_;
}
v_reusejp_5915_:
{
return v___x_5916_;
}
}
}
}
else
{
lean_object* v_a_5919_; lean_object* v___x_5921_; uint8_t v_isShared_5922_; uint8_t v_isSharedCheck_5926_; 
lean_dec_ref(v_decrTactics_5887_);
lean_dec_ref(v_value_5886_);
v_a_5919_ = lean_ctor_get(v___x_5900_, 0);
v_isSharedCheck_5926_ = !lean_is_exclusive(v___x_5900_);
if (v_isSharedCheck_5926_ == 0)
{
v___x_5921_ = v___x_5900_;
v_isShared_5922_ = v_isSharedCheck_5926_;
goto v_resetjp_5920_;
}
else
{
lean_inc(v_a_5919_);
lean_dec(v___x_5900_);
v___x_5921_ = lean_box(0);
v_isShared_5922_ = v_isSharedCheck_5926_;
goto v_resetjp_5920_;
}
v_resetjp_5920_:
{
lean_object* v___x_5924_; 
if (v_isShared_5922_ == 0)
{
v___x_5924_ = v___x_5921_;
goto v_reusejp_5923_;
}
else
{
lean_object* v_reuseFailAlloc_5925_; 
v_reuseFailAlloc_5925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5925_, 0, v_a_5919_);
v___x_5924_ = v_reuseFailAlloc_5925_;
goto v_reusejp_5923_;
}
v_reusejp_5923_:
{
return v___x_5924_;
}
}
}
}
else
{
lean_object* v_a_5927_; lean_object* v___x_5929_; uint8_t v_isShared_5930_; uint8_t v_isSharedCheck_5934_; 
lean_dec_ref(v_decrTactics_5887_);
lean_dec_ref(v_value_5886_);
v_a_5927_ = lean_ctor_get(v___x_5897_, 0);
v_isSharedCheck_5934_ = !lean_is_exclusive(v___x_5897_);
if (v_isSharedCheck_5934_ == 0)
{
v___x_5929_ = v___x_5897_;
v_isShared_5930_ = v_isSharedCheck_5934_;
goto v_resetjp_5928_;
}
else
{
lean_inc(v_a_5927_);
lean_dec(v___x_5897_);
v___x_5929_ = lean_box(0);
v_isShared_5930_ = v_isSharedCheck_5934_;
goto v_resetjp_5928_;
}
v_resetjp_5928_:
{
lean_object* v___x_5932_; 
if (v_isShared_5930_ == 0)
{
v___x_5932_ = v___x_5929_;
goto v_reusejp_5931_;
}
else
{
lean_object* v_reuseFailAlloc_5933_; 
v_reuseFailAlloc_5933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5933_, 0, v_a_5927_);
v___x_5932_ = v_reuseFailAlloc_5933_;
goto v_reusejp_5931_;
}
v_reusejp_5931_:
{
return v___x_5932_;
}
}
}
}
else
{
lean_object* v_a_5935_; lean_object* v___x_5937_; uint8_t v_isShared_5938_; uint8_t v_isSharedCheck_5942_; 
lean_dec_ref(v_decrTactics_5887_);
lean_dec_ref(v_value_5886_);
v_a_5935_ = lean_ctor_get(v___x_5895_, 0);
v_isSharedCheck_5942_ = !lean_is_exclusive(v___x_5895_);
if (v_isSharedCheck_5942_ == 0)
{
v___x_5937_ = v___x_5895_;
v_isShared_5938_ = v_isSharedCheck_5942_;
goto v_resetjp_5936_;
}
else
{
lean_inc(v_a_5935_);
lean_dec(v___x_5895_);
v___x_5937_ = lean_box(0);
v_isShared_5938_ = v_isSharedCheck_5942_;
goto v_resetjp_5936_;
}
v_resetjp_5936_:
{
lean_object* v___x_5940_; 
if (v_isShared_5938_ == 0)
{
v___x_5940_ = v___x_5937_;
goto v_reusejp_5939_;
}
else
{
lean_object* v_reuseFailAlloc_5941_; 
v_reuseFailAlloc_5941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5941_, 0, v_a_5935_);
v___x_5940_ = v_reuseFailAlloc_5941_;
goto v_reusejp_5939_;
}
v_reusejp_5939_:
{
return v___x_5940_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___lam__0___boxed(lean_object* v_value_5943_, lean_object* v_decrTactics_5944_, lean_object* v_argsPacker_5945_, lean_object* v_funNames_5946_, lean_object* v___y_5947_, lean_object* v___y_5948_, lean_object* v___y_5949_, lean_object* v___y_5950_, lean_object* v___y_5951_){
_start:
{
lean_object* v_res_5952_; 
v_res_5952_ = l_Lean_Elab_WF_solveDecreasingGoals___lam__0(v_value_5943_, v_decrTactics_5944_, v_argsPacker_5945_, v_funNames_5946_, v___y_5947_, v___y_5948_, v___y_5949_, v___y_5950_);
lean_dec(v___y_5950_);
lean_dec_ref(v___y_5949_);
lean_dec(v___y_5948_);
lean_dec_ref(v___y_5947_);
lean_dec_ref(v_funNames_5946_);
lean_dec_ref(v_argsPacker_5945_);
return v_res_5952_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(lean_object* v___y_5953_, uint8_t v_isExporting_5954_, lean_object* v___x_5955_, lean_object* v___y_5956_, lean_object* v___x_5957_, lean_object* v_a_x3f_5958_){
_start:
{
lean_object* v___x_5960_; lean_object* v_env_5961_; lean_object* v_nextMacroScope_5962_; lean_object* v_ngen_5963_; lean_object* v_auxDeclNGen_5964_; lean_object* v_traceState_5965_; lean_object* v_messages_5966_; lean_object* v_infoState_5967_; lean_object* v_snapshotTasks_5968_; lean_object* v___x_5970_; uint8_t v_isShared_5971_; uint8_t v_isSharedCheck_5993_; 
v___x_5960_ = lean_st_ref_take(v___y_5953_);
v_env_5961_ = lean_ctor_get(v___x_5960_, 0);
v_nextMacroScope_5962_ = lean_ctor_get(v___x_5960_, 1);
v_ngen_5963_ = lean_ctor_get(v___x_5960_, 2);
v_auxDeclNGen_5964_ = lean_ctor_get(v___x_5960_, 3);
v_traceState_5965_ = lean_ctor_get(v___x_5960_, 4);
v_messages_5966_ = lean_ctor_get(v___x_5960_, 6);
v_infoState_5967_ = lean_ctor_get(v___x_5960_, 7);
v_snapshotTasks_5968_ = lean_ctor_get(v___x_5960_, 8);
v_isSharedCheck_5993_ = !lean_is_exclusive(v___x_5960_);
if (v_isSharedCheck_5993_ == 0)
{
lean_object* v_unused_5994_; 
v_unused_5994_ = lean_ctor_get(v___x_5960_, 5);
lean_dec(v_unused_5994_);
v___x_5970_ = v___x_5960_;
v_isShared_5971_ = v_isSharedCheck_5993_;
goto v_resetjp_5969_;
}
else
{
lean_inc(v_snapshotTasks_5968_);
lean_inc(v_infoState_5967_);
lean_inc(v_messages_5966_);
lean_inc(v_traceState_5965_);
lean_inc(v_auxDeclNGen_5964_);
lean_inc(v_ngen_5963_);
lean_inc(v_nextMacroScope_5962_);
lean_inc(v_env_5961_);
lean_dec(v___x_5960_);
v___x_5970_ = lean_box(0);
v_isShared_5971_ = v_isSharedCheck_5993_;
goto v_resetjp_5969_;
}
v_resetjp_5969_:
{
lean_object* v___x_5972_; lean_object* v___x_5974_; 
v___x_5972_ = l_Lean_Environment_setExporting(v_env_5961_, v_isExporting_5954_);
if (v_isShared_5971_ == 0)
{
lean_ctor_set(v___x_5970_, 5, v___x_5955_);
lean_ctor_set(v___x_5970_, 0, v___x_5972_);
v___x_5974_ = v___x_5970_;
goto v_reusejp_5973_;
}
else
{
lean_object* v_reuseFailAlloc_5992_; 
v_reuseFailAlloc_5992_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5992_, 0, v___x_5972_);
lean_ctor_set(v_reuseFailAlloc_5992_, 1, v_nextMacroScope_5962_);
lean_ctor_set(v_reuseFailAlloc_5992_, 2, v_ngen_5963_);
lean_ctor_set(v_reuseFailAlloc_5992_, 3, v_auxDeclNGen_5964_);
lean_ctor_set(v_reuseFailAlloc_5992_, 4, v_traceState_5965_);
lean_ctor_set(v_reuseFailAlloc_5992_, 5, v___x_5955_);
lean_ctor_set(v_reuseFailAlloc_5992_, 6, v_messages_5966_);
lean_ctor_set(v_reuseFailAlloc_5992_, 7, v_infoState_5967_);
lean_ctor_set(v_reuseFailAlloc_5992_, 8, v_snapshotTasks_5968_);
v___x_5974_ = v_reuseFailAlloc_5992_;
goto v_reusejp_5973_;
}
v_reusejp_5973_:
{
lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v_mctx_5977_; lean_object* v_zetaDeltaFVarIds_5978_; lean_object* v_postponed_5979_; lean_object* v_diag_5980_; lean_object* v___x_5982_; uint8_t v_isShared_5983_; uint8_t v_isSharedCheck_5990_; 
v___x_5975_ = lean_st_ref_put(v___y_5953_, v___x_5974_);
v___x_5976_ = lean_st_ref_take(v___y_5956_);
v_mctx_5977_ = lean_ctor_get(v___x_5976_, 0);
v_zetaDeltaFVarIds_5978_ = lean_ctor_get(v___x_5976_, 2);
v_postponed_5979_ = lean_ctor_get(v___x_5976_, 3);
v_diag_5980_ = lean_ctor_get(v___x_5976_, 4);
v_isSharedCheck_5990_ = !lean_is_exclusive(v___x_5976_);
if (v_isSharedCheck_5990_ == 0)
{
lean_object* v_unused_5991_; 
v_unused_5991_ = lean_ctor_get(v___x_5976_, 1);
lean_dec(v_unused_5991_);
v___x_5982_ = v___x_5976_;
v_isShared_5983_ = v_isSharedCheck_5990_;
goto v_resetjp_5981_;
}
else
{
lean_inc(v_diag_5980_);
lean_inc(v_postponed_5979_);
lean_inc(v_zetaDeltaFVarIds_5978_);
lean_inc(v_mctx_5977_);
lean_dec(v___x_5976_);
v___x_5982_ = lean_box(0);
v_isShared_5983_ = v_isSharedCheck_5990_;
goto v_resetjp_5981_;
}
v_resetjp_5981_:
{
lean_object* v___x_5984_; lean_object* v___x_5986_; 
v___x_5984_ = lean_box(0);
if (v_isShared_5983_ == 0)
{
lean_ctor_set(v___x_5982_, 1, v___x_5957_);
v___x_5986_ = v___x_5982_;
goto v_reusejp_5985_;
}
else
{
lean_object* v_reuseFailAlloc_5989_; 
v_reuseFailAlloc_5989_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5989_, 0, v_mctx_5977_);
lean_ctor_set(v_reuseFailAlloc_5989_, 1, v___x_5957_);
lean_ctor_set(v_reuseFailAlloc_5989_, 2, v_zetaDeltaFVarIds_5978_);
lean_ctor_set(v_reuseFailAlloc_5989_, 3, v_postponed_5979_);
lean_ctor_set(v_reuseFailAlloc_5989_, 4, v_diag_5980_);
v___x_5986_ = v_reuseFailAlloc_5989_;
goto v_reusejp_5985_;
}
v_reusejp_5985_:
{
lean_object* v___x_5987_; lean_object* v___x_5988_; 
v___x_5987_ = lean_st_ref_put(v___y_5956_, v___x_5986_);
v___x_5988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5988_, 0, v___x_5984_);
return v___x_5988_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0___boxed(lean_object* v___y_5995_, lean_object* v_isExporting_5996_, lean_object* v___x_5997_, lean_object* v___y_5998_, lean_object* v___x_5999_, lean_object* v_a_x3f_6000_, lean_object* v___y_6001_){
_start:
{
uint8_t v_isExporting_boxed_6002_; lean_object* v_res_6003_; 
v_isExporting_boxed_6002_ = lean_unbox(v_isExporting_5996_);
v_res_6003_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_5995_, v_isExporting_boxed_6002_, v___x_5997_, v___y_5998_, v___x_5999_, v_a_x3f_6000_);
lean_dec(v_a_x3f_6000_);
lean_dec(v___y_5998_);
lean_dec(v___y_5995_);
return v_res_6003_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_6004_; lean_object* v___x_6005_; 
v___x_6004_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0);
v___x_6005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6005_, 0, v___x_6004_);
return v___x_6005_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_6006_; lean_object* v___x_6007_; 
v___x_6006_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0);
v___x_6007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6007_, 0, v___x_6006_);
lean_ctor_set(v___x_6007_, 1, v___x_6006_);
return v___x_6007_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_6008_; lean_object* v___x_6009_; 
v___x_6008_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0);
v___x_6009_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6009_, 0, v___x_6008_);
lean_ctor_set(v___x_6009_, 1, v___x_6008_);
lean_ctor_set(v___x_6009_, 2, v___x_6008_);
lean_ctor_set(v___x_6009_, 3, v___x_6008_);
lean_ctor_set(v___x_6009_, 4, v___x_6008_);
lean_ctor_set(v___x_6009_, 5, v___x_6008_);
return v___x_6009_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(lean_object* v_x_6010_, uint8_t v_isExporting_6011_, lean_object* v___y_6012_, lean_object* v___y_6013_, lean_object* v___y_6014_, lean_object* v___y_6015_){
_start:
{
lean_object* v___x_6017_; lean_object* v_env_6018_; lean_object* v___x_6019_; uint8_t v_isModule_6020_; 
v___x_6017_ = lean_st_ref_get(v___y_6015_);
v_env_6018_ = lean_ctor_get(v___x_6017_, 0);
lean_inc_ref(v_env_6018_);
lean_dec(v___x_6017_);
v___x_6019_ = l_Lean_Environment_header(v_env_6018_);
v_isModule_6020_ = lean_ctor_get_uint8(v___x_6019_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_6019_);
if (v_isModule_6020_ == 0)
{
lean_object* v___x_6021_; 
lean_dec_ref(v_env_6018_);
lean_inc(v___y_6015_);
lean_inc_ref(v___y_6014_);
lean_inc(v___y_6013_);
lean_inc_ref(v___y_6012_);
v___x_6021_ = lean_apply_5(v_x_6010_, v___y_6012_, v___y_6013_, v___y_6014_, v___y_6015_, lean_box(0));
return v___x_6021_;
}
else
{
uint8_t v_isExporting_6022_; 
v_isExporting_6022_ = lean_ctor_get_uint8(v_env_6018_, sizeof(void*)*8);
lean_dec_ref(v_env_6018_);
if (v_isExporting_6011_ == 0)
{
if (v_isExporting_6022_ == 0)
{
lean_object* v___x_6088_; 
lean_inc(v___y_6015_);
lean_inc_ref(v___y_6014_);
lean_inc(v___y_6013_);
lean_inc_ref(v___y_6012_);
v___x_6088_ = lean_apply_5(v_x_6010_, v___y_6012_, v___y_6013_, v___y_6014_, v___y_6015_, lean_box(0));
return v___x_6088_;
}
else
{
goto v___jp_6023_;
}
}
else
{
if (v_isExporting_6022_ == 0)
{
goto v___jp_6023_;
}
else
{
lean_object* v___x_6089_; 
lean_inc(v___y_6015_);
lean_inc_ref(v___y_6014_);
lean_inc(v___y_6013_);
lean_inc_ref(v___y_6012_);
v___x_6089_ = lean_apply_5(v_x_6010_, v___y_6012_, v___y_6013_, v___y_6014_, v___y_6015_, lean_box(0));
return v___x_6089_;
}
}
v___jp_6023_:
{
lean_object* v___x_6024_; lean_object* v_env_6025_; lean_object* v_nextMacroScope_6026_; lean_object* v_ngen_6027_; lean_object* v_auxDeclNGen_6028_; lean_object* v_traceState_6029_; lean_object* v_messages_6030_; lean_object* v_infoState_6031_; lean_object* v_snapshotTasks_6032_; lean_object* v___x_6034_; uint8_t v_isShared_6035_; uint8_t v_isSharedCheck_6086_; 
v___x_6024_ = lean_st_ref_take(v___y_6015_);
v_env_6025_ = lean_ctor_get(v___x_6024_, 0);
v_nextMacroScope_6026_ = lean_ctor_get(v___x_6024_, 1);
v_ngen_6027_ = lean_ctor_get(v___x_6024_, 2);
v_auxDeclNGen_6028_ = lean_ctor_get(v___x_6024_, 3);
v_traceState_6029_ = lean_ctor_get(v___x_6024_, 4);
v_messages_6030_ = lean_ctor_get(v___x_6024_, 6);
v_infoState_6031_ = lean_ctor_get(v___x_6024_, 7);
v_snapshotTasks_6032_ = lean_ctor_get(v___x_6024_, 8);
v_isSharedCheck_6086_ = !lean_is_exclusive(v___x_6024_);
if (v_isSharedCheck_6086_ == 0)
{
lean_object* v_unused_6087_; 
v_unused_6087_ = lean_ctor_get(v___x_6024_, 5);
lean_dec(v_unused_6087_);
v___x_6034_ = v___x_6024_;
v_isShared_6035_ = v_isSharedCheck_6086_;
goto v_resetjp_6033_;
}
else
{
lean_inc(v_snapshotTasks_6032_);
lean_inc(v_infoState_6031_);
lean_inc(v_messages_6030_);
lean_inc(v_traceState_6029_);
lean_inc(v_auxDeclNGen_6028_);
lean_inc(v_ngen_6027_);
lean_inc(v_nextMacroScope_6026_);
lean_inc(v_env_6025_);
lean_dec(v___x_6024_);
v___x_6034_ = lean_box(0);
v_isShared_6035_ = v_isSharedCheck_6086_;
goto v_resetjp_6033_;
}
v_resetjp_6033_:
{
lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6039_; 
v___x_6036_ = l_Lean_Environment_setExporting(v_env_6025_, v_isExporting_6011_);
v___x_6037_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1);
if (v_isShared_6035_ == 0)
{
lean_ctor_set(v___x_6034_, 5, v___x_6037_);
lean_ctor_set(v___x_6034_, 0, v___x_6036_);
v___x_6039_ = v___x_6034_;
goto v_reusejp_6038_;
}
else
{
lean_object* v_reuseFailAlloc_6085_; 
v_reuseFailAlloc_6085_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6085_, 0, v___x_6036_);
lean_ctor_set(v_reuseFailAlloc_6085_, 1, v_nextMacroScope_6026_);
lean_ctor_set(v_reuseFailAlloc_6085_, 2, v_ngen_6027_);
lean_ctor_set(v_reuseFailAlloc_6085_, 3, v_auxDeclNGen_6028_);
lean_ctor_set(v_reuseFailAlloc_6085_, 4, v_traceState_6029_);
lean_ctor_set(v_reuseFailAlloc_6085_, 5, v___x_6037_);
lean_ctor_set(v_reuseFailAlloc_6085_, 6, v_messages_6030_);
lean_ctor_set(v_reuseFailAlloc_6085_, 7, v_infoState_6031_);
lean_ctor_set(v_reuseFailAlloc_6085_, 8, v_snapshotTasks_6032_);
v___x_6039_ = v_reuseFailAlloc_6085_;
goto v_reusejp_6038_;
}
v_reusejp_6038_:
{
lean_object* v___x_6040_; lean_object* v___x_6041_; lean_object* v_mctx_6042_; lean_object* v_zetaDeltaFVarIds_6043_; lean_object* v_postponed_6044_; lean_object* v_diag_6045_; lean_object* v___x_6047_; uint8_t v_isShared_6048_; uint8_t v_isSharedCheck_6083_; 
v___x_6040_ = lean_st_ref_put(v___y_6015_, v___x_6039_);
v___x_6041_ = lean_st_ref_take(v___y_6013_);
v_mctx_6042_ = lean_ctor_get(v___x_6041_, 0);
v_zetaDeltaFVarIds_6043_ = lean_ctor_get(v___x_6041_, 2);
v_postponed_6044_ = lean_ctor_get(v___x_6041_, 3);
v_diag_6045_ = lean_ctor_get(v___x_6041_, 4);
v_isSharedCheck_6083_ = !lean_is_exclusive(v___x_6041_);
if (v_isSharedCheck_6083_ == 0)
{
lean_object* v_unused_6084_; 
v_unused_6084_ = lean_ctor_get(v___x_6041_, 1);
lean_dec(v_unused_6084_);
v___x_6047_ = v___x_6041_;
v_isShared_6048_ = v_isSharedCheck_6083_;
goto v_resetjp_6046_;
}
else
{
lean_inc(v_diag_6045_);
lean_inc(v_postponed_6044_);
lean_inc(v_zetaDeltaFVarIds_6043_);
lean_inc(v_mctx_6042_);
lean_dec(v___x_6041_);
v___x_6047_ = lean_box(0);
v_isShared_6048_ = v_isSharedCheck_6083_;
goto v_resetjp_6046_;
}
v_resetjp_6046_:
{
lean_object* v___x_6049_; lean_object* v___x_6051_; 
v___x_6049_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2);
if (v_isShared_6048_ == 0)
{
lean_ctor_set(v___x_6047_, 1, v___x_6049_);
v___x_6051_ = v___x_6047_;
goto v_reusejp_6050_;
}
else
{
lean_object* v_reuseFailAlloc_6082_; 
v_reuseFailAlloc_6082_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6082_, 0, v_mctx_6042_);
lean_ctor_set(v_reuseFailAlloc_6082_, 1, v___x_6049_);
lean_ctor_set(v_reuseFailAlloc_6082_, 2, v_zetaDeltaFVarIds_6043_);
lean_ctor_set(v_reuseFailAlloc_6082_, 3, v_postponed_6044_);
lean_ctor_set(v_reuseFailAlloc_6082_, 4, v_diag_6045_);
v___x_6051_ = v_reuseFailAlloc_6082_;
goto v_reusejp_6050_;
}
v_reusejp_6050_:
{
lean_object* v___x_6052_; lean_object* v_r_6053_; 
v___x_6052_ = lean_st_ref_put(v___y_6013_, v___x_6051_);
lean_inc(v___y_6015_);
lean_inc_ref(v___y_6014_);
lean_inc(v___y_6013_);
lean_inc_ref(v___y_6012_);
v_r_6053_ = lean_apply_5(v_x_6010_, v___y_6012_, v___y_6013_, v___y_6014_, v___y_6015_, lean_box(0));
if (lean_obj_tag(v_r_6053_) == 0)
{
lean_object* v_a_6054_; lean_object* v___x_6056_; uint8_t v_isShared_6057_; uint8_t v_isSharedCheck_6070_; 
v_a_6054_ = lean_ctor_get(v_r_6053_, 0);
v_isSharedCheck_6070_ = !lean_is_exclusive(v_r_6053_);
if (v_isSharedCheck_6070_ == 0)
{
v___x_6056_ = v_r_6053_;
v_isShared_6057_ = v_isSharedCheck_6070_;
goto v_resetjp_6055_;
}
else
{
lean_inc(v_a_6054_);
lean_dec(v_r_6053_);
v___x_6056_ = lean_box(0);
v_isShared_6057_ = v_isSharedCheck_6070_;
goto v_resetjp_6055_;
}
v_resetjp_6055_:
{
lean_object* v___x_6059_; 
lean_inc(v_a_6054_);
if (v_isShared_6057_ == 0)
{
lean_ctor_set_tag(v___x_6056_, 1);
v___x_6059_ = v___x_6056_;
goto v_reusejp_6058_;
}
else
{
lean_object* v_reuseFailAlloc_6069_; 
v_reuseFailAlloc_6069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6069_, 0, v_a_6054_);
v___x_6059_ = v_reuseFailAlloc_6069_;
goto v_reusejp_6058_;
}
v_reusejp_6058_:
{
lean_object* v___x_6060_; lean_object* v___x_6062_; uint8_t v_isShared_6063_; uint8_t v_isSharedCheck_6067_; 
v___x_6060_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6015_, v_isExporting_6022_, v___x_6037_, v___y_6013_, v___x_6049_, v___x_6059_);
lean_dec_ref(v___x_6059_);
v_isSharedCheck_6067_ = !lean_is_exclusive(v___x_6060_);
if (v_isSharedCheck_6067_ == 0)
{
lean_object* v_unused_6068_; 
v_unused_6068_ = lean_ctor_get(v___x_6060_, 0);
lean_dec(v_unused_6068_);
v___x_6062_ = v___x_6060_;
v_isShared_6063_ = v_isSharedCheck_6067_;
goto v_resetjp_6061_;
}
else
{
lean_dec(v___x_6060_);
v___x_6062_ = lean_box(0);
v_isShared_6063_ = v_isSharedCheck_6067_;
goto v_resetjp_6061_;
}
v_resetjp_6061_:
{
lean_object* v___x_6065_; 
if (v_isShared_6063_ == 0)
{
lean_ctor_set(v___x_6062_, 0, v_a_6054_);
v___x_6065_ = v___x_6062_;
goto v_reusejp_6064_;
}
else
{
lean_object* v_reuseFailAlloc_6066_; 
v_reuseFailAlloc_6066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6066_, 0, v_a_6054_);
v___x_6065_ = v_reuseFailAlloc_6066_;
goto v_reusejp_6064_;
}
v_reusejp_6064_:
{
return v___x_6065_;
}
}
}
}
}
else
{
lean_object* v_a_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6075_; uint8_t v_isShared_6076_; uint8_t v_isSharedCheck_6080_; 
v_a_6071_ = lean_ctor_get(v_r_6053_, 0);
lean_inc(v_a_6071_);
lean_dec_ref_known(v_r_6053_, 1);
v___x_6072_ = lean_box(0);
v___x_6073_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6015_, v_isExporting_6022_, v___x_6037_, v___y_6013_, v___x_6049_, v___x_6072_);
v_isSharedCheck_6080_ = !lean_is_exclusive(v___x_6073_);
if (v_isSharedCheck_6080_ == 0)
{
lean_object* v_unused_6081_; 
v_unused_6081_ = lean_ctor_get(v___x_6073_, 0);
lean_dec(v_unused_6081_);
v___x_6075_ = v___x_6073_;
v_isShared_6076_ = v_isSharedCheck_6080_;
goto v_resetjp_6074_;
}
else
{
lean_dec(v___x_6073_);
v___x_6075_ = lean_box(0);
v_isShared_6076_ = v_isSharedCheck_6080_;
goto v_resetjp_6074_;
}
v_resetjp_6074_:
{
lean_object* v___x_6078_; 
if (v_isShared_6076_ == 0)
{
lean_ctor_set_tag(v___x_6075_, 1);
lean_ctor_set(v___x_6075_, 0, v_a_6071_);
v___x_6078_ = v___x_6075_;
goto v_reusejp_6077_;
}
else
{
lean_object* v_reuseFailAlloc_6079_; 
v_reuseFailAlloc_6079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6079_, 0, v_a_6071_);
v___x_6078_ = v_reuseFailAlloc_6079_;
goto v_reusejp_6077_;
}
v_reusejp_6077_:
{
return v___x_6078_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___boxed(lean_object* v_x_6090_, lean_object* v_isExporting_6091_, lean_object* v___y_6092_, lean_object* v___y_6093_, lean_object* v___y_6094_, lean_object* v___y_6095_, lean_object* v___y_6096_){
_start:
{
uint8_t v_isExporting_boxed_6097_; lean_object* v_res_6098_; 
v_isExporting_boxed_6097_ = lean_unbox(v_isExporting_6091_);
v_res_6098_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6090_, v_isExporting_boxed_6097_, v___y_6092_, v___y_6093_, v___y_6094_, v___y_6095_);
lean_dec(v___y_6095_);
lean_dec_ref(v___y_6094_);
lean_dec(v___y_6093_);
lean_dec_ref(v___y_6092_);
return v_res_6098_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(lean_object* v_x_6099_, uint8_t v_when_6100_, lean_object* v___y_6101_, lean_object* v___y_6102_, lean_object* v___y_6103_, lean_object* v___y_6104_){
_start:
{
if (v_when_6100_ == 0)
{
lean_object* v___x_6106_; 
lean_inc(v___y_6104_);
lean_inc_ref(v___y_6103_);
lean_inc(v___y_6102_);
lean_inc_ref(v___y_6101_);
v___x_6106_ = lean_apply_5(v_x_6099_, v___y_6101_, v___y_6102_, v___y_6103_, v___y_6104_, lean_box(0));
return v___x_6106_;
}
else
{
uint8_t v___x_6107_; lean_object* v___x_6108_; 
v___x_6107_ = 0;
v___x_6108_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6099_, v___x_6107_, v___y_6101_, v___y_6102_, v___y_6103_, v___y_6104_);
return v___x_6108_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg___boxed(lean_object* v_x_6109_, lean_object* v_when_6110_, lean_object* v___y_6111_, lean_object* v___y_6112_, lean_object* v___y_6113_, lean_object* v___y_6114_, lean_object* v___y_6115_){
_start:
{
uint8_t v_when_boxed_6116_; lean_object* v_res_6117_; 
v_when_boxed_6116_ = lean_unbox(v_when_6110_);
v_res_6117_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v_x_6109_, v_when_boxed_6116_, v___y_6111_, v___y_6112_, v___y_6113_, v___y_6114_);
lean_dec(v___y_6114_);
lean_dec_ref(v___y_6113_);
lean_dec(v___y_6112_);
lean_dec_ref(v___y_6111_);
return v_res_6117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals(lean_object* v_funNames_6118_, lean_object* v_argsPacker_6119_, lean_object* v_decrTactics_6120_, lean_object* v_value_6121_, lean_object* v_a_6122_, lean_object* v_a_6123_, lean_object* v_a_6124_, lean_object* v_a_6125_){
_start:
{
lean_object* v___f_6127_; uint8_t v___x_6128_; lean_object* v___x_6129_; 
v___f_6127_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_solveDecreasingGoals___lam__0___boxed), 9, 4);
lean_closure_set(v___f_6127_, 0, v_value_6121_);
lean_closure_set(v___f_6127_, 1, v_decrTactics_6120_);
lean_closure_set(v___f_6127_, 2, v_argsPacker_6119_);
lean_closure_set(v___f_6127_, 3, v_funNames_6118_);
v___x_6128_ = 1;
v___x_6129_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v___f_6127_, v___x_6128_, v_a_6122_, v_a_6123_, v_a_6124_, v_a_6125_);
return v___x_6129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___boxed(lean_object* v_funNames_6130_, lean_object* v_argsPacker_6131_, lean_object* v_decrTactics_6132_, lean_object* v_value_6133_, lean_object* v_a_6134_, lean_object* v_a_6135_, lean_object* v_a_6136_, lean_object* v_a_6137_, lean_object* v_a_6138_){
_start:
{
lean_object* v_res_6139_; 
v_res_6139_ = l_Lean_Elab_WF_solveDecreasingGoals(v_funNames_6130_, v_argsPacker_6131_, v_decrTactics_6132_, v_value_6133_, v_a_6134_, v_a_6135_, v_a_6136_, v_a_6137_);
lean_dec(v_a_6137_);
lean_dec_ref(v_a_6136_);
lean_dec(v_a_6135_);
lean_dec_ref(v_a_6134_);
return v_res_6139_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1(lean_object* v_00_u03b1_6140_, lean_object* v_msg_6141_, lean_object* v___y_6142_, lean_object* v___y_6143_, lean_object* v___y_6144_, lean_object* v___y_6145_, lean_object* v___y_6146_, lean_object* v___y_6147_){
_start:
{
lean_object* v___x_6149_; 
v___x_6149_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v_msg_6141_, v___y_6142_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_);
return v___x_6149_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___boxed(lean_object* v_00_u03b1_6150_, lean_object* v_msg_6151_, lean_object* v___y_6152_, lean_object* v___y_6153_, lean_object* v___y_6154_, lean_object* v___y_6155_, lean_object* v___y_6156_, lean_object* v___y_6157_, lean_object* v___y_6158_){
_start:
{
lean_object* v_res_6159_; 
v_res_6159_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1(v_00_u03b1_6150_, v_msg_6151_, v___y_6152_, v___y_6153_, v___y_6154_, v___y_6155_, v___y_6156_, v___y_6157_);
lean_dec(v___y_6157_);
lean_dec_ref(v___y_6156_);
lean_dec(v___y_6155_);
lean_dec_ref(v___y_6154_);
lean_dec(v___y_6153_);
lean_dec_ref(v___y_6152_);
return v_res_6159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4(lean_object* v___y_6160_, lean_object* v___y_6161_, lean_object* v___y_6162_, lean_object* v___y_6163_, lean_object* v___y_6164_, lean_object* v___y_6165_, lean_object* v___y_6166_, lean_object* v___y_6167_){
_start:
{
lean_object* v___x_6169_; 
v___x_6169_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_6167_);
return v___x_6169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___boxed(lean_object* v___y_6170_, lean_object* v___y_6171_, lean_object* v___y_6172_, lean_object* v___y_6173_, lean_object* v___y_6174_, lean_object* v___y_6175_, lean_object* v___y_6176_, lean_object* v___y_6177_, lean_object* v___y_6178_){
_start:
{
lean_object* v_res_6179_; 
v_res_6179_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4(v___y_6170_, v___y_6171_, v___y_6172_, v___y_6173_, v___y_6174_, v___y_6175_, v___y_6176_, v___y_6177_);
lean_dec(v___y_6177_);
lean_dec_ref(v___y_6176_);
lean_dec(v___y_6175_);
lean_dec_ref(v___y_6174_);
lean_dec(v___y_6173_);
lean_dec_ref(v___y_6172_);
lean_dec(v___y_6171_);
lean_dec_ref(v___y_6170_);
return v_res_6179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3(lean_object* v_00_u03b1_6180_, lean_object* v_x_6181_, lean_object* v_mkInfoTree_6182_, lean_object* v___y_6183_, lean_object* v___y_6184_, lean_object* v___y_6185_, lean_object* v___y_6186_, lean_object* v___y_6187_, lean_object* v___y_6188_, lean_object* v___y_6189_, lean_object* v___y_6190_){
_start:
{
lean_object* v___x_6192_; 
v___x_6192_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v_x_6181_, v_mkInfoTree_6182_, v___y_6183_, v___y_6184_, v___y_6185_, v___y_6186_, v___y_6187_, v___y_6188_, v___y_6189_, v___y_6190_);
return v___x_6192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___boxed(lean_object* v_00_u03b1_6193_, lean_object* v_x_6194_, lean_object* v_mkInfoTree_6195_, lean_object* v___y_6196_, lean_object* v___y_6197_, lean_object* v___y_6198_, lean_object* v___y_6199_, lean_object* v___y_6200_, lean_object* v___y_6201_, lean_object* v___y_6202_, lean_object* v___y_6203_, lean_object* v___y_6204_){
_start:
{
lean_object* v_res_6205_; 
v_res_6205_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3(v_00_u03b1_6193_, v_x_6194_, v_mkInfoTree_6195_, v___y_6196_, v___y_6197_, v___y_6198_, v___y_6199_, v___y_6200_, v___y_6201_, v___y_6202_, v___y_6203_);
lean_dec(v___y_6203_);
lean_dec_ref(v___y_6202_);
lean_dec(v___y_6201_);
lean_dec_ref(v___y_6200_);
lean_dec(v___y_6199_);
lean_dec_ref(v___y_6198_);
lean_dec(v___y_6197_);
lean_dec_ref(v___y_6196_);
return v_res_6205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5(lean_object* v_as_6206_, size_t v_i_6207_, size_t v_stop_6208_, lean_object* v_b_6209_, lean_object* v___y_6210_, lean_object* v___y_6211_, lean_object* v___y_6212_, lean_object* v___y_6213_, lean_object* v___y_6214_, lean_object* v___y_6215_){
_start:
{
lean_object* v___x_6217_; 
v___x_6217_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v_as_6206_, v_i_6207_, v_stop_6208_, v_b_6209_, v___y_6212_, v___y_6213_, v___y_6214_, v___y_6215_);
return v___x_6217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___boxed(lean_object* v_as_6218_, lean_object* v_i_6219_, lean_object* v_stop_6220_, lean_object* v_b_6221_, lean_object* v___y_6222_, lean_object* v___y_6223_, lean_object* v___y_6224_, lean_object* v___y_6225_, lean_object* v___y_6226_, lean_object* v___y_6227_, lean_object* v___y_6228_){
_start:
{
size_t v_i_boxed_6229_; size_t v_stop_boxed_6230_; lean_object* v_res_6231_; 
v_i_boxed_6229_ = lean_unbox_usize(v_i_6219_);
lean_dec(v_i_6219_);
v_stop_boxed_6230_ = lean_unbox_usize(v_stop_6220_);
lean_dec(v_stop_6220_);
v_res_6231_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5(v_as_6218_, v_i_boxed_6229_, v_stop_boxed_6230_, v_b_6221_, v___y_6222_, v___y_6223_, v___y_6224_, v___y_6225_, v___y_6226_, v___y_6227_);
lean_dec(v___y_6227_);
lean_dec_ref(v___y_6226_);
lean_dec(v___y_6225_);
lean_dec_ref(v___y_6224_);
lean_dec(v___y_6223_);
lean_dec_ref(v___y_6222_);
lean_dec_ref(v_as_6218_);
return v_res_6231_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10(lean_object* v_00_u03b1_6232_, lean_object* v_x_6233_, uint8_t v_isExporting_6234_, lean_object* v___y_6235_, lean_object* v___y_6236_, lean_object* v___y_6237_, lean_object* v___y_6238_){
_start:
{
lean_object* v___x_6240_; 
v___x_6240_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6233_, v_isExporting_6234_, v___y_6235_, v___y_6236_, v___y_6237_, v___y_6238_);
return v___x_6240_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___boxed(lean_object* v_00_u03b1_6241_, lean_object* v_x_6242_, lean_object* v_isExporting_6243_, lean_object* v___y_6244_, lean_object* v___y_6245_, lean_object* v___y_6246_, lean_object* v___y_6247_, lean_object* v___y_6248_){
_start:
{
uint8_t v_isExporting_boxed_6249_; lean_object* v_res_6250_; 
v_isExporting_boxed_6249_ = lean_unbox(v_isExporting_6243_);
v_res_6250_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10(v_00_u03b1_6241_, v_x_6242_, v_isExporting_boxed_6249_, v___y_6244_, v___y_6245_, v___y_6246_, v___y_6247_);
lean_dec(v___y_6247_);
lean_dec_ref(v___y_6246_);
lean_dec(v___y_6245_);
lean_dec_ref(v___y_6244_);
return v_res_6250_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8(lean_object* v_00_u03b1_6251_, lean_object* v_x_6252_, uint8_t v_when_6253_, lean_object* v___y_6254_, lean_object* v___y_6255_, lean_object* v___y_6256_, lean_object* v___y_6257_){
_start:
{
lean_object* v___x_6259_; 
v___x_6259_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v_x_6252_, v_when_6253_, v___y_6254_, v___y_6255_, v___y_6256_, v___y_6257_);
return v___x_6259_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___boxed(lean_object* v_00_u03b1_6260_, lean_object* v_x_6261_, lean_object* v_when_6262_, lean_object* v___y_6263_, lean_object* v___y_6264_, lean_object* v___y_6265_, lean_object* v___y_6266_, lean_object* v___y_6267_){
_start:
{
uint8_t v_when_boxed_6268_; lean_object* v_res_6269_; 
v_when_boxed_6268_ = lean_unbox(v_when_6262_);
v_res_6269_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8(v_00_u03b1_6260_, v_x_6261_, v_when_boxed_6268_, v___y_6263_, v___y_6264_, v___y_6265_, v___y_6266_);
lean_dec(v___y_6266_);
lean_dec_ref(v___y_6265_);
lean_dec(v___y_6264_);
lean_dec_ref(v___y_6263_);
return v_res_6269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1(lean_object* v_msgData_6270_, lean_object* v_macroStack_6271_, lean_object* v___y_6272_, lean_object* v___y_6273_, lean_object* v___y_6274_, lean_object* v___y_6275_, lean_object* v___y_6276_, lean_object* v___y_6277_){
_start:
{
lean_object* v___x_6279_; 
v___x_6279_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_msgData_6270_, v_macroStack_6271_, v___y_6276_);
return v___x_6279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___boxed(lean_object* v_msgData_6280_, lean_object* v_macroStack_6281_, lean_object* v___y_6282_, lean_object* v___y_6283_, lean_object* v___y_6284_, lean_object* v___y_6285_, lean_object* v___y_6286_, lean_object* v___y_6287_, lean_object* v___y_6288_){
_start:
{
lean_object* v_res_6289_; 
v_res_6289_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1(v_msgData_6280_, v_macroStack_6281_, v___y_6282_, v___y_6283_, v___y_6284_, v___y_6285_, v___y_6286_, v___y_6287_);
lean_dec(v___y_6287_);
lean_dec_ref(v___y_6286_);
lean_dec(v___y_6285_);
lean_dec_ref(v___y_6284_);
lean_dec(v___y_6283_);
lean_dec_ref(v___y_6282_);
return v_res_6289_;
}
}
static lean_object* _init_l_Lean_Elab_WF_isNatLtWF___closed__4(void){
_start:
{
lean_object* v___x_6296_; lean_object* v___x_6297_; lean_object* v___x_6298_; 
v___x_6296_ = lean_box(0);
v___x_6297_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__3));
v___x_6298_ = l_Lean_mkConst(v___x_6297_, v___x_6296_);
return v___x_6298_;
}
}
static lean_object* _init_l_Lean_Elab_WF_isNatLtWF___closed__7(void){
_start:
{
lean_object* v___x_6303_; lean_object* v___x_6304_; lean_object* v___x_6305_; 
v___x_6303_ = lean_box(0);
v___x_6304_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__6));
v___x_6305_ = l_Lean_mkConst(v___x_6304_, v___x_6303_);
return v___x_6305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isNatLtWF(lean_object* v_wfRel_6306_, lean_object* v_a_6307_, lean_object* v_a_6308_, lean_object* v_a_6309_, lean_object* v_a_6310_){
_start:
{
lean_object* v___x_6315_; 
v___x_6315_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_wfRel_6306_, v_a_6308_);
if (lean_obj_tag(v___x_6315_) == 0)
{
lean_object* v_a_6316_; lean_object* v___x_6317_; uint8_t v___x_6318_; 
v_a_6316_ = lean_ctor_get(v___x_6315_, 0);
lean_inc(v_a_6316_);
lean_dec_ref_known(v___x_6315_, 1);
v___x_6317_ = l_Lean_Expr_cleanupAnnotations(v_a_6316_);
v___x_6318_ = l_Lean_Expr_isApp(v___x_6317_);
if (v___x_6318_ == 0)
{
lean_dec_ref(v___x_6317_);
goto v___jp_6312_;
}
else
{
lean_object* v_arg_6319_; lean_object* v___x_6320_; uint8_t v___x_6321_; 
v_arg_6319_ = lean_ctor_get(v___x_6317_, 1);
lean_inc_ref(v_arg_6319_);
v___x_6320_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6317_);
v___x_6321_ = l_Lean_Expr_isApp(v___x_6320_);
if (v___x_6321_ == 0)
{
lean_dec_ref(v___x_6320_);
lean_dec_ref(v_arg_6319_);
goto v___jp_6312_;
}
else
{
lean_object* v_arg_6322_; lean_object* v___x_6323_; uint8_t v___x_6324_; 
v_arg_6322_ = lean_ctor_get(v___x_6320_, 1);
lean_inc_ref(v_arg_6322_);
v___x_6323_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6320_);
v___x_6324_ = l_Lean_Expr_isApp(v___x_6323_);
if (v___x_6324_ == 0)
{
lean_dec_ref(v___x_6323_);
lean_dec_ref(v_arg_6322_);
lean_dec_ref(v_arg_6319_);
goto v___jp_6312_;
}
else
{
lean_object* v_arg_6325_; lean_object* v___x_6326_; uint8_t v___x_6327_; 
v_arg_6325_ = lean_ctor_get(v___x_6323_, 1);
lean_inc_ref(v_arg_6325_);
v___x_6326_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6323_);
v___x_6327_ = l_Lean_Expr_isApp(v___x_6326_);
if (v___x_6327_ == 0)
{
lean_dec_ref(v___x_6326_);
lean_dec_ref(v_arg_6325_);
lean_dec_ref(v_arg_6322_);
lean_dec_ref(v_arg_6319_);
goto v___jp_6312_;
}
else
{
lean_object* v___x_6328_; lean_object* v___x_6329_; uint8_t v___x_6330_; 
v___x_6328_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6326_);
v___x_6329_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__1));
v___x_6330_ = l_Lean_Expr_isConstOf(v___x_6328_, v___x_6329_);
lean_dec_ref(v___x_6328_);
if (v___x_6330_ == 0)
{
lean_dec_ref(v_arg_6325_);
lean_dec_ref(v_arg_6322_);
lean_dec_ref(v_arg_6319_);
goto v___jp_6312_;
}
else
{
lean_object* v___x_6331_; lean_object* v___x_6332_; 
v___x_6331_ = lean_obj_once(&l_Lean_Elab_WF_isNatLtWF___closed__4, &l_Lean_Elab_WF_isNatLtWF___closed__4_once, _init_l_Lean_Elab_WF_isNatLtWF___closed__4);
v___x_6332_ = l_Lean_Meta_isExprDefEq(v_arg_6325_, v___x_6331_, v_a_6307_, v_a_6308_, v_a_6309_, v_a_6310_);
if (lean_obj_tag(v___x_6332_) == 0)
{
lean_object* v_a_6333_; lean_object* v___x_6335_; uint8_t v_isShared_6336_; uint8_t v_isSharedCheck_6366_; 
v_a_6333_ = lean_ctor_get(v___x_6332_, 0);
v_isSharedCheck_6366_ = !lean_is_exclusive(v___x_6332_);
if (v_isSharedCheck_6366_ == 0)
{
v___x_6335_ = v___x_6332_;
v_isShared_6336_ = v_isSharedCheck_6366_;
goto v_resetjp_6334_;
}
else
{
lean_inc(v_a_6333_);
lean_dec(v___x_6332_);
v___x_6335_ = lean_box(0);
v_isShared_6336_ = v_isSharedCheck_6366_;
goto v_resetjp_6334_;
}
v_resetjp_6334_:
{
uint8_t v___x_6337_; 
v___x_6337_ = lean_unbox(v_a_6333_);
lean_dec(v_a_6333_);
if (v___x_6337_ == 0)
{
lean_object* v___x_6338_; lean_object* v___x_6340_; 
lean_dec_ref(v_arg_6322_);
lean_dec_ref(v_arg_6319_);
v___x_6338_ = lean_box(0);
if (v_isShared_6336_ == 0)
{
lean_ctor_set(v___x_6335_, 0, v___x_6338_);
v___x_6340_ = v___x_6335_;
goto v_reusejp_6339_;
}
else
{
lean_object* v_reuseFailAlloc_6341_; 
v_reuseFailAlloc_6341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6341_, 0, v___x_6338_);
v___x_6340_ = v_reuseFailAlloc_6341_;
goto v_reusejp_6339_;
}
v_reusejp_6339_:
{
return v___x_6340_;
}
}
else
{
lean_object* v___x_6342_; lean_object* v___x_6343_; 
lean_del_object(v___x_6335_);
v___x_6342_ = lean_obj_once(&l_Lean_Elab_WF_isNatLtWF___closed__7, &l_Lean_Elab_WF_isNatLtWF___closed__7_once, _init_l_Lean_Elab_WF_isNatLtWF___closed__7);
v___x_6343_ = l_Lean_Meta_isExprDefEq(v_arg_6319_, v___x_6342_, v_a_6307_, v_a_6308_, v_a_6309_, v_a_6310_);
if (lean_obj_tag(v___x_6343_) == 0)
{
lean_object* v_a_6344_; lean_object* v___x_6346_; uint8_t v_isShared_6347_; uint8_t v_isSharedCheck_6357_; 
v_a_6344_ = lean_ctor_get(v___x_6343_, 0);
v_isSharedCheck_6357_ = !lean_is_exclusive(v___x_6343_);
if (v_isSharedCheck_6357_ == 0)
{
v___x_6346_ = v___x_6343_;
v_isShared_6347_ = v_isSharedCheck_6357_;
goto v_resetjp_6345_;
}
else
{
lean_inc(v_a_6344_);
lean_dec(v___x_6343_);
v___x_6346_ = lean_box(0);
v_isShared_6347_ = v_isSharedCheck_6357_;
goto v_resetjp_6345_;
}
v_resetjp_6345_:
{
uint8_t v___x_6348_; 
v___x_6348_ = lean_unbox(v_a_6344_);
lean_dec(v_a_6344_);
if (v___x_6348_ == 0)
{
lean_object* v___x_6349_; lean_object* v___x_6351_; 
lean_dec_ref(v_arg_6322_);
v___x_6349_ = lean_box(0);
if (v_isShared_6347_ == 0)
{
lean_ctor_set(v___x_6346_, 0, v___x_6349_);
v___x_6351_ = v___x_6346_;
goto v_reusejp_6350_;
}
else
{
lean_object* v_reuseFailAlloc_6352_; 
v_reuseFailAlloc_6352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6352_, 0, v___x_6349_);
v___x_6351_ = v_reuseFailAlloc_6352_;
goto v_reusejp_6350_;
}
v_reusejp_6350_:
{
return v___x_6351_;
}
}
else
{
lean_object* v___x_6353_; lean_object* v___x_6355_; 
v___x_6353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6353_, 0, v_arg_6322_);
if (v_isShared_6347_ == 0)
{
lean_ctor_set(v___x_6346_, 0, v___x_6353_);
v___x_6355_ = v___x_6346_;
goto v_reusejp_6354_;
}
else
{
lean_object* v_reuseFailAlloc_6356_; 
v_reuseFailAlloc_6356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6356_, 0, v___x_6353_);
v___x_6355_ = v_reuseFailAlloc_6356_;
goto v_reusejp_6354_;
}
v_reusejp_6354_:
{
return v___x_6355_;
}
}
}
}
else
{
lean_object* v_a_6358_; lean_object* v___x_6360_; uint8_t v_isShared_6361_; uint8_t v_isSharedCheck_6365_; 
lean_dec_ref(v_arg_6322_);
v_a_6358_ = lean_ctor_get(v___x_6343_, 0);
v_isSharedCheck_6365_ = !lean_is_exclusive(v___x_6343_);
if (v_isSharedCheck_6365_ == 0)
{
v___x_6360_ = v___x_6343_;
v_isShared_6361_ = v_isSharedCheck_6365_;
goto v_resetjp_6359_;
}
else
{
lean_inc(v_a_6358_);
lean_dec(v___x_6343_);
v___x_6360_ = lean_box(0);
v_isShared_6361_ = v_isSharedCheck_6365_;
goto v_resetjp_6359_;
}
v_resetjp_6359_:
{
lean_object* v___x_6363_; 
if (v_isShared_6361_ == 0)
{
v___x_6363_ = v___x_6360_;
goto v_reusejp_6362_;
}
else
{
lean_object* v_reuseFailAlloc_6364_; 
v_reuseFailAlloc_6364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6364_, 0, v_a_6358_);
v___x_6363_ = v_reuseFailAlloc_6364_;
goto v_reusejp_6362_;
}
v_reusejp_6362_:
{
return v___x_6363_;
}
}
}
}
}
}
else
{
lean_object* v_a_6367_; lean_object* v___x_6369_; uint8_t v_isShared_6370_; uint8_t v_isSharedCheck_6374_; 
lean_dec_ref(v_arg_6322_);
lean_dec_ref(v_arg_6319_);
v_a_6367_ = lean_ctor_get(v___x_6332_, 0);
v_isSharedCheck_6374_ = !lean_is_exclusive(v___x_6332_);
if (v_isSharedCheck_6374_ == 0)
{
v___x_6369_ = v___x_6332_;
v_isShared_6370_ = v_isSharedCheck_6374_;
goto v_resetjp_6368_;
}
else
{
lean_inc(v_a_6367_);
lean_dec(v___x_6332_);
v___x_6369_ = lean_box(0);
v_isShared_6370_ = v_isSharedCheck_6374_;
goto v_resetjp_6368_;
}
v_resetjp_6368_:
{
lean_object* v___x_6372_; 
if (v_isShared_6370_ == 0)
{
v___x_6372_ = v___x_6369_;
goto v_reusejp_6371_;
}
else
{
lean_object* v_reuseFailAlloc_6373_; 
v_reuseFailAlloc_6373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6373_, 0, v_a_6367_);
v___x_6372_ = v_reuseFailAlloc_6373_;
goto v_reusejp_6371_;
}
v_reusejp_6371_:
{
return v___x_6372_;
}
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
lean_object* v_a_6375_; lean_object* v___x_6377_; uint8_t v_isShared_6378_; uint8_t v_isSharedCheck_6382_; 
v_a_6375_ = lean_ctor_get(v___x_6315_, 0);
v_isSharedCheck_6382_ = !lean_is_exclusive(v___x_6315_);
if (v_isSharedCheck_6382_ == 0)
{
v___x_6377_ = v___x_6315_;
v_isShared_6378_ = v_isSharedCheck_6382_;
goto v_resetjp_6376_;
}
else
{
lean_inc(v_a_6375_);
lean_dec(v___x_6315_);
v___x_6377_ = lean_box(0);
v_isShared_6378_ = v_isSharedCheck_6382_;
goto v_resetjp_6376_;
}
v_resetjp_6376_:
{
lean_object* v___x_6380_; 
if (v_isShared_6378_ == 0)
{
v___x_6380_ = v___x_6377_;
goto v_reusejp_6379_;
}
else
{
lean_object* v_reuseFailAlloc_6381_; 
v_reuseFailAlloc_6381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6381_, 0, v_a_6375_);
v___x_6380_ = v_reuseFailAlloc_6381_;
goto v_reusejp_6379_;
}
v_reusejp_6379_:
{
return v___x_6380_;
}
}
}
v___jp_6312_:
{
lean_object* v___x_6313_; lean_object* v___x_6314_; 
v___x_6313_ = lean_box(0);
v___x_6314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6314_, 0, v___x_6313_);
return v___x_6314_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isNatLtWF___boxed(lean_object* v_wfRel_6383_, lean_object* v_a_6384_, lean_object* v_a_6385_, lean_object* v_a_6386_, lean_object* v_a_6387_, lean_object* v_a_6388_){
_start:
{
lean_object* v_res_6389_; 
v_res_6389_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_6383_, v_a_6384_, v_a_6385_, v_a_6386_, v_a_6387_);
lean_dec(v_a_6387_);
lean_dec_ref(v_a_6386_);
lean_dec(v_a_6385_);
lean_dec_ref(v_a_6384_);
return v_res_6389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(lean_object* v_type_6390_, lean_object* v_maxFVars_x3f_6391_, lean_object* v_k_6392_, uint8_t v_cleanupAnnotations_6393_, uint8_t v_whnfType_6394_, lean_object* v___y_6395_, lean_object* v___y_6396_, lean_object* v___y_6397_, lean_object* v___y_6398_, lean_object* v___y_6399_, lean_object* v___y_6400_){
_start:
{
lean_object* v___f_6402_; lean_object* v___x_6403_; 
lean_inc(v___y_6396_);
lean_inc_ref(v___y_6395_);
v___f_6402_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_6402_, 0, v_k_6392_);
lean_closure_set(v___f_6402_, 1, v___y_6395_);
lean_closure_set(v___f_6402_, 2, v___y_6396_);
v___x_6403_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_6390_, v_maxFVars_x3f_6391_, v___f_6402_, v_cleanupAnnotations_6393_, v_whnfType_6394_, v___y_6397_, v___y_6398_, v___y_6399_, v___y_6400_);
if (lean_obj_tag(v___x_6403_) == 0)
{
return v___x_6403_;
}
else
{
lean_object* v_a_6404_; lean_object* v___x_6406_; uint8_t v_isShared_6407_; uint8_t v_isSharedCheck_6411_; 
v_a_6404_ = lean_ctor_get(v___x_6403_, 0);
v_isSharedCheck_6411_ = !lean_is_exclusive(v___x_6403_);
if (v_isSharedCheck_6411_ == 0)
{
v___x_6406_ = v___x_6403_;
v_isShared_6407_ = v_isSharedCheck_6411_;
goto v_resetjp_6405_;
}
else
{
lean_inc(v_a_6404_);
lean_dec(v___x_6403_);
v___x_6406_ = lean_box(0);
v_isShared_6407_ = v_isSharedCheck_6411_;
goto v_resetjp_6405_;
}
v_resetjp_6405_:
{
lean_object* v___x_6409_; 
if (v_isShared_6407_ == 0)
{
v___x_6409_ = v___x_6406_;
goto v_reusejp_6408_;
}
else
{
lean_object* v_reuseFailAlloc_6410_; 
v_reuseFailAlloc_6410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6410_, 0, v_a_6404_);
v___x_6409_ = v_reuseFailAlloc_6410_;
goto v_reusejp_6408_;
}
v_reusejp_6408_:
{
return v___x_6409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg___boxed(lean_object* v_type_6412_, lean_object* v_maxFVars_x3f_6413_, lean_object* v_k_6414_, lean_object* v_cleanupAnnotations_6415_, lean_object* v_whnfType_6416_, lean_object* v___y_6417_, lean_object* v___y_6418_, lean_object* v___y_6419_, lean_object* v___y_6420_, lean_object* v___y_6421_, lean_object* v___y_6422_, lean_object* v___y_6423_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_6424_; uint8_t v_whnfType_boxed_6425_; lean_object* v_res_6426_; 
v_cleanupAnnotations_boxed_6424_ = lean_unbox(v_cleanupAnnotations_6415_);
v_whnfType_boxed_6425_ = lean_unbox(v_whnfType_6416_);
v_res_6426_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_type_6412_, v_maxFVars_x3f_6413_, v_k_6414_, v_cleanupAnnotations_boxed_6424_, v_whnfType_boxed_6425_, v___y_6417_, v___y_6418_, v___y_6419_, v___y_6420_, v___y_6421_, v___y_6422_);
lean_dec(v___y_6422_);
lean_dec_ref(v___y_6421_);
lean_dec(v___y_6420_);
lean_dec_ref(v___y_6419_);
lean_dec(v___y_6418_);
lean_dec_ref(v___y_6417_);
return v_res_6426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0(lean_object* v_00_u03b1_6427_, lean_object* v_type_6428_, lean_object* v_maxFVars_x3f_6429_, lean_object* v_k_6430_, uint8_t v_cleanupAnnotations_6431_, uint8_t v_whnfType_6432_, lean_object* v___y_6433_, lean_object* v___y_6434_, lean_object* v___y_6435_, lean_object* v___y_6436_, lean_object* v___y_6437_, lean_object* v___y_6438_){
_start:
{
lean_object* v___x_6440_; 
v___x_6440_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_type_6428_, v_maxFVars_x3f_6429_, v_k_6430_, v_cleanupAnnotations_6431_, v_whnfType_6432_, v___y_6433_, v___y_6434_, v___y_6435_, v___y_6436_, v___y_6437_, v___y_6438_);
return v___x_6440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___boxed(lean_object* v_00_u03b1_6441_, lean_object* v_type_6442_, lean_object* v_maxFVars_x3f_6443_, lean_object* v_k_6444_, lean_object* v_cleanupAnnotations_6445_, lean_object* v_whnfType_6446_, lean_object* v___y_6447_, lean_object* v___y_6448_, lean_object* v___y_6449_, lean_object* v___y_6450_, lean_object* v___y_6451_, lean_object* v___y_6452_, lean_object* v___y_6453_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_6454_; uint8_t v_whnfType_boxed_6455_; lean_object* v_res_6456_; 
v_cleanupAnnotations_boxed_6454_ = lean_unbox(v_cleanupAnnotations_6445_);
v_whnfType_boxed_6455_ = lean_unbox(v_whnfType_6446_);
v_res_6456_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0(v_00_u03b1_6441_, v_type_6442_, v_maxFVars_x3f_6443_, v_k_6444_, v_cleanupAnnotations_boxed_6454_, v_whnfType_boxed_6455_, v___y_6447_, v___y_6448_, v___y_6449_, v___y_6450_, v___y_6451_, v___y_6452_);
lean_dec(v___y_6452_);
lean_dec_ref(v___y_6451_);
lean_dec(v___y_6450_);
lean_dec_ref(v___y_6449_);
lean_dec(v___y_6448_);
lean_dec_ref(v___y_6447_);
return v_res_6456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(lean_object* v_lctx_6457_, lean_object* v_x_6458_, lean_object* v___y_6459_, lean_object* v___y_6460_, lean_object* v___y_6461_, lean_object* v___y_6462_, lean_object* v___y_6463_, lean_object* v___y_6464_){
_start:
{
lean_object* v_keyedConfig_6466_; uint8_t v_trackZetaDelta_6467_; lean_object* v_zetaDeltaSet_6468_; lean_object* v_localInstances_6469_; lean_object* v_defEqCtx_x3f_6470_; lean_object* v_synthPendingDepth_6471_; lean_object* v_customCanUnfoldPredicate_x3f_6472_; uint8_t v_univApprox_6473_; uint8_t v_inTypeClassResolution_6474_; uint8_t v_cacheInferType_6475_; lean_object* v___x_6476_; lean_object* v___x_6477_; 
v_keyedConfig_6466_ = lean_ctor_get(v___y_6461_, 0);
v_trackZetaDelta_6467_ = lean_ctor_get_uint8(v___y_6461_, sizeof(void*)*7);
v_zetaDeltaSet_6468_ = lean_ctor_get(v___y_6461_, 1);
v_localInstances_6469_ = lean_ctor_get(v___y_6461_, 3);
v_defEqCtx_x3f_6470_ = lean_ctor_get(v___y_6461_, 4);
v_synthPendingDepth_6471_ = lean_ctor_get(v___y_6461_, 5);
v_customCanUnfoldPredicate_x3f_6472_ = lean_ctor_get(v___y_6461_, 6);
v_univApprox_6473_ = lean_ctor_get_uint8(v___y_6461_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_6474_ = lean_ctor_get_uint8(v___y_6461_, sizeof(void*)*7 + 2);
v_cacheInferType_6475_ = lean_ctor_get_uint8(v___y_6461_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_6472_);
lean_inc(v_synthPendingDepth_6471_);
lean_inc(v_defEqCtx_x3f_6470_);
lean_inc_ref(v_localInstances_6469_);
lean_inc(v_zetaDeltaSet_6468_);
lean_inc_ref(v_keyedConfig_6466_);
v___x_6476_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6476_, 0, v_keyedConfig_6466_);
lean_ctor_set(v___x_6476_, 1, v_zetaDeltaSet_6468_);
lean_ctor_set(v___x_6476_, 2, v_lctx_6457_);
lean_ctor_set(v___x_6476_, 3, v_localInstances_6469_);
lean_ctor_set(v___x_6476_, 4, v_defEqCtx_x3f_6470_);
lean_ctor_set(v___x_6476_, 5, v_synthPendingDepth_6471_);
lean_ctor_set(v___x_6476_, 6, v_customCanUnfoldPredicate_x3f_6472_);
lean_ctor_set_uint8(v___x_6476_, sizeof(void*)*7, v_trackZetaDelta_6467_);
lean_ctor_set_uint8(v___x_6476_, sizeof(void*)*7 + 1, v_univApprox_6473_);
lean_ctor_set_uint8(v___x_6476_, sizeof(void*)*7 + 2, v_inTypeClassResolution_6474_);
lean_ctor_set_uint8(v___x_6476_, sizeof(void*)*7 + 3, v_cacheInferType_6475_);
lean_inc(v___y_6464_);
lean_inc_ref(v___y_6463_);
lean_inc(v___y_6462_);
lean_inc(v___y_6460_);
lean_inc_ref(v___y_6459_);
v___x_6477_ = lean_apply_7(v_x_6458_, v___y_6459_, v___y_6460_, v___x_6476_, v___y_6462_, v___y_6463_, v___y_6464_, lean_box(0));
if (lean_obj_tag(v___x_6477_) == 0)
{
lean_object* v_a_6478_; lean_object* v___x_6480_; uint8_t v_isShared_6481_; uint8_t v_isSharedCheck_6485_; 
v_a_6478_ = lean_ctor_get(v___x_6477_, 0);
v_isSharedCheck_6485_ = !lean_is_exclusive(v___x_6477_);
if (v_isSharedCheck_6485_ == 0)
{
v___x_6480_ = v___x_6477_;
v_isShared_6481_ = v_isSharedCheck_6485_;
goto v_resetjp_6479_;
}
else
{
lean_inc(v_a_6478_);
lean_dec(v___x_6477_);
v___x_6480_ = lean_box(0);
v_isShared_6481_ = v_isSharedCheck_6485_;
goto v_resetjp_6479_;
}
v_resetjp_6479_:
{
lean_object* v___x_6483_; 
if (v_isShared_6481_ == 0)
{
v___x_6483_ = v___x_6480_;
goto v_reusejp_6482_;
}
else
{
lean_object* v_reuseFailAlloc_6484_; 
v_reuseFailAlloc_6484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6484_, 0, v_a_6478_);
v___x_6483_ = v_reuseFailAlloc_6484_;
goto v_reusejp_6482_;
}
v_reusejp_6482_:
{
return v___x_6483_;
}
}
}
else
{
return v___x_6477_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg___boxed(lean_object* v_lctx_6486_, lean_object* v_x_6487_, lean_object* v___y_6488_, lean_object* v___y_6489_, lean_object* v___y_6490_, lean_object* v___y_6491_, lean_object* v___y_6492_, lean_object* v___y_6493_, lean_object* v___y_6494_){
_start:
{
lean_object* v_res_6495_; 
v_res_6495_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v_lctx_6486_, v_x_6487_, v___y_6488_, v___y_6489_, v___y_6490_, v___y_6491_, v___y_6492_, v___y_6493_);
lean_dec(v___y_6493_);
lean_dec_ref(v___y_6492_);
lean_dec(v___y_6491_);
lean_dec_ref(v___y_6490_);
lean_dec(v___y_6489_);
lean_dec_ref(v___y_6488_);
return v_res_6495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1(lean_object* v_00_u03b1_6496_, lean_object* v_lctx_6497_, lean_object* v_x_6498_, lean_object* v___y_6499_, lean_object* v___y_6500_, lean_object* v___y_6501_, lean_object* v___y_6502_, lean_object* v___y_6503_, lean_object* v___y_6504_){
_start:
{
lean_object* v___x_6506_; 
v___x_6506_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v_lctx_6497_, v_x_6498_, v___y_6499_, v___y_6500_, v___y_6501_, v___y_6502_, v___y_6503_, v___y_6504_);
return v___x_6506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___boxed(lean_object* v_00_u03b1_6507_, lean_object* v_lctx_6508_, lean_object* v_x_6509_, lean_object* v___y_6510_, lean_object* v___y_6511_, lean_object* v___y_6512_, lean_object* v___y_6513_, lean_object* v___y_6514_, lean_object* v___y_6515_, lean_object* v___y_6516_){
_start:
{
lean_object* v_res_6517_; 
v_res_6517_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1(v_00_u03b1_6507_, v_lctx_6508_, v_x_6509_, v___y_6510_, v___y_6511_, v___y_6512_, v___y_6513_, v___y_6514_, v___y_6515_);
lean_dec(v___y_6515_);
lean_dec_ref(v___y_6514_);
lean_dec(v___y_6513_);
lean_dec_ref(v___y_6512_);
lean_dec(v___y_6511_);
lean_dec_ref(v___y_6510_);
return v_res_6517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__0(lean_object* v_prefixArgs_6518_, lean_object* v_declName_6519_, lean_object* v_x_6520_, lean_object* v_F_6521_, lean_object* v_val_6522_, lean_object* v___y_6523_, lean_object* v___y_6524_, lean_object* v___y_6525_, lean_object* v___y_6526_, lean_object* v___y_6527_, lean_object* v___y_6528_){
_start:
{
lean_object* v___x_6530_; lean_object* v___x_6531_; lean_object* v___x_6532_; 
v___x_6530_ = lean_array_get_size(v_prefixArgs_6518_);
v___x_6531_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___boxed), 11, 2);
lean_closure_set(v___x_6531_, 0, v_declName_6519_);
lean_closure_set(v___x_6531_, 1, v___x_6530_);
v___x_6532_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v_x_6520_, v_F_6521_, v_val_6522_, v___x_6531_, v___y_6523_, v___y_6524_, v___y_6525_, v___y_6526_, v___y_6527_, v___y_6528_);
return v___x_6532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__0___boxed(lean_object* v_prefixArgs_6533_, lean_object* v_declName_6534_, lean_object* v_x_6535_, lean_object* v_F_6536_, lean_object* v_val_6537_, lean_object* v___y_6538_, lean_object* v___y_6539_, lean_object* v___y_6540_, lean_object* v___y_6541_, lean_object* v___y_6542_, lean_object* v___y_6543_, lean_object* v___y_6544_){
_start:
{
lean_object* v_res_6545_; 
v_res_6545_ = l_Lean_Elab_WF_mkFix___lam__0(v_prefixArgs_6533_, v_declName_6534_, v_x_6535_, v_F_6536_, v_val_6537_, v___y_6538_, v___y_6539_, v___y_6540_, v___y_6541_, v___y_6542_, v___y_6543_);
lean_dec(v___y_6543_);
lean_dec_ref(v___y_6542_);
lean_dec(v___y_6541_);
lean_dec_ref(v___y_6540_);
lean_dec(v___y_6539_);
lean_dec_ref(v___y_6538_);
lean_dec_ref(v_prefixArgs_6533_);
return v_res_6545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__1(lean_object* v___x_6562_, lean_object* v___x_6563_, lean_object* v_wfRel_6564_, lean_object* v_x_6565_, lean_object* v_type_6566_, lean_object* v___y_6567_, lean_object* v___y_6568_, lean_object* v___y_6569_, lean_object* v___y_6570_, lean_object* v___y_6571_, lean_object* v___y_6572_){
_start:
{
lean_object* v___x_6574_; lean_object* v___x_6575_; lean_object* v___x_6576_; lean_object* v___x_6577_; 
v___x_6574_ = lean_unsigned_to_nat(0u);
v___x_6575_ = lean_array_get_borrowed(v___x_6562_, v_x_6565_, v___x_6574_);
v___x_6576_ = l_Lean_Expr_fvarId_x21(v___x_6575_);
v___x_6577_ = l_Lean_FVarId_getUserName___redArg(v___x_6576_, v___y_6569_, v___y_6571_, v___y_6572_);
if (lean_obj_tag(v___x_6577_) == 0)
{
lean_object* v_a_6578_; lean_object* v___x_6579_; 
v_a_6578_ = lean_ctor_get(v___x_6577_, 0);
lean_inc(v_a_6578_);
lean_dec_ref_known(v___x_6577_, 1);
lean_inc(v___y_6572_);
lean_inc_ref(v___y_6571_);
lean_inc(v___y_6570_);
lean_inc_ref(v___y_6569_);
lean_inc(v___x_6575_);
v___x_6579_ = lean_infer_type(v___x_6575_, v___y_6569_, v___y_6570_, v___y_6571_, v___y_6572_);
if (lean_obj_tag(v___x_6579_) == 0)
{
lean_object* v_a_6580_; lean_object* v___x_6581_; 
v_a_6580_ = lean_ctor_get(v___x_6579_, 0);
lean_inc_n(v_a_6580_, 2);
lean_dec_ref_known(v___x_6579_, 1);
v___x_6581_ = l_Lean_Meta_getLevel(v_a_6580_, v___y_6569_, v___y_6570_, v___y_6571_, v___y_6572_);
if (lean_obj_tag(v___x_6581_) == 0)
{
lean_object* v_a_6582_; lean_object* v___x_6583_; 
v_a_6582_ = lean_ctor_get(v___x_6581_, 0);
lean_inc(v_a_6582_);
lean_dec_ref_known(v___x_6581_, 1);
lean_inc_ref(v_type_6566_);
v___x_6583_ = l_Lean_Meta_getLevel(v_type_6566_, v___y_6569_, v___y_6570_, v___y_6571_, v___y_6572_);
if (lean_obj_tag(v___x_6583_) == 0)
{
lean_object* v_a_6584_; lean_object* v___x_6585_; lean_object* v___x_6586_; uint8_t v___x_6587_; uint8_t v___x_6588_; uint8_t v___x_6589_; lean_object* v___x_6590_; 
v_a_6584_ = lean_ctor_get(v___x_6583_, 0);
lean_inc(v_a_6584_);
lean_dec_ref_known(v___x_6583_, 1);
v___x_6585_ = lean_mk_empty_array_with_capacity(v___x_6563_);
lean_inc(v___x_6575_);
lean_inc_ref(v___x_6585_);
v___x_6586_ = lean_array_push(v___x_6585_, v___x_6575_);
v___x_6587_ = 0;
v___x_6588_ = 1;
v___x_6589_ = 1;
v___x_6590_ = l_Lean_Meta_mkLambdaFVars(v___x_6586_, v_type_6566_, v___x_6587_, v___x_6588_, v___x_6587_, v___x_6588_, v___x_6589_, v___y_6569_, v___y_6570_, v___y_6571_, v___y_6572_);
lean_dec_ref(v___x_6586_);
if (lean_obj_tag(v___x_6590_) == 0)
{
lean_object* v_a_6591_; lean_object* v___x_6592_; 
v_a_6591_ = lean_ctor_get(v___x_6590_, 0);
lean_inc(v_a_6591_);
lean_dec_ref_known(v___x_6590_, 1);
lean_inc_ref(v_wfRel_6564_);
v___x_6592_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_6564_, v___y_6569_, v___y_6570_, v___y_6571_, v___y_6572_);
if (lean_obj_tag(v___x_6592_) == 0)
{
lean_object* v_a_6593_; lean_object* v___x_6595_; uint8_t v_isShared_6596_; uint8_t v_isSharedCheck_6637_; 
v_a_6593_ = lean_ctor_get(v___x_6592_, 0);
v_isSharedCheck_6637_ = !lean_is_exclusive(v___x_6592_);
if (v_isSharedCheck_6637_ == 0)
{
v___x_6595_ = v___x_6592_;
v_isShared_6596_ = v_isSharedCheck_6637_;
goto v_resetjp_6594_;
}
else
{
lean_inc(v_a_6593_);
lean_dec(v___x_6592_);
v___x_6595_ = lean_box(0);
v_isShared_6596_ = v_isSharedCheck_6637_;
goto v_resetjp_6594_;
}
v_resetjp_6594_:
{
if (lean_obj_tag(v_a_6593_) == 1)
{
lean_object* v_val_6597_; lean_object* v___x_6598_; lean_object* v___x_6599_; lean_object* v___x_6600_; lean_object* v___x_6601_; lean_object* v___x_6602_; lean_object* v___x_6603_; lean_object* v___x_6604_; lean_object* v___x_6606_; 
lean_dec_ref(v___x_6585_);
lean_dec_ref(v_wfRel_6564_);
lean_dec(v___x_6563_);
v_val_6597_ = lean_ctor_get(v_a_6593_, 0);
lean_inc(v_val_6597_);
lean_dec_ref_known(v_a_6593_, 1);
v___x_6598_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__1___closed__2));
v___x_6599_ = lean_box(0);
v___x_6600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6600_, 0, v_a_6584_);
lean_ctor_set(v___x_6600_, 1, v___x_6599_);
v___x_6601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6601_, 0, v_a_6582_);
lean_ctor_set(v___x_6601_, 1, v___x_6600_);
v___x_6602_ = l_Lean_mkConst(v___x_6598_, v___x_6601_);
v___x_6603_ = l_Lean_mkApp3(v___x_6602_, v_a_6580_, v_a_6591_, v_val_6597_);
v___x_6604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6604_, 0, v___x_6603_);
lean_ctor_set(v___x_6604_, 1, v_a_6578_);
if (v_isShared_6596_ == 0)
{
lean_ctor_set(v___x_6595_, 0, v___x_6604_);
v___x_6606_ = v___x_6595_;
goto v_reusejp_6605_;
}
else
{
lean_object* v_reuseFailAlloc_6607_; 
v_reuseFailAlloc_6607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6607_, 0, v___x_6604_);
v___x_6606_ = v_reuseFailAlloc_6607_;
goto v_reusejp_6605_;
}
v_reusejp_6605_:
{
return v___x_6606_;
}
}
else
{
lean_object* v___x_6608_; lean_object* v___x_6609_; lean_object* v___x_6610_; lean_object* v___x_6611_; lean_object* v___x_6612_; lean_object* v___x_6613_; 
lean_del_object(v___x_6595_);
lean_dec(v_a_6593_);
v___x_6608_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__1___closed__4));
lean_inc_ref(v_wfRel_6564_);
v___x_6609_ = l_Lean_mkProj(v___x_6608_, v___x_6574_, v_wfRel_6564_);
v___x_6610_ = l_Lean_mkProj(v___x_6608_, v___x_6563_, v_wfRel_6564_);
v___x_6611_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__1___closed__6));
v___x_6612_ = lean_array_push(v___x_6585_, v___x_6610_);
v___x_6613_ = l_Lean_Meta_mkAppM(v___x_6611_, v___x_6612_, v___y_6569_, v___y_6570_, v___y_6571_, v___y_6572_);
if (lean_obj_tag(v___x_6613_) == 0)
{
lean_object* v_a_6614_; lean_object* v___x_6616_; uint8_t v_isShared_6617_; uint8_t v_isSharedCheck_6628_; 
v_a_6614_ = lean_ctor_get(v___x_6613_, 0);
v_isSharedCheck_6628_ = !lean_is_exclusive(v___x_6613_);
if (v_isSharedCheck_6628_ == 0)
{
v___x_6616_ = v___x_6613_;
v_isShared_6617_ = v_isSharedCheck_6628_;
goto v_resetjp_6615_;
}
else
{
lean_inc(v_a_6614_);
lean_dec(v___x_6613_);
v___x_6616_ = lean_box(0);
v_isShared_6617_ = v_isSharedCheck_6628_;
goto v_resetjp_6615_;
}
v_resetjp_6615_:
{
lean_object* v___x_6618_; lean_object* v___x_6619_; lean_object* v___x_6620_; lean_object* v___x_6621_; lean_object* v___x_6622_; lean_object* v___x_6623_; lean_object* v___x_6624_; lean_object* v___x_6626_; 
v___x_6618_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__1___closed__7));
v___x_6619_ = lean_box(0);
v___x_6620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6620_, 0, v_a_6584_);
lean_ctor_set(v___x_6620_, 1, v___x_6619_);
v___x_6621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6621_, 0, v_a_6582_);
lean_ctor_set(v___x_6621_, 1, v___x_6620_);
v___x_6622_ = l_Lean_mkConst(v___x_6618_, v___x_6621_);
v___x_6623_ = l_Lean_mkApp4(v___x_6622_, v_a_6580_, v_a_6591_, v___x_6609_, v_a_6614_);
v___x_6624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6624_, 0, v___x_6623_);
lean_ctor_set(v___x_6624_, 1, v_a_6578_);
if (v_isShared_6617_ == 0)
{
lean_ctor_set(v___x_6616_, 0, v___x_6624_);
v___x_6626_ = v___x_6616_;
goto v_reusejp_6625_;
}
else
{
lean_object* v_reuseFailAlloc_6627_; 
v_reuseFailAlloc_6627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6627_, 0, v___x_6624_);
v___x_6626_ = v_reuseFailAlloc_6627_;
goto v_reusejp_6625_;
}
v_reusejp_6625_:
{
return v___x_6626_;
}
}
}
else
{
lean_object* v_a_6629_; lean_object* v___x_6631_; uint8_t v_isShared_6632_; uint8_t v_isSharedCheck_6636_; 
lean_dec_ref(v___x_6609_);
lean_dec(v_a_6591_);
lean_dec(v_a_6584_);
lean_dec(v_a_6582_);
lean_dec(v_a_6580_);
lean_dec(v_a_6578_);
v_a_6629_ = lean_ctor_get(v___x_6613_, 0);
v_isSharedCheck_6636_ = !lean_is_exclusive(v___x_6613_);
if (v_isSharedCheck_6636_ == 0)
{
v___x_6631_ = v___x_6613_;
v_isShared_6632_ = v_isSharedCheck_6636_;
goto v_resetjp_6630_;
}
else
{
lean_inc(v_a_6629_);
lean_dec(v___x_6613_);
v___x_6631_ = lean_box(0);
v_isShared_6632_ = v_isSharedCheck_6636_;
goto v_resetjp_6630_;
}
v_resetjp_6630_:
{
lean_object* v___x_6634_; 
if (v_isShared_6632_ == 0)
{
v___x_6634_ = v___x_6631_;
goto v_reusejp_6633_;
}
else
{
lean_object* v_reuseFailAlloc_6635_; 
v_reuseFailAlloc_6635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6635_, 0, v_a_6629_);
v___x_6634_ = v_reuseFailAlloc_6635_;
goto v_reusejp_6633_;
}
v_reusejp_6633_:
{
return v___x_6634_;
}
}
}
}
}
}
else
{
lean_object* v_a_6638_; lean_object* v___x_6640_; uint8_t v_isShared_6641_; uint8_t v_isSharedCheck_6645_; 
lean_dec(v_a_6591_);
lean_dec_ref(v___x_6585_);
lean_dec(v_a_6584_);
lean_dec(v_a_6582_);
lean_dec(v_a_6580_);
lean_dec(v_a_6578_);
lean_dec_ref(v_wfRel_6564_);
lean_dec(v___x_6563_);
v_a_6638_ = lean_ctor_get(v___x_6592_, 0);
v_isSharedCheck_6645_ = !lean_is_exclusive(v___x_6592_);
if (v_isSharedCheck_6645_ == 0)
{
v___x_6640_ = v___x_6592_;
v_isShared_6641_ = v_isSharedCheck_6645_;
goto v_resetjp_6639_;
}
else
{
lean_inc(v_a_6638_);
lean_dec(v___x_6592_);
v___x_6640_ = lean_box(0);
v_isShared_6641_ = v_isSharedCheck_6645_;
goto v_resetjp_6639_;
}
v_resetjp_6639_:
{
lean_object* v___x_6643_; 
if (v_isShared_6641_ == 0)
{
v___x_6643_ = v___x_6640_;
goto v_reusejp_6642_;
}
else
{
lean_object* v_reuseFailAlloc_6644_; 
v_reuseFailAlloc_6644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6644_, 0, v_a_6638_);
v___x_6643_ = v_reuseFailAlloc_6644_;
goto v_reusejp_6642_;
}
v_reusejp_6642_:
{
return v___x_6643_;
}
}
}
}
else
{
lean_object* v_a_6646_; lean_object* v___x_6648_; uint8_t v_isShared_6649_; uint8_t v_isSharedCheck_6653_; 
lean_dec_ref(v___x_6585_);
lean_dec(v_a_6584_);
lean_dec(v_a_6582_);
lean_dec(v_a_6580_);
lean_dec(v_a_6578_);
lean_dec_ref(v_wfRel_6564_);
lean_dec(v___x_6563_);
v_a_6646_ = lean_ctor_get(v___x_6590_, 0);
v_isSharedCheck_6653_ = !lean_is_exclusive(v___x_6590_);
if (v_isSharedCheck_6653_ == 0)
{
v___x_6648_ = v___x_6590_;
v_isShared_6649_ = v_isSharedCheck_6653_;
goto v_resetjp_6647_;
}
else
{
lean_inc(v_a_6646_);
lean_dec(v___x_6590_);
v___x_6648_ = lean_box(0);
v_isShared_6649_ = v_isSharedCheck_6653_;
goto v_resetjp_6647_;
}
v_resetjp_6647_:
{
lean_object* v___x_6651_; 
if (v_isShared_6649_ == 0)
{
v___x_6651_ = v___x_6648_;
goto v_reusejp_6650_;
}
else
{
lean_object* v_reuseFailAlloc_6652_; 
v_reuseFailAlloc_6652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6652_, 0, v_a_6646_);
v___x_6651_ = v_reuseFailAlloc_6652_;
goto v_reusejp_6650_;
}
v_reusejp_6650_:
{
return v___x_6651_;
}
}
}
}
else
{
lean_object* v_a_6654_; lean_object* v___x_6656_; uint8_t v_isShared_6657_; uint8_t v_isSharedCheck_6661_; 
lean_dec(v_a_6582_);
lean_dec(v_a_6580_);
lean_dec(v_a_6578_);
lean_dec_ref(v_type_6566_);
lean_dec_ref(v_wfRel_6564_);
lean_dec(v___x_6563_);
v_a_6654_ = lean_ctor_get(v___x_6583_, 0);
v_isSharedCheck_6661_ = !lean_is_exclusive(v___x_6583_);
if (v_isSharedCheck_6661_ == 0)
{
v___x_6656_ = v___x_6583_;
v_isShared_6657_ = v_isSharedCheck_6661_;
goto v_resetjp_6655_;
}
else
{
lean_inc(v_a_6654_);
lean_dec(v___x_6583_);
v___x_6656_ = lean_box(0);
v_isShared_6657_ = v_isSharedCheck_6661_;
goto v_resetjp_6655_;
}
v_resetjp_6655_:
{
lean_object* v___x_6659_; 
if (v_isShared_6657_ == 0)
{
v___x_6659_ = v___x_6656_;
goto v_reusejp_6658_;
}
else
{
lean_object* v_reuseFailAlloc_6660_; 
v_reuseFailAlloc_6660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6660_, 0, v_a_6654_);
v___x_6659_ = v_reuseFailAlloc_6660_;
goto v_reusejp_6658_;
}
v_reusejp_6658_:
{
return v___x_6659_;
}
}
}
}
else
{
lean_object* v_a_6662_; lean_object* v___x_6664_; uint8_t v_isShared_6665_; uint8_t v_isSharedCheck_6669_; 
lean_dec(v_a_6580_);
lean_dec(v_a_6578_);
lean_dec_ref(v_type_6566_);
lean_dec_ref(v_wfRel_6564_);
lean_dec(v___x_6563_);
v_a_6662_ = lean_ctor_get(v___x_6581_, 0);
v_isSharedCheck_6669_ = !lean_is_exclusive(v___x_6581_);
if (v_isSharedCheck_6669_ == 0)
{
v___x_6664_ = v___x_6581_;
v_isShared_6665_ = v_isSharedCheck_6669_;
goto v_resetjp_6663_;
}
else
{
lean_inc(v_a_6662_);
lean_dec(v___x_6581_);
v___x_6664_ = lean_box(0);
v_isShared_6665_ = v_isSharedCheck_6669_;
goto v_resetjp_6663_;
}
v_resetjp_6663_:
{
lean_object* v___x_6667_; 
if (v_isShared_6665_ == 0)
{
v___x_6667_ = v___x_6664_;
goto v_reusejp_6666_;
}
else
{
lean_object* v_reuseFailAlloc_6668_; 
v_reuseFailAlloc_6668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6668_, 0, v_a_6662_);
v___x_6667_ = v_reuseFailAlloc_6668_;
goto v_reusejp_6666_;
}
v_reusejp_6666_:
{
return v___x_6667_;
}
}
}
}
else
{
lean_object* v_a_6670_; lean_object* v___x_6672_; uint8_t v_isShared_6673_; uint8_t v_isSharedCheck_6677_; 
lean_dec(v_a_6578_);
lean_dec_ref(v_type_6566_);
lean_dec_ref(v_wfRel_6564_);
lean_dec(v___x_6563_);
v_a_6670_ = lean_ctor_get(v___x_6579_, 0);
v_isSharedCheck_6677_ = !lean_is_exclusive(v___x_6579_);
if (v_isSharedCheck_6677_ == 0)
{
v___x_6672_ = v___x_6579_;
v_isShared_6673_ = v_isSharedCheck_6677_;
goto v_resetjp_6671_;
}
else
{
lean_inc(v_a_6670_);
lean_dec(v___x_6579_);
v___x_6672_ = lean_box(0);
v_isShared_6673_ = v_isSharedCheck_6677_;
goto v_resetjp_6671_;
}
v_resetjp_6671_:
{
lean_object* v___x_6675_; 
if (v_isShared_6673_ == 0)
{
v___x_6675_ = v___x_6672_;
goto v_reusejp_6674_;
}
else
{
lean_object* v_reuseFailAlloc_6676_; 
v_reuseFailAlloc_6676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6676_, 0, v_a_6670_);
v___x_6675_ = v_reuseFailAlloc_6676_;
goto v_reusejp_6674_;
}
v_reusejp_6674_:
{
return v___x_6675_;
}
}
}
}
else
{
lean_object* v_a_6678_; lean_object* v___x_6680_; uint8_t v_isShared_6681_; uint8_t v_isSharedCheck_6685_; 
lean_dec_ref(v_type_6566_);
lean_dec_ref(v_wfRel_6564_);
lean_dec(v___x_6563_);
v_a_6678_ = lean_ctor_get(v___x_6577_, 0);
v_isSharedCheck_6685_ = !lean_is_exclusive(v___x_6577_);
if (v_isSharedCheck_6685_ == 0)
{
v___x_6680_ = v___x_6577_;
v_isShared_6681_ = v_isSharedCheck_6685_;
goto v_resetjp_6679_;
}
else
{
lean_inc(v_a_6678_);
lean_dec(v___x_6577_);
v___x_6680_ = lean_box(0);
v_isShared_6681_ = v_isSharedCheck_6685_;
goto v_resetjp_6679_;
}
v_resetjp_6679_:
{
lean_object* v___x_6683_; 
if (v_isShared_6681_ == 0)
{
v___x_6683_ = v___x_6680_;
goto v_reusejp_6682_;
}
else
{
lean_object* v_reuseFailAlloc_6684_; 
v_reuseFailAlloc_6684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6684_, 0, v_a_6678_);
v___x_6683_ = v_reuseFailAlloc_6684_;
goto v_reusejp_6682_;
}
v_reusejp_6682_:
{
return v___x_6683_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__1___boxed(lean_object* v___x_6686_, lean_object* v___x_6687_, lean_object* v_wfRel_6688_, lean_object* v_x_6689_, lean_object* v_type_6690_, lean_object* v___y_6691_, lean_object* v___y_6692_, lean_object* v___y_6693_, lean_object* v___y_6694_, lean_object* v___y_6695_, lean_object* v___y_6696_, lean_object* v___y_6697_){
_start:
{
lean_object* v_res_6698_; 
v_res_6698_ = l_Lean_Elab_WF_mkFix___lam__1(v___x_6686_, v___x_6687_, v_wfRel_6688_, v_x_6689_, v_type_6690_, v___y_6691_, v___y_6692_, v___y_6693_, v___y_6694_, v___y_6695_, v___y_6696_);
lean_dec(v___y_6696_);
lean_dec_ref(v___y_6695_);
lean_dec(v___y_6694_);
lean_dec_ref(v___y_6693_);
lean_dec(v___y_6692_);
lean_dec_ref(v___y_6691_);
lean_dec_ref(v_x_6689_);
lean_dec_ref(v___x_6686_);
return v_res_6698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__2(lean_object* v___x_6699_, lean_object* v___x_6700_, lean_object* v___x_6701_, lean_object* v___f_6702_, lean_object* v_funNames_6703_, lean_object* v_argsPacker_6704_, lean_object* v_decrTactics_6705_, uint8_t v___x_6706_, lean_object* v_fst_6707_, lean_object* v_prefixArgs_6708_, lean_object* v___y_6709_, lean_object* v___y_6710_, lean_object* v___y_6711_, lean_object* v___y_6712_, lean_object* v___y_6713_, lean_object* v___y_6714_){
_start:
{
lean_object* v___x_6716_; 
lean_inc_ref(v___x_6700_);
lean_inc_ref(v___x_6699_);
v___x_6716_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v___x_6699_, v___x_6700_, v___x_6701_, v___f_6702_, v___y_6709_, v___y_6710_, v___y_6711_, v___y_6712_, v___y_6713_, v___y_6714_);
if (lean_obj_tag(v___x_6716_) == 0)
{
lean_object* v_a_6717_; lean_object* v___x_6718_; 
v_a_6717_ = lean_ctor_get(v___x_6716_, 0);
lean_inc(v_a_6717_);
lean_dec_ref_known(v___x_6716_, 1);
v___x_6718_ = l_Lean_Elab_WF_solveDecreasingGoals(v_funNames_6703_, v_argsPacker_6704_, v_decrTactics_6705_, v_a_6717_, v___y_6711_, v___y_6712_, v___y_6713_, v___y_6714_);
if (lean_obj_tag(v___x_6718_) == 0)
{
lean_object* v_a_6719_; lean_object* v___x_6720_; lean_object* v___x_6721_; lean_object* v___x_6722_; lean_object* v___x_6723_; uint8_t v___x_6724_; uint8_t v___x_6725_; lean_object* v___x_6726_; 
v_a_6719_ = lean_ctor_get(v___x_6718_, 0);
lean_inc(v_a_6719_);
lean_dec_ref_known(v___x_6718_, 1);
v___x_6720_ = lean_unsigned_to_nat(2u);
v___x_6721_ = lean_mk_empty_array_with_capacity(v___x_6720_);
v___x_6722_ = lean_array_push(v___x_6721_, v___x_6699_);
v___x_6723_ = lean_array_push(v___x_6722_, v___x_6700_);
v___x_6724_ = 1;
v___x_6725_ = 1;
v___x_6726_ = l_Lean_Meta_mkLambdaFVars(v___x_6723_, v_a_6719_, v___x_6706_, v___x_6724_, v___x_6706_, v___x_6724_, v___x_6725_, v___y_6711_, v___y_6712_, v___y_6713_, v___y_6714_);
lean_dec_ref(v___x_6723_);
if (lean_obj_tag(v___x_6726_) == 0)
{
lean_object* v_a_6727_; lean_object* v___x_6728_; lean_object* v___x_6729_; 
v_a_6727_ = lean_ctor_get(v___x_6726_, 0);
lean_inc(v_a_6727_);
lean_dec_ref_known(v___x_6726_, 1);
v___x_6728_ = l_Lean_Expr_app___override(v_fst_6707_, v_a_6727_);
v___x_6729_ = l_Lean_Meta_mkLambdaFVars(v_prefixArgs_6708_, v___x_6728_, v___x_6706_, v___x_6724_, v___x_6706_, v___x_6724_, v___x_6725_, v___y_6711_, v___y_6712_, v___y_6713_, v___y_6714_);
return v___x_6729_;
}
else
{
lean_dec_ref(v_fst_6707_);
return v___x_6726_;
}
}
else
{
lean_dec_ref(v_fst_6707_);
lean_dec_ref(v___x_6700_);
lean_dec_ref(v___x_6699_);
return v___x_6718_;
}
}
else
{
lean_dec_ref(v_fst_6707_);
lean_dec_ref(v_decrTactics_6705_);
lean_dec_ref(v_argsPacker_6704_);
lean_dec_ref(v_funNames_6703_);
lean_dec_ref(v___x_6700_);
lean_dec_ref(v___x_6699_);
return v___x_6716_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__2___boxed(lean_object** _args){
lean_object* v___x_6730_ = _args[0];
lean_object* v___x_6731_ = _args[1];
lean_object* v___x_6732_ = _args[2];
lean_object* v___f_6733_ = _args[3];
lean_object* v_funNames_6734_ = _args[4];
lean_object* v_argsPacker_6735_ = _args[5];
lean_object* v_decrTactics_6736_ = _args[6];
lean_object* v___x_6737_ = _args[7];
lean_object* v_fst_6738_ = _args[8];
lean_object* v_prefixArgs_6739_ = _args[9];
lean_object* v___y_6740_ = _args[10];
lean_object* v___y_6741_ = _args[11];
lean_object* v___y_6742_ = _args[12];
lean_object* v___y_6743_ = _args[13];
lean_object* v___y_6744_ = _args[14];
lean_object* v___y_6745_ = _args[15];
lean_object* v___y_6746_ = _args[16];
_start:
{
uint8_t v___x_5939__boxed_6747_; lean_object* v_res_6748_; 
v___x_5939__boxed_6747_ = lean_unbox(v___x_6737_);
v_res_6748_ = l_Lean_Elab_WF_mkFix___lam__2(v___x_6730_, v___x_6731_, v___x_6732_, v___f_6733_, v_funNames_6734_, v_argsPacker_6735_, v_decrTactics_6736_, v___x_5939__boxed_6747_, v_fst_6738_, v_prefixArgs_6739_, v___y_6740_, v___y_6741_, v___y_6742_, v___y_6743_, v___y_6744_, v___y_6745_);
lean_dec(v___y_6745_);
lean_dec_ref(v___y_6744_);
lean_dec(v___y_6743_);
lean_dec_ref(v___y_6742_);
lean_dec(v___y_6741_);
lean_dec_ref(v___y_6740_);
lean_dec_ref(v_prefixArgs_6739_);
return v_res_6748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__3(lean_object* v___x_6749_, lean_object* v_snd_6750_, lean_object* v___x_6751_, lean_object* v_prefixArgs_6752_, lean_object* v_value_6753_, lean_object* v___f_6754_, lean_object* v_funNames_6755_, lean_object* v_argsPacker_6756_, lean_object* v_decrTactics_6757_, uint8_t v___x_6758_, lean_object* v_fst_6759_, lean_object* v_xs_6760_, lean_object* v_x_6761_, lean_object* v___y_6762_, lean_object* v___y_6763_, lean_object* v___y_6764_, lean_object* v___y_6765_, lean_object* v___y_6766_, lean_object* v___y_6767_){
_start:
{
lean_object* v_lctx_6769_; lean_object* v___x_6770_; lean_object* v___x_6771_; lean_object* v___x_6772_; lean_object* v___x_6773_; lean_object* v___x_6774_; lean_object* v___x_6775_; lean_object* v___x_6776_; lean_object* v___x_6777_; lean_object* v___f_6778_; lean_object* v___x_6779_; 
v_lctx_6769_ = lean_ctor_get(v___y_6764_, 2);
v___x_6770_ = lean_unsigned_to_nat(0u);
v___x_6771_ = lean_array_get_borrowed(v___x_6749_, v_xs_6760_, v___x_6770_);
v___x_6772_ = l_Lean_Expr_fvarId_x21(v___x_6771_);
lean_inc_ref(v_lctx_6769_);
v___x_6773_ = l_Lean_LocalContext_setUserName(v_lctx_6769_, v___x_6772_, v_snd_6750_);
v___x_6774_ = lean_array_get_borrowed(v___x_6749_, v_xs_6760_, v___x_6751_);
lean_inc_n(v___x_6771_, 2);
lean_inc_ref(v_prefixArgs_6752_);
v___x_6775_ = lean_array_push(v_prefixArgs_6752_, v___x_6771_);
v___x_6776_ = l_Lean_Expr_beta(v_value_6753_, v___x_6775_);
v___x_6777_ = lean_box(v___x_6758_);
lean_inc(v___x_6774_);
v___f_6778_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__2___boxed), 17, 10);
lean_closure_set(v___f_6778_, 0, v___x_6771_);
lean_closure_set(v___f_6778_, 1, v___x_6774_);
lean_closure_set(v___f_6778_, 2, v___x_6776_);
lean_closure_set(v___f_6778_, 3, v___f_6754_);
lean_closure_set(v___f_6778_, 4, v_funNames_6755_);
lean_closure_set(v___f_6778_, 5, v_argsPacker_6756_);
lean_closure_set(v___f_6778_, 6, v_decrTactics_6757_);
lean_closure_set(v___f_6778_, 7, v___x_6777_);
lean_closure_set(v___f_6778_, 8, v_fst_6759_);
lean_closure_set(v___f_6778_, 9, v_prefixArgs_6752_);
v___x_6779_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v___x_6773_, v___f_6778_, v___y_6762_, v___y_6763_, v___y_6764_, v___y_6765_, v___y_6766_, v___y_6767_);
return v___x_6779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__3___boxed(lean_object** _args){
lean_object* v___x_6780_ = _args[0];
lean_object* v_snd_6781_ = _args[1];
lean_object* v___x_6782_ = _args[2];
lean_object* v_prefixArgs_6783_ = _args[3];
lean_object* v_value_6784_ = _args[4];
lean_object* v___f_6785_ = _args[5];
lean_object* v_funNames_6786_ = _args[6];
lean_object* v_argsPacker_6787_ = _args[7];
lean_object* v_decrTactics_6788_ = _args[8];
lean_object* v___x_6789_ = _args[9];
lean_object* v_fst_6790_ = _args[10];
lean_object* v_xs_6791_ = _args[11];
lean_object* v_x_6792_ = _args[12];
lean_object* v___y_6793_ = _args[13];
lean_object* v___y_6794_ = _args[14];
lean_object* v___y_6795_ = _args[15];
lean_object* v___y_6796_ = _args[16];
lean_object* v___y_6797_ = _args[17];
lean_object* v___y_6798_ = _args[18];
lean_object* v___y_6799_ = _args[19];
_start:
{
uint8_t v___x_6009__boxed_6800_; lean_object* v_res_6801_; 
v___x_6009__boxed_6800_ = lean_unbox(v___x_6789_);
v_res_6801_ = l_Lean_Elab_WF_mkFix___lam__3(v___x_6780_, v_snd_6781_, v___x_6782_, v_prefixArgs_6783_, v_value_6784_, v___f_6785_, v_funNames_6786_, v_argsPacker_6787_, v_decrTactics_6788_, v___x_6009__boxed_6800_, v_fst_6790_, v_xs_6791_, v_x_6792_, v___y_6793_, v___y_6794_, v___y_6795_, v___y_6796_, v___y_6797_, v___y_6798_);
lean_dec(v___y_6798_);
lean_dec_ref(v___y_6797_);
lean_dec(v___y_6796_);
lean_dec_ref(v___y_6795_);
lean_dec(v___y_6794_);
lean_dec_ref(v___y_6793_);
lean_dec_ref(v_x_6792_);
lean_dec_ref(v_xs_6791_);
lean_dec(v___x_6782_);
lean_dec_ref(v___x_6780_);
return v_res_6801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix(lean_object* v_preDef_6806_, lean_object* v_prefixArgs_6807_, lean_object* v_argsPacker_6808_, lean_object* v_wfRel_6809_, lean_object* v_funNames_6810_, lean_object* v_decrTactics_6811_, lean_object* v_a_6812_, lean_object* v_a_6813_, lean_object* v_a_6814_, lean_object* v_a_6815_, lean_object* v_a_6816_, lean_object* v_a_6817_){
_start:
{
lean_object* v_declName_6819_; lean_object* v_type_6820_; lean_object* v_value_6821_; lean_object* v___f_6822_; lean_object* v___x_6823_; lean_object* v___x_6824_; 
v_declName_6819_ = lean_ctor_get(v_preDef_6806_, 3);
lean_inc(v_declName_6819_);
v_type_6820_ = lean_ctor_get(v_preDef_6806_, 6);
lean_inc_ref(v_type_6820_);
v_value_6821_ = lean_ctor_get(v_preDef_6806_, 7);
lean_inc_ref(v_value_6821_);
lean_dec_ref(v_preDef_6806_);
lean_inc_ref(v_prefixArgs_6807_);
v___f_6822_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__0___boxed), 12, 2);
lean_closure_set(v___f_6822_, 0, v_prefixArgs_6807_);
lean_closure_set(v___f_6822_, 1, v_declName_6819_);
v___x_6823_ = l_Lean_instInhabitedExpr;
v___x_6824_ = l_Lean_Meta_instantiateForall(v_type_6820_, v_prefixArgs_6807_, v_a_6814_, v_a_6815_, v_a_6816_, v_a_6817_);
if (lean_obj_tag(v___x_6824_) == 0)
{
lean_object* v_a_6825_; lean_object* v___x_6826_; lean_object* v___f_6827_; lean_object* v___x_6828_; uint8_t v___x_6829_; lean_object* v___x_6830_; 
v_a_6825_ = lean_ctor_get(v___x_6824_, 0);
lean_inc(v_a_6825_);
lean_dec_ref_known(v___x_6824_, 1);
v___x_6826_ = lean_unsigned_to_nat(1u);
v___f_6827_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__1___boxed), 12, 3);
lean_closure_set(v___f_6827_, 0, v___x_6823_);
lean_closure_set(v___f_6827_, 1, v___x_6826_);
lean_closure_set(v___f_6827_, 2, v_wfRel_6809_);
v___x_6828_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___closed__0));
v___x_6829_ = 0;
v___x_6830_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_a_6825_, v___x_6828_, v___f_6827_, v___x_6829_, v___x_6829_, v_a_6812_, v_a_6813_, v_a_6814_, v_a_6815_, v_a_6816_, v_a_6817_);
if (lean_obj_tag(v___x_6830_) == 0)
{
lean_object* v_a_6831_; lean_object* v_fst_6832_; lean_object* v_snd_6833_; lean_object* v___x_6834_; lean_object* v___f_6835_; lean_object* v___x_6836_; 
v_a_6831_ = lean_ctor_get(v___x_6830_, 0);
lean_inc(v_a_6831_);
lean_dec_ref_known(v___x_6830_, 1);
v_fst_6832_ = lean_ctor_get(v_a_6831_, 0);
lean_inc_n(v_fst_6832_, 2);
v_snd_6833_ = lean_ctor_get(v_a_6831_, 1);
lean_inc(v_snd_6833_);
lean_dec(v_a_6831_);
v___x_6834_ = lean_box(v___x_6829_);
v___f_6835_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__3___boxed), 20, 11);
lean_closure_set(v___f_6835_, 0, v___x_6823_);
lean_closure_set(v___f_6835_, 1, v_snd_6833_);
lean_closure_set(v___f_6835_, 2, v___x_6826_);
lean_closure_set(v___f_6835_, 3, v_prefixArgs_6807_);
lean_closure_set(v___f_6835_, 4, v_value_6821_);
lean_closure_set(v___f_6835_, 5, v___f_6822_);
lean_closure_set(v___f_6835_, 6, v_funNames_6810_);
lean_closure_set(v___f_6835_, 7, v_argsPacker_6808_);
lean_closure_set(v___f_6835_, 8, v_decrTactics_6811_);
lean_closure_set(v___f_6835_, 9, v___x_6834_);
lean_closure_set(v___f_6835_, 10, v_fst_6832_);
lean_inc(v_a_6817_);
lean_inc_ref(v_a_6816_);
lean_inc(v_a_6815_);
lean_inc_ref(v_a_6814_);
v___x_6836_ = lean_infer_type(v_fst_6832_, v_a_6814_, v_a_6815_, v_a_6816_, v_a_6817_);
if (lean_obj_tag(v___x_6836_) == 0)
{
lean_object* v_a_6837_; lean_object* v___x_6838_; 
v_a_6837_ = lean_ctor_get(v___x_6836_, 0);
lean_inc(v_a_6837_);
lean_dec_ref_known(v___x_6836_, 1);
lean_inc(v_a_6817_);
lean_inc_ref(v_a_6816_);
lean_inc(v_a_6815_);
lean_inc_ref(v_a_6814_);
v___x_6838_ = lean_whnf(v_a_6837_, v_a_6814_, v_a_6815_, v_a_6816_, v_a_6817_);
if (lean_obj_tag(v___x_6838_) == 0)
{
lean_object* v_a_6839_; lean_object* v___x_6840_; lean_object* v___x_6841_; lean_object* v___x_6842_; 
v_a_6839_ = lean_ctor_get(v___x_6838_, 0);
lean_inc(v_a_6839_);
lean_dec_ref_known(v___x_6838_, 1);
v___x_6840_ = l_Lean_Expr_bindingDomain_x21(v_a_6839_);
lean_dec(v_a_6839_);
v___x_6841_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___closed__1));
v___x_6842_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v___x_6840_, v___x_6841_, v___f_6835_, v___x_6829_, v___x_6829_, v_a_6812_, v_a_6813_, v_a_6814_, v_a_6815_, v_a_6816_, v_a_6817_);
return v___x_6842_;
}
else
{
lean_dec_ref(v___f_6835_);
return v___x_6838_;
}
}
else
{
lean_dec_ref(v___f_6835_);
return v___x_6836_;
}
}
else
{
lean_object* v_a_6843_; lean_object* v___x_6845_; uint8_t v_isShared_6846_; uint8_t v_isSharedCheck_6850_; 
lean_dec_ref(v___f_6822_);
lean_dec_ref(v_value_6821_);
lean_dec_ref(v_decrTactics_6811_);
lean_dec_ref(v_funNames_6810_);
lean_dec_ref(v_argsPacker_6808_);
lean_dec_ref(v_prefixArgs_6807_);
v_a_6843_ = lean_ctor_get(v___x_6830_, 0);
v_isSharedCheck_6850_ = !lean_is_exclusive(v___x_6830_);
if (v_isSharedCheck_6850_ == 0)
{
v___x_6845_ = v___x_6830_;
v_isShared_6846_ = v_isSharedCheck_6850_;
goto v_resetjp_6844_;
}
else
{
lean_inc(v_a_6843_);
lean_dec(v___x_6830_);
v___x_6845_ = lean_box(0);
v_isShared_6846_ = v_isSharedCheck_6850_;
goto v_resetjp_6844_;
}
v_resetjp_6844_:
{
lean_object* v___x_6848_; 
if (v_isShared_6846_ == 0)
{
v___x_6848_ = v___x_6845_;
goto v_reusejp_6847_;
}
else
{
lean_object* v_reuseFailAlloc_6849_; 
v_reuseFailAlloc_6849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6849_, 0, v_a_6843_);
v___x_6848_ = v_reuseFailAlloc_6849_;
goto v_reusejp_6847_;
}
v_reusejp_6847_:
{
return v___x_6848_;
}
}
}
}
else
{
lean_dec_ref(v___f_6822_);
lean_dec_ref(v_value_6821_);
lean_dec_ref(v_decrTactics_6811_);
lean_dec_ref(v_funNames_6810_);
lean_dec_ref(v_wfRel_6809_);
lean_dec_ref(v_argsPacker_6808_);
lean_dec_ref(v_prefixArgs_6807_);
return v___x_6824_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___boxed(lean_object* v_preDef_6851_, lean_object* v_prefixArgs_6852_, lean_object* v_argsPacker_6853_, lean_object* v_wfRel_6854_, lean_object* v_funNames_6855_, lean_object* v_decrTactics_6856_, lean_object* v_a_6857_, lean_object* v_a_6858_, lean_object* v_a_6859_, lean_object* v_a_6860_, lean_object* v_a_6861_, lean_object* v_a_6862_, lean_object* v_a_6863_){
_start:
{
lean_object* v_res_6864_; 
v_res_6864_ = l_Lean_Elab_WF_mkFix(v_preDef_6851_, v_prefixArgs_6852_, v_argsPacker_6853_, v_wfRel_6854_, v_funNames_6855_, v_decrTactics_6856_, v_a_6857_, v_a_6858_, v_a_6859_, v_a_6860_, v_a_6861_, v_a_6862_);
lean_dec(v_a_6862_);
lean_dec_ref(v_a_6861_);
lean_dec(v_a_6860_);
lean_dec_ref(v_a_6859_);
lean_dec(v_a_6858_);
lean_dec_ref(v_a_6857_);
return v_res_6864_;
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
