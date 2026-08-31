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
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
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
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
lean_object* l_instMonadEIO(lean_object*);
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addPPExplicitToExposeDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalContext_contains(lean_object*, lean_object*);
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
v_ref_75_ = lean_ctor_get(v_a_72_, 4);
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
v_options_139_ = lean_ctor_get(v___y_131_, 1);
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
v_ref_156_ = lean_ctor_get(v___y_153_, 4);
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
v_ref_323_ = lean_ctor_get(v___y_320_, 4);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12_spec__22___redArg(lean_object* v_x_378_, lean_object* v_x_379_){
_start:
{
if (lean_obj_tag(v_x_379_) == 0)
{
return v_x_378_;
}
else
{
lean_object* v_key_380_; lean_object* v_value_381_; lean_object* v_tail_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_405_; 
v_key_380_ = lean_ctor_get(v_x_379_, 0);
v_value_381_ = lean_ctor_get(v_x_379_, 1);
v_tail_382_ = lean_ctor_get(v_x_379_, 2);
v_isSharedCheck_405_ = !lean_is_exclusive(v_x_379_);
if (v_isSharedCheck_405_ == 0)
{
v___x_384_ = v_x_379_;
v_isShared_385_ = v_isSharedCheck_405_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_tail_382_);
lean_inc(v_value_381_);
lean_inc(v_key_380_);
lean_dec(v_x_379_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_405_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_386_; uint64_t v___x_387_; uint64_t v___x_388_; uint64_t v___x_389_; uint64_t v_fold_390_; uint64_t v___x_391_; uint64_t v___x_392_; uint64_t v___x_393_; size_t v___x_394_; size_t v___x_395_; size_t v___x_396_; size_t v___x_397_; size_t v___x_398_; lean_object* v___x_399_; lean_object* v___x_401_; 
v___x_386_ = lean_array_get_size(v_x_378_);
v___x_387_ = l_Lean_Expr_hash(v_key_380_);
v___x_388_ = 32ULL;
v___x_389_ = lean_uint64_shift_right(v___x_387_, v___x_388_);
v_fold_390_ = lean_uint64_xor(v___x_387_, v___x_389_);
v___x_391_ = 16ULL;
v___x_392_ = lean_uint64_shift_right(v_fold_390_, v___x_391_);
v___x_393_ = lean_uint64_xor(v_fold_390_, v___x_392_);
v___x_394_ = lean_uint64_to_usize(v___x_393_);
v___x_395_ = lean_usize_of_nat(v___x_386_);
v___x_396_ = ((size_t)1ULL);
v___x_397_ = lean_usize_sub(v___x_395_, v___x_396_);
v___x_398_ = lean_usize_land(v___x_394_, v___x_397_);
v___x_399_ = lean_array_uget_borrowed(v_x_378_, v___x_398_);
lean_inc(v___x_399_);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 2, v___x_399_);
v___x_401_ = v___x_384_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_key_380_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_value_381_);
lean_ctor_set(v_reuseFailAlloc_404_, 2, v___x_399_);
v___x_401_ = v_reuseFailAlloc_404_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
lean_object* v___x_402_; 
v___x_402_ = lean_array_uset(v_x_378_, v___x_398_, v___x_401_);
v_x_378_ = v___x_402_;
v_x_379_ = v_tail_382_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12___redArg(lean_object* v_i_406_, lean_object* v_source_407_, lean_object* v_target_408_){
_start:
{
lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_409_ = lean_array_get_size(v_source_407_);
v___x_410_ = lean_nat_dec_lt(v_i_406_, v___x_409_);
if (v___x_410_ == 0)
{
lean_dec_ref(v_source_407_);
lean_dec(v_i_406_);
return v_target_408_;
}
else
{
lean_object* v_es_411_; lean_object* v___x_412_; lean_object* v_source_413_; lean_object* v_target_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v_es_411_ = lean_array_fget(v_source_407_, v_i_406_);
v___x_412_ = lean_box(0);
v_source_413_ = lean_array_fset(v_source_407_, v_i_406_, v___x_412_);
v_target_414_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12_spec__22___redArg(v_target_408_, v_es_411_);
v___x_415_ = lean_unsigned_to_nat(1u);
v___x_416_ = lean_nat_add(v_i_406_, v___x_415_);
lean_dec(v_i_406_);
v_i_406_ = v___x_416_;
v_source_407_ = v_source_413_;
v_target_408_ = v_target_414_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5___redArg(lean_object* v_data_418_){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v_nbuckets_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_419_ = lean_array_get_size(v_data_418_);
v___x_420_ = lean_unsigned_to_nat(2u);
v_nbuckets_421_ = lean_nat_mul(v___x_419_, v___x_420_);
v___x_422_ = lean_unsigned_to_nat(0u);
v___x_423_ = lean_box(0);
v___x_424_ = lean_mk_array(v_nbuckets_421_, v___x_423_);
v___x_425_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12___redArg(v___x_422_, v_data_418_, v___x_424_);
return v___x_425_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg(lean_object* v_a_426_, lean_object* v_x_427_){
_start:
{
if (lean_obj_tag(v_x_427_) == 0)
{
uint8_t v___x_428_; 
v___x_428_ = 0;
return v___x_428_;
}
else
{
lean_object* v_key_429_; lean_object* v_tail_430_; uint8_t v___x_431_; 
v_key_429_ = lean_ctor_get(v_x_427_, 0);
v_tail_430_ = lean_ctor_get(v_x_427_, 2);
v___x_431_ = lean_expr_eqv(v_key_429_, v_a_426_);
if (v___x_431_ == 0)
{
v_x_427_ = v_tail_430_;
goto _start;
}
else
{
return v___x_431_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg___boxed(lean_object* v_a_433_, lean_object* v_x_434_){
_start:
{
uint8_t v_res_435_; lean_object* v_r_436_; 
v_res_435_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg(v_a_433_, v_x_434_);
lean_dec(v_x_434_);
lean_dec_ref(v_a_433_);
v_r_436_ = lean_box(v_res_435_);
return v_r_436_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6___redArg(lean_object* v_a_437_, lean_object* v_b_438_, lean_object* v_x_439_){
_start:
{
if (lean_obj_tag(v_x_439_) == 0)
{
lean_dec(v_b_438_);
lean_dec_ref(v_a_437_);
return v_x_439_;
}
else
{
lean_object* v_key_440_; lean_object* v_value_441_; lean_object* v_tail_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_454_; 
v_key_440_ = lean_ctor_get(v_x_439_, 0);
v_value_441_ = lean_ctor_get(v_x_439_, 1);
v_tail_442_ = lean_ctor_get(v_x_439_, 2);
v_isSharedCheck_454_ = !lean_is_exclusive(v_x_439_);
if (v_isSharedCheck_454_ == 0)
{
v___x_444_ = v_x_439_;
v_isShared_445_ = v_isSharedCheck_454_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_tail_442_);
lean_inc(v_value_441_);
lean_inc(v_key_440_);
lean_dec(v_x_439_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_454_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
uint8_t v___x_446_; 
v___x_446_ = lean_expr_eqv(v_key_440_, v_a_437_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; lean_object* v___x_449_; 
v___x_447_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6___redArg(v_a_437_, v_b_438_, v_tail_442_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 2, v___x_447_);
v___x_449_ = v___x_444_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_key_440_);
lean_ctor_set(v_reuseFailAlloc_450_, 1, v_value_441_);
lean_ctor_set(v_reuseFailAlloc_450_, 2, v___x_447_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
else
{
lean_object* v___x_452_; 
lean_dec(v_value_441_);
lean_dec(v_key_440_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 1, v_b_438_);
lean_ctor_set(v___x_444_, 0, v_a_437_);
v___x_452_ = v___x_444_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_437_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v_b_438_);
lean_ctor_set(v_reuseFailAlloc_453_, 2, v_tail_442_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4___redArg(lean_object* v_m_455_, lean_object* v_a_456_, lean_object* v_b_457_){
_start:
{
lean_object* v_size_458_; lean_object* v_buckets_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_502_; 
v_size_458_ = lean_ctor_get(v_m_455_, 0);
v_buckets_459_ = lean_ctor_get(v_m_455_, 1);
v_isSharedCheck_502_ = !lean_is_exclusive(v_m_455_);
if (v_isSharedCheck_502_ == 0)
{
v___x_461_ = v_m_455_;
v_isShared_462_ = v_isSharedCheck_502_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_buckets_459_);
lean_inc(v_size_458_);
lean_dec(v_m_455_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_502_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_463_; uint64_t v___x_464_; uint64_t v___x_465_; uint64_t v___x_466_; uint64_t v_fold_467_; uint64_t v___x_468_; uint64_t v___x_469_; uint64_t v___x_470_; size_t v___x_471_; size_t v___x_472_; size_t v___x_473_; size_t v___x_474_; size_t v___x_475_; lean_object* v_bkt_476_; uint8_t v___x_477_; 
v___x_463_ = lean_array_get_size(v_buckets_459_);
v___x_464_ = l_Lean_Expr_hash(v_a_456_);
v___x_465_ = 32ULL;
v___x_466_ = lean_uint64_shift_right(v___x_464_, v___x_465_);
v_fold_467_ = lean_uint64_xor(v___x_464_, v___x_466_);
v___x_468_ = 16ULL;
v___x_469_ = lean_uint64_shift_right(v_fold_467_, v___x_468_);
v___x_470_ = lean_uint64_xor(v_fold_467_, v___x_469_);
v___x_471_ = lean_uint64_to_usize(v___x_470_);
v___x_472_ = lean_usize_of_nat(v___x_463_);
v___x_473_ = ((size_t)1ULL);
v___x_474_ = lean_usize_sub(v___x_472_, v___x_473_);
v___x_475_ = lean_usize_land(v___x_471_, v___x_474_);
v_bkt_476_ = lean_array_uget_borrowed(v_buckets_459_, v___x_475_);
v___x_477_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg(v_a_456_, v_bkt_476_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; lean_object* v_size_x27_479_; lean_object* v___x_480_; lean_object* v_buckets_x27_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_478_ = lean_unsigned_to_nat(1u);
v_size_x27_479_ = lean_nat_add(v_size_458_, v___x_478_);
lean_dec(v_size_458_);
lean_inc(v_bkt_476_);
v___x_480_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_480_, 0, v_a_456_);
lean_ctor_set(v___x_480_, 1, v_b_457_);
lean_ctor_set(v___x_480_, 2, v_bkt_476_);
v_buckets_x27_481_ = lean_array_uset(v_buckets_459_, v___x_475_, v___x_480_);
v___x_482_ = lean_unsigned_to_nat(4u);
v___x_483_ = lean_nat_mul(v_size_x27_479_, v___x_482_);
v___x_484_ = lean_unsigned_to_nat(3u);
v___x_485_ = lean_nat_div(v___x_483_, v___x_484_);
lean_dec(v___x_483_);
v___x_486_ = lean_array_get_size(v_buckets_x27_481_);
v___x_487_ = lean_nat_dec_le(v___x_485_, v___x_486_);
lean_dec(v___x_485_);
if (v___x_487_ == 0)
{
lean_object* v_val_488_; lean_object* v___x_490_; 
v_val_488_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5___redArg(v_buckets_x27_481_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 1, v_val_488_);
lean_ctor_set(v___x_461_, 0, v_size_x27_479_);
v___x_490_ = v___x_461_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_size_x27_479_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_val_488_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
else
{
lean_object* v___x_493_; 
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 1, v_buckets_x27_481_);
lean_ctor_set(v___x_461_, 0, v_size_x27_479_);
v___x_493_ = v___x_461_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_size_x27_479_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_buckets_x27_481_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
else
{
lean_object* v___x_495_; lean_object* v_buckets_x27_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_500_; 
lean_inc(v_bkt_476_);
v___x_495_ = lean_box(0);
v_buckets_x27_496_ = lean_array_uset(v_buckets_459_, v___x_475_, v___x_495_);
v___x_497_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6___redArg(v_a_456_, v_b_457_, v_bkt_476_);
v___x_498_ = lean_array_uset(v_buckets_x27_496_, v___x_475_, v___x_497_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 1, v___x_498_);
v___x_500_ = v___x_461_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_size_458_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v___x_498_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(lean_object* v_msg_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
lean_object* v_ref_509_; lean_object* v___x_510_; lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_519_; 
v_ref_509_ = lean_ctor_get(v___y_506_, 4);
v___x_510_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
v_a_511_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_519_ == 0)
{
v___x_513_ = v___x_510_;
v_isShared_514_ = v_isSharedCheck_519_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_510_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_519_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_515_; lean_object* v___x_517_; 
lean_inc(v_ref_509_);
v___x_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_515_, 0, v_ref_509_);
lean_ctor_set(v___x_515_, 1, v_a_511_);
if (v_isShared_514_ == 0)
{
lean_ctor_set_tag(v___x_513_, 1);
lean_ctor_set(v___x_513_, 0, v___x_515_);
v___x_517_ = v___x_513_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_515_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg___boxed(lean_object* v_msg_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v_msg_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
return v_res_526_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__1(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__0));
v___x_529_ = l_Lean_stringToMessageData(v___x_528_);
return v___x_529_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3(void){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__2));
v___x_532_ = l_Lean_stringToMessageData(v___x_531_);
return v___x_532_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__5(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__4));
v___x_535_ = l_Lean_stringToMessageData(v___x_534_);
return v___x_535_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__7(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__6));
v___x_538_ = l_Lean_stringToMessageData(v___x_537_);
return v___x_538_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__9(void){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__8));
v___x_541_ = l_Lean_stringToMessageData(v___x_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0(lean_object* v_a_542_, lean_object* v_e_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v___x_635_; 
lean_inc_ref(v_a_542_);
v___x_635_ = l_Lean_Meta_isTypeCorrect(v_a_542_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; uint8_t v___x_637_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_a_636_);
lean_dec_ref_known(v___x_635_, 1);
v___x_637_ = lean_unbox(v_a_636_);
lean_dec(v_a_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_638_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__9, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__9);
lean_inc_ref(v_e_543_);
v___x_639_ = l_Lean_indentExpr(v_e_543_);
v___x_640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_638_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
v___x_641_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3);
v___x_642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_640_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
lean_inc_ref(v_a_542_);
v___x_643_ = l_Lean_indentExpr(v_a_542_);
v___x_644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_642_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
v___x_645_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v___x_644_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_dec_ref_known(v___x_645_, 1);
v___y_554_ = v___y_544_;
v___y_555_ = v___y_545_;
v___y_556_ = v___y_546_;
v___y_557_ = v___y_547_;
v___y_558_ = v___y_548_;
v___y_559_ = v___y_549_;
v___y_560_ = v___y_550_;
v___y_561_ = v___y_551_;
goto v___jp_553_;
}
else
{
lean_dec_ref(v_e_543_);
lean_dec_ref(v_a_542_);
return v___x_645_;
}
}
else
{
v___y_554_ = v___y_544_;
v___y_555_ = v___y_545_;
v___y_556_ = v___y_546_;
v___y_557_ = v___y_547_;
v___y_558_ = v___y_548_;
v___y_559_ = v___y_549_;
v___y_560_ = v___y_550_;
v___y_561_ = v___y_551_;
goto v___jp_553_;
}
}
else
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_653_; 
lean_dec_ref(v_e_543_);
lean_dec_ref(v_a_542_);
v_a_646_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_653_ == 0)
{
v___x_648_ = v___x_635_;
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_635_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_646_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
v___jp_553_:
{
lean_object* v___x_562_; 
lean_inc(v___y_561_);
lean_inc_ref(v___y_560_);
lean_inc(v___y_559_);
lean_inc_ref(v___y_558_);
lean_inc_ref(v_e_543_);
v___x_562_ = lean_infer_type(v_e_543_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v_a_563_; lean_object* v___x_564_; 
v_a_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc(v_a_563_);
lean_dec_ref_known(v___x_562_, 1);
lean_inc(v___y_561_);
lean_inc_ref(v___y_560_);
lean_inc(v___y_559_);
lean_inc_ref(v___y_558_);
lean_inc_ref(v_a_542_);
v___x_564_ = lean_infer_type(v_a_542_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v___x_566_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
lean_inc_n(v_a_565_, 2);
lean_dec_ref_known(v___x_564_, 1);
lean_inc(v_a_563_);
v___x_566_ = l_Lean_Meta_isExprDefEq(v_a_563_, v_a_565_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_610_; 
v_a_567_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_610_ == 0)
{
v___x_569_ = v___x_566_;
v_isShared_570_ = v_isSharedCheck_610_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_566_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_610_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
uint8_t v___x_571_; 
v___x_571_ = lean_unbox(v_a_567_);
lean_dec(v_a_567_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; 
lean_del_object(v___x_569_);
v___x_572_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_a_563_, v_a_565_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v_fst_574_; lean_object* v_snd_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_597_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_a_573_);
lean_dec_ref_known(v___x_572_, 1);
v_fst_574_ = lean_ctor_get(v_a_573_, 0);
v_snd_575_ = lean_ctor_get(v_a_573_, 1);
v_isSharedCheck_597_ = !lean_is_exclusive(v_a_573_);
if (v_isSharedCheck_597_ == 0)
{
v___x_577_ = v_a_573_;
v_isShared_578_ = v_isSharedCheck_597_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_snd_575_);
lean_inc(v_fst_574_);
lean_dec(v_a_573_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_597_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_582_; 
v___x_579_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__1);
v___x_580_ = l_Lean_indentExpr(v_e_543_);
if (v_isShared_578_ == 0)
{
lean_ctor_set_tag(v___x_577_, 7);
lean_ctor_set(v___x_577_, 1, v___x_580_);
lean_ctor_set(v___x_577_, 0, v___x_579_);
v___x_582_ = v___x_577_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_579_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v___x_580_);
v___x_582_ = v_reuseFailAlloc_596_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_583_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3);
v___x_584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_582_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
v___x_585_ = l_Lean_indentExpr(v_a_542_);
v___x_586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_584_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
v___x_587_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__5);
v___x_588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_586_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
v___x_589_ = l_Lean_indentExpr(v_fst_574_);
v___x_590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_588_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__7, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__7);
v___x_592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_590_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
v___x_593_ = l_Lean_indentExpr(v_snd_575_);
v___x_594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_592_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
v___x_595_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v___x_594_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
return v___x_595_;
}
}
}
else
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
lean_dec_ref(v_e_543_);
lean_dec_ref(v_a_542_);
v_a_598_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_572_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_572_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
else
{
lean_object* v___x_606_; lean_object* v___x_608_; 
lean_dec(v_a_565_);
lean_dec(v_a_563_);
lean_dec_ref(v_e_543_);
lean_dec_ref(v_a_542_);
v___x_606_ = lean_box(0);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 0, v___x_606_);
v___x_608_ = v___x_569_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_606_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
else
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_618_; 
lean_dec(v_a_565_);
lean_dec(v_a_563_);
lean_dec_ref(v_e_543_);
lean_dec_ref(v_a_542_);
v_a_611_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_618_ == 0)
{
v___x_613_ = v___x_566_;
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_566_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_616_; 
if (v_isShared_614_ == 0)
{
v___x_616_ = v___x_613_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_a_611_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
else
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_626_; 
lean_dec(v_a_563_);
lean_dec_ref(v_e_543_);
lean_dec_ref(v_a_542_);
v_a_619_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_626_ == 0)
{
v___x_621_ = v___x_564_;
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___x_564_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_a_619_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
lean_dec_ref(v_e_543_);
lean_dec_ref(v_a_542_);
v_a_627_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_634_ == 0)
{
v___x_629_ = v___x_562_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_562_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_627_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___boxed(lean_object* v_a_654_, lean_object* v_e_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0(v_a_654_, v_e_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec(v___y_656_);
return v_res_665_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0(void){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_666_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0);
v___x_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
return v___x_668_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__2(void){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_669_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1);
v___x_670_ = lean_unsigned_to_nat(0u);
v___x_671_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
lean_ctor_set(v___x_671_, 2, v___x_670_);
lean_ctor_set(v___x_671_, 3, v___x_670_);
lean_ctor_set(v___x_671_, 4, v___x_669_);
lean_ctor_set(v___x_671_, 5, v___x_669_);
lean_ctor_set(v___x_671_, 6, v___x_669_);
lean_ctor_set(v___x_671_, 7, v___x_669_);
lean_ctor_set(v___x_671_, 8, v___x_669_);
lean_ctor_set(v___x_671_, 9, v___x_669_);
lean_ctor_set(v___x_671_, 10, v___x_669_);
return v___x_671_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__3(void){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_672_ = lean_unsigned_to_nat(32u);
v___x_673_ = lean_mk_empty_array_with_capacity(v___x_672_);
v___x_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
return v___x_674_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__4(void){
_start:
{
size_t v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_675_ = ((size_t)5ULL);
v___x_676_ = lean_unsigned_to_nat(0u);
v___x_677_ = lean_unsigned_to_nat(32u);
v___x_678_ = lean_mk_empty_array_with_capacity(v___x_677_);
v___x_679_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__3);
v___x_680_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_680_, 0, v___x_679_);
lean_ctor_set(v___x_680_, 1, v___x_678_);
lean_ctor_set(v___x_680_, 2, v___x_676_);
lean_ctor_set(v___x_680_, 3, v___x_676_);
lean_ctor_set_usize(v___x_680_, 4, v___x_675_);
return v___x_680_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__5(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_681_ = lean_box(1);
v___x_682_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__4);
v___x_683_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1);
v___x_684_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
lean_ctor_set(v___x_684_, 1, v___x_682_);
lean_ctor_set(v___x_684_, 2, v___x_681_);
return v___x_684_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7(void){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__6));
v___x_687_ = l_Lean_stringToMessageData(v___x_686_);
return v___x_687_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__9(void){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__8));
v___x_690_ = l_Lean_stringToMessageData(v___x_689_);
return v___x_690_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__11(void){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__10));
v___x_693_ = l_Lean_stringToMessageData(v___x_692_);
return v___x_693_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__13(void){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__12));
v___x_696_ = l_Lean_stringToMessageData(v___x_695_);
return v___x_696_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__15(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__14));
v___x_699_ = l_Lean_stringToMessageData(v___x_698_);
return v___x_699_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__17(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__16));
v___x_702_ = l_Lean_stringToMessageData(v___x_701_);
return v___x_702_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__19(void){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__18));
v___x_705_ = l_Lean_stringToMessageData(v___x_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(lean_object* v_msg_706_, lean_object* v_declHint_707_, lean_object* v___y_708_){
_start:
{
lean_object* v___x_710_; lean_object* v_env_711_; uint8_t v___x_712_; 
v___x_710_ = lean_st_ref_get(v___y_708_);
v_env_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc_ref(v_env_711_);
lean_dec(v___x_710_);
v___x_712_ = l_Lean_Name_isAnonymous(v_declHint_707_);
if (v___x_712_ == 0)
{
uint8_t v_isExporting_713_; 
v_isExporting_713_ = lean_ctor_get_uint8(v_env_711_, sizeof(void*)*8);
if (v_isExporting_713_ == 0)
{
lean_object* v___x_714_; 
lean_dec_ref(v_env_711_);
lean_dec(v_declHint_707_);
v___x_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_714_, 0, v_msg_706_);
return v___x_714_;
}
else
{
lean_object* v___x_715_; uint8_t v___x_716_; 
lean_inc_ref(v_env_711_);
v___x_715_ = l_Lean_Environment_setExporting(v_env_711_, v___x_712_);
lean_inc(v_declHint_707_);
lean_inc_ref(v___x_715_);
v___x_716_ = l_Lean_Environment_contains(v___x_715_, v_declHint_707_, v_isExporting_713_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; 
lean_dec_ref(v___x_715_);
lean_dec_ref(v_env_711_);
lean_dec(v_declHint_707_);
v___x_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_717_, 0, v_msg_706_);
return v___x_717_;
}
else
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v_c_723_; lean_object* v___x_724_; 
v___x_718_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__2);
v___x_719_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__5);
v___x_720_ = l_Lean_Options_empty;
v___x_721_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_721_, 0, v___x_715_);
lean_ctor_set(v___x_721_, 1, v___x_718_);
lean_ctor_set(v___x_721_, 2, v___x_719_);
lean_ctor_set(v___x_721_, 3, v___x_720_);
lean_inc(v_declHint_707_);
v___x_722_ = l_Lean_MessageData_ofConstName(v_declHint_707_, v___x_712_);
v_c_723_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_723_, 0, v___x_721_);
lean_ctor_set(v_c_723_, 1, v___x_722_);
v___x_724_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_711_, v_declHint_707_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
lean_dec_ref(v_env_711_);
lean_dec(v_declHint_707_);
v___x_725_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7);
v___x_726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
lean_ctor_set(v___x_726_, 1, v_c_723_);
v___x_727_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__9);
v___x_728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_726_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
v___x_729_ = l_Lean_MessageData_note(v___x_728_);
v___x_730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_730_, 0, v_msg_706_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v___x_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
return v___x_731_;
}
else
{
lean_object* v_val_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_767_; 
v_val_732_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_767_ == 0)
{
v___x_734_ = v___x_724_;
v_isShared_735_ = v_isSharedCheck_767_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_val_732_);
lean_dec(v___x_724_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_767_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v_mod_739_; uint8_t v___x_740_; 
v___x_736_ = lean_box(0);
v___x_737_ = l_Lean_Environment_header(v_env_711_);
lean_dec_ref(v_env_711_);
v___x_738_ = l_Lean_EnvironmentHeader_moduleNames(v___x_737_);
v_mod_739_ = lean_array_get(v___x_736_, v___x_738_, v_val_732_);
lean_dec(v_val_732_);
lean_dec_ref(v___x_738_);
v___x_740_ = l_Lean_isPrivateName(v_declHint_707_);
lean_dec(v_declHint_707_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_752_; 
v___x_741_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__11);
v___x_742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
lean_ctor_set(v___x_742_, 1, v_c_723_);
v___x_743_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__13);
v___x_744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_742_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
v___x_745_ = l_Lean_MessageData_ofName(v_mod_739_);
v___x_746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_744_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
v___x_747_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__15);
v___x_748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_746_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
v___x_749_ = l_Lean_MessageData_note(v___x_748_);
v___x_750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_750_, 0, v_msg_706_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
if (v_isShared_735_ == 0)
{
lean_ctor_set_tag(v___x_734_, 0);
lean_ctor_set(v___x_734_, 0, v___x_750_);
v___x_752_ = v___x_734_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_750_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
else
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_765_; 
v___x_754_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7);
v___x_755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
lean_ctor_set(v___x_755_, 1, v_c_723_);
v___x_756_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__17);
v___x_757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_755_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
v___x_758_ = l_Lean_MessageData_ofName(v_mod_739_);
v___x_759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_759_, 0, v___x_757_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
v___x_760_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__19);
v___x_761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_761_, 0, v___x_759_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
v___x_762_ = l_Lean_MessageData_note(v___x_761_);
v___x_763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_763_, 0, v_msg_706_);
lean_ctor_set(v___x_763_, 1, v___x_762_);
if (v_isShared_735_ == 0)
{
lean_ctor_set_tag(v___x_734_, 0);
lean_ctor_set(v___x_734_, 0, v___x_763_);
v___x_765_ = v___x_734_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v___x_763_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_768_; 
lean_dec_ref(v_env_711_);
lean_dec(v_declHint_707_);
v___x_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_768_, 0, v_msg_706_);
return v___x_768_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___boxed(lean_object* v_msg_769_, lean_object* v_declHint_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(v_msg_769_, v_declHint_770_, v___y_771_);
lean_dec(v___y_771_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30(lean_object* v_msg_774_, lean_object* v_declHint_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v___x_785_; lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_795_; 
v___x_785_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(v_msg_774_, v_declHint_775_, v___y_783_);
v_a_786_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_795_ == 0)
{
v___x_788_ = v___x_785_;
v_isShared_789_ = v_isSharedCheck_795_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_785_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_795_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_793_; 
v___x_790_ = l_Lean_unknownIdentifierMessageTag;
v___x_791_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
lean_ctor_set(v___x_791_, 1, v_a_786_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v___x_791_);
v___x_793_ = v___x_788_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_791_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30___boxed(lean_object* v_msg_796_, lean_object* v_declHint_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30(v_msg_796_, v_declHint_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec(v___y_798_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(lean_object* v_ref_808_, lean_object* v_msg_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v_toCold_819_; lean_object* v_options_820_; lean_object* v_currRecDepth_821_; lean_object* v_maxRecDepth_822_; lean_object* v_ref_823_; lean_object* v_currNamespace_824_; lean_object* v_openDecls_825_; lean_object* v_initHeartbeats_826_; lean_object* v_maxHeartbeats_827_; lean_object* v_currMacroScope_828_; uint8_t v_diag_829_; uint8_t v_suppressElabErrors_830_; lean_object* v_ref_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v_toCold_819_ = lean_ctor_get(v___y_816_, 0);
v_options_820_ = lean_ctor_get(v___y_816_, 1);
v_currRecDepth_821_ = lean_ctor_get(v___y_816_, 2);
v_maxRecDepth_822_ = lean_ctor_get(v___y_816_, 3);
v_ref_823_ = lean_ctor_get(v___y_816_, 4);
v_currNamespace_824_ = lean_ctor_get(v___y_816_, 5);
v_openDecls_825_ = lean_ctor_get(v___y_816_, 6);
v_initHeartbeats_826_ = lean_ctor_get(v___y_816_, 7);
v_maxHeartbeats_827_ = lean_ctor_get(v___y_816_, 8);
v_currMacroScope_828_ = lean_ctor_get(v___y_816_, 9);
v_diag_829_ = lean_ctor_get_uint8(v___y_816_, sizeof(void*)*10);
v_suppressElabErrors_830_ = lean_ctor_get_uint8(v___y_816_, sizeof(void*)*10 + 1);
v_ref_831_ = l_Lean_replaceRef(v_ref_808_, v_ref_823_);
lean_inc(v_currMacroScope_828_);
lean_inc(v_maxHeartbeats_827_);
lean_inc(v_initHeartbeats_826_);
lean_inc(v_openDecls_825_);
lean_inc(v_currNamespace_824_);
lean_inc(v_maxRecDepth_822_);
lean_inc(v_currRecDepth_821_);
lean_inc_ref(v_options_820_);
lean_inc_ref(v_toCold_819_);
v___x_832_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_832_, 0, v_toCold_819_);
lean_ctor_set(v___x_832_, 1, v_options_820_);
lean_ctor_set(v___x_832_, 2, v_currRecDepth_821_);
lean_ctor_set(v___x_832_, 3, v_maxRecDepth_822_);
lean_ctor_set(v___x_832_, 4, v_ref_831_);
lean_ctor_set(v___x_832_, 5, v_currNamespace_824_);
lean_ctor_set(v___x_832_, 6, v_openDecls_825_);
lean_ctor_set(v___x_832_, 7, v_initHeartbeats_826_);
lean_ctor_set(v___x_832_, 8, v_maxHeartbeats_827_);
lean_ctor_set(v___x_832_, 9, v_currMacroScope_828_);
lean_ctor_set_uint8(v___x_832_, sizeof(void*)*10, v_diag_829_);
lean_ctor_set_uint8(v___x_832_, sizeof(void*)*10 + 1, v_suppressElabErrors_830_);
v___x_833_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v_msg_809_, v___y_814_, v___y_815_, v___x_832_, v___y_817_);
lean_dec_ref_known(v___x_832_, 10);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg___boxed(lean_object* v_ref_834_, lean_object* v_msg_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(v_ref_834_, v_msg_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
lean_dec(v___y_836_);
lean_dec(v_ref_834_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(lean_object* v_ref_846_, lean_object* v_msg_847_, lean_object* v_declHint_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v___x_858_; lean_object* v_a_859_; lean_object* v___x_860_; 
v___x_858_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30(v_msg_847_, v_declHint_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
v_a_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_a_859_);
lean_dec_ref(v___x_858_);
v___x_860_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(v_ref_846_, v_a_859_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg___boxed(lean_object* v_ref_861_, lean_object* v_msg_862_, lean_object* v_declHint_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(v_ref_861_, v_msg_862_, v_declHint_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec(v___y_864_);
lean_dec(v_ref_861_);
return v_res_873_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__0));
v___x_876_ = l_Lean_stringToMessageData(v___x_875_);
return v___x_876_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3(void){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__2));
v___x_879_ = l_Lean_stringToMessageData(v___x_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(lean_object* v_ref_880_, lean_object* v_constName_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v___x_891_; uint8_t v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_891_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1);
v___x_892_ = 0;
lean_inc(v_constName_881_);
v___x_893_ = l_Lean_MessageData_ofConstName(v_constName_881_, v___x_892_);
v___x_894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_891_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
v___x_895_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3);
v___x_896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_894_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v___x_897_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(v_ref_880_, v___x_896_, v_constName_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___boxed(lean_object* v_ref_898_, lean_object* v_constName_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(v_ref_898_, v_constName_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec(v___y_900_);
lean_dec(v_ref_898_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(lean_object* v_constName_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v_ref_920_; lean_object* v___x_921_; 
v_ref_920_ = lean_ctor_get(v___y_917_, 4);
v___x_921_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(v_ref_920_, v_constName_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg___boxed(lean_object* v_constName_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(v_constName_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec(v___y_923_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(lean_object* v_constName_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v___x_943_; lean_object* v_env_944_; uint8_t v___x_945_; lean_object* v___x_946_; 
v___x_943_ = lean_st_ref_get(v___y_941_);
v_env_944_ = lean_ctor_get(v___x_943_, 0);
lean_inc_ref(v_env_944_);
lean_dec(v___x_943_);
v___x_945_ = 0;
lean_inc(v_constName_933_);
v___x_946_ = l_Lean_Environment_find_x3f(v_env_944_, v_constName_933_, v___x_945_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v___x_947_; 
v___x_947_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(v_constName_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
return v___x_947_;
}
else
{
lean_object* v_val_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
lean_dec(v_constName_933_);
v_val_948_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_946_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_val_948_);
lean_dec(v___x_946_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
lean_ctor_set_tag(v___x_950_, 0);
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_val_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18___boxed(lean_object* v_constName_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(v_constName_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec(v___y_957_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(lean_object* v_declName_967_, lean_object* v___y_968_){
_start:
{
lean_object* v___x_970_; lean_object* v_env_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_970_ = lean_st_ref_get(v___y_968_);
v_env_971_ = lean_ctor_get(v___x_970_, 0);
lean_inc_ref(v_env_971_);
lean_dec(v___x_970_);
v___x_972_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_971_, v_declName_967_);
v___x_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg___boxed(lean_object* v_declName_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(v_declName_974_, v___y_975_);
lean_dec(v___y_975_);
return v_res_977_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0(void){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l_instMonadEIO(lean_box(0));
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19(lean_object* v_msg_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v_toApplicative_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1090_; 
v___x_995_ = lean_obj_once(&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0, &l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0_once, _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0);
v___x_996_ = l_StateRefT_x27_instMonad___redArg(v___x_995_);
v_toApplicative_997_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1090_ == 0)
{
lean_object* v_unused_1091_; 
v_unused_1091_ = lean_ctor_get(v___x_996_, 1);
lean_dec(v_unused_1091_);
v___x_999_ = v___x_996_;
v_isShared_1000_ = v_isSharedCheck_1090_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_toApplicative_997_);
lean_dec(v___x_996_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1090_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v_toFunctor_1001_; lean_object* v_toSeq_1002_; lean_object* v_toSeqLeft_1003_; lean_object* v_toSeqRight_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1088_; 
v_toFunctor_1001_ = lean_ctor_get(v_toApplicative_997_, 0);
v_toSeq_1002_ = lean_ctor_get(v_toApplicative_997_, 2);
v_toSeqLeft_1003_ = lean_ctor_get(v_toApplicative_997_, 3);
v_toSeqRight_1004_ = lean_ctor_get(v_toApplicative_997_, 4);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_toApplicative_997_);
if (v_isSharedCheck_1088_ == 0)
{
lean_object* v_unused_1089_; 
v_unused_1089_ = lean_ctor_get(v_toApplicative_997_, 1);
lean_dec(v_unused_1089_);
v___x_1006_ = v_toApplicative_997_;
v_isShared_1007_ = v_isSharedCheck_1088_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_toSeqRight_1004_);
lean_inc(v_toSeqLeft_1003_);
lean_inc(v_toSeq_1002_);
lean_inc(v_toFunctor_1001_);
lean_dec(v_toApplicative_997_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1088_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___f_1008_; lean_object* v___f_1009_; lean_object* v___f_1010_; lean_object* v___f_1011_; lean_object* v___x_1012_; lean_object* v___f_1013_; lean_object* v___f_1014_; lean_object* v___f_1015_; lean_object* v___x_1017_; 
v___f_1008_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__1));
v___f_1009_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__2));
lean_inc_ref(v_toFunctor_1001_);
v___f_1010_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1010_, 0, v_toFunctor_1001_);
v___f_1011_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1011_, 0, v_toFunctor_1001_);
v___x_1012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___f_1010_);
lean_ctor_set(v___x_1012_, 1, v___f_1011_);
v___f_1013_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1013_, 0, v_toSeqRight_1004_);
v___f_1014_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1014_, 0, v_toSeqLeft_1003_);
v___f_1015_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1015_, 0, v_toSeq_1002_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 4, v___f_1013_);
lean_ctor_set(v___x_1006_, 3, v___f_1014_);
lean_ctor_set(v___x_1006_, 2, v___f_1015_);
lean_ctor_set(v___x_1006_, 1, v___f_1008_);
lean_ctor_set(v___x_1006_, 0, v___x_1012_);
v___x_1017_ = v___x_1006_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1012_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v___f_1008_);
lean_ctor_set(v_reuseFailAlloc_1087_, 2, v___f_1015_);
lean_ctor_set(v_reuseFailAlloc_1087_, 3, v___f_1014_);
lean_ctor_set(v_reuseFailAlloc_1087_, 4, v___f_1013_);
v___x_1017_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1019_; 
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 1, v___f_1009_);
lean_ctor_set(v___x_999_, 0, v___x_1017_);
v___x_1019_ = v___x_999_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1017_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v___f_1009_);
v___x_1019_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
lean_object* v___x_1020_; lean_object* v_toApplicative_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1084_; 
v___x_1020_ = l_StateRefT_x27_instMonad___redArg(v___x_1019_);
v_toApplicative_1021_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1084_ == 0)
{
lean_object* v_unused_1085_; 
v_unused_1085_ = lean_ctor_get(v___x_1020_, 1);
lean_dec(v_unused_1085_);
v___x_1023_ = v___x_1020_;
v_isShared_1024_ = v_isSharedCheck_1084_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_toApplicative_1021_);
lean_dec(v___x_1020_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1084_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v_toFunctor_1025_; lean_object* v_toSeq_1026_; lean_object* v_toSeqLeft_1027_; lean_object* v_toSeqRight_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1082_; 
v_toFunctor_1025_ = lean_ctor_get(v_toApplicative_1021_, 0);
v_toSeq_1026_ = lean_ctor_get(v_toApplicative_1021_, 2);
v_toSeqLeft_1027_ = lean_ctor_get(v_toApplicative_1021_, 3);
v_toSeqRight_1028_ = lean_ctor_get(v_toApplicative_1021_, 4);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_toApplicative_1021_);
if (v_isSharedCheck_1082_ == 0)
{
lean_object* v_unused_1083_; 
v_unused_1083_ = lean_ctor_get(v_toApplicative_1021_, 1);
lean_dec(v_unused_1083_);
v___x_1030_ = v_toApplicative_1021_;
v_isShared_1031_ = v_isSharedCheck_1082_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_toSeqRight_1028_);
lean_inc(v_toSeqLeft_1027_);
lean_inc(v_toSeq_1026_);
lean_inc(v_toFunctor_1025_);
lean_dec(v_toApplicative_1021_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1082_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___f_1032_; lean_object* v___f_1033_; lean_object* v___f_1034_; lean_object* v___f_1035_; lean_object* v___x_1036_; lean_object* v___f_1037_; lean_object* v___f_1038_; lean_object* v___f_1039_; lean_object* v___x_1041_; 
v___f_1032_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__3));
v___f_1033_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__4));
lean_inc_ref(v_toFunctor_1025_);
v___f_1034_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1034_, 0, v_toFunctor_1025_);
v___f_1035_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1035_, 0, v_toFunctor_1025_);
v___x_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___f_1034_);
lean_ctor_set(v___x_1036_, 1, v___f_1035_);
v___f_1037_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1037_, 0, v_toSeqRight_1028_);
v___f_1038_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1038_, 0, v_toSeqLeft_1027_);
v___f_1039_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1039_, 0, v_toSeq_1026_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 4, v___f_1037_);
lean_ctor_set(v___x_1030_, 3, v___f_1038_);
lean_ctor_set(v___x_1030_, 2, v___f_1039_);
lean_ctor_set(v___x_1030_, 1, v___f_1032_);
lean_ctor_set(v___x_1030_, 0, v___x_1036_);
v___x_1041_ = v___x_1030_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v___f_1032_);
lean_ctor_set(v_reuseFailAlloc_1081_, 2, v___f_1039_);
lean_ctor_set(v_reuseFailAlloc_1081_, 3, v___f_1038_);
lean_ctor_set(v_reuseFailAlloc_1081_, 4, v___f_1037_);
v___x_1041_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1043_; 
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 1, v___f_1033_);
lean_ctor_set(v___x_1023_, 0, v___x_1041_);
v___x_1043_ = v___x_1023_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1041_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v___f_1033_);
v___x_1043_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
lean_object* v___x_1044_; lean_object* v_toApplicative_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1078_; 
v___x_1044_ = l_StateRefT_x27_instMonad___redArg(v___x_1043_);
v_toApplicative_1045_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1078_ == 0)
{
lean_object* v_unused_1079_; 
v_unused_1079_ = lean_ctor_get(v___x_1044_, 1);
lean_dec(v_unused_1079_);
v___x_1047_ = v___x_1044_;
v_isShared_1048_ = v_isSharedCheck_1078_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_toApplicative_1045_);
lean_dec(v___x_1044_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1078_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v_toFunctor_1049_; lean_object* v_toSeq_1050_; lean_object* v_toSeqLeft_1051_; lean_object* v_toSeqRight_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1076_; 
v_toFunctor_1049_ = lean_ctor_get(v_toApplicative_1045_, 0);
v_toSeq_1050_ = lean_ctor_get(v_toApplicative_1045_, 2);
v_toSeqLeft_1051_ = lean_ctor_get(v_toApplicative_1045_, 3);
v_toSeqRight_1052_ = lean_ctor_get(v_toApplicative_1045_, 4);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_toApplicative_1045_);
if (v_isSharedCheck_1076_ == 0)
{
lean_object* v_unused_1077_; 
v_unused_1077_ = lean_ctor_get(v_toApplicative_1045_, 1);
lean_dec(v_unused_1077_);
v___x_1054_ = v_toApplicative_1045_;
v_isShared_1055_ = v_isSharedCheck_1076_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_toSeqRight_1052_);
lean_inc(v_toSeqLeft_1051_);
lean_inc(v_toSeq_1050_);
lean_inc(v_toFunctor_1049_);
lean_dec(v_toApplicative_1045_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1076_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___f_1056_; lean_object* v___f_1057_; lean_object* v___f_1058_; lean_object* v___f_1059_; lean_object* v___x_1060_; lean_object* v___f_1061_; lean_object* v___f_1062_; lean_object* v___f_1063_; lean_object* v___x_1065_; 
v___f_1056_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__5));
v___f_1057_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__6));
lean_inc_ref(v_toFunctor_1049_);
v___f_1058_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1058_, 0, v_toFunctor_1049_);
v___f_1059_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1059_, 0, v_toFunctor_1049_);
v___x_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___f_1058_);
lean_ctor_set(v___x_1060_, 1, v___f_1059_);
v___f_1061_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1061_, 0, v_toSeqRight_1052_);
v___f_1062_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1062_, 0, v_toSeqLeft_1051_);
v___f_1063_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1063_, 0, v_toSeq_1050_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 4, v___f_1061_);
lean_ctor_set(v___x_1054_, 3, v___f_1062_);
lean_ctor_set(v___x_1054_, 2, v___f_1063_);
lean_ctor_set(v___x_1054_, 1, v___f_1056_);
lean_ctor_set(v___x_1054_, 0, v___x_1060_);
v___x_1065_ = v___x_1054_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1060_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v___f_1056_);
lean_ctor_set(v_reuseFailAlloc_1075_, 2, v___f_1063_);
lean_ctor_set(v_reuseFailAlloc_1075_, 3, v___f_1062_);
lean_ctor_set(v_reuseFailAlloc_1075_, 4, v___f_1061_);
v___x_1065_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
lean_object* v___x_1067_; 
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 1, v___f_1057_);
lean_ctor_set(v___x_1047_, 0, v___x_1065_);
v___x_1067_ = v___x_1047_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1065_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v___f_1057_);
v___x_1067_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_49991__overap_1072_; lean_object* v___x_1073_; 
v___x_1068_ = l_StateRefT_x27_instMonad___redArg(v___x_1067_);
v___x_1069_ = l_StateRefT_x27_instMonad___redArg(v___x_1068_);
v___x_1070_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_1071_ = l_instInhabitedOfMonad___redArg(v___x_1069_, v___x_1070_);
v___x_49991__overap_1072_ = lean_panic_fn_borrowed(v___x_1071_, v_msg_985_);
lean_dec(v___x_1071_);
lean_inc(v___y_993_);
lean_inc_ref(v___y_992_);
lean_inc(v___y_991_);
lean_inc_ref(v___y_990_);
lean_inc(v___y_989_);
lean_inc_ref(v___y_988_);
lean_inc(v___y_987_);
lean_inc(v___y_986_);
v___x_1073_ = lean_apply_9(v___x_49991__overap_1072_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, lean_box(0));
return v___x_1073_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___boxed(lean_object* v_msg_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19(v_msg_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec(v___y_1093_);
return v_res_1102_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3(void){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1106_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__2));
v___x_1107_ = lean_unsigned_to_nat(53u);
v___x_1108_ = lean_unsigned_to_nat(62u);
v___x_1109_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__1));
v___x_1110_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__0));
v___x_1111_ = l_mkPanicMessageWithDecl(v___x_1110_, v___x_1109_, v___x_1108_, v___x_1107_, v___x_1106_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21(size_t v_sz_1112_, size_t v_i_1113_, lean_object* v_bs_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
uint8_t v___x_1124_; 
v___x_1124_ = lean_usize_dec_lt(v_i_1113_, v_sz_1112_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; 
v___x_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1125_, 0, v_bs_1114_);
return v___x_1125_;
}
else
{
lean_object* v_v_1126_; lean_object* v___x_1127_; 
v_v_1126_ = lean_array_uget_borrowed(v_bs_1114_, v_i_1113_);
lean_inc(v_v_1126_);
v___x_1127_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(v_v_1126_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; lean_object* v___x_1129_; lean_object* v_bs_x27_1130_; lean_object* v_a_1132_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_a_1128_);
lean_dec_ref_known(v___x_1127_, 1);
v___x_1129_ = lean_unsigned_to_nat(0u);
v_bs_x27_1130_ = lean_array_uset(v_bs_1114_, v_i_1113_, v___x_1129_);
if (lean_obj_tag(v_a_1128_) == 6)
{
lean_object* v_val_1137_; lean_object* v_numFields_1138_; uint8_t v___x_1139_; lean_object* v___x_1140_; 
v_val_1137_ = lean_ctor_get(v_a_1128_, 0);
lean_inc_ref(v_val_1137_);
lean_dec_ref_known(v_a_1128_, 1);
v_numFields_1138_ = lean_ctor_get(v_val_1137_, 4);
lean_inc(v_numFields_1138_);
lean_dec_ref(v_val_1137_);
v___x_1139_ = 0;
v___x_1140_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1140_, 0, v_numFields_1138_);
lean_ctor_set(v___x_1140_, 1, v___x_1129_);
lean_ctor_set_uint8(v___x_1140_, sizeof(void*)*2, v___x_1139_);
v_a_1132_ = v___x_1140_;
goto v___jp_1131_;
}
else
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
lean_dec(v_a_1128_);
v___x_1141_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3);
v___x_1142_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19(v___x_1141_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc(v_a_1143_);
lean_dec_ref_known(v___x_1142_, 1);
v_a_1132_ = v_a_1143_;
goto v___jp_1131_;
}
else
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
lean_dec_ref(v_bs_x27_1130_);
v_a_1144_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1146_ = v___x_1142_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1142_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1147_ == 0)
{
v___x_1149_ = v___x_1146_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1144_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
v___jp_1131_:
{
size_t v___x_1133_; size_t v___x_1134_; lean_object* v___x_1135_; 
v___x_1133_ = ((size_t)1ULL);
v___x_1134_ = lean_usize_add(v_i_1113_, v___x_1133_);
v___x_1135_ = lean_array_uset(v_bs_x27_1130_, v_i_1113_, v_a_1132_);
v_i_1113_ = v___x_1134_;
v_bs_1114_ = v___x_1135_;
goto _start;
}
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
lean_dec_ref(v_bs_1114_);
v_a_1152_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1127_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1127_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___boxed(lean_object* v_sz_1160_, lean_object* v_i_1161_, lean_object* v_bs_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
size_t v_sz_boxed_1172_; size_t v_i_boxed_1173_; lean_object* v_res_1174_; 
v_sz_boxed_1172_ = lean_unbox_usize(v_sz_1160_);
lean_dec(v_sz_1160_);
v_i_boxed_1173_ = lean_unbox_usize(v_i_1161_);
lean_dec(v_i_1161_);
v_res_1174_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21(v_sz_boxed_1172_, v_i_boxed_1173_, v_bs_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec(v___y_1163_);
return v_res_1174_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0(void){
_start:
{
lean_object* v___x_1175_; lean_object* v_dummy_1176_; 
v___x_1175_ = lean_box(0);
v_dummy_1176_ = l_Lean_Expr_sort___override(v___x_1175_);
return v_dummy_1176_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1(void){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1177_ = lean_box(0);
v___x_1178_ = lean_unsigned_to_nat(16u);
v___x_1179_ = lean_mk_array(v___x_1178_, v___x_1177_);
return v___x_1179_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2(void){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1180_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1);
v___x_1181_ = lean_unsigned_to_nat(0u);
v___x_1182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1181_);
lean_ctor_set(v___x_1182_, 1, v___x_1180_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(lean_object* v_e_1185_, uint8_t v_alsoCasesOn_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
uint8_t v___x_1199_; 
v___x_1199_ = l_Lean_Expr_isApp(v_e_1185_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
lean_dec_ref(v_e_1185_);
v___x_1200_ = lean_box(0);
v___x_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1200_);
return v___x_1201_;
}
else
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Lean_Expr_getAppFn(v_e_1185_);
if (lean_obj_tag(v___x_1202_) == 4)
{
lean_object* v_declName_1203_; lean_object* v_us_1204_; lean_object* v___x_1205_; lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1359_; 
v_declName_1203_ = lean_ctor_get(v___x_1202_, 0);
lean_inc_n(v_declName_1203_, 2);
v_us_1204_ = lean_ctor_get(v___x_1202_, 1);
lean_inc(v_us_1204_);
lean_dec_ref_known(v___x_1202_, 2);
v___x_1205_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(v_declName_1203_, v___y_1194_);
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1208_ = v___x_1205_;
v_isShared_1209_ = v_isSharedCheck_1359_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1205_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1359_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Lean_instInhabitedExpr;
if (lean_obj_tag(v_a_1206_) == 1)
{
lean_object* v_val_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1252_; 
v_val_1211_ = lean_ctor_get(v_a_1206_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v_a_1206_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1213_ = v_a_1206_;
v_isShared_1214_ = v_isSharedCheck_1252_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_val_1211_);
lean_dec(v_a_1206_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1252_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v_dummy_1215_; lean_object* v_nargs_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v_args_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; uint8_t v___x_1223_; 
v_dummy_1215_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
v_nargs_1216_ = l_Lean_Expr_getAppNumArgs(v_e_1185_);
lean_inc(v_nargs_1216_);
v___x_1217_ = lean_mk_array(v_nargs_1216_, v_dummy_1215_);
v___x_1218_ = lean_unsigned_to_nat(1u);
v___x_1219_ = lean_nat_sub(v_nargs_1216_, v___x_1218_);
lean_dec(v_nargs_1216_);
v_args_1220_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1185_, v___x_1217_, v___x_1219_);
v___x_1221_ = lean_array_get_size(v_args_1220_);
v___x_1222_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_1211_);
v___x_1223_ = lean_nat_dec_lt(v___x_1221_, v___x_1222_);
lean_dec(v___x_1222_);
if (v___x_1223_ == 0)
{
lean_object* v_numParams_1224_; lean_object* v_numDiscrs_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1243_; 
v_numParams_1224_ = lean_ctor_get(v_val_1211_, 0);
v_numDiscrs_1225_ = lean_ctor_get(v_val_1211_, 1);
v___x_1226_ = lean_array_mk(v_us_1204_);
v___x_1227_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1224_);
v___x_1228_ = l_Array_extract___redArg(v_args_1220_, v___x_1227_, v_numParams_1224_);
v___x_1229_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_1211_);
v___x_1230_ = lean_array_get(v___x_1210_, v_args_1220_, v___x_1229_);
lean_dec(v___x_1229_);
v___x_1231_ = lean_nat_add(v_numParams_1224_, v___x_1218_);
v___x_1232_ = lean_nat_add(v___x_1231_, v_numDiscrs_1225_);
lean_inc(v___x_1232_);
lean_inc_ref_n(v_args_1220_, 2);
v___x_1233_ = l_Array_toSubarray___redArg(v_args_1220_, v___x_1231_, v___x_1232_);
v___x_1234_ = l_Subarray_copy___redArg(v___x_1233_);
v___x_1235_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1211_);
v___x_1236_ = lean_nat_add(v___x_1232_, v___x_1235_);
lean_dec(v___x_1235_);
lean_inc(v___x_1236_);
v___x_1237_ = l_Array_toSubarray___redArg(v_args_1220_, v___x_1232_, v___x_1236_);
v___x_1238_ = l_Subarray_copy___redArg(v___x_1237_);
v___x_1239_ = l_Array_toSubarray___redArg(v_args_1220_, v___x_1236_, v___x_1221_);
v___x_1240_ = l_Subarray_copy___redArg(v___x_1239_);
v___x_1241_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1241_, 0, v_val_1211_);
lean_ctor_set(v___x_1241_, 1, v_declName_1203_);
lean_ctor_set(v___x_1241_, 2, v___x_1226_);
lean_ctor_set(v___x_1241_, 3, v___x_1228_);
lean_ctor_set(v___x_1241_, 4, v___x_1230_);
lean_ctor_set(v___x_1241_, 5, v___x_1234_);
lean_ctor_set(v___x_1241_, 6, v___x_1238_);
lean_ctor_set(v___x_1241_, 7, v___x_1240_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v___x_1241_);
v___x_1243_ = v___x_1213_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v___x_1241_);
v___x_1243_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
lean_object* v___x_1245_; 
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v___x_1243_);
v___x_1245_ = v___x_1208_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v___x_1243_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
else
{
lean_object* v___x_1248_; lean_object* v___x_1250_; 
lean_dec_ref(v_args_1220_);
lean_del_object(v___x_1213_);
lean_dec(v_val_1211_);
lean_dec(v_us_1204_);
lean_dec(v_declName_1203_);
v___x_1248_ = lean_box(0);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v___x_1248_);
v___x_1250_ = v___x_1208_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1248_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
else
{
lean_object* v___x_1253_; 
lean_del_object(v___x_1208_);
lean_dec(v_a_1206_);
v___x_1253_ = lean_st_ref_get(v___y_1194_);
if (v_alsoCasesOn_1186_ == 0)
{
lean_dec(v___x_1253_);
lean_dec(v_us_1204_);
lean_dec(v_declName_1203_);
lean_dec_ref(v_e_1185_);
goto v___jp_1196_;
}
else
{
lean_object* v_env_1254_; uint8_t v___x_1255_; 
v_env_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc_ref(v_env_1254_);
lean_dec(v___x_1253_);
lean_inc(v_declName_1203_);
v___x_1255_ = l_Lean_isCasesOnRecursor(v_env_1254_, v_declName_1203_);
if (v___x_1255_ == 0)
{
lean_dec(v_us_1204_);
lean_dec(v_declName_1203_);
lean_dec_ref(v_e_1185_);
goto v___jp_1196_;
}
else
{
lean_object* v_indName_1256_; lean_object* v___x_1257_; 
v_indName_1256_ = l_Lean_Name_getPrefix(v_declName_1203_);
v___x_1257_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(v_indName_1256_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1350_; 
v_a_1258_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1260_ = v___x_1257_;
v_isShared_1261_ = v_isSharedCheck_1350_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1257_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1350_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
if (lean_obj_tag(v_a_1258_) == 5)
{
lean_object* v_val_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1345_; 
v_val_1262_ = lean_ctor_get(v_a_1258_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v_a_1258_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1264_ = v_a_1258_;
v_isShared_1265_ = v_isSharedCheck_1345_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_val_1262_);
lean_dec(v_a_1258_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1345_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v_toConstantVal_1266_; lean_object* v_numParams_1267_; lean_object* v_numIndices_1268_; lean_object* v_ctors_1269_; lean_object* v_nargs_1270_; lean_object* v_dummy_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v_args_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; 
v_toConstantVal_1266_ = lean_ctor_get(v_val_1262_, 0);
lean_inc_ref(v_toConstantVal_1266_);
v_numParams_1267_ = lean_ctor_get(v_val_1262_, 1);
lean_inc(v_numParams_1267_);
v_numIndices_1268_ = lean_ctor_get(v_val_1262_, 2);
lean_inc(v_numIndices_1268_);
v_ctors_1269_ = lean_ctor_get(v_val_1262_, 4);
lean_inc(v_ctors_1269_);
v_nargs_1270_ = l_Lean_Expr_getAppNumArgs(v_e_1185_);
v_dummy_1271_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v_nargs_1270_);
v___x_1272_ = lean_mk_array(v_nargs_1270_, v_dummy_1271_);
v___x_1273_ = lean_unsigned_to_nat(1u);
v___x_1274_ = lean_nat_sub(v_nargs_1270_, v___x_1273_);
lean_dec(v_nargs_1270_);
v_args_1275_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1185_, v___x_1272_, v___x_1274_);
v___x_1276_ = lean_nat_add(v_numParams_1267_, v___x_1273_);
v___x_1277_ = lean_nat_add(v___x_1276_, v_numIndices_1268_);
v___x_1278_ = lean_nat_add(v___x_1277_, v___x_1273_);
lean_dec(v___x_1277_);
v___x_1279_ = l_Lean_InductiveVal_numCtors(v_val_1262_);
lean_dec_ref(v_val_1262_);
v___x_1280_ = lean_nat_add(v___x_1278_, v___x_1279_);
lean_dec(v___x_1279_);
v___x_1281_ = lean_array_get_size(v_args_1275_);
v___x_1282_ = lean_nat_dec_le(v___x_1280_, v___x_1281_);
if (v___x_1282_ == 0)
{
lean_object* v___x_1283_; lean_object* v___x_1285_; 
lean_dec(v___x_1280_);
lean_dec(v___x_1278_);
lean_dec(v___x_1276_);
lean_dec_ref(v_args_1275_);
lean_dec(v_ctors_1269_);
lean_dec(v_numIndices_1268_);
lean_dec(v_numParams_1267_);
lean_dec_ref(v_toConstantVal_1266_);
lean_del_object(v___x_1264_);
lean_dec(v_us_1204_);
lean_dec(v_declName_1203_);
v___x_1283_ = lean_box(0);
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 0, v___x_1283_);
v___x_1285_ = v___x_1260_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1283_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
else
{
lean_object* v___x_1287_; lean_object* v_params_1288_; lean_object* v_motive_1289_; lean_object* v_discrs_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v_discrInfos_1293_; lean_object* v_alts_1294_; lean_object* v___y_1296_; lean_object* v___y_1297_; lean_object* v_lower_1336_; lean_object* v_upper_1337_; uint8_t v___x_1344_; 
lean_del_object(v___x_1260_);
v___x_1287_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1267_);
lean_inc_ref_n(v_args_1275_, 3);
v_params_1288_ = l_Array_toSubarray___redArg(v_args_1275_, v___x_1287_, v_numParams_1267_);
v_motive_1289_ = lean_array_get(v___x_1210_, v_args_1275_, v_numParams_1267_);
lean_dec(v_numParams_1267_);
lean_inc(v___x_1278_);
v_discrs_1290_ = l_Array_toSubarray___redArg(v_args_1275_, v___x_1276_, v___x_1278_);
v___x_1291_ = lean_nat_add(v_numIndices_1268_, v___x_1273_);
lean_dec(v_numIndices_1268_);
v___x_1292_ = lean_box(0);
v_discrInfos_1293_ = lean_mk_array(v___x_1291_, v___x_1292_);
lean_inc(v___x_1280_);
v_alts_1294_ = l_Array_toSubarray___redArg(v_args_1275_, v___x_1278_, v___x_1280_);
v___x_1344_ = lean_nat_dec_le(v___x_1280_, v___x_1287_);
if (v___x_1344_ == 0)
{
v_lower_1336_ = v___x_1280_;
v_upper_1337_ = v___x_1281_;
goto v___jp_1335_;
}
else
{
lean_dec(v___x_1280_);
v_lower_1336_ = v___x_1287_;
v_upper_1337_ = v___x_1281_;
goto v___jp_1335_;
}
v___jp_1295_:
{
lean_object* v___x_1298_; size_t v_sz_1299_; size_t v___x_1300_; lean_object* v___x_1301_; 
v___x_1298_ = lean_array_mk(v_ctors_1269_);
v_sz_1299_ = lean_array_size(v___x_1298_);
v___x_1300_ = ((size_t)0ULL);
v___x_1301_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21(v_sz_1299_, v___x_1300_, v___x_1298_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1326_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1304_ = v___x_1301_;
v_isShared_1305_ = v_isSharedCheck_1326_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1301_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1326_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v_start_1306_; lean_object* v_stop_1307_; lean_object* v_start_1308_; lean_object* v_stop_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1321_; 
v_start_1306_ = lean_ctor_get(v_params_1288_, 1);
lean_inc(v_start_1306_);
v_stop_1307_ = lean_ctor_get(v_params_1288_, 2);
lean_inc(v_stop_1307_);
v_start_1308_ = lean_ctor_get(v_discrs_1290_, 1);
lean_inc(v_start_1308_);
v_stop_1309_ = lean_ctor_get(v_discrs_1290_, 2);
lean_inc(v_stop_1309_);
v___x_1310_ = lean_nat_sub(v_stop_1307_, v_start_1306_);
lean_dec(v_start_1306_);
lean_dec(v_stop_1307_);
v___x_1311_ = lean_nat_sub(v_stop_1309_, v_start_1308_);
lean_dec(v_start_1308_);
lean_dec(v_stop_1309_);
v___x_1312_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2);
v___x_1313_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1310_);
lean_ctor_set(v___x_1313_, 1, v___x_1311_);
lean_ctor_set(v___x_1313_, 2, v_a_1302_);
lean_ctor_set(v___x_1313_, 3, v___y_1297_);
lean_ctor_set(v___x_1313_, 4, v_discrInfos_1293_);
lean_ctor_set(v___x_1313_, 5, v___x_1312_);
v___x_1314_ = lean_array_mk(v_us_1204_);
v___x_1315_ = l_Subarray_copy___redArg(v_params_1288_);
v___x_1316_ = l_Subarray_copy___redArg(v_discrs_1290_);
v___x_1317_ = l_Subarray_copy___redArg(v_alts_1294_);
v___x_1318_ = l_Subarray_copy___redArg(v___y_1296_);
v___x_1319_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1313_);
lean_ctor_set(v___x_1319_, 1, v_declName_1203_);
lean_ctor_set(v___x_1319_, 2, v___x_1314_);
lean_ctor_set(v___x_1319_, 3, v___x_1315_);
lean_ctor_set(v___x_1319_, 4, v_motive_1289_);
lean_ctor_set(v___x_1319_, 5, v___x_1316_);
lean_ctor_set(v___x_1319_, 6, v___x_1317_);
lean_ctor_set(v___x_1319_, 7, v___x_1318_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set_tag(v___x_1264_, 1);
lean_ctor_set(v___x_1264_, 0, v___x_1319_);
v___x_1321_ = v___x_1264_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___x_1319_);
v___x_1321_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
lean_object* v___x_1323_; 
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 0, v___x_1321_);
v___x_1323_ = v___x_1304_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v___x_1321_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec_ref(v_alts_1294_);
lean_dec_ref(v_discrInfos_1293_);
lean_dec_ref(v_discrs_1290_);
lean_dec(v_motive_1289_);
lean_dec_ref(v_params_1288_);
lean_del_object(v___x_1264_);
lean_dec(v_us_1204_);
lean_dec(v_declName_1203_);
v_a_1327_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1301_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1301_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
v___jp_1335_:
{
lean_object* v_levelParams_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; uint8_t v___x_1342_; 
v_levelParams_1338_ = lean_ctor_get(v_toConstantVal_1266_, 1);
lean_inc(v_levelParams_1338_);
lean_dec_ref(v_toConstantVal_1266_);
v___x_1339_ = l_Array_toSubarray___redArg(v_args_1275_, v_lower_1336_, v_upper_1337_);
v___x_1340_ = l_List_lengthTR___redArg(v_levelParams_1338_);
lean_dec(v_levelParams_1338_);
v___x_1341_ = l_List_lengthTR___redArg(v_us_1204_);
v___x_1342_ = lean_nat_dec_eq(v___x_1340_, v___x_1341_);
lean_dec(v___x_1341_);
lean_dec(v___x_1340_);
if (v___x_1342_ == 0)
{
lean_object* v___x_1343_; 
v___x_1343_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__3));
v___y_1296_ = v___x_1339_;
v___y_1297_ = v___x_1343_;
goto v___jp_1295_;
}
else
{
v___y_1296_ = v___x_1339_;
v___y_1297_ = v___x_1292_;
goto v___jp_1295_;
}
}
}
}
}
else
{
lean_object* v___x_1346_; lean_object* v___x_1348_; 
lean_dec(v_a_1258_);
lean_dec(v_us_1204_);
lean_dec(v_declName_1203_);
lean_dec_ref(v_e_1185_);
v___x_1346_ = lean_box(0);
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 0, v___x_1346_);
v___x_1348_ = v___x_1260_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1346_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
else
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
lean_dec(v_us_1204_);
lean_dec(v_declName_1203_);
lean_dec_ref(v_e_1185_);
v_a_1351_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1353_ = v___x_1257_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1257_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1351_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
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
lean_dec_ref(v___x_1202_);
lean_dec_ref(v_e_1185_);
goto v___jp_1196_;
}
}
v___jp_1196_:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = lean_box(0);
v___x_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
return v___x_1198_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___boxed(lean_object* v_e_1360_, lean_object* v_alsoCasesOn_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
uint8_t v_alsoCasesOn_boxed_1371_; lean_object* v_res_1372_; 
v_alsoCasesOn_boxed_1371_ = lean_unbox(v_alsoCasesOn_1361_);
v_res_1372_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(v_e_1360_, v_alsoCasesOn_boxed_1371_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1363_);
lean_dec(v___y_1362_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0(lean_object* v_k_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v_b_1378_, lean_object* v_c_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v___x_1385_; 
lean_inc(v___y_1383_);
lean_inc_ref(v___y_1382_);
lean_inc(v___y_1381_);
lean_inc_ref(v___y_1380_);
lean_inc(v___y_1377_);
lean_inc_ref(v___y_1376_);
lean_inc(v___y_1375_);
lean_inc(v___y_1374_);
v___x_1385_ = lean_apply_11(v_k_1373_, v_b_1378_, v_c_1379_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, lean_box(0));
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0___boxed(lean_object* v_k_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v_b_1391_, lean_object* v_c_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0(v_k_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v_b_1391_, v_c_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec(v___y_1387_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(lean_object* v_e_1399_, lean_object* v_maxFVars_1400_, lean_object* v_k_1401_, uint8_t v_cleanupAnnotations_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v___f_1412_; uint8_t v___x_1413_; uint8_t v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
lean_inc(v___y_1406_);
lean_inc_ref(v___y_1405_);
lean_inc(v___y_1404_);
lean_inc(v___y_1403_);
v___f_1412_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1412_, 0, v_k_1401_);
lean_closure_set(v___f_1412_, 1, v___y_1403_);
lean_closure_set(v___f_1412_, 2, v___y_1404_);
lean_closure_set(v___f_1412_, 3, v___y_1405_);
lean_closure_set(v___f_1412_, 4, v___y_1406_);
v___x_1413_ = 1;
v___x_1414_ = 0;
v___x_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1415_, 0, v_maxFVars_1400_);
v___x_1416_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1399_, v___x_1413_, v___x_1414_, v___x_1413_, v___x_1414_, v___x_1415_, v___f_1412_, v_cleanupAnnotations_1402_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
lean_dec_ref_known(v___x_1415_, 1);
if (lean_obj_tag(v___x_1416_) == 0)
{
return v___x_1416_;
}
else
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1424_; 
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1419_ = v___x_1416_;
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1416_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___boxed(lean_object* v_e_1425_, lean_object* v_maxFVars_1426_, lean_object* v_k_1427_, lean_object* v_cleanupAnnotations_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1438_; lean_object* v_res_1439_; 
v_cleanupAnnotations_boxed_1438_ = lean_unbox(v_cleanupAnnotations_1428_);
v_res_1439_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(v_e_1425_, v_maxFVars_1426_, v_k_1427_, v_cleanupAnnotations_boxed_1438_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec(v___y_1429_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0(lean_object* v_k_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v_b_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v___x_1451_; 
lean_inc(v___y_1449_);
lean_inc_ref(v___y_1448_);
lean_inc(v___y_1447_);
lean_inc_ref(v___y_1446_);
lean_inc(v___y_1444_);
lean_inc_ref(v___y_1443_);
lean_inc(v___y_1442_);
lean_inc(v___y_1441_);
v___x_1451_ = lean_apply_10(v_k_1440_, v_b_1445_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, lean_box(0));
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0___boxed(lean_object* v_k_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v_b_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0(v_k_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v_b_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
lean_dec(v___y_1454_);
lean_dec(v___y_1453_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(lean_object* v_name_1464_, lean_object* v_type_1465_, lean_object* v_val_1466_, lean_object* v_k_1467_, uint8_t v_nondep_1468_, uint8_t v_kind_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v___f_1479_; lean_object* v___x_1480_; 
lean_inc(v___y_1473_);
lean_inc_ref(v___y_1472_);
lean_inc(v___y_1471_);
lean_inc(v___y_1470_);
v___f_1479_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1479_, 0, v_k_1467_);
lean_closure_set(v___f_1479_, 1, v___y_1470_);
lean_closure_set(v___f_1479_, 2, v___y_1471_);
lean_closure_set(v___f_1479_, 3, v___y_1472_);
lean_closure_set(v___f_1479_, 4, v___y_1473_);
v___x_1480_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1464_, v_type_1465_, v_val_1466_, v___f_1479_, v_nondep_1468_, v_kind_1469_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
if (lean_obj_tag(v___x_1480_) == 0)
{
return v___x_1480_;
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1480_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1480_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg___boxed(lean_object* v_name_1489_, lean_object* v_type_1490_, lean_object* v_val_1491_, lean_object* v_k_1492_, lean_object* v_nondep_1493_, lean_object* v_kind_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
uint8_t v_nondep_boxed_1504_; uint8_t v_kind_boxed_1505_; lean_object* v_res_1506_; 
v_nondep_boxed_1504_ = lean_unbox(v_nondep_1493_);
v_kind_boxed_1505_ = lean_unbox(v_kind_1494_);
v_res_1506_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(v_name_1489_, v_type_1490_, v_val_1491_, v_k_1492_, v_nondep_boxed_1504_, v_kind_boxed_1505_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec(v___y_1495_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0(lean_object* v_k_1507_, uint8_t v_usedLetOnly_1508_, lean_object* v_x_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v___x_1519_; 
lean_inc(v___y_1517_);
lean_inc_ref(v___y_1516_);
lean_inc(v___y_1515_);
lean_inc_ref(v___y_1514_);
lean_inc(v___y_1513_);
lean_inc_ref(v___y_1512_);
lean_inc(v___y_1511_);
lean_inc(v___y_1510_);
lean_inc_ref(v_x_1509_);
v___x_1519_ = lean_apply_10(v_k_1507_, v_x_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, lean_box(0));
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v_a_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; uint8_t v___x_1524_; uint8_t v___x_1525_; lean_object* v___x_1526_; 
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_a_1520_);
lean_dec_ref_known(v___x_1519_, 1);
v___x_1521_ = lean_unsigned_to_nat(1u);
v___x_1522_ = lean_mk_empty_array_with_capacity(v___x_1521_);
v___x_1523_ = lean_array_push(v___x_1522_, v_x_1509_);
v___x_1524_ = 0;
v___x_1525_ = 1;
v___x_1526_ = l_Lean_Meta_mkLetFVars(v___x_1523_, v_a_1520_, v_usedLetOnly_1508_, v___x_1524_, v___x_1525_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
lean_dec_ref(v___x_1523_);
return v___x_1526_;
}
else
{
lean_dec_ref(v_x_1509_);
return v___x_1519_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0___boxed(lean_object* v_k_1527_, lean_object* v_usedLetOnly_1528_, lean_object* v_x_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
uint8_t v_usedLetOnly_boxed_1539_; lean_object* v_res_1540_; 
v_usedLetOnly_boxed_1539_ = lean_unbox(v_usedLetOnly_1528_);
v_res_1540_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0(v_k_1527_, v_usedLetOnly_boxed_1539_, v_x_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec(v___y_1531_);
lean_dec(v___y_1530_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(lean_object* v_name_1541_, lean_object* v_type_1542_, lean_object* v_val_1543_, lean_object* v_k_1544_, uint8_t v_nondep_1545_, uint8_t v_kind_1546_, uint8_t v_usedLetOnly_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
lean_object* v___x_1557_; lean_object* v___f_1558_; lean_object* v___x_1559_; 
v___x_1557_ = lean_box(v_usedLetOnly_1547_);
v___f_1558_ = lean_alloc_closure((void*)(l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0___boxed), 12, 2);
lean_closure_set(v___f_1558_, 0, v_k_1544_);
lean_closure_set(v___f_1558_, 1, v___x_1557_);
v___x_1559_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(v_name_1541_, v_type_1542_, v_val_1543_, v___f_1558_, v_nondep_1545_, v_kind_1546_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___boxed(lean_object* v_name_1560_, lean_object* v_type_1561_, lean_object* v_val_1562_, lean_object* v_k_1563_, lean_object* v_nondep_1564_, lean_object* v_kind_1565_, lean_object* v_usedLetOnly_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
uint8_t v_nondep_boxed_1576_; uint8_t v_kind_boxed_1577_; uint8_t v_usedLetOnly_boxed_1578_; lean_object* v_res_1579_; 
v_nondep_boxed_1576_ = lean_unbox(v_nondep_1564_);
v_kind_boxed_1577_ = lean_unbox(v_kind_1565_);
v_usedLetOnly_boxed_1578_ = lean_unbox(v_usedLetOnly_1566_);
v_res_1579_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(v_name_1560_, v_type_1561_, v_val_1562_, v_k_1563_, v_nondep_boxed_1576_, v_kind_boxed_1577_, v_usedLetOnly_boxed_1578_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec(v___y_1567_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(lean_object* v_name_1580_, uint8_t v_bi_1581_, lean_object* v_type_1582_, lean_object* v_k_1583_, uint8_t v_kind_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
lean_object* v___f_1594_; lean_object* v___x_1595_; 
lean_inc(v___y_1588_);
lean_inc_ref(v___y_1587_);
lean_inc(v___y_1586_);
lean_inc(v___y_1585_);
v___f_1594_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1594_, 0, v_k_1583_);
lean_closure_set(v___f_1594_, 1, v___y_1585_);
lean_closure_set(v___f_1594_, 2, v___y_1586_);
lean_closure_set(v___f_1594_, 3, v___y_1587_);
lean_closure_set(v___f_1594_, 4, v___y_1588_);
v___x_1595_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1580_, v_bi_1581_, v_type_1582_, v___f_1594_, v_kind_1584_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
if (lean_obj_tag(v___x_1595_) == 0)
{
return v___x_1595_;
}
else
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1595_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1595_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1596_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___boxed(lean_object* v_name_1604_, lean_object* v_bi_1605_, lean_object* v_type_1606_, lean_object* v_k_1607_, lean_object* v_kind_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
uint8_t v_bi_boxed_1618_; uint8_t v_kind_boxed_1619_; lean_object* v_res_1620_; 
v_bi_boxed_1618_ = lean_unbox(v_bi_1605_);
v_kind_boxed_1619_ = lean_unbox(v_kind_1608_);
v_res_1620_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_name_1604_, v_bi_boxed_1618_, v_type_1606_, v_k_1607_, v_kind_boxed_1619_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
lean_dec(v___y_1610_);
lean_dec(v___y_1609_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0(lean_object* v_k_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v___x_1631_; 
lean_inc(v___y_1625_);
lean_inc_ref(v___y_1624_);
lean_inc(v___y_1623_);
lean_inc(v___y_1622_);
v___x_1631_ = lean_apply_9(v_k_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, lean_box(0));
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0___boxed(lean_object* v_k_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0(v_k_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v___y_1634_);
lean_dec(v___y_1633_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(lean_object* v_k_1643_, uint8_t v_allowLevelAssignments_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
lean_object* v___f_1654_; lean_object* v___x_1655_; 
lean_inc(v___y_1648_);
lean_inc_ref(v___y_1647_);
lean_inc(v___y_1646_);
lean_inc(v___y_1645_);
v___f_1654_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1654_, 0, v_k_1643_);
lean_closure_set(v___f_1654_, 1, v___y_1645_);
lean_closure_set(v___f_1654_, 2, v___y_1646_);
lean_closure_set(v___f_1654_, 3, v___y_1647_);
lean_closure_set(v___f_1654_, 4, v___y_1648_);
v___x_1655_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1644_, v___f_1654_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_);
if (lean_obj_tag(v___x_1655_) == 0)
{
return v___x_1655_;
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1655_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1655_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___boxed(lean_object* v_k_1664_, lean_object* v_allowLevelAssignments_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1675_; lean_object* v_res_1676_; 
v_allowLevelAssignments_boxed_1675_ = lean_unbox(v_allowLevelAssignments_1665_);
v_res_1676_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v_k_1664_, v_allowLevelAssignments_boxed_1675_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec(v___y_1666_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(lean_object* v_a_1677_, lean_object* v_x_1678_){
_start:
{
if (lean_obj_tag(v_x_1678_) == 0)
{
lean_object* v___x_1679_; 
v___x_1679_ = lean_box(0);
return v___x_1679_;
}
else
{
lean_object* v_key_1680_; lean_object* v_value_1681_; lean_object* v_tail_1682_; uint8_t v___x_1683_; 
v_key_1680_ = lean_ctor_get(v_x_1678_, 0);
v_value_1681_ = lean_ctor_get(v_x_1678_, 1);
v_tail_1682_ = lean_ctor_get(v_x_1678_, 2);
v___x_1683_ = lean_expr_eqv(v_key_1680_, v_a_1677_);
if (v___x_1683_ == 0)
{
v_x_1678_ = v_tail_1682_;
goto _start;
}
else
{
lean_object* v___x_1685_; 
lean_inc(v_value_1681_);
v___x_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1685_, 0, v_value_1681_);
return v___x_1685_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg___boxed(lean_object* v_a_1686_, lean_object* v_x_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(v_a_1686_, v_x_1687_);
lean_dec(v_x_1687_);
lean_dec_ref(v_a_1686_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(lean_object* v_m_1689_, lean_object* v_a_1690_){
_start:
{
lean_object* v_buckets_1691_; lean_object* v___x_1692_; uint64_t v___x_1693_; uint64_t v___x_1694_; uint64_t v___x_1695_; uint64_t v_fold_1696_; uint64_t v___x_1697_; uint64_t v___x_1698_; uint64_t v___x_1699_; size_t v___x_1700_; size_t v___x_1701_; size_t v___x_1702_; size_t v___x_1703_; size_t v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
v_buckets_1691_ = lean_ctor_get(v_m_1689_, 1);
v___x_1692_ = lean_array_get_size(v_buckets_1691_);
v___x_1693_ = l_Lean_Expr_hash(v_a_1690_);
v___x_1694_ = 32ULL;
v___x_1695_ = lean_uint64_shift_right(v___x_1693_, v___x_1694_);
v_fold_1696_ = lean_uint64_xor(v___x_1693_, v___x_1695_);
v___x_1697_ = 16ULL;
v___x_1698_ = lean_uint64_shift_right(v_fold_1696_, v___x_1697_);
v___x_1699_ = lean_uint64_xor(v_fold_1696_, v___x_1698_);
v___x_1700_ = lean_uint64_to_usize(v___x_1699_);
v___x_1701_ = lean_usize_of_nat(v___x_1692_);
v___x_1702_ = ((size_t)1ULL);
v___x_1703_ = lean_usize_sub(v___x_1701_, v___x_1702_);
v___x_1704_ = lean_usize_land(v___x_1700_, v___x_1703_);
v___x_1705_ = lean_array_uget_borrowed(v_buckets_1691_, v___x_1704_);
v___x_1706_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(v_a_1690_, v___x_1705_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg___boxed(lean_object* v_m_1707_, lean_object* v_a_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v_m_1707_, v_a_1708_);
lean_dec_ref(v_a_1708_);
lean_dec_ref(v_m_1707_);
return v_res_1709_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(lean_object* v_opts_1710_, lean_object* v_opt_1711_){
_start:
{
lean_object* v_name_1712_; lean_object* v_defValue_1713_; lean_object* v_map_1714_; lean_object* v___x_1715_; 
v_name_1712_ = lean_ctor_get(v_opt_1711_, 0);
v_defValue_1713_ = lean_ctor_get(v_opt_1711_, 1);
v_map_1714_ = lean_ctor_get(v_opts_1710_, 0);
v___x_1715_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1714_, v_name_1712_);
if (lean_obj_tag(v___x_1715_) == 0)
{
uint8_t v___x_1716_; 
v___x_1716_ = lean_unbox(v_defValue_1713_);
return v___x_1716_;
}
else
{
lean_object* v_val_1717_; 
v_val_1717_ = lean_ctor_get(v___x_1715_, 0);
lean_inc(v_val_1717_);
lean_dec_ref_known(v___x_1715_, 1);
if (lean_obj_tag(v_val_1717_) == 1)
{
uint8_t v_v_1718_; 
v_v_1718_ = lean_ctor_get_uint8(v_val_1717_, 0);
lean_dec_ref_known(v_val_1717_, 0);
return v_v_1718_;
}
else
{
uint8_t v___x_1719_; 
lean_dec(v_val_1717_);
v___x_1719_ = lean_unbox(v_defValue_1713_);
return v___x_1719_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5___boxed(lean_object* v_opts_1720_, lean_object* v_opt_1721_){
_start:
{
uint8_t v_res_1722_; lean_object* v_r_1723_; 
v_res_1722_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v_opts_1720_, v_opt_1721_);
lean_dec_ref(v_opt_1721_);
lean_dec_ref(v_opts_1720_);
v_r_1723_ = lean_box(v_res_1722_);
return v_r_1723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(lean_object* v_a_1724_, lean_object* v_b_1725_){
_start:
{
lean_object* v_array_1726_; lean_object* v_start_1727_; lean_object* v_stop_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1741_; 
v_array_1726_ = lean_ctor_get(v_a_1724_, 0);
v_start_1727_ = lean_ctor_get(v_a_1724_, 1);
v_stop_1728_ = lean_ctor_get(v_a_1724_, 2);
v_isSharedCheck_1741_ = !lean_is_exclusive(v_a_1724_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1730_ = v_a_1724_;
v_isShared_1731_ = v_isSharedCheck_1741_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_stop_1728_);
lean_inc(v_start_1727_);
lean_inc(v_array_1726_);
lean_dec(v_a_1724_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1741_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
uint8_t v___x_1732_; 
v___x_1732_ = lean_nat_dec_lt(v_start_1727_, v_stop_1728_);
if (v___x_1732_ == 0)
{
lean_del_object(v___x_1730_);
lean_dec(v_stop_1728_);
lean_dec(v_start_1727_);
lean_dec_ref(v_array_1726_);
return v_b_1725_;
}
else
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1736_; 
v___x_1733_ = lean_unsigned_to_nat(1u);
v___x_1734_ = lean_nat_add(v_start_1727_, v___x_1733_);
lean_inc_ref(v_array_1726_);
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 1, v___x_1734_);
v___x_1736_ = v___x_1730_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_array_1726_);
lean_ctor_set(v_reuseFailAlloc_1740_, 1, v___x_1734_);
lean_ctor_set(v_reuseFailAlloc_1740_, 2, v_stop_1728_);
v___x_1736_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1737_ = lean_array_fget(v_array_1726_, v_start_1727_);
lean_dec(v_start_1727_);
lean_dec_ref(v_array_1726_);
v___x_1738_ = lean_array_push(v_b_1725_, v___x_1737_);
v_a_1724_ = v___x_1736_;
v_b_1725_ = v___x_1738_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0(lean_object* v_body_1742_, lean_object* v_recFnName_1743_, lean_object* v_fixedPrefixSize_1744_, lean_object* v_F_1745_, lean_object* v_x_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1756_ = lean_expr_instantiate1(v_body_1742_, v_x_1746_);
v___x_1757_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1743_, v_fixedPrefixSize_1744_, v_F_1745_, v___x_1756_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; uint8_t v___x_1762_; uint8_t v___x_1763_; uint8_t v___x_1764_; lean_object* v___x_1765_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_a_1758_);
lean_dec_ref_known(v___x_1757_, 1);
v___x_1759_ = lean_unsigned_to_nat(1u);
v___x_1760_ = lean_mk_empty_array_with_capacity(v___x_1759_);
v___x_1761_ = lean_array_push(v___x_1760_, v_x_1746_);
v___x_1762_ = 0;
v___x_1763_ = 1;
v___x_1764_ = 1;
v___x_1765_ = l_Lean_Meta_mkLambdaFVars(v___x_1761_, v_a_1758_, v___x_1762_, v___x_1763_, v___x_1762_, v___x_1763_, v___x_1764_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
lean_dec_ref(v___x_1761_);
return v___x_1765_;
}
else
{
lean_dec_ref(v_x_1746_);
return v___x_1757_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0___boxed(lean_object* v_body_1766_, lean_object* v_recFnName_1767_, lean_object* v_fixedPrefixSize_1768_, lean_object* v_F_1769_, lean_object* v_x_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0(v_body_1766_, v_recFnName_1767_, v_fixedPrefixSize_1768_, v_F_1769_, v_x_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v_body_1766_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1(lean_object* v_body_1781_, lean_object* v_recFnName_1782_, lean_object* v_fixedPrefixSize_1783_, lean_object* v_F_1784_, lean_object* v_x_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1795_ = lean_expr_instantiate1(v_body_1781_, v_x_1785_);
v___x_1796_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1782_, v_fixedPrefixSize_1783_, v_F_1784_, v___x_1795_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; uint8_t v___x_1801_; uint8_t v___x_1802_; uint8_t v___x_1803_; lean_object* v___x_1804_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_a_1797_);
lean_dec_ref_known(v___x_1796_, 1);
v___x_1798_ = lean_unsigned_to_nat(1u);
v___x_1799_ = lean_mk_empty_array_with_capacity(v___x_1798_);
v___x_1800_ = lean_array_push(v___x_1799_, v_x_1785_);
v___x_1801_ = 0;
v___x_1802_ = 1;
v___x_1803_ = 1;
v___x_1804_ = l_Lean_Meta_mkForallFVars(v___x_1800_, v_a_1797_, v___x_1801_, v___x_1802_, v___x_1802_, v___x_1803_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_);
lean_dec_ref(v___x_1800_);
return v___x_1804_;
}
else
{
lean_dec_ref(v_x_1785_);
return v___x_1796_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1___boxed(lean_object* v_body_1805_, lean_object* v_recFnName_1806_, lean_object* v_fixedPrefixSize_1807_, lean_object* v_F_1808_, lean_object* v_x_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1(v_body_1805_, v_recFnName_1806_, v_fixedPrefixSize_1807_, v_F_1808_, v_x_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v_body_1805_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2___boxed(lean_object* v_body_1820_, lean_object* v_recFnName_1821_, lean_object* v_fixedPrefixSize_1822_, lean_object* v_F_1823_, lean_object* v_x_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2(v_body_1820_, v_recFnName_1821_, v_fixedPrefixSize_1822_, v_F_1823_, v_x_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v___y_1826_);
lean_dec(v___y_1825_);
lean_dec_ref(v_x_1824_);
lean_dec_ref(v_body_1820_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(lean_object* v_recFnName_1837_, lean_object* v_fixedPrefixSize_1838_, lean_object* v_F_1839_, size_t v_sz_1840_, size_t v_i_1841_, lean_object* v_bs_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
uint8_t v___x_1852_; 
v___x_1852_ = lean_usize_dec_lt(v_i_1841_, v_sz_1840_);
if (v___x_1852_ == 0)
{
lean_object* v___x_1853_; 
lean_dec_ref(v_F_1839_);
lean_dec(v_fixedPrefixSize_1838_);
lean_dec(v_recFnName_1837_);
v___x_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1853_, 0, v_bs_1842_);
return v___x_1853_;
}
else
{
lean_object* v_v_1854_; lean_object* v___x_1855_; 
v_v_1854_ = lean_array_uget_borrowed(v_bs_1842_, v_i_1841_);
lean_inc(v_v_1854_);
lean_inc_ref(v_F_1839_);
lean_inc(v_fixedPrefixSize_1838_);
lean_inc(v_recFnName_1837_);
v___x_1855_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1837_, v_fixedPrefixSize_1838_, v_F_1839_, v_v_1854_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_a_1856_; lean_object* v___x_1857_; lean_object* v_bs_x27_1858_; size_t v___x_1859_; size_t v___x_1860_; lean_object* v___x_1861_; 
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_a_1856_);
lean_dec_ref_known(v___x_1855_, 1);
v___x_1857_ = lean_unsigned_to_nat(0u);
v_bs_x27_1858_ = lean_array_uset(v_bs_1842_, v_i_1841_, v___x_1857_);
v___x_1859_ = ((size_t)1ULL);
v___x_1860_ = lean_usize_add(v_i_1841_, v___x_1859_);
v___x_1861_ = lean_array_uset(v_bs_x27_1858_, v_i_1841_, v_a_1856_);
v_i_1841_ = v___x_1860_;
v_bs_1842_ = v___x_1861_;
goto _start;
}
else
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1870_; 
lean_dec_ref(v_bs_1842_);
lean_dec_ref(v_F_1839_);
lean_dec(v_fixedPrefixSize_1838_);
lean_dec(v_recFnName_1837_);
v_a_1863_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1865_ = v___x_1855_;
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1855_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1868_; 
if (v_isShared_1866_ == 0)
{
v___x_1868_ = v___x_1865_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1863_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4(void){
_start:
{
lean_object* v_cls_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v_cls_1878_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_1879_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__3));
v___x_1880_ = l_Lean_Name_append(v___x_1879_, v_cls_1878_);
return v___x_1880_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6(void){
_start:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1882_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5));
v___x_1883_ = l_Lean_stringToMessageData(v___x_1882_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(lean_object* v_recFnName_1884_, lean_object* v_fixedPrefixSize_1885_, lean_object* v_F_1886_, lean_object* v_e_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_){
_start:
{
lean_object* v___y_1898_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; uint8_t v___x_1912_; 
v___x_1909_ = l_Lean_Expr_getAppNumArgs(v_e_1887_);
v___x_1910_ = lean_unsigned_to_nat(1u);
v___x_1911_ = lean_nat_add(v_fixedPrefixSize_1885_, v___x_1910_);
v___x_1912_ = lean_nat_dec_lt(v___x_1909_, v___x_1911_);
if (v___x_1912_ == 0)
{
lean_object* v___x_1913_; lean_object* v_dummy_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v_args_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1913_ = l_Lean_instInhabitedExpr;
v_dummy_1914_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_1909_);
v___x_1915_ = lean_mk_array(v___x_1909_, v_dummy_1914_);
v___x_1916_ = lean_nat_sub(v___x_1909_, v___x_1910_);
lean_dec(v___x_1909_);
v_args_1917_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1887_, v___x_1915_, v___x_1916_);
v___x_1918_ = lean_array_get(v___x_1913_, v_args_1917_, v_fixedPrefixSize_1885_);
lean_inc_ref(v_F_1886_);
lean_inc(v_fixedPrefixSize_1885_);
lean_inc(v_recFnName_1884_);
v___x_1919_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1884_, v_fixedPrefixSize_1885_, v_F_1886_, v___x_1918_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_a_1920_);
lean_dec_ref_known(v___x_1919_, 1);
lean_inc_ref(v_F_1886_);
v___x_1921_ = l_Lean_Expr_app___override(v_F_1886_, v_a_1920_);
lean_inc(v_a_1895_);
lean_inc_ref(v_a_1894_);
lean_inc(v_a_1893_);
lean_inc_ref(v_a_1892_);
lean_inc_ref(v___x_1921_);
v___x_1922_ = lean_infer_type(v___x_1921_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v_a_1923_; lean_object* v___x_1924_; 
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
lean_inc(v_a_1923_);
lean_dec_ref_known(v___x_1922_, 1);
lean_inc(v_a_1895_);
lean_inc_ref(v_a_1894_);
lean_inc(v_a_1893_);
lean_inc_ref(v_a_1892_);
v___x_1924_ = lean_whnf(v_a_1923_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_a_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc(v_a_1925_);
lean_dec_ref_known(v___x_1924_, 1);
v___x_1926_ = l_Lean_Expr_bindingDomain_x21(v_a_1925_);
lean_dec(v_a_1925_);
v___x_1927_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg(v___x_1926_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1929_; lean_object* v_lower_1931_; lean_object* v_upper_1932_; lean_object* v___x_1956_; lean_object* v___x_1957_; uint8_t v___x_1958_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref_known(v___x_1927_, 1);
v___x_1929_ = l_Lean_Expr_app___override(v___x_1921_, v_a_1928_);
v___x_1956_ = lean_unsigned_to_nat(0u);
v___x_1957_ = lean_array_get_size(v_args_1917_);
v___x_1958_ = lean_nat_dec_le(v___x_1911_, v___x_1956_);
if (v___x_1958_ == 0)
{
v_lower_1931_ = v___x_1911_;
v_upper_1932_ = v___x_1957_;
goto v___jp_1930_;
}
else
{
lean_dec(v___x_1911_);
v_lower_1931_ = v___x_1956_;
v_upper_1932_ = v___x_1957_;
goto v___jp_1930_;
}
v___jp_1930_:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; size_t v_sz_1936_; size_t v___x_1937_; lean_object* v___x_1938_; 
v___x_1933_ = l_Array_toSubarray___redArg(v_args_1917_, v_lower_1931_, v_upper_1932_);
v___x_1934_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
v___x_1935_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(v___x_1933_, v___x_1934_);
v_sz_1936_ = lean_array_size(v___x_1935_);
v___x_1937_ = ((size_t)0ULL);
v___x_1938_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_1884_, v_fixedPrefixSize_1885_, v_F_1886_, v_sz_1936_, v___x_1937_, v___x_1935_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1947_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1941_ = v___x_1938_;
v_isShared_1942_ = v_isSharedCheck_1947_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1938_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1947_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1943_; lean_object* v___x_1945_; 
v___x_1943_ = l_Lean_mkAppN(v___x_1929_, v_a_1939_);
lean_dec(v_a_1939_);
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 0, v___x_1943_);
v___x_1945_ = v___x_1941_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___x_1943_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
lean_dec_ref(v___x_1929_);
v_a_1948_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1938_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1938_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1921_);
lean_dec_ref(v_args_1917_);
lean_dec(v___x_1911_);
lean_dec_ref(v_F_1886_);
lean_dec(v_fixedPrefixSize_1885_);
lean_dec(v_recFnName_1884_);
return v___x_1927_;
}
}
else
{
lean_dec_ref(v___x_1921_);
lean_dec_ref(v_args_1917_);
lean_dec(v___x_1911_);
lean_dec_ref(v_F_1886_);
lean_dec(v_fixedPrefixSize_1885_);
lean_dec(v_recFnName_1884_);
return v___x_1924_;
}
}
else
{
lean_dec_ref(v___x_1921_);
lean_dec_ref(v_args_1917_);
lean_dec(v___x_1911_);
lean_dec_ref(v_F_1886_);
lean_dec(v_fixedPrefixSize_1885_);
lean_dec(v_recFnName_1884_);
return v___x_1922_;
}
}
else
{
lean_dec_ref(v_args_1917_);
lean_dec(v___x_1911_);
lean_dec_ref(v_F_1886_);
lean_dec(v_fixedPrefixSize_1885_);
lean_dec(v_recFnName_1884_);
return v___x_1919_;
}
}
else
{
lean_object* v_options_1959_; uint8_t v_hasTrace_1960_; 
lean_dec(v___x_1911_);
lean_dec(v___x_1909_);
v_options_1959_ = lean_ctor_get(v_a_1894_, 1);
v_hasTrace_1960_ = lean_ctor_get_uint8(v_options_1959_, sizeof(void*)*1);
if (v_hasTrace_1960_ == 0)
{
v___y_1898_ = v_a_1888_;
v___y_1899_ = v_a_1889_;
v___y_1900_ = v_a_1890_;
v___y_1901_ = v_a_1891_;
v___y_1902_ = v_a_1892_;
v___y_1903_ = v_a_1893_;
v___y_1904_ = v_a_1894_;
v___y_1905_ = v_a_1895_;
goto v___jp_1897_;
}
else
{
lean_object* v_toCold_1961_; lean_object* v_inheritedTraceOptions_1962_; lean_object* v_cls_1963_; lean_object* v___x_1964_; uint8_t v___x_1965_; 
v_toCold_1961_ = lean_ctor_get(v_a_1894_, 0);
v_inheritedTraceOptions_1962_ = lean_ctor_get(v_toCold_1961_, 4);
v_cls_1963_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_1964_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_1965_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1962_, v_options_1959_, v___x_1964_);
if (v___x_1965_ == 0)
{
v___y_1898_ = v_a_1888_;
v___y_1899_ = v_a_1889_;
v___y_1900_ = v_a_1890_;
v___y_1901_ = v_a_1891_;
v___y_1902_ = v_a_1892_;
v___y_1903_ = v_a_1893_;
v___y_1904_ = v_a_1894_;
v___y_1905_ = v_a_1895_;
goto v___jp_1897_;
}
else
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1966_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6);
lean_inc_ref(v_e_1887_);
v___x_1967_ = l_Lean_indentExpr(v_e_1887_);
v___x_1968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1966_);
lean_ctor_set(v___x_1968_, 1, v___x_1967_);
v___x_1969_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(v_cls_1963_, v___x_1968_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_dec_ref_known(v___x_1969_, 1);
v___y_1898_ = v_a_1888_;
v___y_1899_ = v_a_1889_;
v___y_1900_ = v_a_1890_;
v___y_1901_ = v_a_1891_;
v___y_1902_ = v_a_1892_;
v___y_1903_ = v_a_1893_;
v___y_1904_ = v_a_1894_;
v___y_1905_ = v_a_1895_;
goto v___jp_1897_;
}
else
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1977_; 
lean_dec_ref(v_e_1887_);
lean_dec_ref(v_F_1886_);
lean_dec(v_fixedPrefixSize_1885_);
lean_dec(v_recFnName_1884_);
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1972_ = v___x_1969_;
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1969_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1975_; 
if (v_isShared_1973_ == 0)
{
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1970_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
}
}
v___jp_1897_:
{
lean_object* v___x_1906_; 
v___x_1906_ = l_Lean_Meta_etaExpand(v_e_1887_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1908_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
lean_inc(v_a_1907_);
lean_dec_ref_known(v___x_1906_, 1);
v___x_1908_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1884_, v_fixedPrefixSize_1885_, v_F_1886_, v_a_1907_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
return v___x_1908_;
}
else
{
lean_dec_ref(v_F_1886_);
lean_dec(v_fixedPrefixSize_1885_);
lean_dec(v_recFnName_1884_);
return v___x_1906_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(lean_object* v_recFnName_1978_, lean_object* v_fixedPrefixSize_1979_, lean_object* v_F_1980_, lean_object* v_x_1981_, lean_object* v_x_1982_, lean_object* v_x_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
if (lean_obj_tag(v_x_1981_) == 5)
{
lean_object* v_fn_1993_; lean_object* v_arg_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
v_fn_1993_ = lean_ctor_get(v_x_1981_, 0);
lean_inc_ref(v_fn_1993_);
v_arg_1994_ = lean_ctor_get(v_x_1981_, 1);
lean_inc_ref(v_arg_1994_);
lean_dec_ref_known(v_x_1981_, 2);
v___x_1995_ = lean_array_set(v_x_1982_, v_x_1983_, v_arg_1994_);
v___x_1996_ = lean_unsigned_to_nat(1u);
v___x_1997_ = lean_nat_sub(v_x_1983_, v___x_1996_);
lean_dec(v_x_1983_);
v_x_1981_ = v_fn_1993_;
v_x_1982_ = v___x_1995_;
v_x_1983_ = v___x_1997_;
goto _start;
}
else
{
lean_object* v___x_1999_; 
lean_dec(v_x_1983_);
lean_inc_ref(v_F_1980_);
lean_inc(v_fixedPrefixSize_1979_);
lean_inc(v_recFnName_1978_);
v___x_1999_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1978_, v_fixedPrefixSize_1979_, v_F_1980_, v_x_1981_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; size_t v_sz_2001_; size_t v___x_2002_; lean_object* v___x_2003_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_a_2000_);
lean_dec_ref_known(v___x_1999_, 1);
v_sz_2001_ = lean_array_size(v_x_1982_);
v___x_2002_ = ((size_t)0ULL);
v___x_2003_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_1978_, v_fixedPrefixSize_1979_, v_F_1980_, v_sz_2001_, v___x_2002_, v_x_1982_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_a_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2012_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2006_ = v___x_2003_;
v_isShared_2007_ = v_isSharedCheck_2012_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_a_2004_);
lean_dec(v___x_2003_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2012_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2008_; lean_object* v___x_2010_; 
v___x_2008_ = l_Lean_mkAppN(v_a_2000_, v_a_2004_);
lean_dec(v_a_2004_);
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 0, v___x_2008_);
v___x_2010_ = v___x_2006_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v___x_2008_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
else
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
lean_dec(v_a_2000_);
v_a_2013_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_2003_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_2003_);
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
else
{
lean_dec_ref(v_x_1982_);
lean_dec_ref(v_F_1980_);
lean_dec(v_fixedPrefixSize_1979_);
lean_dec(v_recFnName_1978_);
return v___x_1999_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(lean_object* v_recFnName_2021_, lean_object* v_fixedPrefixSize_2022_, lean_object* v_F_2023_, lean_object* v_e_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_){
_start:
{
uint8_t v___x_2034_; 
v___x_2034_ = l_Lean_Expr_isAppOf(v_e_2024_, v_recFnName_2021_);
if (v___x_2034_ == 0)
{
lean_object* v_dummy_2035_; lean_object* v_nargs_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; 
v_dummy_2035_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
v_nargs_2036_ = l_Lean_Expr_getAppNumArgs(v_e_2024_);
lean_inc(v_nargs_2036_);
v___x_2037_ = lean_mk_array(v_nargs_2036_, v_dummy_2035_);
v___x_2038_ = lean_unsigned_to_nat(1u);
v___x_2039_ = lean_nat_sub(v_nargs_2036_, v___x_2038_);
lean_dec(v_nargs_2036_);
v___x_2040_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(v_recFnName_2021_, v_fixedPrefixSize_2022_, v_F_2023_, v_e_2024_, v___x_2037_, v___x_2039_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_);
return v___x_2040_;
}
else
{
lean_object* v___x_2041_; 
v___x_2041_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2021_, v_fixedPrefixSize_2022_, v_F_2023_, v_e_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_);
return v___x_2041_;
}
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2043_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__0));
v___x_2044_ = l_Lean_stringToMessageData(v___x_2043_);
return v___x_2044_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__2));
v___x_2047_ = l_Lean_stringToMessageData(v___x_2046_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0(lean_object* v___x_2048_, lean_object* v_b_2049_, lean_object* v_recFnName_2050_, lean_object* v_fixedPrefixSize_2051_, uint8_t v___x_2052_, lean_object* v___x_2053_, lean_object* v_a_2054_, lean_object* v_e_2055_, lean_object* v_xs_2056_, lean_object* v_altBody_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v___x_2074_; uint8_t v___x_2075_; 
v___x_2074_ = lean_array_get_size(v_xs_2056_);
v___x_2075_ = lean_nat_dec_eq(v___x_2074_, v___x_2053_);
if (v___x_2075_ == 0)
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v_a_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2091_; 
lean_dec_ref(v_altBody_2057_);
lean_dec(v_fixedPrefixSize_2051_);
lean_dec(v_recFnName_2050_);
v___x_2076_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1);
v___x_2077_ = l_Lean_indentExpr(v_a_2054_);
v___x_2078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2076_);
lean_ctor_set(v___x_2078_, 1, v___x_2077_);
v___x_2079_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3);
v___x_2080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2078_);
lean_ctor_set(v___x_2080_, 1, v___x_2079_);
v___x_2081_ = l_Lean_indentExpr(v_e_2055_);
v___x_2082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2080_);
lean_ctor_set(v___x_2082_, 1, v___x_2081_);
v___x_2083_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v___x_2082_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
v_a_2084_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2086_ = v___x_2083_;
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_a_2084_);
lean_dec(v___x_2083_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2089_; 
if (v_isShared_2087_ == 0)
{
v___x_2089_ = v___x_2086_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_a_2084_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
else
{
lean_dec_ref(v_e_2055_);
lean_dec_ref(v_a_2054_);
goto v___jp_2067_;
}
v___jp_2067_:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2068_ = lean_array_get_borrowed(v___x_2048_, v_xs_2056_, v_b_2049_);
lean_inc(v___x_2068_);
v___x_2069_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2050_, v_fixedPrefixSize_2051_, v___x_2068_, v_altBody_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v_a_2070_; uint8_t v___x_2071_; uint8_t v___x_2072_; lean_object* v___x_2073_; 
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
lean_inc(v_a_2070_);
lean_dec_ref_known(v___x_2069_, 1);
v___x_2071_ = 0;
v___x_2072_ = 1;
v___x_2073_ = l_Lean_Meta_mkLambdaFVars(v_xs_2056_, v_a_2070_, v___x_2071_, v___x_2052_, v___x_2071_, v___x_2052_, v___x_2072_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
return v___x_2073_;
}
else
{
return v___x_2069_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___boxed(lean_object** _args){
lean_object* v___x_2092_ = _args[0];
lean_object* v_b_2093_ = _args[1];
lean_object* v_recFnName_2094_ = _args[2];
lean_object* v_fixedPrefixSize_2095_ = _args[3];
lean_object* v___x_2096_ = _args[4];
lean_object* v___x_2097_ = _args[5];
lean_object* v_a_2098_ = _args[6];
lean_object* v_e_2099_ = _args[7];
lean_object* v_xs_2100_ = _args[8];
lean_object* v_altBody_2101_ = _args[9];
lean_object* v___y_2102_ = _args[10];
lean_object* v___y_2103_ = _args[11];
lean_object* v___y_2104_ = _args[12];
lean_object* v___y_2105_ = _args[13];
lean_object* v___y_2106_ = _args[14];
lean_object* v___y_2107_ = _args[15];
lean_object* v___y_2108_ = _args[16];
lean_object* v___y_2109_ = _args[17];
lean_object* v___y_2110_ = _args[18];
_start:
{
uint8_t v___x_58202__boxed_2111_; lean_object* v_res_2112_; 
v___x_58202__boxed_2111_ = lean_unbox(v___x_2096_);
v_res_2112_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0(v___x_2092_, v_b_2093_, v_recFnName_2094_, v_fixedPrefixSize_2095_, v___x_58202__boxed_2111_, v___x_2097_, v_a_2098_, v_e_2099_, v_xs_2100_, v_altBody_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v_xs_2100_);
lean_dec(v___x_2097_);
lean_dec(v_b_2093_);
lean_dec_ref(v___x_2092_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(lean_object* v_recFnName_2113_, lean_object* v_fixedPrefixSize_2114_, lean_object* v_e_2115_, lean_object* v_as_2116_, lean_object* v_bs_2117_, lean_object* v_i_2118_, lean_object* v_cs_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v___x_2129_; uint8_t v___x_2130_; 
v___x_2129_ = lean_array_get_size(v_as_2116_);
v___x_2130_ = lean_nat_dec_lt(v_i_2118_, v___x_2129_);
if (v___x_2130_ == 0)
{
lean_object* v___x_2131_; 
lean_dec(v_i_2118_);
lean_dec_ref(v_e_2115_);
lean_dec(v_fixedPrefixSize_2114_);
lean_dec(v_recFnName_2113_);
v___x_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2131_, 0, v_cs_2119_);
return v___x_2131_;
}
else
{
lean_object* v___x_2132_; uint8_t v___x_2133_; 
v___x_2132_ = lean_array_get_size(v_bs_2117_);
v___x_2133_ = lean_nat_dec_lt(v_i_2118_, v___x_2132_);
if (v___x_2133_ == 0)
{
lean_object* v___x_2134_; 
lean_dec(v_i_2118_);
lean_dec_ref(v_e_2115_);
lean_dec(v_fixedPrefixSize_2114_);
lean_dec(v_recFnName_2113_);
v___x_2134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2134_, 0, v_cs_2119_);
return v___x_2134_;
}
else
{
lean_object* v___x_2135_; lean_object* v_a_2136_; lean_object* v_b_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___f_2141_; uint8_t v___x_2142_; lean_object* v___x_2143_; 
v___x_2135_ = l_Lean_instInhabitedExpr;
v_a_2136_ = lean_array_fget_borrowed(v_as_2116_, v_i_2118_);
v_b_2137_ = lean_array_fget_borrowed(v_bs_2117_, v_i_2118_);
v___x_2138_ = lean_unsigned_to_nat(1u);
v___x_2139_ = lean_nat_add(v_b_2137_, v___x_2138_);
v___x_2140_ = lean_box(v___x_2133_);
lean_inc_ref(v_e_2115_);
lean_inc_n(v_a_2136_, 2);
lean_inc(v___x_2139_);
lean_inc(v_fixedPrefixSize_2114_);
lean_inc(v_recFnName_2113_);
lean_inc(v_b_2137_);
v___f_2141_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___boxed), 19, 8);
lean_closure_set(v___f_2141_, 0, v___x_2135_);
lean_closure_set(v___f_2141_, 1, v_b_2137_);
lean_closure_set(v___f_2141_, 2, v_recFnName_2113_);
lean_closure_set(v___f_2141_, 3, v_fixedPrefixSize_2114_);
lean_closure_set(v___f_2141_, 4, v___x_2140_);
lean_closure_set(v___f_2141_, 5, v___x_2139_);
lean_closure_set(v___f_2141_, 6, v_a_2136_);
lean_closure_set(v___f_2141_, 7, v_e_2115_);
v___x_2142_ = 0;
v___x_2143_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(v_a_2136_, v___x_2139_, v___f_2141_, v___x_2142_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2144_);
lean_dec_ref_known(v___x_2143_, 1);
v___x_2145_ = lean_nat_add(v_i_2118_, v___x_2138_);
lean_dec(v_i_2118_);
v___x_2146_ = lean_array_push(v_cs_2119_, v_a_2144_);
v_i_2118_ = v___x_2145_;
v_cs_2119_ = v___x_2146_;
goto _start;
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_dec_ref(v_cs_2119_);
lean_dec(v_i_2118_);
lean_dec_ref(v_e_2115_);
lean_dec(v_fixedPrefixSize_2114_);
lean_dec(v_recFnName_2113_);
v_a_2148_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2143_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2143_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(lean_object* v_recFnName_2156_, lean_object* v_fixedPrefixSize_2157_, lean_object* v_F_2158_, lean_object* v_e_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_){
_start:
{
switch(lean_obj_tag(v_e_2159_))
{
case 6:
{
lean_object* v_binderName_2169_; lean_object* v_binderType_2170_; lean_object* v_body_2171_; uint8_t v_binderInfo_2172_; lean_object* v___x_2173_; 
v_binderName_2169_ = lean_ctor_get(v_e_2159_, 0);
lean_inc(v_binderName_2169_);
v_binderType_2170_ = lean_ctor_get(v_e_2159_, 1);
lean_inc_ref(v_binderType_2170_);
v_body_2171_ = lean_ctor_get(v_e_2159_, 2);
lean_inc_ref(v_body_2171_);
v_binderInfo_2172_ = lean_ctor_get_uint8(v_e_2159_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2159_, 3);
lean_inc_ref(v_F_2158_);
lean_inc(v_fixedPrefixSize_2157_);
lean_inc(v_recFnName_2156_);
v___x_2173_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2156_, v_fixedPrefixSize_2157_, v_F_2158_, v_binderType_2170_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v_a_2174_; lean_object* v___f_2175_; uint8_t v___x_2176_; lean_object* v___x_2177_; 
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
lean_inc(v_a_2174_);
lean_dec_ref_known(v___x_2173_, 1);
v___f_2175_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0___boxed), 14, 4);
lean_closure_set(v___f_2175_, 0, v_body_2171_);
lean_closure_set(v___f_2175_, 1, v_recFnName_2156_);
lean_closure_set(v___f_2175_, 2, v_fixedPrefixSize_2157_);
lean_closure_set(v___f_2175_, 3, v_F_2158_);
v___x_2176_ = 0;
v___x_2177_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_binderName_2169_, v_binderInfo_2172_, v_a_2174_, v___f_2175_, v___x_2176_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
return v___x_2177_;
}
else
{
lean_dec_ref(v_body_2171_);
lean_dec(v_binderName_2169_);
lean_dec_ref(v_F_2158_);
lean_dec(v_fixedPrefixSize_2157_);
lean_dec(v_recFnName_2156_);
return v___x_2173_;
}
}
case 7:
{
lean_object* v_binderName_2178_; lean_object* v_binderType_2179_; lean_object* v_body_2180_; uint8_t v_binderInfo_2181_; lean_object* v___x_2182_; 
v_binderName_2178_ = lean_ctor_get(v_e_2159_, 0);
lean_inc(v_binderName_2178_);
v_binderType_2179_ = lean_ctor_get(v_e_2159_, 1);
lean_inc_ref(v_binderType_2179_);
v_body_2180_ = lean_ctor_get(v_e_2159_, 2);
lean_inc_ref(v_body_2180_);
v_binderInfo_2181_ = lean_ctor_get_uint8(v_e_2159_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2159_, 3);
lean_inc_ref(v_F_2158_);
lean_inc(v_fixedPrefixSize_2157_);
lean_inc(v_recFnName_2156_);
v___x_2182_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2156_, v_fixedPrefixSize_2157_, v_F_2158_, v_binderType_2179_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v_a_2183_; lean_object* v___f_2184_; uint8_t v___x_2185_; lean_object* v___x_2186_; 
v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
lean_inc(v_a_2183_);
lean_dec_ref_known(v___x_2182_, 1);
v___f_2184_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1___boxed), 14, 4);
lean_closure_set(v___f_2184_, 0, v_body_2180_);
lean_closure_set(v___f_2184_, 1, v_recFnName_2156_);
lean_closure_set(v___f_2184_, 2, v_fixedPrefixSize_2157_);
lean_closure_set(v___f_2184_, 3, v_F_2158_);
v___x_2185_ = 0;
v___x_2186_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_binderName_2178_, v_binderInfo_2181_, v_a_2183_, v___f_2184_, v___x_2185_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
return v___x_2186_;
}
else
{
lean_dec_ref(v_body_2180_);
lean_dec(v_binderName_2178_);
lean_dec_ref(v_F_2158_);
lean_dec(v_fixedPrefixSize_2157_);
lean_dec(v_recFnName_2156_);
return v___x_2182_;
}
}
case 8:
{
lean_object* v_declName_2187_; lean_object* v_type_2188_; lean_object* v_value_2189_; lean_object* v_body_2190_; uint8_t v_nondep_2191_; lean_object* v___x_2192_; 
v_declName_2187_ = lean_ctor_get(v_e_2159_, 0);
lean_inc(v_declName_2187_);
v_type_2188_ = lean_ctor_get(v_e_2159_, 1);
lean_inc_ref(v_type_2188_);
v_value_2189_ = lean_ctor_get(v_e_2159_, 2);
lean_inc_ref(v_value_2189_);
v_body_2190_ = lean_ctor_get(v_e_2159_, 3);
lean_inc_ref(v_body_2190_);
v_nondep_2191_ = lean_ctor_get_uint8(v_e_2159_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2159_, 4);
lean_inc_ref(v_F_2158_);
lean_inc(v_fixedPrefixSize_2157_);
lean_inc(v_recFnName_2156_);
v___x_2192_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2156_, v_fixedPrefixSize_2157_, v_F_2158_, v_type_2188_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v_a_2193_; lean_object* v___x_2194_; 
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_a_2193_);
lean_dec_ref_known(v___x_2192_, 1);
lean_inc_ref(v_F_2158_);
lean_inc(v_fixedPrefixSize_2157_);
lean_inc(v_recFnName_2156_);
v___x_2194_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2156_, v_fixedPrefixSize_2157_, v_F_2158_, v_value_2189_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; lean_object* v___f_2196_; uint8_t v___x_2197_; uint8_t v___x_2198_; lean_object* v___x_2199_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_a_2195_);
lean_dec_ref_known(v___x_2194_, 1);
v___f_2196_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2___boxed), 14, 4);
lean_closure_set(v___f_2196_, 0, v_body_2190_);
lean_closure_set(v___f_2196_, 1, v_recFnName_2156_);
lean_closure_set(v___f_2196_, 2, v_fixedPrefixSize_2157_);
lean_closure_set(v___f_2196_, 3, v_F_2158_);
v___x_2197_ = 0;
v___x_2198_ = 0;
v___x_2199_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(v_declName_2187_, v_a_2193_, v_a_2195_, v___f_2196_, v_nondep_2191_, v___x_2197_, v___x_2198_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
return v___x_2199_;
}
else
{
lean_dec(v_a_2193_);
lean_dec_ref(v_body_2190_);
lean_dec(v_declName_2187_);
lean_dec_ref(v_F_2158_);
lean_dec(v_fixedPrefixSize_2157_);
lean_dec(v_recFnName_2156_);
return v___x_2194_;
}
}
else
{
lean_dec_ref(v_body_2190_);
lean_dec_ref(v_value_2189_);
lean_dec(v_declName_2187_);
lean_dec_ref(v_F_2158_);
lean_dec(v_fixedPrefixSize_2157_);
lean_dec(v_recFnName_2156_);
return v___x_2192_;
}
}
case 10:
{
lean_object* v_data_2200_; lean_object* v_expr_2201_; lean_object* v___x_2202_; 
v_data_2200_ = lean_ctor_get(v_e_2159_, 0);
lean_inc(v_data_2200_);
v_expr_2201_ = lean_ctor_get(v_e_2159_, 1);
lean_inc_ref(v_expr_2201_);
v___x_2202_ = l_Lean_getRecAppSyntax_x3f(v_e_2159_);
lean_dec_ref_known(v_e_2159_, 2);
if (lean_obj_tag(v___x_2202_) == 1)
{
lean_object* v_val_2203_; lean_object* v_toCold_2204_; lean_object* v_options_2205_; lean_object* v_currRecDepth_2206_; lean_object* v_maxRecDepth_2207_; lean_object* v_ref_2208_; lean_object* v_currNamespace_2209_; lean_object* v_openDecls_2210_; lean_object* v_initHeartbeats_2211_; lean_object* v_maxHeartbeats_2212_; lean_object* v_currMacroScope_2213_; uint8_t v_diag_2214_; uint8_t v_suppressElabErrors_2215_; lean_object* v_ref_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
lean_dec(v_data_2200_);
v_val_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_val_2203_);
lean_dec_ref_known(v___x_2202_, 1);
v_toCold_2204_ = lean_ctor_get(v_a_2166_, 0);
v_options_2205_ = lean_ctor_get(v_a_2166_, 1);
v_currRecDepth_2206_ = lean_ctor_get(v_a_2166_, 2);
v_maxRecDepth_2207_ = lean_ctor_get(v_a_2166_, 3);
v_ref_2208_ = lean_ctor_get(v_a_2166_, 4);
v_currNamespace_2209_ = lean_ctor_get(v_a_2166_, 5);
v_openDecls_2210_ = lean_ctor_get(v_a_2166_, 6);
v_initHeartbeats_2211_ = lean_ctor_get(v_a_2166_, 7);
v_maxHeartbeats_2212_ = lean_ctor_get(v_a_2166_, 8);
v_currMacroScope_2213_ = lean_ctor_get(v_a_2166_, 9);
v_diag_2214_ = lean_ctor_get_uint8(v_a_2166_, sizeof(void*)*10);
v_suppressElabErrors_2215_ = lean_ctor_get_uint8(v_a_2166_, sizeof(void*)*10 + 1);
v_ref_2216_ = l_Lean_replaceRef(v_val_2203_, v_ref_2208_);
lean_dec(v_val_2203_);
lean_inc(v_currMacroScope_2213_);
lean_inc(v_maxHeartbeats_2212_);
lean_inc(v_initHeartbeats_2211_);
lean_inc(v_openDecls_2210_);
lean_inc(v_currNamespace_2209_);
lean_inc(v_maxRecDepth_2207_);
lean_inc(v_currRecDepth_2206_);
lean_inc_ref(v_options_2205_);
lean_inc_ref(v_toCold_2204_);
v___x_2217_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_2217_, 0, v_toCold_2204_);
lean_ctor_set(v___x_2217_, 1, v_options_2205_);
lean_ctor_set(v___x_2217_, 2, v_currRecDepth_2206_);
lean_ctor_set(v___x_2217_, 3, v_maxRecDepth_2207_);
lean_ctor_set(v___x_2217_, 4, v_ref_2216_);
lean_ctor_set(v___x_2217_, 5, v_currNamespace_2209_);
lean_ctor_set(v___x_2217_, 6, v_openDecls_2210_);
lean_ctor_set(v___x_2217_, 7, v_initHeartbeats_2211_);
lean_ctor_set(v___x_2217_, 8, v_maxHeartbeats_2212_);
lean_ctor_set(v___x_2217_, 9, v_currMacroScope_2213_);
lean_ctor_set_uint8(v___x_2217_, sizeof(void*)*10, v_diag_2214_);
lean_ctor_set_uint8(v___x_2217_, sizeof(void*)*10 + 1, v_suppressElabErrors_2215_);
v___x_2218_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2156_, v_fixedPrefixSize_2157_, v_F_2158_, v_expr_2201_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v___x_2217_, v_a_2167_);
lean_dec_ref_known(v___x_2217_, 10);
return v___x_2218_;
}
else
{
lean_object* v___x_2219_; 
lean_dec(v___x_2202_);
v___x_2219_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2156_, v_fixedPrefixSize_2157_, v_F_2158_, v_expr_2201_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2228_; 
v_a_2220_ = lean_ctor_get(v___x_2219_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2222_ = v___x_2219_;
v_isShared_2223_ = v_isSharedCheck_2228_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2219_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2228_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2224_; lean_object* v___x_2226_; 
v___x_2224_ = l_Lean_mkMData(v_data_2200_, v_a_2220_);
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 0, v___x_2224_);
v___x_2226_ = v___x_2222_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v___x_2224_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
else
{
lean_dec(v_data_2200_);
return v___x_2219_;
}
}
}
case 11:
{
lean_object* v_typeName_2229_; lean_object* v_idx_2230_; lean_object* v_struct_2231_; lean_object* v___x_2232_; 
v_typeName_2229_ = lean_ctor_get(v_e_2159_, 0);
lean_inc(v_typeName_2229_);
v_idx_2230_ = lean_ctor_get(v_e_2159_, 1);
lean_inc(v_idx_2230_);
v_struct_2231_ = lean_ctor_get(v_e_2159_, 2);
lean_inc_ref(v_struct_2231_);
lean_dec_ref_known(v_e_2159_, 3);
v___x_2232_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2156_, v_fixedPrefixSize_2157_, v_F_2158_, v_struct_2231_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2241_; 
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2235_ = v___x_2232_;
v_isShared_2236_ = v_isSharedCheck_2241_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2232_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2241_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2237_; lean_object* v___x_2239_; 
v___x_2237_ = l_Lean_mkProj(v_typeName_2229_, v_idx_2230_, v_a_2233_);
if (v_isShared_2236_ == 0)
{
lean_ctor_set(v___x_2235_, 0, v___x_2237_);
v___x_2239_ = v___x_2235_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2237_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
else
{
lean_dec(v_idx_2230_);
lean_dec(v_typeName_2229_);
return v___x_2232_;
}
}
case 4:
{
uint8_t v___x_2242_; 
v___x_2242_ = l_Lean_Expr_isConstOf(v_e_2159_, v_recFnName_2156_);
if (v___x_2242_ == 0)
{
lean_object* v___x_2243_; 
lean_dec_ref(v_F_2158_);
lean_dec(v_fixedPrefixSize_2157_);
lean_dec(v_recFnName_2156_);
v___x_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2243_, 0, v_e_2159_);
return v___x_2243_;
}
else
{
lean_object* v___x_2244_; 
v___x_2244_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2156_, v_fixedPrefixSize_2157_, v_F_2158_, v_e_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
return v___x_2244_;
}
}
case 5:
{
uint8_t v___x_2245_; lean_object* v___x_2246_; 
v___x_2245_ = 1;
lean_inc_ref(v_e_2159_);
v___x_2246_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(v_e_2159_, v___x_2245_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v_a_2247_; 
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
lean_inc(v_a_2247_);
lean_dec_ref_known(v___x_2246_, 1);
if (lean_obj_tag(v_a_2247_) == 0)
{
lean_object* v___x_2248_; 
v___x_2248_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2156_, v_fixedPrefixSize_2157_, v_F_2158_, v_e_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
return v___x_2248_;
}
else
{
lean_object* v_val_2249_; lean_object* v___x_2250_; 
v_val_2249_ = lean_ctor_get(v_a_2247_, 0);
lean_inc(v_val_2249_);
lean_dec_ref_known(v_a_2247_, 1);
lean_inc_ref(v_F_2158_);
v___x_2250_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_val_2249_, v_F_2158_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
if (lean_obj_tag(v___x_2250_) == 0)
{
lean_object* v_a_2251_; 
v_a_2251_ = lean_ctor_get(v___x_2250_, 0);
lean_inc(v_a_2251_);
lean_dec_ref_known(v___x_2250_, 1);
if (lean_obj_tag(v_a_2251_) == 1)
{
lean_object* v_val_2252_; lean_object* v_toMatcherInfo_2253_; lean_object* v_matcherName_2254_; lean_object* v_matcherLevels_2255_; lean_object* v_params_2256_; lean_object* v_motive_2257_; lean_object* v_discrs_2258_; lean_object* v_alts_2259_; lean_object* v_remaining_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v_val_2252_ = lean_ctor_get(v_a_2251_, 0);
lean_inc(v_val_2252_);
lean_dec_ref_known(v_a_2251_, 1);
v_toMatcherInfo_2253_ = lean_ctor_get(v_val_2252_, 0);
lean_inc_ref(v_toMatcherInfo_2253_);
v_matcherName_2254_ = lean_ctor_get(v_val_2252_, 1);
lean_inc(v_matcherName_2254_);
v_matcherLevels_2255_ = lean_ctor_get(v_val_2252_, 2);
lean_inc_ref(v_matcherLevels_2255_);
v_params_2256_ = lean_ctor_get(v_val_2252_, 3);
lean_inc_ref(v_params_2256_);
v_motive_2257_ = lean_ctor_get(v_val_2252_, 4);
lean_inc_ref(v_motive_2257_);
v_discrs_2258_ = lean_ctor_get(v_val_2252_, 5);
lean_inc_ref(v_discrs_2258_);
v_alts_2259_ = lean_ctor_get(v_val_2252_, 6);
lean_inc_ref(v_alts_2259_);
v_remaining_2260_ = lean_ctor_get(v_val_2252_, 7);
lean_inc_ref(v_remaining_2260_);
v___x_2261_ = l_Lean_Meta_MatcherApp_altNumParams(v_val_2252_);
v___x_2262_ = lean_unsigned_to_nat(0u);
v___x_2263_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
lean_inc(v_fixedPrefixSize_2157_);
lean_inc(v_recFnName_2156_);
v___x_2264_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(v_recFnName_2156_, v_fixedPrefixSize_2157_, v_e_2159_, v_alts_2259_, v___x_2261_, v___x_2262_, v___x_2263_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
lean_dec_ref(v___x_2261_);
lean_dec_ref(v_alts_2259_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v_a_2265_; size_t v_sz_2266_; size_t v___x_2267_; lean_object* v___x_2268_; 
v_a_2265_ = lean_ctor_get(v___x_2264_, 0);
lean_inc(v_a_2265_);
lean_dec_ref_known(v___x_2264_, 1);
v_sz_2266_ = lean_array_size(v_discrs_2258_);
v___x_2267_ = ((size_t)0ULL);
v___x_2268_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_2156_, v_fixedPrefixSize_2157_, v_F_2158_, v_sz_2266_, v___x_2267_, v_discrs_2258_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2278_; 
v_a_2269_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2271_ = v___x_2268_;
v_isShared_2272_ = v_isSharedCheck_2278_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___x_2268_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2278_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2276_; 
v___x_2273_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2273_, 0, v_toMatcherInfo_2253_);
lean_ctor_set(v___x_2273_, 1, v_matcherName_2254_);
lean_ctor_set(v___x_2273_, 2, v_matcherLevels_2255_);
lean_ctor_set(v___x_2273_, 3, v_params_2256_);
lean_ctor_set(v___x_2273_, 4, v_motive_2257_);
lean_ctor_set(v___x_2273_, 5, v_a_2269_);
lean_ctor_set(v___x_2273_, 6, v_a_2265_);
lean_ctor_set(v___x_2273_, 7, v_remaining_2260_);
v___x_2274_ = l_Lean_Meta_MatcherApp_toExpr(v___x_2273_);
if (v_isShared_2272_ == 0)
{
lean_ctor_set(v___x_2271_, 0, v___x_2274_);
v___x_2276_ = v___x_2271_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v___x_2274_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
}
else
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2286_; 
lean_dec(v_a_2265_);
lean_dec_ref(v_remaining_2260_);
lean_dec_ref(v_motive_2257_);
lean_dec_ref(v_params_2256_);
lean_dec_ref(v_matcherLevels_2255_);
lean_dec(v_matcherName_2254_);
lean_dec_ref(v_toMatcherInfo_2253_);
v_a_2279_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2281_ = v___x_2268_;
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2268_);
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
lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2294_; 
lean_dec_ref(v_remaining_2260_);
lean_dec_ref(v_discrs_2258_);
lean_dec_ref(v_motive_2257_);
lean_dec_ref(v_params_2256_);
lean_dec_ref(v_matcherLevels_2255_);
lean_dec(v_matcherName_2254_);
lean_dec_ref(v_toMatcherInfo_2253_);
lean_dec_ref(v_F_2158_);
lean_dec(v_fixedPrefixSize_2157_);
lean_dec(v_recFnName_2156_);
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
else
{
lean_object* v___x_2295_; 
lean_dec(v_a_2251_);
v___x_2295_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2156_, v_fixedPrefixSize_2157_, v_F_2158_, v_e_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
return v___x_2295_;
}
}
else
{
lean_object* v_a_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2303_; 
lean_dec_ref_known(v_e_2159_, 2);
lean_dec_ref(v_F_2158_);
lean_dec(v_fixedPrefixSize_2157_);
lean_dec(v_recFnName_2156_);
v_a_2296_ = lean_ctor_get(v___x_2250_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2298_ = v___x_2250_;
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_a_2296_);
lean_dec(v___x_2250_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2301_; 
if (v_isShared_2299_ == 0)
{
v___x_2301_ = v___x_2298_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_a_2296_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
return v___x_2301_;
}
}
}
}
}
else
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2311_; 
lean_dec_ref_known(v_e_2159_, 2);
lean_dec_ref(v_F_2158_);
lean_dec(v_fixedPrefixSize_2157_);
lean_dec(v_recFnName_2156_);
v_a_2304_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2306_ = v___x_2246_;
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2246_);
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
default: 
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
lean_dec_ref(v_F_2158_);
lean_dec(v_fixedPrefixSize_2157_);
v___x_2312_ = lean_unsigned_to_nat(1u);
v___x_2313_ = lean_mk_empty_array_with_capacity(v___x_2312_);
v___x_2314_ = lean_array_push(v___x_2313_, v_recFnName_2156_);
lean_inc_ref(v_e_2159_);
v___x_2315_ = l_Lean_Elab_ensureNoRecFn(v___x_2314_, v_e_2159_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2322_ == 0)
{
lean_object* v_unused_2323_; 
v_unused_2323_ = lean_ctor_get(v___x_2315_, 0);
lean_dec(v_unused_2323_);
v___x_2317_ = v___x_2315_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_dec(v___x_2315_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 0, v_e_2159_);
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_e_2159_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
else
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2331_; 
lean_dec_ref(v_e_2159_);
v_a_2324_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2326_ = v___x_2315_;
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2315_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2329_; 
if (v_isShared_2327_ == 0)
{
v___x_2329_ = v___x_2326_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2324_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(lean_object* v_recFnName_2332_, lean_object* v_fixedPrefixSize_2333_, lean_object* v_F_2334_, lean_object* v_e_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_){
_start:
{
lean_object* v___y_2346_; lean_object* v___y_2347_; lean_object* v___x_2364_; 
lean_inc_ref(v_e_2335_);
lean_inc(v_recFnName_2332_);
v___x_2364_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___redArg(v_recFnName_2332_, v_e_2335_, v_a_2336_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2452_; 
v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2367_ = v___x_2364_;
v_isShared_2368_ = v_isSharedCheck_2452_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2364_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2452_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
uint8_t v___x_2369_; 
v___x_2369_ = lean_unbox(v_a_2365_);
lean_dec(v_a_2365_);
if (v___x_2369_ == 0)
{
lean_object* v___x_2371_; 
lean_dec_ref(v_F_2334_);
lean_dec(v_fixedPrefixSize_2333_);
lean_dec(v_recFnName_2332_);
if (v_isShared_2368_ == 0)
{
lean_ctor_set(v___x_2367_, 0, v_e_2335_);
v___x_2371_ = v___x_2367_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_e_2335_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
else
{
lean_object* v___x_2373_; uint8_t v___x_2374_; lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___x_2430_; 
lean_del_object(v___x_2367_);
v___x_2373_ = lean_st_ref_get(v_a_2337_);
v___x_2374_ = 0;
v___x_2430_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v___x_2373_, v_e_2335_);
lean_dec(v___x_2373_);
if (lean_obj_tag(v___x_2430_) == 1)
{
lean_object* v_val_2431_; lean_object* v_fst_2432_; lean_object* v_snd_2433_; lean_object* v___x_2434_; 
v_val_2431_ = lean_ctor_get(v___x_2430_, 0);
lean_inc(v_val_2431_);
lean_dec_ref_known(v___x_2430_, 1);
v_fst_2432_ = lean_ctor_get(v_val_2431_, 0);
lean_inc(v_fst_2432_);
v_snd_2433_ = lean_ctor_get(v_val_2431_, 1);
lean_inc(v_snd_2433_);
lean_dec(v_val_2431_);
v___x_2434_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___redArg(v_snd_2433_, v_a_2340_);
lean_dec(v_snd_2433_);
if (lean_obj_tag(v___x_2434_) == 0)
{
lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2443_; 
v_a_2435_ = lean_ctor_get(v___x_2434_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2434_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2437_ = v___x_2434_;
v_isShared_2438_ = v_isSharedCheck_2443_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v___x_2434_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2443_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
uint8_t v___x_2439_; 
v___x_2439_ = lean_unbox(v_a_2435_);
lean_dec(v_a_2435_);
if (v___x_2439_ == 0)
{
lean_del_object(v___x_2437_);
lean_dec(v_fst_2432_);
v___y_2376_ = v_a_2336_;
v___y_2377_ = v_a_2337_;
v___y_2378_ = v_a_2338_;
v___y_2379_ = v_a_2339_;
v___y_2380_ = v_a_2340_;
v___y_2381_ = v_a_2341_;
v___y_2382_ = v_a_2342_;
v___y_2383_ = v_a_2343_;
goto v___jp_2375_;
}
else
{
lean_object* v___x_2441_; 
lean_dec_ref(v_e_2335_);
lean_dec_ref(v_F_2334_);
lean_dec(v_fixedPrefixSize_2333_);
lean_dec(v_recFnName_2332_);
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 0, v_fst_2432_);
v___x_2441_ = v___x_2437_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_fst_2432_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
}
else
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2451_; 
lean_dec(v_fst_2432_);
lean_dec_ref(v_e_2335_);
lean_dec_ref(v_F_2334_);
lean_dec(v_fixedPrefixSize_2333_);
lean_dec(v_recFnName_2332_);
v_a_2444_ = lean_ctor_get(v___x_2434_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2434_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2446_ = v___x_2434_;
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2434_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2449_; 
if (v_isShared_2447_ == 0)
{
v___x_2449_ = v___x_2446_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_a_2444_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
}
else
{
lean_dec(v___x_2430_);
v___y_2376_ = v_a_2336_;
v___y_2377_ = v_a_2337_;
v___y_2378_ = v_a_2338_;
v___y_2379_ = v_a_2339_;
v___y_2380_ = v_a_2340_;
v___y_2381_ = v_a_2341_;
v___y_2382_ = v_a_2342_;
v___y_2383_ = v_a_2343_;
goto v___jp_2375_;
}
v___jp_2375_:
{
lean_object* v___x_2384_; 
lean_inc_ref(v_e_2335_);
v___x_2384_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(v_recFnName_2332_, v_fixedPrefixSize_2333_, v_F_2334_, v_e_2335_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_object* v_a_2385_; lean_object* v___x_2386_; 
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
lean_inc(v_a_2385_);
lean_dec_ref_known(v___x_2384_, 1);
v___x_2386_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId(v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2421_; 
v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2389_ = v___x_2386_;
v_isShared_2390_ = v_isSharedCheck_2421_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2386_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2421_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v_options_2395_; lean_object* v___x_2396_; uint8_t v___x_2397_; 
v___x_2391_ = lean_st_ref_take(v___y_2377_);
lean_inc(v_a_2385_);
v___x_2392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2392_, 0, v_a_2385_);
lean_ctor_set(v___x_2392_, 1, v_a_2387_);
lean_inc_ref(v_e_2335_);
v___x_2393_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4___redArg(v___x_2391_, v_e_2335_, v___x_2392_);
v___x_2394_ = lean_st_ref_put(v___y_2377_, v___x_2393_);
v_options_2395_ = lean_ctor_get(v___y_2382_, 1);
v___x_2396_ = l_Lean_Elab_WF_debug_definition_wf_replaceRecApps;
v___x_2397_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v_options_2395_, v___x_2396_);
if (v___x_2397_ == 0)
{
lean_object* v___x_2399_; 
lean_dec_ref(v_e_2335_);
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 0, v_a_2385_);
v___x_2399_ = v___x_2389_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_a_2385_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
else
{
lean_object* v___x_2401_; uint8_t v_transparency_2402_; lean_object* v___f_2403_; uint8_t v___x_2404_; uint8_t v___x_2405_; 
lean_del_object(v___x_2389_);
v___x_2401_ = l_Lean_Meta_Context_config(v___y_2380_);
v_transparency_2402_ = lean_ctor_get_uint8(v___x_2401_, 9);
lean_dec_ref(v___x_2401_);
lean_inc(v_a_2385_);
v___f_2403_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___boxed), 11, 2);
lean_closure_set(v___f_2403_, 0, v_a_2385_);
lean_closure_set(v___f_2403_, 1, v_e_2335_);
v___x_2404_ = 0;
v___x_2405_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2402_, v___x_2404_);
if (v___x_2405_ == 0)
{
lean_object* v_keyedConfig_2406_; uint8_t v_trackZetaDelta_2407_; lean_object* v_zetaDeltaSet_2408_; lean_object* v_lctx_2409_; lean_object* v_localInstances_2410_; lean_object* v_defEqCtx_x3f_2411_; lean_object* v_synthPendingDepth_2412_; lean_object* v_customCanUnfoldPredicate_x3f_2413_; uint8_t v_univApprox_2414_; uint8_t v_inTypeClassResolution_2415_; uint8_t v_cacheInferType_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v_keyedConfig_2406_ = lean_ctor_get(v___y_2380_, 0);
v_trackZetaDelta_2407_ = lean_ctor_get_uint8(v___y_2380_, sizeof(void*)*7);
v_zetaDeltaSet_2408_ = lean_ctor_get(v___y_2380_, 1);
v_lctx_2409_ = lean_ctor_get(v___y_2380_, 2);
v_localInstances_2410_ = lean_ctor_get(v___y_2380_, 3);
v_defEqCtx_x3f_2411_ = lean_ctor_get(v___y_2380_, 4);
v_synthPendingDepth_2412_ = lean_ctor_get(v___y_2380_, 5);
v_customCanUnfoldPredicate_x3f_2413_ = lean_ctor_get(v___y_2380_, 6);
v_univApprox_2414_ = lean_ctor_get_uint8(v___y_2380_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2415_ = lean_ctor_get_uint8(v___y_2380_, sizeof(void*)*7 + 2);
v_cacheInferType_2416_ = lean_ctor_get_uint8(v___y_2380_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2406_);
v___x_2417_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2404_, v_keyedConfig_2406_);
lean_inc(v_customCanUnfoldPredicate_x3f_2413_);
lean_inc(v_synthPendingDepth_2412_);
lean_inc(v_defEqCtx_x3f_2411_);
lean_inc_ref(v_localInstances_2410_);
lean_inc_ref(v_lctx_2409_);
lean_inc(v_zetaDeltaSet_2408_);
v___x_2418_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2418_, 0, v___x_2417_);
lean_ctor_set(v___x_2418_, 1, v_zetaDeltaSet_2408_);
lean_ctor_set(v___x_2418_, 2, v_lctx_2409_);
lean_ctor_set(v___x_2418_, 3, v_localInstances_2410_);
lean_ctor_set(v___x_2418_, 4, v_defEqCtx_x3f_2411_);
lean_ctor_set(v___x_2418_, 5, v_synthPendingDepth_2412_);
lean_ctor_set(v___x_2418_, 6, v_customCanUnfoldPredicate_x3f_2413_);
lean_ctor_set_uint8(v___x_2418_, sizeof(void*)*7, v_trackZetaDelta_2407_);
lean_ctor_set_uint8(v___x_2418_, sizeof(void*)*7 + 1, v_univApprox_2414_);
lean_ctor_set_uint8(v___x_2418_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2415_);
lean_ctor_set_uint8(v___x_2418_, sizeof(void*)*7 + 3, v_cacheInferType_2416_);
v___x_2419_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v___f_2403_, v___x_2374_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___x_2418_, v___y_2381_, v___y_2382_, v___y_2383_);
lean_dec_ref_known(v___x_2418_, 7);
v___y_2346_ = v_a_2385_;
v___y_2347_ = v___x_2419_;
goto v___jp_2345_;
}
else
{
lean_object* v___x_2420_; 
v___x_2420_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v___f_2403_, v___x_2374_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
v___y_2346_ = v_a_2385_;
v___y_2347_ = v___x_2420_;
goto v___jp_2345_;
}
}
}
}
else
{
lean_object* v_a_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2429_; 
lean_dec(v_a_2385_);
lean_dec_ref(v_e_2335_);
v_a_2422_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2424_ = v___x_2386_;
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_a_2422_);
lean_dec(v___x_2386_);
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
else
{
lean_dec_ref(v_e_2335_);
return v___x_2384_;
}
}
}
}
}
else
{
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2460_; 
lean_dec_ref(v_e_2335_);
lean_dec_ref(v_F_2334_);
lean_dec(v_fixedPrefixSize_2333_);
lean_dec(v_recFnName_2332_);
v_a_2453_ = lean_ctor_get(v___x_2364_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2455_ = v___x_2364_;
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2364_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2458_; 
if (v_isShared_2456_ == 0)
{
v___x_2458_ = v___x_2455_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_a_2453_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
}
v___jp_2345_:
{
if (lean_obj_tag(v___y_2347_) == 0)
{
lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2354_; 
v_isSharedCheck_2354_ = !lean_is_exclusive(v___y_2347_);
if (v_isSharedCheck_2354_ == 0)
{
lean_object* v_unused_2355_; 
v_unused_2355_ = lean_ctor_get(v___y_2347_, 0);
lean_dec(v_unused_2355_);
v___x_2349_ = v___y_2347_;
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
else
{
lean_dec(v___y_2347_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2352_; 
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 0, v___y_2346_);
v___x_2352_ = v___x_2349_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v___y_2346_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
else
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2363_; 
lean_dec_ref(v___y_2346_);
v_a_2356_ = lean_ctor_get(v___y_2347_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___y_2347_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2358_ = v___y_2347_;
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___y_2347_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2361_; 
if (v_isShared_2359_ == 0)
{
v___x_2361_ = v___x_2358_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_a_2356_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2(lean_object* v_body_2461_, lean_object* v_recFnName_2462_, lean_object* v_fixedPrefixSize_2463_, lean_object* v_F_2464_, lean_object* v_x_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_){
_start:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2475_ = lean_expr_instantiate1(v_body_2461_, v_x_2465_);
v___x_2476_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2462_, v_fixedPrefixSize_2463_, v_F_2464_, v___x_2475_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_);
return v___x_2476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp___boxed(lean_object* v_recFnName_2477_, lean_object* v_fixedPrefixSize_2478_, lean_object* v_F_2479_, lean_object* v_e_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2477_, v_fixedPrefixSize_2478_, v_F_2479_, v_e_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_);
lean_dec(v_a_2488_);
lean_dec_ref(v_a_2487_);
lean_dec(v_a_2486_);
lean_dec_ref(v_a_2485_);
lean_dec(v_a_2484_);
lean_dec_ref(v_a_2483_);
lean_dec(v_a_2482_);
lean_dec(v_a_2481_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1___boxed(lean_object* v_recFnName_2491_, lean_object* v_fixedPrefixSize_2492_, lean_object* v_F_2493_, lean_object* v_sz_2494_, lean_object* v_i_2495_, lean_object* v_bs_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
size_t v_sz_boxed_2506_; size_t v_i_boxed_2507_; lean_object* v_res_2508_; 
v_sz_boxed_2506_ = lean_unbox_usize(v_sz_2494_);
lean_dec(v_sz_2494_);
v_i_boxed_2507_ = lean_unbox_usize(v_i_2495_);
lean_dec(v_i_2495_);
v_res_2508_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_2491_, v_fixedPrefixSize_2492_, v_F_2493_, v_sz_boxed_2506_, v_i_boxed_2507_, v_bs_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec(v___y_2497_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16___boxed(lean_object* v_recFnName_2509_, lean_object* v_fixedPrefixSize_2510_, lean_object* v_F_2511_, lean_object* v_x_2512_, lean_object* v_x_2513_, lean_object* v_x_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(v_recFnName_2509_, v_fixedPrefixSize_2510_, v_F_2511_, v_x_2512_, v_x_2513_, v_x_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
lean_dec(v___y_2516_);
lean_dec(v___y_2515_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___boxed(lean_object* v_recFnName_2525_, lean_object* v_fixedPrefixSize_2526_, lean_object* v_e_2527_, lean_object* v_as_2528_, lean_object* v_bs_2529_, lean_object* v_i_2530_, lean_object* v_cs_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_){
_start:
{
lean_object* v_res_2541_; 
v_res_2541_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(v_recFnName_2525_, v_fixedPrefixSize_2526_, v_e_2527_, v_as_2528_, v_bs_2529_, v_i_2530_, v_cs_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
lean_dec(v___y_2533_);
lean_dec(v___y_2532_);
lean_dec_ref(v_bs_2529_);
lean_dec_ref(v_as_2528_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___boxed(lean_object* v_recFnName_2542_, lean_object* v_fixedPrefixSize_2543_, lean_object* v_F_2544_, lean_object* v_e_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2542_, v_fixedPrefixSize_2543_, v_F_2544_, v_e_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_);
lean_dec(v_a_2553_);
lean_dec_ref(v_a_2552_);
lean_dec(v_a_2551_);
lean_dec_ref(v_a_2550_);
lean_dec(v_a_2549_);
lean_dec_ref(v_a_2548_);
lean_dec(v_a_2547_);
lean_dec(v_a_2546_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___boxed(lean_object* v_recFnName_2556_, lean_object* v_fixedPrefixSize_2557_, lean_object* v_F_2558_, lean_object* v_e_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_){
_start:
{
lean_object* v_res_2569_; 
v_res_2569_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2556_, v_fixedPrefixSize_2557_, v_F_2558_, v_e_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_);
lean_dec(v_a_2567_);
lean_dec_ref(v_a_2566_);
lean_dec(v_a_2565_);
lean_dec_ref(v_a_2564_);
lean_dec(v_a_2563_);
lean_dec_ref(v_a_2562_);
lean_dec(v_a_2561_);
lean_dec(v_a_2560_);
return v_res_2569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___boxed(lean_object* v_recFnName_2570_, lean_object* v_fixedPrefixSize_2571_, lean_object* v_F_2572_, lean_object* v_e_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_){
_start:
{
lean_object* v_res_2583_; 
v_res_2583_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(v_recFnName_2570_, v_fixedPrefixSize_2571_, v_F_2572_, v_e_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_);
lean_dec(v_a_2581_);
lean_dec_ref(v_a_2580_);
lean_dec(v_a_2579_);
lean_dec_ref(v_a_2578_);
lean_dec(v_a_2577_);
lean_dec_ref(v_a_2576_);
lean_dec(v_a_2575_);
lean_dec(v_a_2574_);
return v_res_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7(lean_object* v_00_u03b1_2584_, lean_object* v_k_2585_, uint8_t v_allowLevelAssignments_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
lean_object* v___x_2596_; 
v___x_2596_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v_k_2585_, v_allowLevelAssignments_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
return v___x_2596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___boxed(lean_object* v_00_u03b1_2597_, lean_object* v_k_2598_, lean_object* v_allowLevelAssignments_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2609_; lean_object* v_res_2610_; 
v_allowLevelAssignments_boxed_2609_ = lean_unbox(v_allowLevelAssignments_2599_);
v_res_2610_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7(v_00_u03b1_2597_, v_k_2598_, v_allowLevelAssignments_boxed_2609_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
lean_dec(v___y_2601_);
lean_dec(v___y_2600_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10(lean_object* v_00_u03b1_2611_, lean_object* v_name_2612_, uint8_t v_bi_2613_, lean_object* v_type_2614_, lean_object* v_k_2615_, uint8_t v_kind_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
lean_object* v___x_2626_; 
v___x_2626_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_name_2612_, v_bi_2613_, v_type_2614_, v_k_2615_, v_kind_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
return v___x_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___boxed(lean_object* v_00_u03b1_2627_, lean_object* v_name_2628_, lean_object* v_bi_2629_, lean_object* v_type_2630_, lean_object* v_k_2631_, lean_object* v_kind_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
uint8_t v_bi_boxed_2642_; uint8_t v_kind_boxed_2643_; lean_object* v_res_2644_; 
v_bi_boxed_2642_ = lean_unbox(v_bi_2629_);
v_kind_boxed_2643_ = lean_unbox(v_kind_2632_);
v_res_2644_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10(v_00_u03b1_2627_, v_name_2628_, v_bi_boxed_2642_, v_type_2630_, v_k_2631_, v_kind_boxed_2643_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec(v___y_2633_);
return v_res_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(lean_object* v_00_u03b1_2645_, lean_object* v_e_2646_, lean_object* v_maxFVars_2647_, lean_object* v_k_2648_, uint8_t v_cleanupAnnotations_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_){
_start:
{
lean_object* v___x_2659_; 
v___x_2659_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(v_e_2646_, v_maxFVars_2647_, v_k_2648_, v_cleanupAnnotations_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
return v___x_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___boxed(lean_object* v_00_u03b1_2660_, lean_object* v_e_2661_, lean_object* v_maxFVars_2662_, lean_object* v_k_2663_, lean_object* v_cleanupAnnotations_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2674_; lean_object* v_res_2675_; 
v_cleanupAnnotations_boxed_2674_ = lean_unbox(v_cleanupAnnotations_2664_);
v_res_2675_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(v_00_u03b1_2660_, v_e_2661_, v_maxFVars_2662_, v_k_2663_, v_cleanupAnnotations_boxed_2674_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v___y_2666_);
lean_dec(v___y_2665_);
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0(lean_object* v_inst_2676_, lean_object* v_R_2677_, lean_object* v_a_2678_, lean_object* v_b_2679_){
_start:
{
lean_object* v___x_2680_; 
v___x_2680_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(v_a_2678_, v_b_2679_);
return v___x_2680_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2(lean_object* v_cls_2681_, lean_object* v_msg_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_){
_start:
{
lean_object* v___x_2692_; 
v___x_2692_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(v_cls_2681_, v_msg_2682_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___boxed(lean_object* v_cls_2693_, lean_object* v_msg_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
lean_object* v_res_2704_; 
v_res_2704_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2(v_cls_2693_, v_msg_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_);
lean_dec(v___y_2702_);
lean_dec_ref(v___y_2701_);
lean_dec(v___y_2700_);
lean_dec_ref(v___y_2699_);
lean_dec(v___y_2698_);
lean_dec_ref(v___y_2697_);
lean_dec(v___y_2696_);
lean_dec(v___y_2695_);
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4(lean_object* v_00_u03b2_2705_, lean_object* v_m_2706_, lean_object* v_a_2707_, lean_object* v_b_2708_){
_start:
{
lean_object* v___x_2709_; 
v___x_2709_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4___redArg(v_m_2706_, v_a_2707_, v_b_2708_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(lean_object* v_00_u03b1_2710_, lean_object* v_msg_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
lean_object* v___x_2721_; 
v___x_2721_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v_msg_2711_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___boxed(lean_object* v_00_u03b1_2722_, lean_object* v_msg_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_){
_start:
{
lean_object* v_res_2733_; 
v_res_2733_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(v_00_u03b1_2722_, v_msg_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec(v___y_2724_);
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8(lean_object* v_00_u03b2_2734_, lean_object* v_m_2735_, lean_object* v_a_2736_){
_start:
{
lean_object* v___x_2737_; 
v___x_2737_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v_m_2735_, v_a_2736_);
return v___x_2737_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___boxed(lean_object* v_00_u03b2_2738_, lean_object* v_m_2739_, lean_object* v_a_2740_){
_start:
{
lean_object* v_res_2741_; 
v_res_2741_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8(v_00_u03b2_2738_, v_m_2739_, v_a_2740_);
lean_dec_ref(v_a_2740_);
lean_dec_ref(v_m_2739_);
return v_res_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15(lean_object* v_00_u03b1_2742_, lean_object* v_name_2743_, lean_object* v_type_2744_, lean_object* v_val_2745_, lean_object* v_k_2746_, uint8_t v_nondep_2747_, uint8_t v_kind_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_){
_start:
{
lean_object* v___x_2758_; 
v___x_2758_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(v_name_2743_, v_type_2744_, v_val_2745_, v_k_2746_, v_nondep_2747_, v_kind_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___boxed(lean_object* v_00_u03b1_2759_, lean_object* v_name_2760_, lean_object* v_type_2761_, lean_object* v_val_2762_, lean_object* v_k_2763_, lean_object* v_nondep_2764_, lean_object* v_kind_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
uint8_t v_nondep_boxed_2775_; uint8_t v_kind_boxed_2776_; lean_object* v_res_2777_; 
v_nondep_boxed_2775_ = lean_unbox(v_nondep_2764_);
v_kind_boxed_2776_ = lean_unbox(v_kind_2765_);
v_res_2777_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15(v_00_u03b1_2759_, v_name_2760_, v_type_2761_, v_val_2762_, v_k_2763_, v_nondep_boxed_2775_, v_kind_boxed_2776_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20(lean_object* v_declName_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
lean_object* v___x_2788_; 
v___x_2788_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(v_declName_2778_, v___y_2786_);
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___boxed(lean_object* v_declName_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20(v_declName_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec(v___y_2793_);
lean_dec_ref(v___y_2792_);
lean_dec(v___y_2791_);
lean_dec(v___y_2790_);
return v_res_2799_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4(lean_object* v_00_u03b2_2800_, lean_object* v_a_2801_, lean_object* v_x_2802_){
_start:
{
uint8_t v___x_2803_; 
v___x_2803_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg(v_a_2801_, v_x_2802_);
return v___x_2803_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___boxed(lean_object* v_00_u03b2_2804_, lean_object* v_a_2805_, lean_object* v_x_2806_){
_start:
{
uint8_t v_res_2807_; lean_object* v_r_2808_; 
v_res_2807_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4(v_00_u03b2_2804_, v_a_2805_, v_x_2806_);
lean_dec(v_x_2806_);
lean_dec_ref(v_a_2805_);
v_r_2808_ = lean_box(v_res_2807_);
return v_r_2808_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5(lean_object* v_00_u03b2_2809_, lean_object* v_data_2810_){
_start:
{
lean_object* v___x_2811_; 
v___x_2811_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5___redArg(v_data_2810_);
return v___x_2811_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6(lean_object* v_00_u03b2_2812_, lean_object* v_a_2813_, lean_object* v_b_2814_, lean_object* v_x_2815_){
_start:
{
lean_object* v___x_2816_; 
v___x_2816_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6___redArg(v_a_2813_, v_b_2814_, v_x_2815_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11(lean_object* v_00_u03b2_2817_, lean_object* v_a_2818_, lean_object* v_x_2819_){
_start:
{
lean_object* v___x_2820_; 
v___x_2820_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(v_a_2818_, v_x_2819_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___boxed(lean_object* v_00_u03b2_2821_, lean_object* v_a_2822_, lean_object* v_x_2823_){
_start:
{
lean_object* v_res_2824_; 
v_res_2824_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11(v_00_u03b2_2821_, v_a_2822_, v_x_2823_);
lean_dec(v_x_2823_);
lean_dec_ref(v_a_2822_);
return v_res_2824_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12(lean_object* v_00_u03b2_2825_, lean_object* v_i_2826_, lean_object* v_source_2827_, lean_object* v_target_2828_){
_start:
{
lean_object* v___x_2829_; 
v___x_2829_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12___redArg(v_i_2826_, v_source_2827_, v_target_2828_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21(lean_object* v_00_u03b1_2830_, lean_object* v_constName_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_){
_start:
{
lean_object* v___x_2841_; 
v___x_2841_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(v_constName_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___boxed(lean_object* v_00_u03b1_2842_, lean_object* v_constName_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21(v_00_u03b1_2842_, v_constName_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec(v___y_2844_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12_spec__22(lean_object* v_00_u03b2_2854_, lean_object* v_x_2855_, lean_object* v_x_2856_){
_start:
{
lean_object* v___x_2857_; 
v___x_2857_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12_spec__22___redArg(v_x_2855_, v_x_2856_);
return v___x_2857_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27(lean_object* v_00_u03b1_2858_, lean_object* v_ref_2859_, lean_object* v_constName_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
lean_object* v___x_2870_; 
v___x_2870_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(v_ref_2859_, v_constName_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___boxed(lean_object* v_00_u03b1_2871_, lean_object* v_ref_2872_, lean_object* v_constName_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_){
_start:
{
lean_object* v_res_2883_; 
v_res_2883_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27(v_00_u03b1_2871_, v_ref_2872_, v_constName_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec(v_ref_2872_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29(lean_object* v_00_u03b1_2884_, lean_object* v_ref_2885_, lean_object* v_msg_2886_, lean_object* v_declHint_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_){
_start:
{
lean_object* v___x_2897_; 
v___x_2897_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(v_ref_2885_, v_msg_2886_, v_declHint_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___boxed(lean_object* v_00_u03b1_2898_, lean_object* v_ref_2899_, lean_object* v_msg_2900_, lean_object* v_declHint_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_){
_start:
{
lean_object* v_res_2911_; 
v_res_2911_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29(v_00_u03b1_2898_, v_ref_2899_, v_msg_2900_, v_declHint_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_);
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec(v___y_2903_);
lean_dec(v___y_2902_);
lean_dec(v_ref_2899_);
return v_res_2911_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31(lean_object* v_msg_2912_, lean_object* v_declHint_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_){
_start:
{
lean_object* v___x_2923_; 
v___x_2923_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(v_msg_2912_, v_declHint_2913_, v___y_2921_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___boxed(lean_object* v_msg_2924_, lean_object* v_declHint_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_){
_start:
{
lean_object* v_res_2935_; 
v_res_2935_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31(v_msg_2924_, v_declHint_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec(v___y_2926_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31(lean_object* v_00_u03b1_2936_, lean_object* v_ref_2937_, lean_object* v_msg_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
lean_object* v___x_2948_; 
v___x_2948_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(v_ref_2937_, v_msg_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___boxed(lean_object* v_00_u03b1_2949_, lean_object* v_ref_2950_, lean_object* v_msg_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31(v_00_u03b1_2949_, v_ref_2950_, v_msg_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec(v_ref_2950_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(lean_object* v_cls_2962_, lean_object* v_msg_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v_ref_2969_; lean_object* v___x_2970_; lean_object* v_a_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_3015_; 
v_ref_2969_ = lean_ctor_get(v___y_2966_, 4);
v___x_2970_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
v_a_2971_ = lean_ctor_get(v___x_2970_, 0);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_2973_ = v___x_2970_;
v_isShared_2974_ = v_isSharedCheck_3015_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_a_2971_);
lean_dec(v___x_2970_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_3015_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2975_; lean_object* v_traceState_2976_; lean_object* v_env_2977_; lean_object* v_nextMacroScope_2978_; lean_object* v_ngen_2979_; lean_object* v_auxDeclNGen_2980_; lean_object* v_cache_2981_; lean_object* v_messages_2982_; lean_object* v_infoState_2983_; lean_object* v_snapshotTasks_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_3014_; 
v___x_2975_ = lean_st_ref_take(v___y_2967_);
v_traceState_2976_ = lean_ctor_get(v___x_2975_, 4);
v_env_2977_ = lean_ctor_get(v___x_2975_, 0);
v_nextMacroScope_2978_ = lean_ctor_get(v___x_2975_, 1);
v_ngen_2979_ = lean_ctor_get(v___x_2975_, 2);
v_auxDeclNGen_2980_ = lean_ctor_get(v___x_2975_, 3);
v_cache_2981_ = lean_ctor_get(v___x_2975_, 5);
v_messages_2982_ = lean_ctor_get(v___x_2975_, 6);
v_infoState_2983_ = lean_ctor_get(v___x_2975_, 7);
v_snapshotTasks_2984_ = lean_ctor_get(v___x_2975_, 8);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_2986_ = v___x_2975_;
v_isShared_2987_ = v_isSharedCheck_3014_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_snapshotTasks_2984_);
lean_inc(v_infoState_2983_);
lean_inc(v_messages_2982_);
lean_inc(v_cache_2981_);
lean_inc(v_traceState_2976_);
lean_inc(v_auxDeclNGen_2980_);
lean_inc(v_ngen_2979_);
lean_inc(v_nextMacroScope_2978_);
lean_inc(v_env_2977_);
lean_dec(v___x_2975_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_3014_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
uint64_t v_tid_2988_; lean_object* v_traces_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_3013_; 
v_tid_2988_ = lean_ctor_get_uint64(v_traceState_2976_, sizeof(void*)*1);
v_traces_2989_ = lean_ctor_get(v_traceState_2976_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v_traceState_2976_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_2991_ = v_traceState_2976_;
v_isShared_2992_ = v_isSharedCheck_3013_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_traces_2989_);
lean_dec(v_traceState_2976_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_3013_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2993_; double v___x_2994_; uint8_t v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3003_; 
v___x_2993_ = lean_box(0);
v___x_2994_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0);
v___x_2995_ = 0;
v___x_2996_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__1));
v___x_2997_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2997_, 0, v_cls_2962_);
lean_ctor_set(v___x_2997_, 1, v___x_2993_);
lean_ctor_set(v___x_2997_, 2, v___x_2996_);
lean_ctor_set_float(v___x_2997_, sizeof(void*)*3, v___x_2994_);
lean_ctor_set_float(v___x_2997_, sizeof(void*)*3 + 8, v___x_2994_);
lean_ctor_set_uint8(v___x_2997_, sizeof(void*)*3 + 16, v___x_2995_);
v___x_2998_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__2));
v___x_2999_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2999_, 0, v___x_2997_);
lean_ctor_set(v___x_2999_, 1, v_a_2971_);
lean_ctor_set(v___x_2999_, 2, v___x_2998_);
lean_inc(v_ref_2969_);
v___x_3000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3000_, 0, v_ref_2969_);
lean_ctor_set(v___x_3000_, 1, v___x_2999_);
v___x_3001_ = l_Lean_PersistentArray_push___redArg(v_traces_2989_, v___x_3000_);
if (v_isShared_2992_ == 0)
{
lean_ctor_set(v___x_2991_, 0, v___x_3001_);
v___x_3003_ = v___x_2991_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v___x_3001_);
lean_ctor_set_uint64(v_reuseFailAlloc_3012_, sizeof(void*)*1, v_tid_2988_);
v___x_3003_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
lean_object* v___x_3005_; 
if (v_isShared_2987_ == 0)
{
lean_ctor_set(v___x_2986_, 4, v___x_3003_);
v___x_3005_ = v___x_2986_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_env_2977_);
lean_ctor_set(v_reuseFailAlloc_3011_, 1, v_nextMacroScope_2978_);
lean_ctor_set(v_reuseFailAlloc_3011_, 2, v_ngen_2979_);
lean_ctor_set(v_reuseFailAlloc_3011_, 3, v_auxDeclNGen_2980_);
lean_ctor_set(v_reuseFailAlloc_3011_, 4, v___x_3003_);
lean_ctor_set(v_reuseFailAlloc_3011_, 5, v_cache_2981_);
lean_ctor_set(v_reuseFailAlloc_3011_, 6, v_messages_2982_);
lean_ctor_set(v_reuseFailAlloc_3011_, 7, v_infoState_2983_);
lean_ctor_set(v_reuseFailAlloc_3011_, 8, v_snapshotTasks_2984_);
v___x_3005_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3009_; 
v___x_3006_ = lean_st_ref_put(v___y_2967_, v___x_3005_);
v___x_3007_ = lean_box(0);
if (v_isShared_2974_ == 0)
{
lean_ctor_set(v___x_2973_, 0, v___x_3007_);
v___x_3009_ = v___x_2973_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v___x_3007_);
v___x_3009_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
return v___x_3009_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg___boxed(lean_object* v_cls_3016_, lean_object* v_msg_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_){
_start:
{
lean_object* v_res_3023_; 
v_res_3023_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3016_, v_msg_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_);
lean_dec(v___y_3021_);
lean_dec_ref(v___y_3020_);
lean_dec(v___y_3019_);
lean_dec_ref(v___y_3018_);
return v_res_3023_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0(void){
_start:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3024_ = lean_box(0);
v___x_3025_ = lean_unsigned_to_nat(16u);
v___x_3026_ = lean_mk_array(v___x_3025_, v___x_3024_);
return v___x_3026_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1(void){
_start:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3027_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0);
v___x_3028_ = lean_unsigned_to_nat(0u);
v___x_3029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3028_);
lean_ctor_set(v___x_3029_, 1, v___x_3027_);
return v___x_3029_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3(void){
_start:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3031_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__2));
v___x_3032_ = l_Lean_stringToMessageData(v___x_3031_);
return v___x_3032_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5(void){
_start:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3034_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__4));
v___x_3035_ = l_Lean_stringToMessageData(v___x_3034_);
return v___x_3035_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7(void){
_start:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3037_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__6));
v___x_3038_ = l_Lean_stringToMessageData(v___x_3037_);
return v___x_3038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(lean_object* v_recFnName_3039_, lean_object* v_fixedPrefixSize_3040_, lean_object* v_F_3041_, lean_object* v_e_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_){
_start:
{
lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v_options_3071_; uint8_t v_hasTrace_3072_; 
v_options_3071_ = lean_ctor_get(v_a_3047_, 1);
v_hasTrace_3072_ = lean_ctor_get_uint8(v_options_3071_, sizeof(void*)*1);
if (v_hasTrace_3072_ == 0)
{
v___y_3051_ = v_a_3043_;
v___y_3052_ = v_a_3044_;
v___y_3053_ = v_a_3045_;
v___y_3054_ = v_a_3046_;
v___y_3055_ = v_a_3047_;
v___y_3056_ = v_a_3048_;
goto v___jp_3050_;
}
else
{
lean_object* v_toCold_3073_; lean_object* v_inheritedTraceOptions_3074_; lean_object* v_cls_3075_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v_inheritedTraceOptions_3082_; lean_object* v_options_3083_; lean_object* v___y_3084_; lean_object* v___x_3105_; uint8_t v___x_3106_; 
v_toCold_3073_ = lean_ctor_get(v_a_3047_, 0);
v_inheritedTraceOptions_3074_ = lean_ctor_get(v_toCold_3073_, 4);
v_cls_3075_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_3105_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_3106_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3074_, v_options_3071_, v___x_3105_);
if (v___x_3106_ == 0)
{
v___y_3077_ = v_a_3043_;
v___y_3078_ = v_a_3044_;
v___y_3079_ = v_a_3045_;
v___y_3080_ = v_a_3046_;
v___y_3081_ = v_a_3047_;
v_inheritedTraceOptions_3082_ = v_inheritedTraceOptions_3074_;
v_options_3083_ = v_options_3071_;
v___y_3084_ = v_a_3048_;
goto v___jp_3076_;
}
else
{
lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
v___x_3107_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7);
lean_inc_ref(v_e_3042_);
v___x_3108_ = l_Lean_indentExpr(v_e_3042_);
v___x_3109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3107_);
lean_ctor_set(v___x_3109_, 1, v___x_3108_);
v___x_3110_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3075_, v___x_3109_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_);
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_dec_ref_known(v___x_3110_, 1);
v___y_3077_ = v_a_3043_;
v___y_3078_ = v_a_3044_;
v___y_3079_ = v_a_3045_;
v___y_3080_ = v_a_3046_;
v___y_3081_ = v_a_3047_;
v_inheritedTraceOptions_3082_ = v_inheritedTraceOptions_3074_;
v_options_3083_ = v_options_3071_;
v___y_3084_ = v_a_3048_;
goto v___jp_3076_;
}
else
{
lean_object* v_a_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3118_; 
lean_dec_ref(v_e_3042_);
lean_dec_ref(v_F_3041_);
lean_dec(v_fixedPrefixSize_3040_);
lean_dec(v_recFnName_3039_);
v_a_3111_ = lean_ctor_get(v___x_3110_, 0);
v_isSharedCheck_3118_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3113_ = v___x_3110_;
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_a_3111_);
lean_dec(v___x_3110_);
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
v___jp_3076_:
{
lean_object* v___x_3085_; uint8_t v___x_3086_; 
v___x_3085_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_3086_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3082_, v_options_3083_, v___x_3085_);
if (v___x_3086_ == 0)
{
v___y_3051_ = v___y_3077_;
v___y_3052_ = v___y_3078_;
v___y_3053_ = v___y_3079_;
v___y_3054_ = v___y_3080_;
v___y_3055_ = v___y_3081_;
v___y_3056_ = v___y_3084_;
goto v___jp_3050_;
}
else
{
lean_object* v___x_3087_; 
lean_inc(v___y_3084_);
lean_inc_ref(v___y_3081_);
lean_inc(v___y_3080_);
lean_inc_ref(v___y_3079_);
lean_inc_ref(v_F_3041_);
v___x_3087_ = lean_infer_type(v_F_3041_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3084_);
if (lean_obj_tag(v___x_3087_) == 0)
{
lean_object* v_a_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; 
v_a_3088_ = lean_ctor_get(v___x_3087_, 0);
lean_inc(v_a_3088_);
lean_dec_ref_known(v___x_3087_, 1);
v___x_3089_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3);
lean_inc_ref(v_F_3041_);
v___x_3090_ = l_Lean_MessageData_ofExpr(v_F_3041_);
v___x_3091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3089_);
lean_ctor_set(v___x_3091_, 1, v___x_3090_);
v___x_3092_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5);
v___x_3093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3091_);
lean_ctor_set(v___x_3093_, 1, v___x_3092_);
v___x_3094_ = l_Lean_indentExpr(v_a_3088_);
v___x_3095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3095_, 0, v___x_3093_);
lean_ctor_set(v___x_3095_, 1, v___x_3094_);
v___x_3096_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3075_, v___x_3095_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3084_);
if (lean_obj_tag(v___x_3096_) == 0)
{
lean_dec_ref_known(v___x_3096_, 1);
v___y_3051_ = v___y_3077_;
v___y_3052_ = v___y_3078_;
v___y_3053_ = v___y_3079_;
v___y_3054_ = v___y_3080_;
v___y_3055_ = v___y_3081_;
v___y_3056_ = v___y_3084_;
goto v___jp_3050_;
}
else
{
lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3104_; 
lean_dec_ref(v_e_3042_);
lean_dec_ref(v_F_3041_);
lean_dec(v_fixedPrefixSize_3040_);
lean_dec(v_recFnName_3039_);
v_a_3097_ = lean_ctor_get(v___x_3096_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3096_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3099_ = v___x_3096_;
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3096_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3102_; 
if (v_isShared_3100_ == 0)
{
v___x_3102_ = v___x_3099_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_a_3097_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
return v___x_3102_;
}
}
}
}
else
{
lean_dec_ref(v_e_3042_);
lean_dec_ref(v_F_3041_);
lean_dec(v_fixedPrefixSize_3040_);
lean_dec(v_recFnName_3039_);
return v___x_3087_;
}
}
}
}
v___jp_3050_:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3057_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1);
v___x_3058_ = lean_st_mk_ref(v___x_3057_);
v___x_3059_ = lean_st_mk_ref(v___x_3057_);
v___x_3060_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_3039_, v_fixedPrefixSize_3040_, v_F_3041_, v_e_3042_, v___x_3059_, v___x_3058_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_);
if (lean_obj_tag(v___x_3060_) == 0)
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3070_; 
v_a_3061_ = lean_ctor_get(v___x_3060_, 0);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_3063_ = v___x_3060_;
v_isShared_3064_ = v_isSharedCheck_3070_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_3060_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3070_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3068_; 
v___x_3065_ = lean_st_ref_get(v___x_3059_);
lean_dec(v___x_3059_);
lean_dec(v___x_3065_);
v___x_3066_ = lean_st_ref_get(v___x_3058_);
lean_dec(v___x_3058_);
lean_dec(v___x_3066_);
if (v_isShared_3064_ == 0)
{
v___x_3068_ = v___x_3063_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_a_3061_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
}
else
{
lean_dec(v___x_3059_);
lean_dec(v___x_3058_);
return v___x_3060_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___boxed(lean_object* v_recFnName_3119_, lean_object* v_fixedPrefixSize_3120_, lean_object* v_F_3121_, lean_object* v_e_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_){
_start:
{
lean_object* v_res_3130_; 
v_res_3130_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(v_recFnName_3119_, v_fixedPrefixSize_3120_, v_F_3121_, v_e_3122_, v_a_3123_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_, v_a_3128_);
lean_dec(v_a_3128_);
lean_dec_ref(v_a_3127_);
lean_dec(v_a_3126_);
lean_dec_ref(v_a_3125_);
lean_dec(v_a_3124_);
lean_dec_ref(v_a_3123_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0(lean_object* v_cls_3131_, lean_object* v_msg_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_){
_start:
{
lean_object* v___x_3140_; 
v___x_3140_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3131_, v_msg_3132_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_);
return v___x_3140_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___boxed(lean_object* v_cls_3141_, lean_object* v_msg_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0(v_cls_3141_, v_msg_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
lean_dec(v___y_3148_);
lean_dec_ref(v___y_3147_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3145_);
lean_dec(v___y_3144_);
lean_dec_ref(v___y_3143_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0(lean_object* v_k_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v_b_3154_, lean_object* v_c_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_){
_start:
{
lean_object* v___x_3161_; 
lean_inc(v___y_3159_);
lean_inc_ref(v___y_3158_);
lean_inc(v___y_3157_);
lean_inc_ref(v___y_3156_);
lean_inc(v___y_3153_);
lean_inc_ref(v___y_3152_);
v___x_3161_ = lean_apply_9(v_k_3151_, v_b_3154_, v_c_3155_, v___y_3152_, v___y_3153_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, lean_box(0));
return v___x_3161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed(lean_object* v_k_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v_b_3165_, lean_object* v_c_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0(v_k_3162_, v___y_3163_, v___y_3164_, v_b_3165_, v_c_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
lean_dec(v___y_3164_);
lean_dec_ref(v___y_3163_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(lean_object* v_e_3173_, lean_object* v_k_3174_, uint8_t v_cleanupAnnotations_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_){
_start:
{
lean_object* v___f_3183_; uint8_t v___x_3184_; uint8_t v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
lean_inc(v___y_3177_);
lean_inc_ref(v___y_3176_);
v___f_3183_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3183_, 0, v_k_3174_);
lean_closure_set(v___f_3183_, 1, v___y_3176_);
lean_closure_set(v___f_3183_, 2, v___y_3177_);
v___x_3184_ = 1;
v___x_3185_ = 0;
v___x_3186_ = lean_box(0);
v___x_3187_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3173_, v___x_3184_, v___x_3185_, v___x_3184_, v___x_3185_, v___x_3186_, v___f_3183_, v_cleanupAnnotations_3175_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
if (lean_obj_tag(v___x_3187_) == 0)
{
return v___x_3187_;
}
else
{
lean_object* v_a_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3195_; 
v_a_3188_ = lean_ctor_get(v___x_3187_, 0);
v_isSharedCheck_3195_ = !lean_is_exclusive(v___x_3187_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3190_ = v___x_3187_;
v_isShared_3191_ = v_isSharedCheck_3195_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_a_3188_);
lean_dec(v___x_3187_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3195_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
lean_object* v___x_3193_; 
if (v_isShared_3191_ == 0)
{
v___x_3193_ = v___x_3190_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v_a_3188_);
v___x_3193_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
return v___x_3193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___boxed(lean_object* v_e_3196_, lean_object* v_k_3197_, lean_object* v_cleanupAnnotations_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3206_; lean_object* v_res_3207_; 
v_cleanupAnnotations_boxed_3206_ = lean_unbox(v_cleanupAnnotations_3198_);
v_res_3207_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v_e_3196_, v_k_3197_, v_cleanupAnnotations_boxed_3206_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_);
lean_dec(v___y_3204_);
lean_dec_ref(v___y_3203_);
lean_dec(v___y_3202_);
lean_dec_ref(v___y_3201_);
lean_dec(v___y_3200_);
lean_dec_ref(v___y_3199_);
return v_res_3207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0(lean_object* v_00_u03b1_3208_, lean_object* v_e_3209_, lean_object* v_k_3210_, uint8_t v_cleanupAnnotations_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_){
_start:
{
lean_object* v___x_3219_; 
v___x_3219_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v_e_3209_, v_k_3210_, v_cleanupAnnotations_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_);
return v___x_3219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___boxed(lean_object* v_00_u03b1_3220_, lean_object* v_e_3221_, lean_object* v_k_3222_, lean_object* v_cleanupAnnotations_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3231_; lean_object* v_res_3232_; 
v_cleanupAnnotations_boxed_3231_ = lean_unbox(v_cleanupAnnotations_3223_);
v_res_3232_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0(v_00_u03b1_3220_, v_e_3221_, v_k_3222_, v_cleanupAnnotations_boxed_3231_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_);
lean_dec(v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
return v_res_3232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(lean_object* v_e_3233_, lean_object* v_maxFVars_3234_, lean_object* v_k_3235_, uint8_t v_cleanupAnnotations_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_){
_start:
{
lean_object* v___f_3244_; uint8_t v___x_3245_; uint8_t v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
lean_inc(v___y_3238_);
lean_inc_ref(v___y_3237_);
v___f_3244_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3244_, 0, v_k_3235_);
lean_closure_set(v___f_3244_, 1, v___y_3237_);
lean_closure_set(v___f_3244_, 2, v___y_3238_);
v___x_3245_ = 1;
v___x_3246_ = 0;
v___x_3247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3247_, 0, v_maxFVars_3234_);
v___x_3248_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3233_, v___x_3245_, v___x_3246_, v___x_3245_, v___x_3246_, v___x_3247_, v___f_3244_, v_cleanupAnnotations_3236_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_);
lean_dec_ref_known(v___x_3247_, 1);
if (lean_obj_tag(v___x_3248_) == 0)
{
return v___x_3248_;
}
else
{
lean_object* v_a_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3256_; 
v_a_3249_ = lean_ctor_get(v___x_3248_, 0);
v_isSharedCheck_3256_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3251_ = v___x_3248_;
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_a_3249_);
lean_dec(v___x_3248_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3254_; 
if (v_isShared_3252_ == 0)
{
v___x_3254_ = v___x_3251_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_a_3249_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
return v___x_3254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg___boxed(lean_object* v_e_3257_, lean_object* v_maxFVars_3258_, lean_object* v_k_3259_, lean_object* v_cleanupAnnotations_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3268_; lean_object* v_res_3269_; 
v_cleanupAnnotations_boxed_3268_ = lean_unbox(v_cleanupAnnotations_3260_);
v_res_3269_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_e_3257_, v_maxFVars_3258_, v_k_3259_, v_cleanupAnnotations_boxed_3268_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_);
lean_dec(v___y_3266_);
lean_dec_ref(v___y_3265_);
lean_dec(v___y_3264_);
lean_dec_ref(v___y_3263_);
lean_dec(v___y_3262_);
lean_dec_ref(v___y_3261_);
return v_res_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2(lean_object* v_00_u03b1_3270_, lean_object* v_e_3271_, lean_object* v_maxFVars_3272_, lean_object* v_k_3273_, uint8_t v_cleanupAnnotations_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_){
_start:
{
lean_object* v___x_3282_; 
v___x_3282_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_e_3271_, v_maxFVars_3272_, v_k_3273_, v_cleanupAnnotations_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
return v___x_3282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___boxed(lean_object* v_00_u03b1_3283_, lean_object* v_e_3284_, lean_object* v_maxFVars_3285_, lean_object* v_k_3286_, lean_object* v_cleanupAnnotations_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3295_; lean_object* v_res_3296_; 
v_cleanupAnnotations_boxed_3295_ = lean_unbox(v_cleanupAnnotations_3287_);
v_res_3296_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2(v_00_u03b1_3283_, v_e_3284_, v_maxFVars_3285_, v_k_3286_, v_cleanupAnnotations_boxed_3295_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
lean_dec(v___y_3289_);
lean_dec_ref(v___y_3288_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0(lean_object* v_a_3297_, lean_object* v___x_3298_, lean_object* v___x_3299_, lean_object* v_x_3300_, uint8_t v___x_3301_, lean_object* v_xs_3302_, lean_object* v_type_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_){
_start:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; 
v___x_3311_ = l_Lean_LocalDecl_type(v_a_3297_);
v___x_3312_ = lean_array_get_borrowed(v___x_3298_, v_xs_3302_, v___x_3299_);
v___x_3313_ = l_Lean_Expr_replaceFVar(v___x_3311_, v_x_3300_, v___x_3312_);
lean_dec_ref(v___x_3311_);
v___x_3314_ = l_Lean_mkArrow(v___x_3313_, v_type_3303_, v___y_3308_, v___y_3309_);
if (lean_obj_tag(v___x_3314_) == 0)
{
lean_object* v_a_3315_; uint8_t v___x_3316_; uint8_t v___x_3317_; lean_object* v___x_3318_; 
v_a_3315_ = lean_ctor_get(v___x_3314_, 0);
lean_inc_n(v_a_3315_, 2);
lean_dec_ref_known(v___x_3314_, 1);
v___x_3316_ = 0;
v___x_3317_ = 1;
v___x_3318_ = l_Lean_Meta_mkLambdaFVars(v_xs_3302_, v_a_3315_, v___x_3316_, v___x_3301_, v___x_3316_, v___x_3301_, v___x_3317_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v_a_3319_; lean_object* v___x_3320_; 
v_a_3319_ = lean_ctor_get(v___x_3318_, 0);
lean_inc(v_a_3319_);
lean_dec_ref_known(v___x_3318_, 1);
v___x_3320_ = l_Lean_Meta_getLevel(v_a_3315_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
if (lean_obj_tag(v___x_3320_) == 0)
{
lean_object* v_a_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3329_; 
v_a_3321_ = lean_ctor_get(v___x_3320_, 0);
v_isSharedCheck_3329_ = !lean_is_exclusive(v___x_3320_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3323_ = v___x_3320_;
v_isShared_3324_ = v_isSharedCheck_3329_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_a_3321_);
lean_dec(v___x_3320_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3329_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3325_; lean_object* v___x_3327_; 
v___x_3325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3325_, 0, v_a_3319_);
lean_ctor_set(v___x_3325_, 1, v_a_3321_);
if (v_isShared_3324_ == 0)
{
lean_ctor_set(v___x_3323_, 0, v___x_3325_);
v___x_3327_ = v___x_3323_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v___x_3325_);
v___x_3327_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
return v___x_3327_;
}
}
}
else
{
lean_object* v_a_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3337_; 
lean_dec(v_a_3319_);
v_a_3330_ = lean_ctor_get(v___x_3320_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3320_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3332_ = v___x_3320_;
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_a_3330_);
lean_dec(v___x_3320_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3335_; 
if (v_isShared_3333_ == 0)
{
v___x_3335_ = v___x_3332_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v_a_3330_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
return v___x_3335_;
}
}
}
}
else
{
lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3345_; 
lean_dec(v_a_3315_);
v_a_3338_ = lean_ctor_get(v___x_3318_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3318_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3340_ = v___x_3318_;
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3318_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___x_3343_; 
if (v_isShared_3341_ == 0)
{
v___x_3343_ = v___x_3340_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_a_3338_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
}
}
else
{
lean_object* v_a_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3353_; 
v_a_3346_ = lean_ctor_get(v___x_3314_, 0);
v_isSharedCheck_3353_ = !lean_is_exclusive(v___x_3314_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3348_ = v___x_3314_;
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_dec(v___x_3314_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v___x_3351_; 
if (v_isShared_3349_ == 0)
{
v___x_3351_ = v___x_3348_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_a_3346_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed(lean_object* v_a_3354_, lean_object* v___x_3355_, lean_object* v___x_3356_, lean_object* v_x_3357_, lean_object* v___x_3358_, lean_object* v_xs_3359_, lean_object* v_type_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_){
_start:
{
uint8_t v___x_6244__boxed_3368_; lean_object* v_res_3369_; 
v___x_6244__boxed_3368_ = lean_unbox(v___x_3358_);
v_res_3369_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0(v_a_3354_, v___x_3355_, v___x_3356_, v_x_3357_, v___x_6244__boxed_3368_, v_xs_3359_, v_type_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_);
lean_dec(v___y_3366_);
lean_dec_ref(v___y_3365_);
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
lean_dec(v___y_3362_);
lean_dec_ref(v___y_3361_);
lean_dec_ref(v_xs_3359_);
lean_dec(v___x_3356_);
lean_dec_ref(v___x_3355_);
lean_dec_ref(v_a_3354_);
return v_res_3369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0(lean_object* v_k_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v_b_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_){
_start:
{
lean_object* v___x_3379_; 
lean_inc(v___y_3377_);
lean_inc_ref(v___y_3376_);
lean_inc(v___y_3375_);
lean_inc_ref(v___y_3374_);
lean_inc(v___y_3372_);
lean_inc_ref(v___y_3371_);
v___x_3379_ = lean_apply_8(v_k_3370_, v_b_3373_, v___y_3371_, v___y_3372_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, lean_box(0));
return v___x_3379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_k_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v_b_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_){
_start:
{
lean_object* v_res_3389_; 
v_res_3389_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0(v_k_3380_, v___y_3381_, v___y_3382_, v_b_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
lean_dec(v___y_3387_);
lean_dec_ref(v___y_3386_);
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3384_);
lean_dec(v___y_3382_);
lean_dec_ref(v___y_3381_);
return v_res_3389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(lean_object* v_name_3390_, uint8_t v_bi_3391_, lean_object* v_type_3392_, lean_object* v_k_3393_, uint8_t v_kind_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
lean_object* v___f_3402_; lean_object* v___x_3403_; 
lean_inc(v___y_3396_);
lean_inc_ref(v___y_3395_);
v___f_3402_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3402_, 0, v_k_3393_);
lean_closure_set(v___f_3402_, 1, v___y_3395_);
lean_closure_set(v___f_3402_, 2, v___y_3396_);
v___x_3403_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3390_, v_bi_3391_, v_type_3392_, v___f_3402_, v_kind_3394_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
if (lean_obj_tag(v___x_3403_) == 0)
{
return v___x_3403_;
}
else
{
lean_object* v_a_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3411_; 
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___boxed(lean_object* v_name_3412_, lean_object* v_bi_3413_, lean_object* v_type_3414_, lean_object* v_k_3415_, lean_object* v_kind_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_){
_start:
{
uint8_t v_bi_boxed_3424_; uint8_t v_kind_boxed_3425_; lean_object* v_res_3426_; 
v_bi_boxed_3424_ = lean_unbox(v_bi_3413_);
v_kind_boxed_3425_ = lean_unbox(v_kind_3416_);
v_res_3426_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(v_name_3412_, v_bi_boxed_3424_, v_type_3414_, v_k_3415_, v_kind_boxed_3425_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_);
lean_dec(v___y_3422_);
lean_dec_ref(v___y_3421_);
lean_dec(v___y_3420_);
lean_dec_ref(v___y_3419_);
lean_dec(v___y_3418_);
lean_dec_ref(v___y_3417_);
return v_res_3426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(lean_object* v_name_3427_, lean_object* v_type_3428_, lean_object* v_k_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_){
_start:
{
uint8_t v___x_3437_; uint8_t v___x_3438_; lean_object* v___x_3439_; 
v___x_3437_ = 0;
v___x_3438_ = 0;
v___x_3439_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(v_name_3427_, v___x_3437_, v_type_3428_, v_k_3429_, v___x_3438_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
return v___x_3439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___boxed(lean_object* v_name_3440_, lean_object* v_type_3441_, lean_object* v_k_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_){
_start:
{
lean_object* v_res_3450_; 
v_res_3450_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_name_3440_, v_type_3441_, v_k_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
lean_dec(v___y_3448_);
lean_dec_ref(v___y_3447_);
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3445_);
lean_dec(v___y_3444_);
lean_dec_ref(v___y_3443_);
return v_res_3450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(lean_object* v_x_3464_, lean_object* v_F_3465_, lean_object* v_val_3466_, lean_object* v_k_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_){
_start:
{
lean_object* v___x_3475_; uint8_t v___y_3477_; uint8_t v___x_3591_; 
v___x_3475_ = l_Lean_instInhabitedExpr;
v___x_3591_ = l_Lean_Expr_isFVar(v_x_3464_);
if (v___x_3591_ == 0)
{
v___y_3477_ = v___x_3591_;
goto v___jp_3476_;
}
else
{
lean_object* v___x_3592_; lean_object* v___x_3593_; uint8_t v___x_3594_; 
v___x_3592_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6));
v___x_3593_ = lean_unsigned_to_nat(6u);
v___x_3594_ = l_Lean_Expr_isAppOfArity(v_val_3466_, v___x_3592_, v___x_3593_);
v___y_3477_ = v___x_3594_;
goto v___jp_3476_;
}
v___jp_3476_:
{
if (v___y_3477_ == 0)
{
lean_object* v___x_3478_; 
lean_inc(v_a_3473_);
lean_inc_ref(v_a_3472_);
lean_inc(v_a_3471_);
lean_inc_ref(v_a_3470_);
lean_inc(v_a_3469_);
lean_inc_ref(v_a_3468_);
v___x_3478_ = lean_apply_10(v_k_3467_, v_x_3464_, v_F_3465_, v_val_3466_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_, lean_box(0));
return v___x_3478_;
}
else
{
lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; uint8_t v___x_3485_; 
v___x_3479_ = lean_unsigned_to_nat(3u);
v___x_3480_ = l_Lean_Expr_getAppNumArgs(v_val_3466_);
v___x_3481_ = lean_nat_sub(v___x_3480_, v___x_3479_);
v___x_3482_ = lean_unsigned_to_nat(1u);
v___x_3483_ = lean_nat_sub(v___x_3481_, v___x_3482_);
lean_dec(v___x_3481_);
v___x_3484_ = l_Lean_Expr_getRevArg_x21(v_val_3466_, v___x_3483_);
v___x_3485_ = lean_expr_eqv(v___x_3484_, v_x_3464_);
lean_dec_ref(v___x_3484_);
if (v___x_3485_ == 0)
{
lean_object* v___x_3486_; 
lean_dec(v___x_3480_);
lean_inc(v_a_3473_);
lean_inc_ref(v_a_3472_);
lean_inc(v_a_3471_);
lean_inc_ref(v_a_3470_);
lean_inc(v_a_3469_);
lean_inc_ref(v_a_3468_);
v___x_3486_ = lean_apply_10(v_k_3467_, v_x_3464_, v_F_3465_, v_val_3466_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_, lean_box(0));
return v___x_3486_;
}
else
{
lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; uint8_t v___x_3491_; 
v___x_3487_ = lean_unsigned_to_nat(4u);
v___x_3488_ = lean_nat_sub(v___x_3480_, v___x_3487_);
v___x_3489_ = lean_nat_sub(v___x_3488_, v___x_3482_);
lean_dec(v___x_3488_);
v___x_3490_ = l_Lean_Expr_getRevArg_x21(v_val_3466_, v___x_3489_);
v___x_3491_ = l_Lean_Expr_isLambda(v___x_3490_);
lean_dec_ref(v___x_3490_);
if (v___x_3491_ == 0)
{
lean_object* v___x_3492_; 
lean_dec(v___x_3480_);
lean_inc(v_a_3473_);
lean_inc_ref(v_a_3472_);
lean_inc(v_a_3471_);
lean_inc_ref(v_a_3470_);
lean_inc(v_a_3469_);
lean_inc_ref(v_a_3468_);
v___x_3492_ = lean_apply_10(v_k_3467_, v_x_3464_, v_F_3465_, v_val_3466_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_, lean_box(0));
return v___x_3492_;
}
else
{
lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; uint8_t v___x_3497_; 
v___x_3493_ = lean_unsigned_to_nat(5u);
v___x_3494_ = lean_nat_sub(v___x_3480_, v___x_3493_);
v___x_3495_ = lean_nat_sub(v___x_3494_, v___x_3482_);
lean_dec(v___x_3494_);
v___x_3496_ = l_Lean_Expr_getRevArg_x21(v_val_3466_, v___x_3495_);
v___x_3497_ = l_Lean_Expr_isLambda(v___x_3496_);
lean_dec_ref(v___x_3496_);
if (v___x_3497_ == 0)
{
lean_object* v___x_3498_; 
lean_dec(v___x_3480_);
lean_inc(v_a_3473_);
lean_inc_ref(v_a_3472_);
lean_inc(v_a_3471_);
lean_inc_ref(v_a_3470_);
lean_inc(v_a_3469_);
lean_inc_ref(v_a_3468_);
v___x_3498_ = lean_apply_10(v_k_3467_, v_x_3464_, v_F_3465_, v_val_3466_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_, lean_box(0));
return v___x_3498_;
}
else
{
lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3499_ = l_Lean_Expr_fvarId_x21(v_F_3465_);
v___x_3500_ = l_Lean_FVarId_getDecl___redArg(v___x_3499_, v_a_3470_, v_a_3472_, v_a_3473_);
if (lean_obj_tag(v___x_3500_) == 0)
{
lean_object* v_a_3501_; lean_object* v_dummy_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v_args_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___f_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; uint8_t v___x_3511_; lean_object* v___x_3512_; 
v_a_3501_ = lean_ctor_get(v___x_3500_, 0);
lean_inc_n(v_a_3501_, 2);
lean_dec_ref_known(v___x_3500_, 1);
v_dummy_3502_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_3480_);
v___x_3503_ = lean_mk_array(v___x_3480_, v_dummy_3502_);
v___x_3504_ = lean_nat_sub(v___x_3480_, v___x_3482_);
lean_dec(v___x_3480_);
v_args_3505_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_3466_, v___x_3503_, v___x_3504_);
v___x_3506_ = lean_unsigned_to_nat(0u);
v___x_3507_ = lean_box(v___x_3491_);
lean_inc_ref(v_x_3464_);
v___f_3508_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed), 14, 5);
lean_closure_set(v___f_3508_, 0, v_a_3501_);
lean_closure_set(v___f_3508_, 1, v___x_3475_);
lean_closure_set(v___f_3508_, 2, v___x_3506_);
lean_closure_set(v___f_3508_, 3, v_x_3464_);
lean_closure_set(v___f_3508_, 4, v___x_3507_);
v___x_3509_ = lean_unsigned_to_nat(2u);
v___x_3510_ = lean_array_get(v___x_3475_, v_args_3505_, v___x_3509_);
v___x_3511_ = 0;
v___x_3512_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_3510_, v___f_3508_, v___x_3511_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_);
if (lean_obj_tag(v___x_3512_) == 0)
{
lean_object* v_a_3513_; lean_object* v_fst_3514_; lean_object* v_snd_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3574_; 
v_a_3513_ = lean_ctor_get(v___x_3512_, 0);
lean_inc(v_a_3513_);
lean_dec_ref_known(v___x_3512_, 1);
v_fst_3514_ = lean_ctor_get(v_a_3513_, 0);
v_snd_3515_ = lean_ctor_get(v_a_3513_, 1);
v_isSharedCheck_3574_ = !lean_is_exclusive(v_a_3513_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3517_ = v_a_3513_;
v_isShared_3518_ = v_isSharedCheck_3574_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_snd_3515_);
lean_inc(v_fst_3514_);
lean_dec(v_a_3513_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3574_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
lean_object* v_00_u03b1_3519_; lean_object* v_00_u03b2_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
v_00_u03b1_3519_ = lean_array_get(v___x_3475_, v_args_3505_, v___x_3506_);
v_00_u03b2_3520_ = lean_array_get(v___x_3475_, v_args_3505_, v___x_3482_);
v___x_3521_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__2));
v___x_3522_ = lean_array_get(v___x_3475_, v_args_3505_, v___x_3487_);
lean_inc_ref(v_x_3464_);
lean_inc(v_a_3501_);
lean_inc_ref(v_k_3467_);
lean_inc(v_00_u03b2_3520_);
lean_inc(v_00_u03b1_3519_);
v___x_3523_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3475_, v___x_3506_, v_00_u03b1_3519_, v_00_u03b2_3520_, v___x_3479_, v_k_3467_, v___x_3509_, v___x_3511_, v___x_3491_, v_a_3501_, v_x_3464_, v___x_3482_, v___x_3521_, v___x_3522_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_);
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v_a_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; 
v_a_3524_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_a_3524_);
lean_dec_ref_known(v___x_3523_, 1);
v___x_3525_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__4));
v___x_3526_ = lean_array_get(v___x_3475_, v_args_3505_, v___x_3493_);
lean_dec_ref(v_args_3505_);
lean_inc_ref(v_x_3464_);
lean_inc(v_00_u03b2_3520_);
lean_inc(v_00_u03b1_3519_);
v___x_3527_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3475_, v___x_3506_, v_00_u03b1_3519_, v_00_u03b2_3520_, v___x_3479_, v_k_3467_, v___x_3509_, v___x_3511_, v___x_3491_, v_a_3501_, v_x_3464_, v___x_3482_, v___x_3525_, v___x_3526_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_);
if (lean_obj_tag(v___x_3527_) == 0)
{
lean_object* v_a_3528_; lean_object* v___x_3529_; 
v_a_3528_ = lean_ctor_get(v___x_3527_, 0);
lean_inc(v_a_3528_);
lean_dec_ref_known(v___x_3527_, 1);
lean_inc(v_00_u03b1_3519_);
v___x_3529_ = l_Lean_Meta_getLevel(v_00_u03b1_3519_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_);
if (lean_obj_tag(v___x_3529_) == 0)
{
lean_object* v_a_3530_; lean_object* v___x_3531_; 
v_a_3530_ = lean_ctor_get(v___x_3529_, 0);
lean_inc(v_a_3530_);
lean_dec_ref_known(v___x_3529_, 1);
lean_inc(v_00_u03b2_3520_);
v___x_3531_ = l_Lean_Meta_getLevel(v_00_u03b2_3520_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_);
if (lean_obj_tag(v___x_3531_) == 0)
{
lean_object* v_a_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3557_; 
v_a_3532_ = lean_ctor_get(v___x_3531_, 0);
v_isSharedCheck_3557_ = !lean_is_exclusive(v___x_3531_);
if (v_isSharedCheck_3557_ == 0)
{
v___x_3534_ = v___x_3531_;
v_isShared_3535_ = v_isSharedCheck_3557_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_a_3532_);
lean_dec(v___x_3531_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3557_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3539_; 
v___x_3536_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6));
v___x_3537_ = lean_box(0);
if (v_isShared_3518_ == 0)
{
lean_ctor_set_tag(v___x_3517_, 1);
lean_ctor_set(v___x_3517_, 1, v___x_3537_);
lean_ctor_set(v___x_3517_, 0, v_a_3532_);
v___x_3539_ = v___x_3517_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v_a_3532_);
lean_ctor_set(v_reuseFailAlloc_3556_, 1, v___x_3537_);
v___x_3539_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3554_; 
v___x_3540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3540_, 0, v_a_3530_);
lean_ctor_set(v___x_3540_, 1, v___x_3539_);
v___x_3541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3541_, 0, v_snd_3515_);
lean_ctor_set(v___x_3541_, 1, v___x_3540_);
v___x_3542_ = l_Lean_mkConst(v___x_3536_, v___x_3541_);
v___x_3543_ = lean_unsigned_to_nat(7u);
v___x_3544_ = lean_mk_empty_array_with_capacity(v___x_3543_);
v___x_3545_ = lean_array_push(v___x_3544_, v_00_u03b1_3519_);
v___x_3546_ = lean_array_push(v___x_3545_, v_00_u03b2_3520_);
v___x_3547_ = lean_array_push(v___x_3546_, v_fst_3514_);
v___x_3548_ = lean_array_push(v___x_3547_, v_x_3464_);
v___x_3549_ = lean_array_push(v___x_3548_, v_a_3524_);
v___x_3550_ = lean_array_push(v___x_3549_, v_a_3528_);
v___x_3551_ = lean_array_push(v___x_3550_, v_F_3465_);
v___x_3552_ = l_Lean_mkAppN(v___x_3542_, v___x_3551_);
lean_dec_ref(v___x_3551_);
if (v_isShared_3535_ == 0)
{
lean_ctor_set(v___x_3534_, 0, v___x_3552_);
v___x_3554_ = v___x_3534_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v___x_3552_);
v___x_3554_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
return v___x_3554_;
}
}
}
}
else
{
lean_object* v_a_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3565_; 
lean_dec(v_a_3530_);
lean_dec(v_a_3528_);
lean_dec(v_a_3524_);
lean_dec(v_00_u03b2_3520_);
lean_dec(v_00_u03b1_3519_);
lean_del_object(v___x_3517_);
lean_dec(v_snd_3515_);
lean_dec(v_fst_3514_);
lean_dec_ref(v_F_3465_);
lean_dec_ref(v_x_3464_);
v_a_3558_ = lean_ctor_get(v___x_3531_, 0);
v_isSharedCheck_3565_ = !lean_is_exclusive(v___x_3531_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3560_ = v___x_3531_;
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_a_3558_);
lean_dec(v___x_3531_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3563_; 
if (v_isShared_3561_ == 0)
{
v___x_3563_ = v___x_3560_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_a_3558_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
}
}
}
}
else
{
lean_object* v_a_3566_; lean_object* v___x_3568_; uint8_t v_isShared_3569_; uint8_t v_isSharedCheck_3573_; 
lean_dec(v_a_3528_);
lean_dec(v_a_3524_);
lean_dec(v_00_u03b2_3520_);
lean_dec(v_00_u03b1_3519_);
lean_del_object(v___x_3517_);
lean_dec(v_snd_3515_);
lean_dec(v_fst_3514_);
lean_dec_ref(v_F_3465_);
lean_dec_ref(v_x_3464_);
v_a_3566_ = lean_ctor_get(v___x_3529_, 0);
v_isSharedCheck_3573_ = !lean_is_exclusive(v___x_3529_);
if (v_isSharedCheck_3573_ == 0)
{
v___x_3568_ = v___x_3529_;
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
else
{
lean_inc(v_a_3566_);
lean_dec(v___x_3529_);
v___x_3568_ = lean_box(0);
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
v_resetjp_3567_:
{
lean_object* v___x_3571_; 
if (v_isShared_3569_ == 0)
{
v___x_3571_ = v___x_3568_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v_a_3566_);
v___x_3571_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
return v___x_3571_;
}
}
}
}
else
{
lean_dec(v_a_3524_);
lean_dec(v_00_u03b2_3520_);
lean_dec(v_00_u03b1_3519_);
lean_del_object(v___x_3517_);
lean_dec(v_snd_3515_);
lean_dec(v_fst_3514_);
lean_dec_ref(v_F_3465_);
lean_dec_ref(v_x_3464_);
return v___x_3527_;
}
}
else
{
lean_dec(v_00_u03b2_3520_);
lean_dec(v_00_u03b1_3519_);
lean_del_object(v___x_3517_);
lean_dec(v_snd_3515_);
lean_dec(v_fst_3514_);
lean_dec_ref(v_args_3505_);
lean_dec(v_a_3501_);
lean_dec_ref(v_k_3467_);
lean_dec_ref(v_F_3465_);
lean_dec_ref(v_x_3464_);
return v___x_3523_;
}
}
}
else
{
lean_object* v_a_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3582_; 
lean_dec_ref(v_args_3505_);
lean_dec(v_a_3501_);
lean_dec_ref(v_k_3467_);
lean_dec_ref(v_F_3465_);
lean_dec_ref(v_x_3464_);
v_a_3575_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3577_ = v___x_3512_;
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_a_3575_);
lean_dec(v___x_3512_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3580_; 
if (v_isShared_3578_ == 0)
{
v___x_3580_ = v___x_3577_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_a_3575_);
v___x_3580_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
return v___x_3580_;
}
}
}
}
else
{
lean_object* v_a_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3590_; 
lean_dec(v___x_3480_);
lean_dec_ref(v_k_3467_);
lean_dec_ref(v_val_3466_);
lean_dec_ref(v_F_3465_);
lean_dec_ref(v_x_3464_);
v_a_3583_ = lean_ctor_get(v___x_3500_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_3500_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3585_ = v___x_3500_;
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_a_3583_);
lean_dec(v___x_3500_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3588_; 
if (v_isShared_3586_ == 0)
{
v___x_3588_ = v___x_3585_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_a_3583_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1(lean_object* v___x_3595_, lean_object* v_body_3596_, lean_object* v_k_3597_, lean_object* v___x_3598_, uint8_t v___x_3599_, uint8_t v___x_3600_, lean_object* v_FNew_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_){
_start:
{
lean_object* v___x_3609_; 
lean_inc_ref(v_FNew_3601_);
lean_inc_ref(v___x_3595_);
v___x_3609_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v___x_3595_, v_FNew_3601_, v_body_3596_, v_k_3597_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_);
if (lean_obj_tag(v___x_3609_) == 0)
{
lean_object* v_a_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; uint8_t v___x_3614_; lean_object* v___x_3615_; 
v_a_3610_ = lean_ctor_get(v___x_3609_, 0);
lean_inc(v_a_3610_);
lean_dec_ref_known(v___x_3609_, 1);
v___x_3611_ = lean_mk_empty_array_with_capacity(v___x_3598_);
v___x_3612_ = lean_array_push(v___x_3611_, v___x_3595_);
v___x_3613_ = lean_array_push(v___x_3612_, v_FNew_3601_);
v___x_3614_ = 1;
v___x_3615_ = l_Lean_Meta_mkLambdaFVars(v___x_3613_, v_a_3610_, v___x_3599_, v___x_3600_, v___x_3599_, v___x_3600_, v___x_3614_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_);
lean_dec_ref(v___x_3613_);
return v___x_3615_;
}
else
{
lean_dec_ref(v_FNew_3601_);
lean_dec_ref(v___x_3595_);
return v___x_3609_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1___boxed(lean_object* v___x_3616_, lean_object* v_body_3617_, lean_object* v_k_3618_, lean_object* v___x_3619_, lean_object* v___x_3620_, lean_object* v___x_3621_, lean_object* v_FNew_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_){
_start:
{
uint8_t v___x_6490__boxed_3630_; uint8_t v___x_6491__boxed_3631_; lean_object* v_res_3632_; 
v___x_6490__boxed_3630_ = lean_unbox(v___x_3620_);
v___x_6491__boxed_3631_ = lean_unbox(v___x_3621_);
v_res_3632_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1(v___x_3616_, v_body_3617_, v_k_3618_, v___x_3619_, v___x_6490__boxed_3630_, v___x_6491__boxed_3631_, v_FNew_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_);
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
lean_dec(v___y_3626_);
lean_dec_ref(v___y_3625_);
lean_dec(v___y_3624_);
lean_dec_ref(v___y_3623_);
lean_dec(v___x_3619_);
return v_res_3632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2(lean_object* v___x_3633_, lean_object* v___x_3634_, lean_object* v_00_u03b1_3635_, lean_object* v_00_u03b2_3636_, lean_object* v___x_3637_, lean_object* v_ctorName_3638_, lean_object* v_k_3639_, lean_object* v___x_3640_, uint8_t v___x_3641_, uint8_t v___x_3642_, lean_object* v_a_3643_, lean_object* v_x_3644_, lean_object* v_xs_3645_, lean_object* v_body_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_){
_start:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; 
v___x_3654_ = lean_array_get_borrowed(v___x_3633_, v_xs_3645_, v___x_3634_);
v___x_3655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3655_, 0, v_00_u03b1_3635_);
v___x_3656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3656_, 0, v_00_u03b2_3636_);
lean_inc(v___x_3654_);
v___x_3657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3654_);
v___x_3658_ = lean_mk_empty_array_with_capacity(v___x_3637_);
v___x_3659_ = lean_array_push(v___x_3658_, v___x_3655_);
v___x_3660_ = lean_array_push(v___x_3659_, v___x_3656_);
v___x_3661_ = lean_array_push(v___x_3660_, v___x_3657_);
v___x_3662_ = l_Lean_Meta_mkAppOptM(v_ctorName_3638_, v___x_3661_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
if (lean_obj_tag(v___x_3662_) == 0)
{
lean_object* v_a_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___f_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; 
v_a_3663_ = lean_ctor_get(v___x_3662_, 0);
lean_inc(v_a_3663_);
lean_dec_ref_known(v___x_3662_, 1);
v___x_3664_ = lean_box(v___x_3641_);
v___x_3665_ = lean_box(v___x_3642_);
lean_inc(v___x_3654_);
v___f_3666_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1___boxed), 14, 6);
lean_closure_set(v___f_3666_, 0, v___x_3654_);
lean_closure_set(v___f_3666_, 1, v_body_3646_);
lean_closure_set(v___f_3666_, 2, v_k_3639_);
lean_closure_set(v___f_3666_, 3, v___x_3640_);
lean_closure_set(v___f_3666_, 4, v___x_3664_);
lean_closure_set(v___f_3666_, 5, v___x_3665_);
v___x_3667_ = l_Lean_LocalDecl_type(v_a_3643_);
v___x_3668_ = l_Lean_Expr_replaceFVar(v___x_3667_, v_x_3644_, v_a_3663_);
lean_dec(v_a_3663_);
lean_dec_ref(v___x_3667_);
v___x_3669_ = l_Lean_LocalDecl_userName(v_a_3643_);
v___x_3670_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v___x_3669_, v___x_3668_, v___f_3666_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
return v___x_3670_;
}
else
{
lean_dec_ref(v_body_3646_);
lean_dec_ref(v_x_3644_);
lean_dec(v___x_3640_);
lean_dec_ref(v_k_3639_);
return v___x_3662_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2___boxed(lean_object** _args){
lean_object* v___x_3671_ = _args[0];
lean_object* v___x_3672_ = _args[1];
lean_object* v_00_u03b1_3673_ = _args[2];
lean_object* v_00_u03b2_3674_ = _args[3];
lean_object* v___x_3675_ = _args[4];
lean_object* v_ctorName_3676_ = _args[5];
lean_object* v_k_3677_ = _args[6];
lean_object* v___x_3678_ = _args[7];
lean_object* v___x_3679_ = _args[8];
lean_object* v___x_3680_ = _args[9];
lean_object* v_a_3681_ = _args[10];
lean_object* v_x_3682_ = _args[11];
lean_object* v_xs_3683_ = _args[12];
lean_object* v_body_3684_ = _args[13];
lean_object* v___y_3685_ = _args[14];
lean_object* v___y_3686_ = _args[15];
lean_object* v___y_3687_ = _args[16];
lean_object* v___y_3688_ = _args[17];
lean_object* v___y_3689_ = _args[18];
lean_object* v___y_3690_ = _args[19];
lean_object* v___y_3691_ = _args[20];
_start:
{
uint8_t v___x_6511__boxed_3692_; uint8_t v___x_6512__boxed_3693_; lean_object* v_res_3694_; 
v___x_6511__boxed_3692_ = lean_unbox(v___x_3679_);
v___x_6512__boxed_3693_ = lean_unbox(v___x_3680_);
v_res_3694_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2(v___x_3671_, v___x_3672_, v_00_u03b1_3673_, v_00_u03b2_3674_, v___x_3675_, v_ctorName_3676_, v_k_3677_, v___x_3678_, v___x_6511__boxed_3692_, v___x_6512__boxed_3693_, v_a_3681_, v_x_3682_, v_xs_3683_, v_body_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_);
lean_dec(v___y_3690_);
lean_dec_ref(v___y_3689_);
lean_dec(v___y_3688_);
lean_dec_ref(v___y_3687_);
lean_dec(v___y_3686_);
lean_dec_ref(v___y_3685_);
lean_dec_ref(v_xs_3683_);
lean_dec_ref(v_a_3681_);
lean_dec(v___x_3675_);
lean_dec(v___x_3672_);
lean_dec_ref(v___x_3671_);
return v_res_3694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(lean_object* v___x_3695_, lean_object* v___x_3696_, lean_object* v_00_u03b1_3697_, lean_object* v_00_u03b2_3698_, lean_object* v___x_3699_, lean_object* v_k_3700_, lean_object* v___x_3701_, uint8_t v___x_3702_, uint8_t v___x_3703_, lean_object* v_a_3704_, lean_object* v_x_3705_, lean_object* v___x_3706_, lean_object* v_ctorName_3707_, lean_object* v_minor_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_){
_start:
{
lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___f_3718_; lean_object* v___x_3719_; 
v___x_3716_ = lean_box(v___x_3702_);
v___x_3717_ = lean_box(v___x_3703_);
v___f_3718_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2___boxed), 21, 12);
lean_closure_set(v___f_3718_, 0, v___x_3695_);
lean_closure_set(v___f_3718_, 1, v___x_3696_);
lean_closure_set(v___f_3718_, 2, v_00_u03b1_3697_);
lean_closure_set(v___f_3718_, 3, v_00_u03b2_3698_);
lean_closure_set(v___f_3718_, 4, v___x_3699_);
lean_closure_set(v___f_3718_, 5, v_ctorName_3707_);
lean_closure_set(v___f_3718_, 6, v_k_3700_);
lean_closure_set(v___f_3718_, 7, v___x_3701_);
lean_closure_set(v___f_3718_, 8, v___x_3716_);
lean_closure_set(v___f_3718_, 9, v___x_3717_);
lean_closure_set(v___f_3718_, 10, v_a_3704_);
lean_closure_set(v___f_3718_, 11, v_x_3705_);
v___x_3719_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_minor_3708_, v___x_3706_, v___f_3718_, v___x_3702_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_);
return v___x_3719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3___boxed(lean_object** _args){
lean_object* v___x_3720_ = _args[0];
lean_object* v___x_3721_ = _args[1];
lean_object* v_00_u03b1_3722_ = _args[2];
lean_object* v_00_u03b2_3723_ = _args[3];
lean_object* v___x_3724_ = _args[4];
lean_object* v_k_3725_ = _args[5];
lean_object* v___x_3726_ = _args[6];
lean_object* v___x_3727_ = _args[7];
lean_object* v___x_3728_ = _args[8];
lean_object* v_a_3729_ = _args[9];
lean_object* v_x_3730_ = _args[10];
lean_object* v___x_3731_ = _args[11];
lean_object* v_ctorName_3732_ = _args[12];
lean_object* v_minor_3733_ = _args[13];
lean_object* v___y_3734_ = _args[14];
lean_object* v___y_3735_ = _args[15];
lean_object* v___y_3736_ = _args[16];
lean_object* v___y_3737_ = _args[17];
lean_object* v___y_3738_ = _args[18];
lean_object* v___y_3739_ = _args[19];
lean_object* v___y_3740_ = _args[20];
_start:
{
uint8_t v___x_6475__boxed_3741_; uint8_t v___x_6476__boxed_3742_; lean_object* v_res_3743_; 
v___x_6475__boxed_3741_ = lean_unbox(v___x_3727_);
v___x_6476__boxed_3742_ = lean_unbox(v___x_3728_);
v_res_3743_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3720_, v___x_3721_, v_00_u03b1_3722_, v_00_u03b2_3723_, v___x_3724_, v_k_3725_, v___x_3726_, v___x_6475__boxed_3741_, v___x_6476__boxed_3742_, v_a_3729_, v_x_3730_, v___x_3731_, v_ctorName_3732_, v_minor_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
lean_dec(v___y_3739_);
lean_dec_ref(v___y_3738_);
lean_dec(v___y_3737_);
lean_dec_ref(v___y_3736_);
lean_dec(v___y_3735_);
lean_dec_ref(v___y_3734_);
return v_res_3743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___boxed(lean_object* v_x_3744_, lean_object* v_F_3745_, lean_object* v_val_3746_, lean_object* v_k_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_, lean_object* v_a_3752_, lean_object* v_a_3753_, lean_object* v_a_3754_){
_start:
{
lean_object* v_res_3755_; 
v_res_3755_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v_x_3744_, v_F_3745_, v_val_3746_, v_k_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_, v_a_3753_);
lean_dec(v_a_3753_);
lean_dec_ref(v_a_3752_);
lean_dec(v_a_3751_);
lean_dec_ref(v_a_3750_);
lean_dec(v_a_3749_);
lean_dec_ref(v_a_3748_);
return v_res_3755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1(lean_object* v_00_u03b1_3756_, lean_object* v_name_3757_, uint8_t v_bi_3758_, lean_object* v_type_3759_, lean_object* v_k_3760_, uint8_t v_kind_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_){
_start:
{
lean_object* v___x_3769_; 
v___x_3769_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(v_name_3757_, v_bi_3758_, v_type_3759_, v_k_3760_, v_kind_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_);
return v___x_3769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___boxed(lean_object* v_00_u03b1_3770_, lean_object* v_name_3771_, lean_object* v_bi_3772_, lean_object* v_type_3773_, lean_object* v_k_3774_, lean_object* v_kind_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_){
_start:
{
uint8_t v_bi_boxed_3783_; uint8_t v_kind_boxed_3784_; lean_object* v_res_3785_; 
v_bi_boxed_3783_ = lean_unbox(v_bi_3772_);
v_kind_boxed_3784_ = lean_unbox(v_kind_3775_);
v_res_3785_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1(v_00_u03b1_3770_, v_name_3771_, v_bi_boxed_3783_, v_type_3773_, v_k_3774_, v_kind_boxed_3784_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_);
lean_dec(v___y_3781_);
lean_dec_ref(v___y_3780_);
lean_dec(v___y_3779_);
lean_dec_ref(v___y_3778_);
lean_dec(v___y_3777_);
lean_dec_ref(v___y_3776_);
return v_res_3785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1(lean_object* v_00_u03b1_3786_, lean_object* v_name_3787_, lean_object* v_type_3788_, lean_object* v_k_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_){
_start:
{
lean_object* v___x_3797_; 
v___x_3797_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_name_3787_, v_type_3788_, v_k_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_);
return v___x_3797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___boxed(lean_object* v_00_u03b1_3798_, lean_object* v_name_3799_, lean_object* v_type_3800_, lean_object* v_k_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
lean_object* v_res_3809_; 
v_res_3809_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1(v_00_u03b1_3798_, v_name_3799_, v_type_3800_, v_k_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
lean_dec(v___y_3803_);
lean_dec_ref(v___y_3802_);
return v_res_3809_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3810_; 
v___x_3810_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return v___x_3810_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(lean_object* v_msg_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_){
_start:
{
lean_object* v___x_3819_; lean_object* v___x_3331__overap_3820_; lean_object* v___x_3821_; 
v___x_3819_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0, &l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0);
v___x_3331__overap_3820_ = lean_panic_fn_borrowed(v___x_3819_, v_msg_3811_);
lean_inc(v___y_3817_);
lean_inc_ref(v___y_3816_);
lean_inc(v___y_3815_);
lean_inc_ref(v___y_3814_);
lean_inc(v___y_3813_);
lean_inc_ref(v___y_3812_);
v___x_3821_ = lean_apply_7(v___x_3331__overap_3820_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_, lean_box(0));
return v___x_3821_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___boxed(lean_object* v_msg_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_){
_start:
{
lean_object* v_res_3830_; 
v_res_3830_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(v_msg_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
lean_dec(v___y_3828_);
lean_dec_ref(v___y_3827_);
lean_dec(v___y_3826_);
lean_dec_ref(v___y_3825_);
lean_dec(v___y_3824_);
lean_dec_ref(v___y_3823_);
return v_res_3830_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3(void){
_start:
{
lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; 
v___x_3834_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__2));
v___x_3835_ = lean_unsigned_to_nat(49u);
v___x_3836_ = lean_unsigned_to_nat(186u);
v___x_3837_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__1));
v___x_3838_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__0));
v___x_3839_ = l_mkPanicMessageWithDecl(v___x_3838_, v___x_3837_, v___x_3836_, v___x_3835_, v___x_3834_);
return v___x_3839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1___boxed(lean_object* v___x_3845_, lean_object* v_a_3846_, lean_object* v_k_3847_, lean_object* v___x_3848_, lean_object* v___x_3849_, lean_object* v___x_3850_, lean_object* v___x_3851_, lean_object* v___x_3852_, lean_object* v_FNew_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_){
_start:
{
uint8_t v___x_3499__boxed_3861_; uint8_t v___x_3500__boxed_3862_; uint8_t v___x_3501__boxed_3863_; lean_object* v_res_3864_; 
v___x_3499__boxed_3861_ = lean_unbox(v___x_3850_);
v___x_3500__boxed_3862_ = lean_unbox(v___x_3851_);
v___x_3501__boxed_3863_ = lean_unbox(v___x_3852_);
v_res_3864_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1(v___x_3845_, v_a_3846_, v_k_3847_, v___x_3848_, v___x_3849_, v___x_3499__boxed_3861_, v___x_3500__boxed_3862_, v___x_3501__boxed_3863_, v_FNew_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
lean_dec(v___y_3859_);
lean_dec_ref(v___y_3858_);
lean_dec(v___y_3857_);
lean_dec_ref(v___y_3856_);
lean_dec(v___y_3855_);
lean_dec_ref(v___y_3854_);
lean_dec(v___x_3848_);
return v_res_3864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0(lean_object* v___x_3865_, lean_object* v___x_3866_, lean_object* v___x_3867_, lean_object* v___x_3868_, uint8_t v___x_3869_, uint8_t v___x_3870_, lean_object* v_00_u03b1_3871_, lean_object* v_00_u03b2_3872_, lean_object* v___x_3873_, lean_object* v_k_3874_, lean_object* v___x_3875_, lean_object* v_a_3876_, lean_object* v_x_3877_, lean_object* v_xs_3878_, lean_object* v_body_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_){
_start:
{
lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; uint8_t v___x_3892_; lean_object* v___x_3893_; 
v___x_3887_ = lean_array_get(v___x_3865_, v_xs_3878_, v___x_3866_);
v___x_3888_ = lean_array_get(v___x_3865_, v_xs_3878_, v___x_3867_);
v___x_3889_ = lean_array_get_size(v_xs_3878_);
v___x_3890_ = l_Array_toSubarray___redArg(v_xs_3878_, v___x_3868_, v___x_3889_);
v___x_3891_ = l_Subarray_copy___redArg(v___x_3890_);
v___x_3892_ = 1;
v___x_3893_ = l_Lean_Meta_mkLambdaFVars(v___x_3891_, v_body_3879_, v___x_3869_, v___x_3870_, v___x_3869_, v___x_3870_, v___x_3892_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
lean_dec_ref(v___x_3891_);
if (lean_obj_tag(v___x_3893_) == 0)
{
lean_object* v_a_3894_; lean_object* v___x_3896_; uint8_t v_isShared_3897_; uint8_t v_isSharedCheck_3920_; 
v_a_3894_ = lean_ctor_get(v___x_3893_, 0);
v_isSharedCheck_3920_ = !lean_is_exclusive(v___x_3893_);
if (v_isSharedCheck_3920_ == 0)
{
v___x_3896_ = v___x_3893_;
v_isShared_3897_ = v_isSharedCheck_3920_;
goto v_resetjp_3895_;
}
else
{
lean_inc(v_a_3894_);
lean_dec(v___x_3893_);
v___x_3896_ = lean_box(0);
v_isShared_3897_ = v_isSharedCheck_3920_;
goto v_resetjp_3895_;
}
v_resetjp_3895_:
{
lean_object* v___x_3898_; lean_object* v___x_3900_; 
v___x_3898_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__2));
if (v_isShared_3897_ == 0)
{
lean_ctor_set_tag(v___x_3896_, 1);
lean_ctor_set(v___x_3896_, 0, v_00_u03b1_3871_);
v___x_3900_ = v___x_3896_;
goto v_reusejp_3899_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v_00_u03b1_3871_);
v___x_3900_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3899_;
}
v_reusejp_3899_:
{
lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; 
v___x_3901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3901_, 0, v_00_u03b2_3872_);
lean_inc(v___x_3887_);
v___x_3902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3902_, 0, v___x_3887_);
lean_inc(v___x_3888_);
v___x_3903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3903_, 0, v___x_3888_);
v___x_3904_ = lean_mk_empty_array_with_capacity(v___x_3873_);
v___x_3905_ = lean_array_push(v___x_3904_, v___x_3900_);
v___x_3906_ = lean_array_push(v___x_3905_, v___x_3901_);
v___x_3907_ = lean_array_push(v___x_3906_, v___x_3902_);
v___x_3908_ = lean_array_push(v___x_3907_, v___x_3903_);
v___x_3909_ = l_Lean_Meta_mkAppOptM(v___x_3898_, v___x_3908_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v_a_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___f_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; 
v_a_3910_ = lean_ctor_get(v___x_3909_, 0);
lean_inc(v_a_3910_);
lean_dec_ref_known(v___x_3909_, 1);
v___x_3911_ = lean_box(v___x_3869_);
v___x_3912_ = lean_box(v___x_3870_);
v___x_3913_ = lean_box(v___x_3892_);
v___f_3914_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1___boxed), 16, 8);
lean_closure_set(v___f_3914_, 0, v___x_3888_);
lean_closure_set(v___f_3914_, 1, v_a_3894_);
lean_closure_set(v___f_3914_, 2, v_k_3874_);
lean_closure_set(v___f_3914_, 3, v___x_3875_);
lean_closure_set(v___f_3914_, 4, v___x_3887_);
lean_closure_set(v___f_3914_, 5, v___x_3911_);
lean_closure_set(v___f_3914_, 6, v___x_3912_);
lean_closure_set(v___f_3914_, 7, v___x_3913_);
v___x_3915_ = l_Lean_LocalDecl_type(v_a_3876_);
v___x_3916_ = l_Lean_Expr_replaceFVar(v___x_3915_, v_x_3877_, v_a_3910_);
lean_dec(v_a_3910_);
lean_dec_ref(v___x_3915_);
v___x_3917_ = l_Lean_LocalDecl_userName(v_a_3876_);
v___x_3918_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v___x_3917_, v___x_3916_, v___f_3914_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
return v___x_3918_;
}
else
{
lean_dec(v_a_3894_);
lean_dec(v___x_3888_);
lean_dec(v___x_3887_);
lean_dec_ref(v_x_3877_);
lean_dec(v___x_3875_);
lean_dec_ref(v_k_3874_);
return v___x_3909_;
}
}
}
}
else
{
lean_dec(v___x_3888_);
lean_dec(v___x_3887_);
lean_dec_ref(v_x_3877_);
lean_dec(v___x_3875_);
lean_dec_ref(v_k_3874_);
lean_dec_ref(v_00_u03b2_3872_);
lean_dec_ref(v_00_u03b1_3871_);
return v___x_3893_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___boxed(lean_object** _args){
lean_object* v___x_3921_ = _args[0];
lean_object* v___x_3922_ = _args[1];
lean_object* v___x_3923_ = _args[2];
lean_object* v___x_3924_ = _args[3];
lean_object* v___x_3925_ = _args[4];
lean_object* v___x_3926_ = _args[5];
lean_object* v_00_u03b1_3927_ = _args[6];
lean_object* v_00_u03b2_3928_ = _args[7];
lean_object* v___x_3929_ = _args[8];
lean_object* v_k_3930_ = _args[9];
lean_object* v___x_3931_ = _args[10];
lean_object* v_a_3932_ = _args[11];
lean_object* v_x_3933_ = _args[12];
lean_object* v_xs_3934_ = _args[13];
lean_object* v_body_3935_ = _args[14];
lean_object* v___y_3936_ = _args[15];
lean_object* v___y_3937_ = _args[16];
lean_object* v___y_3938_ = _args[17];
lean_object* v___y_3939_ = _args[18];
lean_object* v___y_3940_ = _args[19];
lean_object* v___y_3941_ = _args[20];
lean_object* v___y_3942_ = _args[21];
_start:
{
uint8_t v___x_3526__boxed_3943_; uint8_t v___x_3527__boxed_3944_; lean_object* v_res_3945_; 
v___x_3526__boxed_3943_ = lean_unbox(v___x_3925_);
v___x_3527__boxed_3944_ = lean_unbox(v___x_3926_);
v_res_3945_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0(v___x_3921_, v___x_3922_, v___x_3923_, v___x_3924_, v___x_3526__boxed_3943_, v___x_3527__boxed_3944_, v_00_u03b1_3927_, v_00_u03b2_3928_, v___x_3929_, v_k_3930_, v___x_3931_, v_a_3932_, v_x_3933_, v_xs_3934_, v_body_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_);
lean_dec(v___y_3941_);
lean_dec_ref(v___y_3940_);
lean_dec(v___y_3939_);
lean_dec_ref(v___y_3938_);
lean_dec(v___y_3937_);
lean_dec_ref(v___y_3936_);
lean_dec_ref(v_a_3932_);
lean_dec(v___x_3929_);
lean_dec(v___x_3923_);
lean_dec(v___x_3922_);
lean_dec_ref(v___x_3921_);
return v_res_3945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(lean_object* v_x_3949_, lean_object* v_F_3950_, lean_object* v_val_3951_, lean_object* v_k_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_){
_start:
{
lean_object* v___y_3961_; lean_object* v___y_3962_; lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___x_3969_; uint8_t v___y_3971_; uint8_t v___x_4062_; 
v___x_3969_ = l_Lean_instInhabitedExpr;
v___x_4062_ = l_Lean_Expr_isFVar(v_x_3949_);
if (v___x_4062_ == 0)
{
v___y_3971_ = v___x_4062_;
goto v___jp_3970_;
}
else
{
lean_object* v___x_4063_; lean_object* v___x_4064_; uint8_t v___x_4065_; 
v___x_4063_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4));
v___x_4064_ = lean_unsigned_to_nat(5u);
v___x_4065_ = l_Lean_Expr_isAppOfArity(v_val_3951_, v___x_4063_, v___x_4064_);
v___y_3971_ = v___x_4065_;
goto v___jp_3970_;
}
v___jp_3960_:
{
lean_object* v___x_3967_; lean_object* v___x_3968_; 
v___x_3967_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3);
v___x_3968_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(v___x_3967_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_);
return v___x_3968_;
}
v___jp_3970_:
{
if (v___y_3971_ == 0)
{
lean_object* v___x_3972_; 
lean_dec_ref(v_x_3949_);
lean_inc(v_a_3958_);
lean_inc_ref(v_a_3957_);
lean_inc(v_a_3956_);
lean_inc_ref(v_a_3955_);
lean_inc(v_a_3954_);
lean_inc_ref(v_a_3953_);
v___x_3972_ = lean_apply_9(v_k_3952_, v_F_3950_, v_val_3951_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, lean_box(0));
return v___x_3972_;
}
else
{
lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; uint8_t v___x_3979_; 
v___x_3973_ = lean_unsigned_to_nat(3u);
v___x_3974_ = l_Lean_Expr_getAppNumArgs(v_val_3951_);
v___x_3975_ = lean_nat_sub(v___x_3974_, v___x_3973_);
v___x_3976_ = lean_unsigned_to_nat(1u);
v___x_3977_ = lean_nat_sub(v___x_3975_, v___x_3976_);
lean_dec(v___x_3975_);
v___x_3978_ = l_Lean_Expr_getRevArg_x21(v_val_3951_, v___x_3977_);
v___x_3979_ = lean_expr_eqv(v___x_3978_, v_x_3949_);
lean_dec_ref(v___x_3978_);
if (v___x_3979_ == 0)
{
lean_object* v___x_3980_; 
lean_dec(v___x_3974_);
lean_dec_ref(v_x_3949_);
lean_inc(v_a_3958_);
lean_inc_ref(v_a_3957_);
lean_inc(v_a_3956_);
lean_inc_ref(v_a_3955_);
lean_inc(v_a_3954_);
lean_inc_ref(v_a_3953_);
v___x_3980_ = lean_apply_9(v_k_3952_, v_F_3950_, v_val_3951_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, lean_box(0));
return v___x_3980_;
}
else
{
lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; uint8_t v___x_3985_; 
v___x_3981_ = lean_unsigned_to_nat(4u);
v___x_3982_ = lean_nat_sub(v___x_3974_, v___x_3981_);
v___x_3983_ = lean_nat_sub(v___x_3982_, v___x_3976_);
lean_dec(v___x_3982_);
v___x_3984_ = l_Lean_Expr_getRevArg_x21(v_val_3951_, v___x_3983_);
v___x_3985_ = l_Lean_Expr_isLambda(v___x_3984_);
if (v___x_3985_ == 0)
{
lean_object* v___x_3986_; 
lean_dec_ref(v___x_3984_);
lean_dec(v___x_3974_);
lean_dec_ref(v_x_3949_);
lean_inc(v_a_3958_);
lean_inc_ref(v_a_3957_);
lean_inc(v_a_3956_);
lean_inc_ref(v_a_3955_);
lean_inc(v_a_3954_);
lean_inc_ref(v_a_3953_);
v___x_3986_ = lean_apply_9(v_k_3952_, v_F_3950_, v_val_3951_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, lean_box(0));
return v___x_3986_;
}
else
{
lean_object* v___x_3987_; uint8_t v___x_3988_; 
v___x_3987_ = l_Lean_Expr_bindingBody_x21(v___x_3984_);
lean_dec_ref(v___x_3984_);
v___x_3988_ = l_Lean_Expr_isLambda(v___x_3987_);
lean_dec_ref(v___x_3987_);
if (v___x_3988_ == 0)
{
lean_object* v___x_3989_; 
lean_dec(v___x_3974_);
lean_dec_ref(v_x_3949_);
lean_inc(v_a_3958_);
lean_inc_ref(v_a_3957_);
lean_inc(v_a_3956_);
lean_inc_ref(v_a_3955_);
lean_inc(v_a_3954_);
lean_inc_ref(v_a_3953_);
v___x_3989_ = lean_apply_9(v_k_3952_, v_F_3950_, v_val_3951_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, lean_box(0));
return v___x_3989_;
}
else
{
lean_object* v___x_3990_; lean_object* v___x_3991_; 
v___x_3990_ = l_Lean_Expr_getAppFn(v_val_3951_);
v___x_3991_ = l_Lean_Expr_constLevels_x21(v___x_3990_);
lean_dec_ref(v___x_3990_);
if (lean_obj_tag(v___x_3991_) == 1)
{
lean_object* v_tail_3992_; 
v_tail_3992_ = lean_ctor_get(v___x_3991_, 1);
lean_inc(v_tail_3992_);
lean_dec_ref_known(v___x_3991_, 2);
if (lean_obj_tag(v_tail_3992_) == 1)
{
lean_object* v_tail_3993_; 
v_tail_3993_ = lean_ctor_get(v_tail_3992_, 1);
lean_inc(v_tail_3993_);
if (lean_obj_tag(v_tail_3993_) == 1)
{
lean_object* v_tail_3994_; lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4060_; 
v_tail_3994_ = lean_ctor_get(v_tail_3993_, 1);
v_isSharedCheck_4060_ = !lean_is_exclusive(v_tail_3993_);
if (v_isSharedCheck_4060_ == 0)
{
lean_object* v_unused_4061_; 
v_unused_4061_ = lean_ctor_get(v_tail_3993_, 0);
lean_dec(v_unused_4061_);
v___x_3996_ = v_tail_3993_;
v_isShared_3997_ = v_isSharedCheck_4060_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_tail_3994_);
lean_dec(v_tail_3993_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4060_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
if (lean_obj_tag(v_tail_3994_) == 0)
{
lean_object* v___x_3998_; lean_object* v___x_3999_; 
v___x_3998_ = l_Lean_Expr_fvarId_x21(v_F_3950_);
v___x_3999_ = l_Lean_FVarId_getDecl___redArg(v___x_3998_, v_a_3955_, v_a_3957_, v_a_3958_);
if (lean_obj_tag(v___x_3999_) == 0)
{
lean_object* v_a_4000_; lean_object* v_dummy_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v_args_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___f_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; uint8_t v___x_4010_; lean_object* v___x_4011_; 
v_a_4000_ = lean_ctor_get(v___x_3999_, 0);
lean_inc_n(v_a_4000_, 2);
lean_dec_ref_known(v___x_3999_, 1);
v_dummy_4001_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_3974_);
v___x_4002_ = lean_mk_array(v___x_3974_, v_dummy_4001_);
v___x_4003_ = lean_nat_sub(v___x_3974_, v___x_3976_);
lean_dec(v___x_3974_);
v_args_4004_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_3951_, v___x_4002_, v___x_4003_);
v___x_4005_ = lean_unsigned_to_nat(0u);
v___x_4006_ = lean_box(v___x_3985_);
lean_inc_ref(v_x_3949_);
v___f_4007_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed), 14, 5);
lean_closure_set(v___f_4007_, 0, v_a_4000_);
lean_closure_set(v___f_4007_, 1, v___x_3969_);
lean_closure_set(v___f_4007_, 2, v___x_4005_);
lean_closure_set(v___f_4007_, 3, v_x_3949_);
lean_closure_set(v___f_4007_, 4, v___x_4006_);
v___x_4008_ = lean_unsigned_to_nat(2u);
v___x_4009_ = lean_array_get(v___x_3969_, v_args_4004_, v___x_4008_);
v___x_4010_ = 0;
v___x_4011_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_4009_, v___f_4007_, v___x_4010_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_);
if (lean_obj_tag(v___x_4011_) == 0)
{
lean_object* v_a_4012_; lean_object* v_fst_4013_; lean_object* v_snd_4014_; lean_object* v_00_u03b1_4015_; lean_object* v_00_u03b2_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___f_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; 
v_a_4012_ = lean_ctor_get(v___x_4011_, 0);
lean_inc(v_a_4012_);
lean_dec_ref_known(v___x_4011_, 1);
v_fst_4013_ = lean_ctor_get(v_a_4012_, 0);
lean_inc(v_fst_4013_);
v_snd_4014_ = lean_ctor_get(v_a_4012_, 1);
lean_inc(v_snd_4014_);
lean_dec(v_a_4012_);
v_00_u03b1_4015_ = lean_array_get(v___x_3969_, v_args_4004_, v___x_4005_);
v_00_u03b2_4016_ = lean_array_get(v___x_3969_, v_args_4004_, v___x_3976_);
v___x_4017_ = lean_box(v___x_4010_);
v___x_4018_ = lean_box(v___x_3985_);
lean_inc_ref(v_x_3949_);
lean_inc(v_00_u03b2_4016_);
lean_inc(v_00_u03b1_4015_);
v___f_4019_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___boxed), 22, 13);
lean_closure_set(v___f_4019_, 0, v___x_3969_);
lean_closure_set(v___f_4019_, 1, v___x_4005_);
lean_closure_set(v___f_4019_, 2, v___x_3976_);
lean_closure_set(v___f_4019_, 3, v___x_4008_);
lean_closure_set(v___f_4019_, 4, v___x_4017_);
lean_closure_set(v___f_4019_, 5, v___x_4018_);
lean_closure_set(v___f_4019_, 6, v_00_u03b1_4015_);
lean_closure_set(v___f_4019_, 7, v_00_u03b2_4016_);
lean_closure_set(v___f_4019_, 8, v___x_3981_);
lean_closure_set(v___f_4019_, 9, v_k_3952_);
lean_closure_set(v___f_4019_, 10, v___x_3973_);
lean_closure_set(v___f_4019_, 11, v_a_4000_);
lean_closure_set(v___f_4019_, 12, v_x_3949_);
v___x_4020_ = lean_array_get(v___x_3969_, v_args_4004_, v___x_3981_);
lean_dec_ref(v_args_4004_);
v___x_4021_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_4020_, v___f_4019_, v___x_4010_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_);
if (lean_obj_tag(v___x_4021_) == 0)
{
lean_object* v_a_4022_; lean_object* v___x_4024_; uint8_t v_isShared_4025_; uint8_t v_isSharedCheck_4043_; 
v_a_4022_ = lean_ctor_get(v___x_4021_, 0);
v_isSharedCheck_4043_ = !lean_is_exclusive(v___x_4021_);
if (v_isSharedCheck_4043_ == 0)
{
v___x_4024_ = v___x_4021_;
v_isShared_4025_ = v_isSharedCheck_4043_;
goto v_resetjp_4023_;
}
else
{
lean_inc(v_a_4022_);
lean_dec(v___x_4021_);
v___x_4024_ = lean_box(0);
v_isShared_4025_ = v_isSharedCheck_4043_;
goto v_resetjp_4023_;
}
v_resetjp_4023_:
{
lean_object* v___x_4026_; lean_object* v___x_4028_; 
v___x_4026_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4));
if (v_isShared_3997_ == 0)
{
lean_ctor_set(v___x_3996_, 1, v_tail_3992_);
lean_ctor_set(v___x_3996_, 0, v_snd_4014_);
v___x_4028_ = v___x_3996_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4042_; 
v_reuseFailAlloc_4042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4042_, 0, v_snd_4014_);
lean_ctor_set(v_reuseFailAlloc_4042_, 1, v_tail_3992_);
v___x_4028_ = v_reuseFailAlloc_4042_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4040_; 
v___x_4029_ = l_Lean_mkConst(v___x_4026_, v___x_4028_);
v___x_4030_ = lean_unsigned_to_nat(6u);
v___x_4031_ = lean_mk_empty_array_with_capacity(v___x_4030_);
v___x_4032_ = lean_array_push(v___x_4031_, v_00_u03b1_4015_);
v___x_4033_ = lean_array_push(v___x_4032_, v_00_u03b2_4016_);
v___x_4034_ = lean_array_push(v___x_4033_, v_fst_4013_);
v___x_4035_ = lean_array_push(v___x_4034_, v_x_3949_);
v___x_4036_ = lean_array_push(v___x_4035_, v_a_4022_);
v___x_4037_ = lean_array_push(v___x_4036_, v_F_3950_);
v___x_4038_ = l_Lean_mkAppN(v___x_4029_, v___x_4037_);
lean_dec_ref(v___x_4037_);
if (v_isShared_4025_ == 0)
{
lean_ctor_set(v___x_4024_, 0, v___x_4038_);
v___x_4040_ = v___x_4024_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v___x_4038_);
v___x_4040_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
return v___x_4040_;
}
}
}
}
else
{
lean_dec(v_00_u03b2_4016_);
lean_dec(v_00_u03b1_4015_);
lean_dec(v_snd_4014_);
lean_dec(v_fst_4013_);
lean_del_object(v___x_3996_);
lean_dec_ref_known(v_tail_3992_, 2);
lean_dec_ref(v_F_3950_);
lean_dec_ref(v_x_3949_);
return v___x_4021_;
}
}
else
{
lean_object* v_a_4044_; lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4051_; 
lean_dec_ref(v_args_4004_);
lean_dec(v_a_4000_);
lean_del_object(v___x_3996_);
lean_dec_ref_known(v_tail_3992_, 2);
lean_dec_ref(v_k_3952_);
lean_dec_ref(v_F_3950_);
lean_dec_ref(v_x_3949_);
v_a_4044_ = lean_ctor_get(v___x_4011_, 0);
v_isSharedCheck_4051_ = !lean_is_exclusive(v___x_4011_);
if (v_isSharedCheck_4051_ == 0)
{
v___x_4046_ = v___x_4011_;
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
else
{
lean_inc(v_a_4044_);
lean_dec(v___x_4011_);
v___x_4046_ = lean_box(0);
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
v_resetjp_4045_:
{
lean_object* v___x_4049_; 
if (v_isShared_4047_ == 0)
{
v___x_4049_ = v___x_4046_;
goto v_reusejp_4048_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_a_4044_);
v___x_4049_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4048_;
}
v_reusejp_4048_:
{
return v___x_4049_;
}
}
}
}
else
{
lean_object* v_a_4052_; lean_object* v___x_4054_; uint8_t v_isShared_4055_; uint8_t v_isSharedCheck_4059_; 
lean_del_object(v___x_3996_);
lean_dec_ref_known(v_tail_3992_, 2);
lean_dec(v___x_3974_);
lean_dec_ref(v_k_3952_);
lean_dec_ref(v_val_3951_);
lean_dec_ref(v_F_3950_);
lean_dec_ref(v_x_3949_);
v_a_4052_ = lean_ctor_get(v___x_3999_, 0);
v_isSharedCheck_4059_ = !lean_is_exclusive(v___x_3999_);
if (v_isSharedCheck_4059_ == 0)
{
v___x_4054_ = v___x_3999_;
v_isShared_4055_ = v_isSharedCheck_4059_;
goto v_resetjp_4053_;
}
else
{
lean_inc(v_a_4052_);
lean_dec(v___x_3999_);
v___x_4054_ = lean_box(0);
v_isShared_4055_ = v_isSharedCheck_4059_;
goto v_resetjp_4053_;
}
v_resetjp_4053_:
{
lean_object* v___x_4057_; 
if (v_isShared_4055_ == 0)
{
v___x_4057_ = v___x_4054_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v_a_4052_);
v___x_4057_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
return v___x_4057_;
}
}
}
}
else
{
lean_del_object(v___x_3996_);
lean_dec(v_tail_3994_);
lean_dec_ref_known(v_tail_3992_, 2);
lean_dec(v___x_3974_);
lean_dec_ref(v_k_3952_);
lean_dec_ref(v_val_3951_);
lean_dec_ref(v_F_3950_);
lean_dec_ref(v_x_3949_);
v___y_3961_ = v_a_3953_;
v___y_3962_ = v_a_3954_;
v___y_3963_ = v_a_3955_;
v___y_3964_ = v_a_3956_;
v___y_3965_ = v_a_3957_;
v___y_3966_ = v_a_3958_;
goto v___jp_3960_;
}
}
}
else
{
lean_dec(v_tail_3993_);
lean_dec_ref_known(v_tail_3992_, 2);
lean_dec(v___x_3974_);
lean_dec_ref(v_k_3952_);
lean_dec_ref(v_val_3951_);
lean_dec_ref(v_F_3950_);
lean_dec_ref(v_x_3949_);
v___y_3961_ = v_a_3953_;
v___y_3962_ = v_a_3954_;
v___y_3963_ = v_a_3955_;
v___y_3964_ = v_a_3956_;
v___y_3965_ = v_a_3957_;
v___y_3966_ = v_a_3958_;
goto v___jp_3960_;
}
}
else
{
lean_dec(v_tail_3992_);
lean_dec(v___x_3974_);
lean_dec_ref(v_k_3952_);
lean_dec_ref(v_val_3951_);
lean_dec_ref(v_F_3950_);
lean_dec_ref(v_x_3949_);
v___y_3961_ = v_a_3953_;
v___y_3962_ = v_a_3954_;
v___y_3963_ = v_a_3955_;
v___y_3964_ = v_a_3956_;
v___y_3965_ = v_a_3957_;
v___y_3966_ = v_a_3958_;
goto v___jp_3960_;
}
}
else
{
lean_dec(v___x_3991_);
lean_dec(v___x_3974_);
lean_dec_ref(v_k_3952_);
lean_dec_ref(v_val_3951_);
lean_dec_ref(v_F_3950_);
lean_dec_ref(v_x_3949_);
v___y_3961_ = v_a_3953_;
v___y_3962_ = v_a_3954_;
v___y_3963_ = v_a_3955_;
v___y_3964_ = v_a_3956_;
v___y_3965_ = v_a_3957_;
v___y_3966_ = v_a_3958_;
goto v___jp_3960_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1(lean_object* v___x_4066_, lean_object* v_a_4067_, lean_object* v_k_4068_, lean_object* v___x_4069_, lean_object* v___x_4070_, uint8_t v___x_4071_, uint8_t v___x_4072_, uint8_t v___x_4073_, lean_object* v_FNew_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_){
_start:
{
lean_object* v___x_4082_; 
lean_inc_ref(v_FNew_4074_);
lean_inc_ref(v___x_4066_);
v___x_4082_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v___x_4066_, v_FNew_4074_, v_a_4067_, v_k_4068_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
if (lean_obj_tag(v___x_4082_) == 0)
{
lean_object* v_a_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; 
v_a_4083_ = lean_ctor_get(v___x_4082_, 0);
lean_inc(v_a_4083_);
lean_dec_ref_known(v___x_4082_, 1);
v___x_4084_ = lean_mk_empty_array_with_capacity(v___x_4069_);
v___x_4085_ = lean_array_push(v___x_4084_, v___x_4070_);
v___x_4086_ = lean_array_push(v___x_4085_, v___x_4066_);
v___x_4087_ = lean_array_push(v___x_4086_, v_FNew_4074_);
v___x_4088_ = l_Lean_Meta_mkLambdaFVars(v___x_4087_, v_a_4083_, v___x_4071_, v___x_4072_, v___x_4071_, v___x_4072_, v___x_4073_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
lean_dec_ref(v___x_4087_);
return v___x_4088_;
}
else
{
lean_dec_ref(v_FNew_4074_);
lean_dec_ref(v___x_4070_);
lean_dec_ref(v___x_4066_);
return v___x_4082_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___boxed(lean_object* v_x_4089_, lean_object* v_F_4090_, lean_object* v_val_4091_, lean_object* v_k_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_, lean_object* v_a_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_){
_start:
{
lean_object* v_res_4100_; 
v_res_4100_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v_x_4089_, v_F_4090_, v_val_4091_, v_k_4092_, v_a_4093_, v_a_4094_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_);
lean_dec(v_a_4098_);
lean_dec_ref(v_a_4097_);
lean_dec(v_a_4096_);
lean_dec_ref(v_a_4095_);
lean_dec(v_a_4094_);
lean_dec_ref(v_a_4093_);
return v_res_4100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0(lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_){
_start:
{
lean_object* v___x_4114_; 
v___x_4114_ = l_Lean_Elab_WF_applyCleanWfTactic(v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
if (lean_obj_tag(v___x_4114_) == 0)
{
lean_object* v_ref_4115_; uint8_t v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; 
lean_dec_ref_known(v___x_4114_, 1);
v_ref_4115_ = lean_ctor_get(v___y_4111_, 4);
v___x_4116_ = 0;
v___x_4117_ = l_Lean_SourceInfo_fromRef(v_ref_4115_, v___x_4116_);
v___x_4118_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__1));
v___x_4119_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__2));
lean_inc(v___x_4117_);
v___x_4120_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4120_, 0, v___x_4117_);
lean_ctor_set(v___x_4120_, 1, v___x_4119_);
v___x_4121_ = l_Lean_Syntax_node1(v___x_4117_, v___x_4118_, v___x_4120_);
v___x_4122_ = l_Lean_Elab_Tactic_evalTactic(v___x_4121_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
return v___x_4122_;
}
else
{
return v___x_4114_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___boxed(lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_){
_start:
{
lean_object* v_res_4132_; 
v_res_4132_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0(v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_);
lean_dec(v___y_4130_);
lean_dec_ref(v___y_4129_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
lean_dec(v___y_4124_);
lean_dec_ref(v___y_4123_);
return v_res_4132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(lean_object* v_mvarId_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_){
_start:
{
lean_object* v___f_4142_; lean_object* v___x_4143_; 
v___f_4142_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___closed__0));
v___x_4143_ = l_Lean_Elab_Tactic_run(v_mvarId_4134_, v___f_4142_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_);
if (lean_obj_tag(v___x_4143_) == 0)
{
lean_object* v_a_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4154_; 
v_a_4144_ = lean_ctor_get(v___x_4143_, 0);
v_isSharedCheck_4154_ = !lean_is_exclusive(v___x_4143_);
if (v_isSharedCheck_4154_ == 0)
{
v___x_4146_ = v___x_4143_;
v_isShared_4147_ = v_isSharedCheck_4154_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_a_4144_);
lean_dec(v___x_4143_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4154_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
uint8_t v___x_4148_; 
v___x_4148_ = l_List_isEmpty___redArg(v_a_4144_);
if (v___x_4148_ == 0)
{
lean_object* v___x_4149_; 
lean_del_object(v___x_4146_);
v___x_4149_ = l_Lean_Elab_Term_reportUnsolvedGoals(v_a_4144_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_);
return v___x_4149_;
}
else
{
lean_object* v___x_4150_; lean_object* v___x_4152_; 
lean_dec(v_a_4144_);
v___x_4150_ = lean_box(0);
if (v_isShared_4147_ == 0)
{
lean_ctor_set(v___x_4146_, 0, v___x_4150_);
v___x_4152_ = v___x_4146_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v___x_4150_);
v___x_4152_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
return v___x_4152_;
}
}
}
}
else
{
lean_object* v_a_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4162_; 
v_a_4155_ = lean_ctor_get(v___x_4143_, 0);
v_isSharedCheck_4162_ = !lean_is_exclusive(v___x_4143_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4157_ = v___x_4143_;
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
else
{
lean_inc(v_a_4155_);
lean_dec(v___x_4143_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
lean_object* v___x_4160_; 
if (v_isShared_4158_ == 0)
{
v___x_4160_ = v___x_4157_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v_a_4155_);
v___x_4160_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
return v___x_4160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___boxed(lean_object* v_mvarId_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_){
_start:
{
lean_object* v_res_4171_; 
v_res_4171_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(v_mvarId_4163_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_);
lean_dec(v_a_4169_);
lean_dec_ref(v_a_4168_);
lean_dec(v_a_4167_);
lean_dec_ref(v_a_4166_);
lean_dec(v_a_4165_);
lean_dec_ref(v_a_4164_);
return v_res_4171_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(lean_object* v_x_4172_, lean_object* v_x_4173_, lean_object* v_x_4174_, lean_object* v_x_4175_){
_start:
{
lean_object* v_ks_4176_; lean_object* v_vs_4177_; lean_object* v___x_4179_; uint8_t v_isShared_4180_; uint8_t v_isSharedCheck_4201_; 
v_ks_4176_ = lean_ctor_get(v_x_4172_, 0);
v_vs_4177_ = lean_ctor_get(v_x_4172_, 1);
v_isSharedCheck_4201_ = !lean_is_exclusive(v_x_4172_);
if (v_isSharedCheck_4201_ == 0)
{
v___x_4179_ = v_x_4172_;
v_isShared_4180_ = v_isSharedCheck_4201_;
goto v_resetjp_4178_;
}
else
{
lean_inc(v_vs_4177_);
lean_inc(v_ks_4176_);
lean_dec(v_x_4172_);
v___x_4179_ = lean_box(0);
v_isShared_4180_ = v_isSharedCheck_4201_;
goto v_resetjp_4178_;
}
v_resetjp_4178_:
{
lean_object* v___x_4181_; uint8_t v___x_4182_; 
v___x_4181_ = lean_array_get_size(v_ks_4176_);
v___x_4182_ = lean_nat_dec_lt(v_x_4173_, v___x_4181_);
if (v___x_4182_ == 0)
{
lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4186_; 
lean_dec(v_x_4173_);
v___x_4183_ = lean_array_push(v_ks_4176_, v_x_4174_);
v___x_4184_ = lean_array_push(v_vs_4177_, v_x_4175_);
if (v_isShared_4180_ == 0)
{
lean_ctor_set(v___x_4179_, 1, v___x_4184_);
lean_ctor_set(v___x_4179_, 0, v___x_4183_);
v___x_4186_ = v___x_4179_;
goto v_reusejp_4185_;
}
else
{
lean_object* v_reuseFailAlloc_4187_; 
v_reuseFailAlloc_4187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4187_, 0, v___x_4183_);
lean_ctor_set(v_reuseFailAlloc_4187_, 1, v___x_4184_);
v___x_4186_ = v_reuseFailAlloc_4187_;
goto v_reusejp_4185_;
}
v_reusejp_4185_:
{
return v___x_4186_;
}
}
else
{
lean_object* v_k_x27_4188_; uint8_t v___x_4189_; 
v_k_x27_4188_ = lean_array_fget_borrowed(v_ks_4176_, v_x_4173_);
v___x_4189_ = l_Lean_instBEqMVarId_beq(v_x_4174_, v_k_x27_4188_);
if (v___x_4189_ == 0)
{
lean_object* v___x_4191_; 
if (v_isShared_4180_ == 0)
{
v___x_4191_ = v___x_4179_;
goto v_reusejp_4190_;
}
else
{
lean_object* v_reuseFailAlloc_4195_; 
v_reuseFailAlloc_4195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4195_, 0, v_ks_4176_);
lean_ctor_set(v_reuseFailAlloc_4195_, 1, v_vs_4177_);
v___x_4191_ = v_reuseFailAlloc_4195_;
goto v_reusejp_4190_;
}
v_reusejp_4190_:
{
lean_object* v___x_4192_; lean_object* v___x_4193_; 
v___x_4192_ = lean_unsigned_to_nat(1u);
v___x_4193_ = lean_nat_add(v_x_4173_, v___x_4192_);
lean_dec(v_x_4173_);
v_x_4172_ = v___x_4191_;
v_x_4173_ = v___x_4193_;
goto _start;
}
}
else
{
lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4199_; 
v___x_4196_ = lean_array_fset(v_ks_4176_, v_x_4173_, v_x_4174_);
v___x_4197_ = lean_array_fset(v_vs_4177_, v_x_4173_, v_x_4175_);
lean_dec(v_x_4173_);
if (v_isShared_4180_ == 0)
{
lean_ctor_set(v___x_4179_, 1, v___x_4197_);
lean_ctor_set(v___x_4179_, 0, v___x_4196_);
v___x_4199_ = v___x_4179_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v___x_4196_);
lean_ctor_set(v_reuseFailAlloc_4200_, 1, v___x_4197_);
v___x_4199_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
return v___x_4199_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_4202_, lean_object* v_k_4203_, lean_object* v_v_4204_){
_start:
{
lean_object* v___x_4205_; lean_object* v___x_4206_; 
v___x_4205_ = lean_unsigned_to_nat(0u);
v___x_4206_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_n_4202_, v___x_4205_, v_k_4203_, v_v_4204_);
return v___x_4206_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4207_; 
v___x_4207_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(lean_object* v_x_4208_, size_t v_x_4209_, size_t v_x_4210_, lean_object* v_x_4211_, lean_object* v_x_4212_){
_start:
{
if (lean_obj_tag(v_x_4208_) == 0)
{
lean_object* v_es_4213_; size_t v___x_4214_; size_t v___x_4215_; lean_object* v_j_4216_; lean_object* v___x_4217_; uint8_t v___x_4218_; 
v_es_4213_ = lean_ctor_get(v_x_4208_, 0);
v___x_4214_ = ((size_t)31ULL);
v___x_4215_ = lean_usize_land(v_x_4209_, v___x_4214_);
v_j_4216_ = lean_usize_to_nat(v___x_4215_);
v___x_4217_ = lean_array_get_size(v_es_4213_);
v___x_4218_ = lean_nat_dec_lt(v_j_4216_, v___x_4217_);
if (v___x_4218_ == 0)
{
lean_dec(v_j_4216_);
lean_dec(v_x_4212_);
lean_dec(v_x_4211_);
return v_x_4208_;
}
else
{
lean_object* v___x_4220_; uint8_t v_isShared_4221_; uint8_t v_isSharedCheck_4257_; 
lean_inc_ref(v_es_4213_);
v_isSharedCheck_4257_ = !lean_is_exclusive(v_x_4208_);
if (v_isSharedCheck_4257_ == 0)
{
lean_object* v_unused_4258_; 
v_unused_4258_ = lean_ctor_get(v_x_4208_, 0);
lean_dec(v_unused_4258_);
v___x_4220_ = v_x_4208_;
v_isShared_4221_ = v_isSharedCheck_4257_;
goto v_resetjp_4219_;
}
else
{
lean_dec(v_x_4208_);
v___x_4220_ = lean_box(0);
v_isShared_4221_ = v_isSharedCheck_4257_;
goto v_resetjp_4219_;
}
v_resetjp_4219_:
{
lean_object* v_v_4222_; lean_object* v___x_4223_; lean_object* v_xs_x27_4224_; lean_object* v___y_4226_; 
v_v_4222_ = lean_array_fget(v_es_4213_, v_j_4216_);
v___x_4223_ = lean_box(0);
v_xs_x27_4224_ = lean_array_fset(v_es_4213_, v_j_4216_, v___x_4223_);
switch(lean_obj_tag(v_v_4222_))
{
case 0:
{
lean_object* v_key_4231_; lean_object* v_val_4232_; lean_object* v___x_4234_; uint8_t v_isShared_4235_; uint8_t v_isSharedCheck_4242_; 
v_key_4231_ = lean_ctor_get(v_v_4222_, 0);
v_val_4232_ = lean_ctor_get(v_v_4222_, 1);
v_isSharedCheck_4242_ = !lean_is_exclusive(v_v_4222_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4234_ = v_v_4222_;
v_isShared_4235_ = v_isSharedCheck_4242_;
goto v_resetjp_4233_;
}
else
{
lean_inc(v_val_4232_);
lean_inc(v_key_4231_);
lean_dec(v_v_4222_);
v___x_4234_ = lean_box(0);
v_isShared_4235_ = v_isSharedCheck_4242_;
goto v_resetjp_4233_;
}
v_resetjp_4233_:
{
uint8_t v___x_4236_; 
v___x_4236_ = l_Lean_instBEqMVarId_beq(v_x_4211_, v_key_4231_);
if (v___x_4236_ == 0)
{
lean_object* v___x_4237_; lean_object* v___x_4238_; 
lean_del_object(v___x_4234_);
v___x_4237_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4231_, v_val_4232_, v_x_4211_, v_x_4212_);
v___x_4238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4238_, 0, v___x_4237_);
v___y_4226_ = v___x_4238_;
goto v___jp_4225_;
}
else
{
lean_object* v___x_4240_; 
lean_dec(v_val_4232_);
lean_dec(v_key_4231_);
if (v_isShared_4235_ == 0)
{
lean_ctor_set(v___x_4234_, 1, v_x_4212_);
lean_ctor_set(v___x_4234_, 0, v_x_4211_);
v___x_4240_ = v___x_4234_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v_x_4211_);
lean_ctor_set(v_reuseFailAlloc_4241_, 1, v_x_4212_);
v___x_4240_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4239_;
}
v_reusejp_4239_:
{
v___y_4226_ = v___x_4240_;
goto v___jp_4225_;
}
}
}
}
case 1:
{
lean_object* v_node_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4255_; 
v_node_4243_ = lean_ctor_get(v_v_4222_, 0);
v_isSharedCheck_4255_ = !lean_is_exclusive(v_v_4222_);
if (v_isSharedCheck_4255_ == 0)
{
v___x_4245_ = v_v_4222_;
v_isShared_4246_ = v_isSharedCheck_4255_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_node_4243_);
lean_dec(v_v_4222_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4255_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
size_t v___x_4247_; size_t v___x_4248_; size_t v___x_4249_; size_t v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4253_; 
v___x_4247_ = ((size_t)5ULL);
v___x_4248_ = lean_usize_shift_right(v_x_4209_, v___x_4247_);
v___x_4249_ = ((size_t)1ULL);
v___x_4250_ = lean_usize_add(v_x_4210_, v___x_4249_);
v___x_4251_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_node_4243_, v___x_4248_, v___x_4250_, v_x_4211_, v_x_4212_);
if (v_isShared_4246_ == 0)
{
lean_ctor_set(v___x_4245_, 0, v___x_4251_);
v___x_4253_ = v___x_4245_;
goto v_reusejp_4252_;
}
else
{
lean_object* v_reuseFailAlloc_4254_; 
v_reuseFailAlloc_4254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4254_, 0, v___x_4251_);
v___x_4253_ = v_reuseFailAlloc_4254_;
goto v_reusejp_4252_;
}
v_reusejp_4252_:
{
v___y_4226_ = v___x_4253_;
goto v___jp_4225_;
}
}
}
default: 
{
lean_object* v___x_4256_; 
v___x_4256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4256_, 0, v_x_4211_);
lean_ctor_set(v___x_4256_, 1, v_x_4212_);
v___y_4226_ = v___x_4256_;
goto v___jp_4225_;
}
}
v___jp_4225_:
{
lean_object* v___x_4227_; lean_object* v___x_4229_; 
v___x_4227_ = lean_array_fset(v_xs_x27_4224_, v_j_4216_, v___y_4226_);
lean_dec(v_j_4216_);
if (v_isShared_4221_ == 0)
{
lean_ctor_set(v___x_4220_, 0, v___x_4227_);
v___x_4229_ = v___x_4220_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v___x_4227_);
v___x_4229_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
return v___x_4229_;
}
}
}
}
}
else
{
lean_object* v_ks_4259_; lean_object* v_vs_4260_; lean_object* v___x_4262_; uint8_t v_isShared_4263_; uint8_t v_isSharedCheck_4278_; 
v_ks_4259_ = lean_ctor_get(v_x_4208_, 0);
v_vs_4260_ = lean_ctor_get(v_x_4208_, 1);
v_isSharedCheck_4278_ = !lean_is_exclusive(v_x_4208_);
if (v_isSharedCheck_4278_ == 0)
{
v___x_4262_ = v_x_4208_;
v_isShared_4263_ = v_isSharedCheck_4278_;
goto v_resetjp_4261_;
}
else
{
lean_inc(v_vs_4260_);
lean_inc(v_ks_4259_);
lean_dec(v_x_4208_);
v___x_4262_ = lean_box(0);
v_isShared_4263_ = v_isSharedCheck_4278_;
goto v_resetjp_4261_;
}
v_resetjp_4261_:
{
lean_object* v___x_4265_; 
if (v_isShared_4263_ == 0)
{
v___x_4265_ = v___x_4262_;
goto v_reusejp_4264_;
}
else
{
lean_object* v_reuseFailAlloc_4277_; 
v_reuseFailAlloc_4277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4277_, 0, v_ks_4259_);
lean_ctor_set(v_reuseFailAlloc_4277_, 1, v_vs_4260_);
v___x_4265_ = v_reuseFailAlloc_4277_;
goto v_reusejp_4264_;
}
v_reusejp_4264_:
{
lean_object* v_newNode_4266_; size_t v___x_4267_; uint8_t v___x_4268_; 
v_newNode_4266_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(v___x_4265_, v_x_4211_, v_x_4212_);
v___x_4267_ = ((size_t)7ULL);
v___x_4268_ = lean_usize_dec_le(v___x_4267_, v_x_4210_);
if (v___x_4268_ == 0)
{
lean_object* v___x_4269_; lean_object* v___x_4270_; uint8_t v___x_4271_; 
v___x_4269_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4266_);
v___x_4270_ = lean_unsigned_to_nat(4u);
v___x_4271_ = lean_nat_dec_lt(v___x_4269_, v___x_4270_);
lean_dec(v___x_4269_);
if (v___x_4271_ == 0)
{
lean_object* v_ks_4272_; lean_object* v_vs_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; 
v_ks_4272_ = lean_ctor_get(v_newNode_4266_, 0);
lean_inc_ref(v_ks_4272_);
v_vs_4273_ = lean_ctor_get(v_newNode_4266_, 1);
lean_inc_ref(v_vs_4273_);
lean_dec_ref(v_newNode_4266_);
v___x_4274_ = lean_unsigned_to_nat(0u);
v___x_4275_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_4276_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_x_4210_, v_ks_4272_, v_vs_4273_, v___x_4274_, v___x_4275_);
lean_dec_ref(v_vs_4273_);
lean_dec_ref(v_ks_4272_);
return v___x_4276_;
}
else
{
return v_newNode_4266_;
}
}
else
{
return v_newNode_4266_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_4279_, lean_object* v_keys_4280_, lean_object* v_vals_4281_, lean_object* v_i_4282_, lean_object* v_entries_4283_){
_start:
{
lean_object* v___x_4284_; uint8_t v___x_4285_; 
v___x_4284_ = lean_array_get_size(v_keys_4280_);
v___x_4285_ = lean_nat_dec_lt(v_i_4282_, v___x_4284_);
if (v___x_4285_ == 0)
{
lean_dec(v_i_4282_);
return v_entries_4283_;
}
else
{
lean_object* v_k_4286_; lean_object* v_v_4287_; uint64_t v___x_4288_; size_t v_h_4289_; size_t v___x_4290_; lean_object* v___x_4291_; size_t v___x_4292_; size_t v___x_4293_; size_t v___x_4294_; size_t v_h_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; 
v_k_4286_ = lean_array_fget_borrowed(v_keys_4280_, v_i_4282_);
v_v_4287_ = lean_array_fget_borrowed(v_vals_4281_, v_i_4282_);
v___x_4288_ = l_Lean_instHashableMVarId_hash(v_k_4286_);
v_h_4289_ = lean_uint64_to_usize(v___x_4288_);
v___x_4290_ = ((size_t)5ULL);
v___x_4291_ = lean_unsigned_to_nat(1u);
v___x_4292_ = ((size_t)1ULL);
v___x_4293_ = lean_usize_sub(v_depth_4279_, v___x_4292_);
v___x_4294_ = lean_usize_mul(v___x_4290_, v___x_4293_);
v_h_4295_ = lean_usize_shift_right(v_h_4289_, v___x_4294_);
v___x_4296_ = lean_nat_add(v_i_4282_, v___x_4291_);
lean_dec(v_i_4282_);
lean_inc(v_v_4287_);
lean_inc(v_k_4286_);
v___x_4297_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_entries_4283_, v_h_4295_, v_depth_4279_, v_k_4286_, v_v_4287_);
v_i_4282_ = v___x_4296_;
v_entries_4283_ = v___x_4297_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_4299_, lean_object* v_keys_4300_, lean_object* v_vals_4301_, lean_object* v_i_4302_, lean_object* v_entries_4303_){
_start:
{
size_t v_depth_boxed_4304_; lean_object* v_res_4305_; 
v_depth_boxed_4304_ = lean_unbox_usize(v_depth_4299_);
lean_dec(v_depth_4299_);
v_res_4305_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_4304_, v_keys_4300_, v_vals_4301_, v_i_4302_, v_entries_4303_);
lean_dec_ref(v_vals_4301_);
lean_dec_ref(v_keys_4300_);
return v_res_4305_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_4306_, lean_object* v_x_4307_, lean_object* v_x_4308_, lean_object* v_x_4309_, lean_object* v_x_4310_){
_start:
{
size_t v_x_3982__boxed_4311_; size_t v_x_3983__boxed_4312_; lean_object* v_res_4313_; 
v_x_3982__boxed_4311_ = lean_unbox_usize(v_x_4307_);
lean_dec(v_x_4307_);
v_x_3983__boxed_4312_ = lean_unbox_usize(v_x_4308_);
lean_dec(v_x_4308_);
v_res_4313_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4306_, v_x_3982__boxed_4311_, v_x_3983__boxed_4312_, v_x_4309_, v_x_4310_);
return v_res_4313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(lean_object* v_x_4314_, lean_object* v_x_4315_, lean_object* v_x_4316_){
_start:
{
uint64_t v___x_4317_; size_t v___x_4318_; size_t v___x_4319_; lean_object* v___x_4320_; 
v___x_4317_ = l_Lean_instHashableMVarId_hash(v_x_4315_);
v___x_4318_ = lean_uint64_to_usize(v___x_4317_);
v___x_4319_ = ((size_t)1ULL);
v___x_4320_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4314_, v___x_4318_, v___x_4319_, v_x_4315_, v_x_4316_);
return v___x_4320_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(lean_object* v_mvarId_4321_, lean_object* v_val_4322_, lean_object* v___y_4323_){
_start:
{
lean_object* v___x_4325_; lean_object* v_mctx_4326_; lean_object* v_cache_4327_; lean_object* v_zetaDeltaFVarIds_4328_; lean_object* v_postponed_4329_; lean_object* v_diag_4330_; lean_object* v___x_4332_; uint8_t v_isShared_4333_; uint8_t v_isSharedCheck_4359_; 
v___x_4325_ = lean_st_ref_take(v___y_4323_);
v_mctx_4326_ = lean_ctor_get(v___x_4325_, 0);
v_cache_4327_ = lean_ctor_get(v___x_4325_, 1);
v_zetaDeltaFVarIds_4328_ = lean_ctor_get(v___x_4325_, 2);
v_postponed_4329_ = lean_ctor_get(v___x_4325_, 3);
v_diag_4330_ = lean_ctor_get(v___x_4325_, 4);
v_isSharedCheck_4359_ = !lean_is_exclusive(v___x_4325_);
if (v_isSharedCheck_4359_ == 0)
{
v___x_4332_ = v___x_4325_;
v_isShared_4333_ = v_isSharedCheck_4359_;
goto v_resetjp_4331_;
}
else
{
lean_inc(v_diag_4330_);
lean_inc(v_postponed_4329_);
lean_inc(v_zetaDeltaFVarIds_4328_);
lean_inc(v_cache_4327_);
lean_inc(v_mctx_4326_);
lean_dec(v___x_4325_);
v___x_4332_ = lean_box(0);
v_isShared_4333_ = v_isSharedCheck_4359_;
goto v_resetjp_4331_;
}
v_resetjp_4331_:
{
lean_object* v_depth_4334_; lean_object* v_levelAssignDepth_4335_; lean_object* v_lmvarCounter_4336_; lean_object* v_mvarCounter_4337_; lean_object* v_lDecls_4338_; lean_object* v_decls_4339_; lean_object* v_userNames_4340_; lean_object* v_lAssignment_4341_; lean_object* v_eAssignment_4342_; lean_object* v_dAssignment_4343_; lean_object* v_instanceTypedMVars_4344_; lean_object* v___x_4346_; uint8_t v_isShared_4347_; uint8_t v_isSharedCheck_4358_; 
v_depth_4334_ = lean_ctor_get(v_mctx_4326_, 0);
v_levelAssignDepth_4335_ = lean_ctor_get(v_mctx_4326_, 1);
v_lmvarCounter_4336_ = lean_ctor_get(v_mctx_4326_, 2);
v_mvarCounter_4337_ = lean_ctor_get(v_mctx_4326_, 3);
v_lDecls_4338_ = lean_ctor_get(v_mctx_4326_, 4);
v_decls_4339_ = lean_ctor_get(v_mctx_4326_, 5);
v_userNames_4340_ = lean_ctor_get(v_mctx_4326_, 6);
v_lAssignment_4341_ = lean_ctor_get(v_mctx_4326_, 7);
v_eAssignment_4342_ = lean_ctor_get(v_mctx_4326_, 8);
v_dAssignment_4343_ = lean_ctor_get(v_mctx_4326_, 9);
v_instanceTypedMVars_4344_ = lean_ctor_get(v_mctx_4326_, 10);
v_isSharedCheck_4358_ = !lean_is_exclusive(v_mctx_4326_);
if (v_isSharedCheck_4358_ == 0)
{
v___x_4346_ = v_mctx_4326_;
v_isShared_4347_ = v_isSharedCheck_4358_;
goto v_resetjp_4345_;
}
else
{
lean_inc(v_instanceTypedMVars_4344_);
lean_inc(v_dAssignment_4343_);
lean_inc(v_eAssignment_4342_);
lean_inc(v_lAssignment_4341_);
lean_inc(v_userNames_4340_);
lean_inc(v_decls_4339_);
lean_inc(v_lDecls_4338_);
lean_inc(v_mvarCounter_4337_);
lean_inc(v_lmvarCounter_4336_);
lean_inc(v_levelAssignDepth_4335_);
lean_inc(v_depth_4334_);
lean_dec(v_mctx_4326_);
v___x_4346_ = lean_box(0);
v_isShared_4347_ = v_isSharedCheck_4358_;
goto v_resetjp_4345_;
}
v_resetjp_4345_:
{
lean_object* v___x_4348_; lean_object* v___x_4350_; 
v___x_4348_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(v_eAssignment_4342_, v_mvarId_4321_, v_val_4322_);
if (v_isShared_4347_ == 0)
{
lean_ctor_set(v___x_4346_, 8, v___x_4348_);
v___x_4350_ = v___x_4346_;
goto v_reusejp_4349_;
}
else
{
lean_object* v_reuseFailAlloc_4357_; 
v_reuseFailAlloc_4357_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_4357_, 0, v_depth_4334_);
lean_ctor_set(v_reuseFailAlloc_4357_, 1, v_levelAssignDepth_4335_);
lean_ctor_set(v_reuseFailAlloc_4357_, 2, v_lmvarCounter_4336_);
lean_ctor_set(v_reuseFailAlloc_4357_, 3, v_mvarCounter_4337_);
lean_ctor_set(v_reuseFailAlloc_4357_, 4, v_lDecls_4338_);
lean_ctor_set(v_reuseFailAlloc_4357_, 5, v_decls_4339_);
lean_ctor_set(v_reuseFailAlloc_4357_, 6, v_userNames_4340_);
lean_ctor_set(v_reuseFailAlloc_4357_, 7, v_lAssignment_4341_);
lean_ctor_set(v_reuseFailAlloc_4357_, 8, v___x_4348_);
lean_ctor_set(v_reuseFailAlloc_4357_, 9, v_dAssignment_4343_);
lean_ctor_set(v_reuseFailAlloc_4357_, 10, v_instanceTypedMVars_4344_);
v___x_4350_ = v_reuseFailAlloc_4357_;
goto v_reusejp_4349_;
}
v_reusejp_4349_:
{
lean_object* v___x_4352_; 
if (v_isShared_4333_ == 0)
{
lean_ctor_set(v___x_4332_, 0, v___x_4350_);
v___x_4352_ = v___x_4332_;
goto v_reusejp_4351_;
}
else
{
lean_object* v_reuseFailAlloc_4356_; 
v_reuseFailAlloc_4356_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4356_, 0, v___x_4350_);
lean_ctor_set(v_reuseFailAlloc_4356_, 1, v_cache_4327_);
lean_ctor_set(v_reuseFailAlloc_4356_, 2, v_zetaDeltaFVarIds_4328_);
lean_ctor_set(v_reuseFailAlloc_4356_, 3, v_postponed_4329_);
lean_ctor_set(v_reuseFailAlloc_4356_, 4, v_diag_4330_);
v___x_4352_ = v_reuseFailAlloc_4356_;
goto v_reusejp_4351_;
}
v_reusejp_4351_:
{
lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; 
v___x_4353_ = lean_st_ref_put(v___y_4323_, v___x_4352_);
v___x_4354_ = lean_box(0);
v___x_4355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4355_, 0, v___x_4354_);
return v___x_4355_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg___boxed(lean_object* v_mvarId_4360_, lean_object* v_val_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_){
_start:
{
lean_object* v_res_4364_; 
v_res_4364_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mvarId_4360_, v_val_4361_, v___y_4362_);
lean_dec(v___y_4362_);
return v_res_4364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___lam__0(lean_object* v_mv_u2081_4369_, lean_object* v_mv_u2082_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_){
_start:
{
lean_object* v___x_4379_; 
lean_inc(v_mv_u2081_4369_);
v___x_4379_ = l_Lean_MVarId_getDecl(v_mv_u2081_4369_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_);
if (lean_obj_tag(v___x_4379_) == 0)
{
lean_object* v_a_4380_; lean_object* v___x_4381_; 
v_a_4380_ = lean_ctor_get(v___x_4379_, 0);
lean_inc(v_a_4380_);
lean_dec_ref_known(v___x_4379_, 1);
lean_inc(v_mv_u2082_4370_);
v___x_4381_ = l_Lean_MVarId_getDecl(v_mv_u2082_4370_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_);
if (lean_obj_tag(v___x_4381_) == 0)
{
lean_object* v_a_4382_; lean_object* v_lctx_4383_; lean_object* v_type_4384_; lean_object* v_lctx_4385_; lean_object* v_type_4386_; uint8_t v___x_4387_; 
v_a_4382_ = lean_ctor_get(v___x_4381_, 0);
lean_inc(v_a_4382_);
lean_dec_ref_known(v___x_4381_, 1);
v_lctx_4383_ = lean_ctor_get(v_a_4380_, 1);
lean_inc_ref(v_lctx_4383_);
v_type_4384_ = lean_ctor_get(v_a_4380_, 2);
lean_inc_ref(v_type_4384_);
lean_dec(v_a_4380_);
v_lctx_4385_ = lean_ctor_get(v_a_4382_, 1);
lean_inc_ref(v_lctx_4385_);
v_type_4386_ = lean_ctor_get(v_a_4382_, 2);
lean_inc_ref(v_type_4386_);
lean_dec(v_a_4382_);
v___x_4387_ = lean_expr_eqv(v_type_4384_, v_type_4386_);
lean_dec_ref(v_type_4386_);
lean_dec_ref(v_type_4384_);
if (v___x_4387_ == 0)
{
lean_dec_ref(v_lctx_4385_);
lean_dec_ref(v_lctx_4383_);
lean_dec(v_mv_u2082_4370_);
lean_dec(v_mv_u2081_4369_);
goto v___jp_4376_;
}
else
{
lean_object* v___x_4388_; uint8_t v___x_4389_; 
v___x_4388_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
v___x_4389_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_4383_, v_lctx_4385_, v___x_4388_);
if (v___x_4389_ == 0)
{
uint8_t v___x_4390_; 
v___x_4390_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_4385_, v_lctx_4383_, v___x_4388_);
lean_dec_ref(v_lctx_4383_);
lean_dec_ref(v_lctx_4385_);
if (v___x_4390_ == 0)
{
lean_dec(v_mv_u2082_4370_);
lean_dec(v_mv_u2081_4369_);
goto v___jp_4376_;
}
else
{
lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4394_; uint8_t v_isShared_4395_; uint8_t v_isSharedCheck_4402_; 
v___x_4391_ = l_Lean_Expr_mvar___override(v_mv_u2082_4370_);
v___x_4392_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mv_u2081_4369_, v___x_4391_, v___y_4372_);
v_isSharedCheck_4402_ = !lean_is_exclusive(v___x_4392_);
if (v_isSharedCheck_4402_ == 0)
{
lean_object* v_unused_4403_; 
v_unused_4403_ = lean_ctor_get(v___x_4392_, 0);
lean_dec(v_unused_4403_);
v___x_4394_ = v___x_4392_;
v_isShared_4395_ = v_isSharedCheck_4402_;
goto v_resetjp_4393_;
}
else
{
lean_dec(v___x_4392_);
v___x_4394_ = lean_box(0);
v_isShared_4395_ = v_isSharedCheck_4402_;
goto v_resetjp_4393_;
}
v_resetjp_4393_:
{
lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4400_; 
v___x_4396_ = lean_box(v___x_4389_);
v___x_4397_ = lean_box(v___x_4387_);
v___x_4398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4398_, 0, v___x_4396_);
lean_ctor_set(v___x_4398_, 1, v___x_4397_);
if (v_isShared_4395_ == 0)
{
lean_ctor_set(v___x_4394_, 0, v___x_4398_);
v___x_4400_ = v___x_4394_;
goto v_reusejp_4399_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v___x_4398_);
v___x_4400_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4399_;
}
v_reusejp_4399_:
{
return v___x_4400_;
}
}
}
}
else
{
lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4407_; uint8_t v_isShared_4408_; uint8_t v_isSharedCheck_4416_; 
lean_dec_ref(v_lctx_4385_);
lean_dec_ref(v_lctx_4383_);
v___x_4404_ = l_Lean_Expr_mvar___override(v_mv_u2081_4369_);
v___x_4405_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mv_u2082_4370_, v___x_4404_, v___y_4372_);
v_isSharedCheck_4416_ = !lean_is_exclusive(v___x_4405_);
if (v_isSharedCheck_4416_ == 0)
{
lean_object* v_unused_4417_; 
v_unused_4417_ = lean_ctor_get(v___x_4405_, 0);
lean_dec(v_unused_4417_);
v___x_4407_ = v___x_4405_;
v_isShared_4408_ = v_isSharedCheck_4416_;
goto v_resetjp_4406_;
}
else
{
lean_dec(v___x_4405_);
v___x_4407_ = lean_box(0);
v_isShared_4408_ = v_isSharedCheck_4416_;
goto v_resetjp_4406_;
}
v_resetjp_4406_:
{
uint8_t v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4414_; 
v___x_4409_ = 0;
v___x_4410_ = lean_box(v___x_4387_);
v___x_4411_ = lean_box(v___x_4409_);
v___x_4412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4412_, 0, v___x_4410_);
lean_ctor_set(v___x_4412_, 1, v___x_4411_);
if (v_isShared_4408_ == 0)
{
lean_ctor_set(v___x_4407_, 0, v___x_4412_);
v___x_4414_ = v___x_4407_;
goto v_reusejp_4413_;
}
else
{
lean_object* v_reuseFailAlloc_4415_; 
v_reuseFailAlloc_4415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4415_, 0, v___x_4412_);
v___x_4414_ = v_reuseFailAlloc_4415_;
goto v_reusejp_4413_;
}
v_reusejp_4413_:
{
return v___x_4414_;
}
}
}
}
}
else
{
lean_object* v_a_4418_; lean_object* v___x_4420_; uint8_t v_isShared_4421_; uint8_t v_isSharedCheck_4425_; 
lean_dec(v_a_4380_);
lean_dec(v_mv_u2082_4370_);
lean_dec(v_mv_u2081_4369_);
v_a_4418_ = lean_ctor_get(v___x_4381_, 0);
v_isSharedCheck_4425_ = !lean_is_exclusive(v___x_4381_);
if (v_isSharedCheck_4425_ == 0)
{
v___x_4420_ = v___x_4381_;
v_isShared_4421_ = v_isSharedCheck_4425_;
goto v_resetjp_4419_;
}
else
{
lean_inc(v_a_4418_);
lean_dec(v___x_4381_);
v___x_4420_ = lean_box(0);
v_isShared_4421_ = v_isSharedCheck_4425_;
goto v_resetjp_4419_;
}
v_resetjp_4419_:
{
lean_object* v___x_4423_; 
if (v_isShared_4421_ == 0)
{
v___x_4423_ = v___x_4420_;
goto v_reusejp_4422_;
}
else
{
lean_object* v_reuseFailAlloc_4424_; 
v_reuseFailAlloc_4424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4424_, 0, v_a_4418_);
v___x_4423_ = v_reuseFailAlloc_4424_;
goto v_reusejp_4422_;
}
v_reusejp_4422_:
{
return v___x_4423_;
}
}
}
}
else
{
lean_object* v_a_4426_; lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4433_; 
lean_dec(v_mv_u2082_4370_);
lean_dec(v_mv_u2081_4369_);
v_a_4426_ = lean_ctor_get(v___x_4379_, 0);
v_isSharedCheck_4433_ = !lean_is_exclusive(v___x_4379_);
if (v_isSharedCheck_4433_ == 0)
{
v___x_4428_ = v___x_4379_;
v_isShared_4429_ = v_isSharedCheck_4433_;
goto v_resetjp_4427_;
}
else
{
lean_inc(v_a_4426_);
lean_dec(v___x_4379_);
v___x_4428_ = lean_box(0);
v_isShared_4429_ = v_isSharedCheck_4433_;
goto v_resetjp_4427_;
}
v_resetjp_4427_:
{
lean_object* v___x_4431_; 
if (v_isShared_4429_ == 0)
{
v___x_4431_ = v___x_4428_;
goto v_reusejp_4430_;
}
else
{
lean_object* v_reuseFailAlloc_4432_; 
v_reuseFailAlloc_4432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4432_, 0, v_a_4426_);
v___x_4431_ = v_reuseFailAlloc_4432_;
goto v_reusejp_4430_;
}
v_reusejp_4430_:
{
return v___x_4431_;
}
}
}
v___jp_4376_:
{
lean_object* v___x_4377_; lean_object* v___x_4378_; 
v___x_4377_ = ((lean_object*)(l_Lean_Elab_WF_assignSubsumed___lam__0___closed__0));
v___x_4378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4378_, 0, v___x_4377_);
return v___x_4378_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___lam__0___boxed(lean_object* v_mv_u2081_4434_, lean_object* v_mv_u2082_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_){
_start:
{
lean_object* v_res_4441_; 
v_res_4441_ = l_Lean_Elab_WF_assignSubsumed___lam__0(v_mv_u2081_4434_, v_mv_u2082_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_);
lean_dec(v___y_4439_);
lean_dec_ref(v___y_4438_);
lean_dec(v___y_4437_);
lean_dec_ref(v___y_4436_);
return v_res_4441_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1(lean_object* v___x_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_){
_start:
{
lean_object* v___x_4448_; 
v___x_4448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4448_, 0, v___x_4442_);
return v___x_4448_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1___boxed(lean_object* v___x_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_){
_start:
{
lean_object* v_res_4455_; 
v_res_4455_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1(v___x_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_);
lean_dec(v___y_4453_);
lean_dec_ref(v___y_4452_);
lean_dec(v___y_4451_);
lean_dec_ref(v___y_4450_);
return v_res_4455_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0(lean_object* v_f_4456_, lean_object* v___x_4457_, lean_object* v___x_4458_, lean_object* v___x_4459_, lean_object* v_a_4460_, uint8_t v___x_4461_, lean_object* v_snd_4462_, lean_object* v_fst_4463_, lean_object* v_next_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_){
_start:
{
lean_object* v___x_4470_; 
v___x_4470_ = lean_apply_7(v_f_4456_, v___x_4457_, v___x_4458_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_, lean_box(0));
if (lean_obj_tag(v___x_4470_) == 0)
{
lean_object* v_a_4471_; lean_object* v___x_4473_; uint8_t v_isShared_4474_; uint8_t v_isSharedCheck_4506_; 
v_a_4471_ = lean_ctor_get(v___x_4470_, 0);
v_isSharedCheck_4506_ = !lean_is_exclusive(v___x_4470_);
if (v_isSharedCheck_4506_ == 0)
{
v___x_4473_ = v___x_4470_;
v_isShared_4474_ = v_isSharedCheck_4506_;
goto v_resetjp_4472_;
}
else
{
lean_inc(v_a_4471_);
lean_dec(v___x_4470_);
v___x_4473_ = lean_box(0);
v_isShared_4474_ = v_isSharedCheck_4506_;
goto v_resetjp_4472_;
}
v_resetjp_4472_:
{
lean_object* v_fst_4475_; lean_object* v_snd_4476_; lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4505_; 
v_fst_4475_ = lean_ctor_get(v_a_4471_, 0);
v_snd_4476_ = lean_ctor_get(v_a_4471_, 1);
v_isSharedCheck_4505_ = !lean_is_exclusive(v_a_4471_);
if (v_isSharedCheck_4505_ == 0)
{
v___x_4478_ = v_a_4471_;
v_isShared_4479_ = v_isSharedCheck_4505_;
goto v_resetjp_4477_;
}
else
{
lean_inc(v_snd_4476_);
lean_inc(v_fst_4475_);
lean_dec(v_a_4471_);
v___x_4478_ = lean_box(0);
v_isShared_4479_ = v_isSharedCheck_4505_;
goto v_resetjp_4477_;
}
v_resetjp_4477_:
{
lean_object* v_removed_4481_; lean_object* v_numRemoved_4482_; uint8_t v___x_4501_; 
v___x_4501_ = lean_unbox(v_fst_4475_);
lean_dec(v_fst_4475_);
if (v___x_4501_ == 0)
{
lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; 
v___x_4502_ = lean_nat_add(v_snd_4462_, v___x_4459_);
lean_dec(v_snd_4462_);
v___x_4503_ = lean_box(v___x_4461_);
v___x_4504_ = lean_array_set(v_fst_4463_, v_next_4464_, v___x_4503_);
v_removed_4481_ = v___x_4504_;
v_numRemoved_4482_ = v___x_4502_;
goto v___jp_4480_;
}
else
{
v_removed_4481_ = v_fst_4463_;
v_numRemoved_4482_ = v_snd_4462_;
goto v___jp_4480_;
}
v___jp_4480_:
{
uint8_t v___x_4483_; 
v___x_4483_ = lean_unbox(v_snd_4476_);
lean_dec(v_snd_4476_);
if (v___x_4483_ == 0)
{
lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4488_; 
v___x_4484_ = lean_nat_add(v_numRemoved_4482_, v___x_4459_);
lean_dec(v_numRemoved_4482_);
v___x_4485_ = lean_box(v___x_4461_);
v___x_4486_ = lean_array_set(v_removed_4481_, v_a_4460_, v___x_4485_);
if (v_isShared_4479_ == 0)
{
lean_ctor_set(v___x_4478_, 1, v___x_4484_);
lean_ctor_set(v___x_4478_, 0, v___x_4486_);
v___x_4488_ = v___x_4478_;
goto v_reusejp_4487_;
}
else
{
lean_object* v_reuseFailAlloc_4493_; 
v_reuseFailAlloc_4493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4493_, 0, v___x_4486_);
lean_ctor_set(v_reuseFailAlloc_4493_, 1, v___x_4484_);
v___x_4488_ = v_reuseFailAlloc_4493_;
goto v_reusejp_4487_;
}
v_reusejp_4487_:
{
lean_object* v___x_4489_; lean_object* v___x_4491_; 
v___x_4489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4489_, 0, v___x_4488_);
if (v_isShared_4474_ == 0)
{
lean_ctor_set(v___x_4473_, 0, v___x_4489_);
v___x_4491_ = v___x_4473_;
goto v_reusejp_4490_;
}
else
{
lean_object* v_reuseFailAlloc_4492_; 
v_reuseFailAlloc_4492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4492_, 0, v___x_4489_);
v___x_4491_ = v_reuseFailAlloc_4492_;
goto v_reusejp_4490_;
}
v_reusejp_4490_:
{
return v___x_4491_;
}
}
}
else
{
lean_object* v___x_4495_; 
if (v_isShared_4479_ == 0)
{
lean_ctor_set(v___x_4478_, 1, v_numRemoved_4482_);
lean_ctor_set(v___x_4478_, 0, v_removed_4481_);
v___x_4495_ = v___x_4478_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v_removed_4481_);
lean_ctor_set(v_reuseFailAlloc_4500_, 1, v_numRemoved_4482_);
v___x_4495_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
lean_object* v___x_4496_; lean_object* v___x_4498_; 
v___x_4496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4496_, 0, v___x_4495_);
if (v_isShared_4474_ == 0)
{
lean_ctor_set(v___x_4473_, 0, v___x_4496_);
v___x_4498_ = v___x_4473_;
goto v_reusejp_4497_;
}
else
{
lean_object* v_reuseFailAlloc_4499_; 
v_reuseFailAlloc_4499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4499_, 0, v___x_4496_);
v___x_4498_ = v_reuseFailAlloc_4499_;
goto v_reusejp_4497_;
}
v_reusejp_4497_:
{
return v___x_4498_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4507_; lean_object* v___x_4509_; uint8_t v_isShared_4510_; uint8_t v_isSharedCheck_4514_; 
lean_dec(v_fst_4463_);
lean_dec(v_snd_4462_);
v_a_4507_ = lean_ctor_get(v___x_4470_, 0);
v_isSharedCheck_4514_ = !lean_is_exclusive(v___x_4470_);
if (v_isSharedCheck_4514_ == 0)
{
v___x_4509_ = v___x_4470_;
v_isShared_4510_ = v_isSharedCheck_4514_;
goto v_resetjp_4508_;
}
else
{
lean_inc(v_a_4507_);
lean_dec(v___x_4470_);
v___x_4509_ = lean_box(0);
v_isShared_4510_ = v_isSharedCheck_4514_;
goto v_resetjp_4508_;
}
v_resetjp_4508_:
{
lean_object* v___x_4512_; 
if (v_isShared_4510_ == 0)
{
v___x_4512_ = v___x_4509_;
goto v_reusejp_4511_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_a_4507_);
v___x_4512_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4511_;
}
v_reusejp_4511_:
{
return v___x_4512_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_f_4515_, lean_object* v___x_4516_, lean_object* v___x_4517_, lean_object* v___x_4518_, lean_object* v_a_4519_, lean_object* v___x_4520_, lean_object* v_snd_4521_, lean_object* v_fst_4522_, lean_object* v_next_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_){
_start:
{
uint8_t v___x_4355__boxed_4529_; lean_object* v_res_4530_; 
v___x_4355__boxed_4529_ = lean_unbox(v___x_4520_);
v_res_4530_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0(v_f_4515_, v___x_4516_, v___x_4517_, v___x_4518_, v_a_4519_, v___x_4355__boxed_4529_, v_snd_4521_, v_fst_4522_, v_next_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_);
lean_dec(v_next_4523_);
lean_dec(v_a_4519_);
lean_dec(v___x_4518_);
return v_res_4530_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(lean_object* v_upperBound_4531_, lean_object* v_a_4532_, lean_object* v_next_4533_, lean_object* v_f_4534_, lean_object* v_a_4535_, lean_object* v_b_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_){
_start:
{
uint8_t v___x_4542_; 
v___x_4542_ = lean_nat_dec_lt(v_a_4535_, v_upperBound_4531_);
if (v___x_4542_ == 0)
{
lean_object* v___x_4543_; 
lean_dec(v_a_4535_);
lean_dec_ref(v_f_4534_);
lean_dec(v_next_4533_);
v___x_4543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4543_, 0, v_b_4536_);
return v___x_4543_;
}
else
{
lean_object* v_fst_4544_; lean_object* v_snd_4545_; lean_object* v___x_4547_; uint8_t v_isShared_4548_; uint8_t v_isSharedCheck_4592_; 
v_fst_4544_ = lean_ctor_get(v_b_4536_, 0);
v_snd_4545_ = lean_ctor_get(v_b_4536_, 1);
v_isSharedCheck_4592_ = !lean_is_exclusive(v_b_4536_);
if (v_isSharedCheck_4592_ == 0)
{
v___x_4547_ = v_b_4536_;
v_isShared_4548_ = v_isSharedCheck_4592_;
goto v_resetjp_4546_;
}
else
{
lean_inc(v_snd_4545_);
lean_inc(v_fst_4544_);
lean_dec(v_b_4536_);
v___x_4547_ = lean_box(0);
v_isShared_4548_ = v_isSharedCheck_4592_;
goto v_resetjp_4546_;
}
v_resetjp_4546_:
{
lean_object* v___x_4549_; lean_object* v___y_4551_; uint8_t v___y_4574_; uint8_t v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; uint8_t v___x_4587_; 
v___x_4549_ = lean_unsigned_to_nat(1u);
v___x_4584_ = 0;
v___x_4585_ = lean_box(v___x_4584_);
v___x_4586_ = lean_array_get(v___x_4585_, v_fst_4544_, v_next_4533_);
lean_dec(v___x_4585_);
v___x_4587_ = lean_unbox(v___x_4586_);
if (v___x_4587_ == 0)
{
lean_object* v___x_4588_; lean_object* v___x_4589_; uint8_t v___x_4590_; 
lean_dec(v___x_4586_);
v___x_4588_ = lean_box(v___x_4584_);
v___x_4589_ = lean_array_get(v___x_4588_, v_fst_4544_, v_a_4535_);
lean_dec(v___x_4588_);
v___x_4590_ = lean_unbox(v___x_4589_);
lean_dec(v___x_4589_);
v___y_4574_ = v___x_4590_;
goto v___jp_4573_;
}
else
{
uint8_t v___x_4591_; 
v___x_4591_ = lean_unbox(v___x_4586_);
lean_dec(v___x_4586_);
v___y_4574_ = v___x_4591_;
goto v___jp_4573_;
}
v___jp_4550_:
{
lean_object* v___x_4552_; 
lean_inc(v___y_4540_);
lean_inc_ref(v___y_4539_);
lean_inc(v___y_4538_);
lean_inc_ref(v___y_4537_);
v___x_4552_ = lean_apply_5(v___y_4551_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, lean_box(0));
if (lean_obj_tag(v___x_4552_) == 0)
{
lean_object* v_a_4553_; lean_object* v___x_4555_; uint8_t v_isShared_4556_; uint8_t v_isSharedCheck_4564_; 
v_a_4553_ = lean_ctor_get(v___x_4552_, 0);
v_isSharedCheck_4564_ = !lean_is_exclusive(v___x_4552_);
if (v_isSharedCheck_4564_ == 0)
{
v___x_4555_ = v___x_4552_;
v_isShared_4556_ = v_isSharedCheck_4564_;
goto v_resetjp_4554_;
}
else
{
lean_inc(v_a_4553_);
lean_dec(v___x_4552_);
v___x_4555_ = lean_box(0);
v_isShared_4556_ = v_isSharedCheck_4564_;
goto v_resetjp_4554_;
}
v_resetjp_4554_:
{
if (lean_obj_tag(v_a_4553_) == 0)
{
lean_object* v_a_4557_; lean_object* v___x_4559_; 
lean_dec(v_a_4535_);
lean_dec_ref(v_f_4534_);
lean_dec(v_next_4533_);
v_a_4557_ = lean_ctor_get(v_a_4553_, 0);
lean_inc(v_a_4557_);
lean_dec_ref_known(v_a_4553_, 1);
if (v_isShared_4556_ == 0)
{
lean_ctor_set(v___x_4555_, 0, v_a_4557_);
v___x_4559_ = v___x_4555_;
goto v_reusejp_4558_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v_a_4557_);
v___x_4559_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4558_;
}
v_reusejp_4558_:
{
return v___x_4559_;
}
}
else
{
lean_object* v_a_4561_; lean_object* v___x_4562_; 
lean_del_object(v___x_4555_);
v_a_4561_ = lean_ctor_get(v_a_4553_, 0);
lean_inc(v_a_4561_);
lean_dec_ref_known(v_a_4553_, 1);
v___x_4562_ = lean_nat_add(v_a_4535_, v___x_4549_);
lean_dec(v_a_4535_);
v_a_4535_ = v___x_4562_;
v_b_4536_ = v_a_4561_;
goto _start;
}
}
}
else
{
lean_object* v_a_4565_; lean_object* v___x_4567_; uint8_t v_isShared_4568_; uint8_t v_isSharedCheck_4572_; 
lean_dec(v_a_4535_);
lean_dec_ref(v_f_4534_);
lean_dec(v_next_4533_);
v_a_4565_ = lean_ctor_get(v___x_4552_, 0);
v_isSharedCheck_4572_ = !lean_is_exclusive(v___x_4552_);
if (v_isSharedCheck_4572_ == 0)
{
v___x_4567_ = v___x_4552_;
v_isShared_4568_ = v_isSharedCheck_4572_;
goto v_resetjp_4566_;
}
else
{
lean_inc(v_a_4565_);
lean_dec(v___x_4552_);
v___x_4567_ = lean_box(0);
v_isShared_4568_ = v_isSharedCheck_4572_;
goto v_resetjp_4566_;
}
v_resetjp_4566_:
{
lean_object* v___x_4570_; 
if (v_isShared_4568_ == 0)
{
v___x_4570_ = v___x_4567_;
goto v_reusejp_4569_;
}
else
{
lean_object* v_reuseFailAlloc_4571_; 
v_reuseFailAlloc_4571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4571_, 0, v_a_4565_);
v___x_4570_ = v_reuseFailAlloc_4571_;
goto v_reusejp_4569_;
}
v_reusejp_4569_:
{
return v___x_4570_;
}
}
}
}
v___jp_4573_:
{
if (v___y_4574_ == 0)
{
lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___f_4578_; 
lean_del_object(v___x_4547_);
v___x_4575_ = lean_array_fget_borrowed(v_a_4532_, v_next_4533_);
v___x_4576_ = lean_array_fget_borrowed(v_a_4532_, v_a_4535_);
v___x_4577_ = lean_box(v___x_4542_);
lean_inc(v_next_4533_);
lean_inc(v_a_4535_);
lean_inc(v___x_4576_);
lean_inc(v___x_4575_);
lean_inc_ref(v_f_4534_);
v___f_4578_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4578_, 0, v_f_4534_);
lean_closure_set(v___f_4578_, 1, v___x_4575_);
lean_closure_set(v___f_4578_, 2, v___x_4576_);
lean_closure_set(v___f_4578_, 3, v___x_4549_);
lean_closure_set(v___f_4578_, 4, v_a_4535_);
lean_closure_set(v___f_4578_, 5, v___x_4577_);
lean_closure_set(v___f_4578_, 6, v_snd_4545_);
lean_closure_set(v___f_4578_, 7, v_fst_4544_);
lean_closure_set(v___f_4578_, 8, v_next_4533_);
v___y_4551_ = v___f_4578_;
goto v___jp_4550_;
}
else
{
lean_object* v___x_4580_; 
if (v_isShared_4548_ == 0)
{
v___x_4580_ = v___x_4547_;
goto v_reusejp_4579_;
}
else
{
lean_object* v_reuseFailAlloc_4583_; 
v_reuseFailAlloc_4583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4583_, 0, v_fst_4544_);
lean_ctor_set(v_reuseFailAlloc_4583_, 1, v_snd_4545_);
v___x_4580_ = v_reuseFailAlloc_4583_;
goto v_reusejp_4579_;
}
v_reusejp_4579_:
{
lean_object* v___x_4581_; lean_object* v___f_4582_; 
v___x_4581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4581_, 0, v___x_4580_);
v___f_4582_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1___boxed), 6, 1);
lean_closure_set(v___f_4582_, 0, v___x_4581_);
v___y_4551_ = v___f_4582_;
goto v___jp_4550_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___boxed(lean_object* v_upperBound_4593_, lean_object* v_a_4594_, lean_object* v_next_4595_, lean_object* v_f_4596_, lean_object* v_a_4597_, lean_object* v_b_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_){
_start:
{
lean_object* v_res_4604_; 
v_res_4604_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v_upperBound_4593_, v_a_4594_, v_next_4595_, v_f_4596_, v_a_4597_, v_b_4598_, v___y_4599_, v___y_4600_, v___y_4601_, v___y_4602_);
lean_dec(v___y_4602_);
lean_dec_ref(v___y_4601_);
lean_dec(v___y_4600_);
lean_dec_ref(v___y_4599_);
lean_dec_ref(v_a_4594_);
lean_dec(v_upperBound_4593_);
return v_res_4604_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(lean_object* v_upperBound_4605_, lean_object* v___x_4606_, lean_object* v_a_4607_, lean_object* v_f_4608_, lean_object* v_a_4609_, lean_object* v_b_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_){
_start:
{
uint8_t v___x_4616_; 
v___x_4616_ = lean_nat_dec_lt(v_a_4609_, v_upperBound_4605_);
if (v___x_4616_ == 0)
{
lean_object* v___x_4617_; 
lean_dec(v_a_4609_);
lean_dec_ref(v_f_4608_);
v___x_4617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4617_, 0, v_b_4610_);
return v___x_4617_;
}
else
{
lean_object* v_fst_4618_; lean_object* v_snd_4619_; lean_object* v___x_4621_; uint8_t v_isShared_4622_; uint8_t v_isSharedCheck_4640_; 
v_fst_4618_ = lean_ctor_get(v_b_4610_, 0);
v_snd_4619_ = lean_ctor_get(v_b_4610_, 1);
v_isSharedCheck_4640_ = !lean_is_exclusive(v_b_4610_);
if (v_isSharedCheck_4640_ == 0)
{
v___x_4621_ = v_b_4610_;
v_isShared_4622_ = v_isSharedCheck_4640_;
goto v_resetjp_4620_;
}
else
{
lean_inc(v_snd_4619_);
lean_inc(v_fst_4618_);
lean_dec(v_b_4610_);
v___x_4621_ = lean_box(0);
v_isShared_4622_ = v_isSharedCheck_4640_;
goto v_resetjp_4620_;
}
v_resetjp_4620_:
{
lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4626_; 
v___x_4623_ = lean_unsigned_to_nat(1u);
v___x_4624_ = lean_nat_add(v_a_4609_, v___x_4623_);
if (v_isShared_4622_ == 0)
{
v___x_4626_ = v___x_4621_;
goto v_reusejp_4625_;
}
else
{
lean_object* v_reuseFailAlloc_4639_; 
v_reuseFailAlloc_4639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4639_, 0, v_fst_4618_);
lean_ctor_set(v_reuseFailAlloc_4639_, 1, v_snd_4619_);
v___x_4626_ = v_reuseFailAlloc_4639_;
goto v_reusejp_4625_;
}
v_reusejp_4625_:
{
lean_object* v___x_4627_; 
lean_inc(v___x_4624_);
lean_inc_ref(v_f_4608_);
v___x_4627_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v___x_4606_, v_a_4607_, v_a_4609_, v_f_4608_, v___x_4624_, v___x_4626_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_);
if (lean_obj_tag(v___x_4627_) == 0)
{
lean_object* v_a_4628_; lean_object* v_fst_4629_; lean_object* v_snd_4630_; lean_object* v___x_4632_; uint8_t v_isShared_4633_; uint8_t v_isSharedCheck_4638_; 
v_a_4628_ = lean_ctor_get(v___x_4627_, 0);
lean_inc(v_a_4628_);
lean_dec_ref_known(v___x_4627_, 1);
v_fst_4629_ = lean_ctor_get(v_a_4628_, 0);
v_snd_4630_ = lean_ctor_get(v_a_4628_, 1);
v_isSharedCheck_4638_ = !lean_is_exclusive(v_a_4628_);
if (v_isSharedCheck_4638_ == 0)
{
v___x_4632_ = v_a_4628_;
v_isShared_4633_ = v_isSharedCheck_4638_;
goto v_resetjp_4631_;
}
else
{
lean_inc(v_snd_4630_);
lean_inc(v_fst_4629_);
lean_dec(v_a_4628_);
v___x_4632_ = lean_box(0);
v_isShared_4633_ = v_isSharedCheck_4638_;
goto v_resetjp_4631_;
}
v_resetjp_4631_:
{
lean_object* v___x_4635_; 
if (v_isShared_4633_ == 0)
{
v___x_4635_ = v___x_4632_;
goto v_reusejp_4634_;
}
else
{
lean_object* v_reuseFailAlloc_4637_; 
v_reuseFailAlloc_4637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4637_, 0, v_fst_4629_);
lean_ctor_set(v_reuseFailAlloc_4637_, 1, v_snd_4630_);
v___x_4635_ = v_reuseFailAlloc_4637_;
goto v_reusejp_4634_;
}
v_reusejp_4634_:
{
v_a_4609_ = v___x_4624_;
v_b_4610_ = v___x_4635_;
goto _start;
}
}
}
else
{
lean_dec(v___x_4624_);
lean_dec_ref(v_f_4608_);
return v___x_4627_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_4641_, lean_object* v___x_4642_, lean_object* v_a_4643_, lean_object* v_f_4644_, lean_object* v_a_4645_, lean_object* v_b_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_){
_start:
{
lean_object* v_res_4652_; 
v_res_4652_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v_upperBound_4641_, v___x_4642_, v_a_4643_, v_f_4644_, v_a_4645_, v_b_4646_, v___y_4647_, v___y_4648_, v___y_4649_, v___y_4650_);
lean_dec(v___y_4650_);
lean_dec_ref(v___y_4649_);
lean_dec(v___y_4648_);
lean_dec_ref(v___y_4647_);
lean_dec_ref(v_a_4643_);
lean_dec(v___x_4642_);
lean_dec(v_upperBound_4641_);
return v_res_4652_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0(lean_object* v___x_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_){
_start:
{
lean_object* v___x_4659_; 
v___x_4659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4659_, 0, v___x_4653_);
return v___x_4659_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed(lean_object* v___x_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_){
_start:
{
lean_object* v_res_4666_; 
v_res_4666_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0(v___x_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_);
lean_dec(v___y_4664_);
lean_dec_ref(v___y_4663_);
lean_dec(v___y_4662_);
lean_dec_ref(v___y_4661_);
return v_res_4666_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(lean_object* v_upperBound_4667_, lean_object* v_removed_4668_, lean_object* v_a_4669_, lean_object* v_a_4670_, lean_object* v_b_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_){
_start:
{
lean_object* v___y_4678_; uint8_t v___x_4701_; 
v___x_4701_ = lean_nat_dec_lt(v_a_4670_, v_upperBound_4667_);
if (v___x_4701_ == 0)
{
lean_object* v___x_4702_; 
lean_dec(v_a_4670_);
v___x_4702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4702_, 0, v_b_4671_);
return v___x_4702_;
}
else
{
uint8_t v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; uint8_t v___x_4706_; 
v___x_4703_ = 0;
v___x_4704_ = lean_box(v___x_4703_);
v___x_4705_ = lean_array_get(v___x_4704_, v_removed_4668_, v_a_4670_);
lean_dec(v___x_4704_);
v___x_4706_ = lean_unbox(v___x_4705_);
lean_dec(v___x_4705_);
if (v___x_4706_ == 0)
{
lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___f_4710_; 
v___x_4707_ = lean_array_fget_borrowed(v_a_4669_, v_a_4670_);
lean_inc(v___x_4707_);
v___x_4708_ = lean_array_push(v_b_4671_, v___x_4707_);
v___x_4709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4709_, 0, v___x_4708_);
v___f_4710_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4710_, 0, v___x_4709_);
v___y_4678_ = v___f_4710_;
goto v___jp_4677_;
}
else
{
lean_object* v___x_4711_; lean_object* v___f_4712_; 
v___x_4711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4711_, 0, v_b_4671_);
v___f_4712_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4712_, 0, v___x_4711_);
v___y_4678_ = v___f_4712_;
goto v___jp_4677_;
}
}
v___jp_4677_:
{
lean_object* v___x_4679_; 
lean_inc(v___y_4675_);
lean_inc_ref(v___y_4674_);
lean_inc(v___y_4673_);
lean_inc_ref(v___y_4672_);
v___x_4679_ = lean_apply_5(v___y_4678_, v___y_4672_, v___y_4673_, v___y_4674_, v___y_4675_, lean_box(0));
if (lean_obj_tag(v___x_4679_) == 0)
{
lean_object* v_a_4680_; lean_object* v___x_4682_; uint8_t v_isShared_4683_; uint8_t v_isSharedCheck_4692_; 
v_a_4680_ = lean_ctor_get(v___x_4679_, 0);
v_isSharedCheck_4692_ = !lean_is_exclusive(v___x_4679_);
if (v_isSharedCheck_4692_ == 0)
{
v___x_4682_ = v___x_4679_;
v_isShared_4683_ = v_isSharedCheck_4692_;
goto v_resetjp_4681_;
}
else
{
lean_inc(v_a_4680_);
lean_dec(v___x_4679_);
v___x_4682_ = lean_box(0);
v_isShared_4683_ = v_isSharedCheck_4692_;
goto v_resetjp_4681_;
}
v_resetjp_4681_:
{
if (lean_obj_tag(v_a_4680_) == 0)
{
lean_object* v_a_4684_; lean_object* v___x_4686_; 
lean_dec(v_a_4670_);
v_a_4684_ = lean_ctor_get(v_a_4680_, 0);
lean_inc(v_a_4684_);
lean_dec_ref_known(v_a_4680_, 1);
if (v_isShared_4683_ == 0)
{
lean_ctor_set(v___x_4682_, 0, v_a_4684_);
v___x_4686_ = v___x_4682_;
goto v_reusejp_4685_;
}
else
{
lean_object* v_reuseFailAlloc_4687_; 
v_reuseFailAlloc_4687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4687_, 0, v_a_4684_);
v___x_4686_ = v_reuseFailAlloc_4687_;
goto v_reusejp_4685_;
}
v_reusejp_4685_:
{
return v___x_4686_;
}
}
else
{
lean_object* v_a_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; 
lean_del_object(v___x_4682_);
v_a_4688_ = lean_ctor_get(v_a_4680_, 0);
lean_inc(v_a_4688_);
lean_dec_ref_known(v_a_4680_, 1);
v___x_4689_ = lean_unsigned_to_nat(1u);
v___x_4690_ = lean_nat_add(v_a_4670_, v___x_4689_);
lean_dec(v_a_4670_);
v_a_4670_ = v___x_4690_;
v_b_4671_ = v_a_4688_;
goto _start;
}
}
}
else
{
lean_object* v_a_4693_; lean_object* v___x_4695_; uint8_t v_isShared_4696_; uint8_t v_isSharedCheck_4700_; 
lean_dec(v_a_4670_);
v_a_4693_ = lean_ctor_get(v___x_4679_, 0);
v_isSharedCheck_4700_ = !lean_is_exclusive(v___x_4679_);
if (v_isSharedCheck_4700_ == 0)
{
v___x_4695_ = v___x_4679_;
v_isShared_4696_ = v_isSharedCheck_4700_;
goto v_resetjp_4694_;
}
else
{
lean_inc(v_a_4693_);
lean_dec(v___x_4679_);
v___x_4695_ = lean_box(0);
v_isShared_4696_ = v_isSharedCheck_4700_;
goto v_resetjp_4694_;
}
v_resetjp_4694_:
{
lean_object* v___x_4698_; 
if (v_isShared_4696_ == 0)
{
v___x_4698_ = v___x_4695_;
goto v_reusejp_4697_;
}
else
{
lean_object* v_reuseFailAlloc_4699_; 
v_reuseFailAlloc_4699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4699_, 0, v_a_4693_);
v___x_4698_ = v_reuseFailAlloc_4699_;
goto v_reusejp_4697_;
}
v_reusejp_4697_:
{
return v___x_4698_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___boxed(lean_object* v_upperBound_4713_, lean_object* v_removed_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_, lean_object* v_b_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_){
_start:
{
lean_object* v_res_4723_; 
v_res_4723_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v_upperBound_4713_, v_removed_4714_, v_a_4715_, v_a_4716_, v_b_4717_, v___y_4718_, v___y_4719_, v___y_4720_, v___y_4721_);
lean_dec(v___y_4721_);
lean_dec_ref(v___y_4720_);
lean_dec(v___y_4719_);
lean_dec_ref(v___y_4718_);
lean_dec_ref(v_a_4715_);
lean_dec_ref(v_removed_4714_);
lean_dec(v_upperBound_4713_);
return v_res_4723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(lean_object* v_a_4724_, lean_object* v_f_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_){
_start:
{
lean_object* v___x_4731_; uint8_t v___x_4732_; lean_object* v___x_4733_; lean_object* v_removed_4734_; lean_object* v_numRemoved_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; 
v___x_4731_ = lean_array_get_size(v_a_4724_);
v___x_4732_ = 0;
v___x_4733_ = lean_box(v___x_4732_);
v_removed_4734_ = lean_mk_array(v___x_4731_, v___x_4733_);
v_numRemoved_4735_ = lean_unsigned_to_nat(0u);
v___x_4736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4736_, 0, v_removed_4734_);
lean_ctor_set(v___x_4736_, 1, v_numRemoved_4735_);
v___x_4737_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v___x_4731_, v___x_4731_, v_a_4724_, v_f_4725_, v_numRemoved_4735_, v___x_4736_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_);
if (lean_obj_tag(v___x_4737_) == 0)
{
lean_object* v_a_4738_; lean_object* v_fst_4739_; lean_object* v_snd_4740_; lean_object* v_a_x27_4741_; lean_object* v___x_4742_; 
v_a_4738_ = lean_ctor_get(v___x_4737_, 0);
lean_inc(v_a_4738_);
lean_dec_ref_known(v___x_4737_, 1);
v_fst_4739_ = lean_ctor_get(v_a_4738_, 0);
lean_inc(v_fst_4739_);
v_snd_4740_ = lean_ctor_get(v_a_4738_, 1);
lean_inc(v_snd_4740_);
lean_dec(v_a_4738_);
v_a_x27_4741_ = lean_mk_empty_array_with_capacity(v_snd_4740_);
lean_dec(v_snd_4740_);
v___x_4742_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v___x_4731_, v_fst_4739_, v_a_4724_, v_numRemoved_4735_, v_a_x27_4741_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_);
lean_dec(v_fst_4739_);
return v___x_4742_;
}
else
{
lean_object* v_a_4743_; lean_object* v___x_4745_; uint8_t v_isShared_4746_; uint8_t v_isSharedCheck_4750_; 
v_a_4743_ = lean_ctor_get(v___x_4737_, 0);
v_isSharedCheck_4750_ = !lean_is_exclusive(v___x_4737_);
if (v_isSharedCheck_4750_ == 0)
{
v___x_4745_ = v___x_4737_;
v_isShared_4746_ = v_isSharedCheck_4750_;
goto v_resetjp_4744_;
}
else
{
lean_inc(v_a_4743_);
lean_dec(v___x_4737_);
v___x_4745_ = lean_box(0);
v_isShared_4746_ = v_isSharedCheck_4750_;
goto v_resetjp_4744_;
}
v_resetjp_4744_:
{
lean_object* v___x_4748_; 
if (v_isShared_4746_ == 0)
{
v___x_4748_ = v___x_4745_;
goto v_reusejp_4747_;
}
else
{
lean_object* v_reuseFailAlloc_4749_; 
v_reuseFailAlloc_4749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4749_, 0, v_a_4743_);
v___x_4748_ = v_reuseFailAlloc_4749_;
goto v_reusejp_4747_;
}
v_reusejp_4747_:
{
return v___x_4748_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg___boxed(lean_object* v_a_4751_, lean_object* v_f_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_, lean_object* v___y_4756_, lean_object* v___y_4757_){
_start:
{
lean_object* v_res_4758_; 
v_res_4758_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_a_4751_, v_f_4752_, v___y_4753_, v___y_4754_, v___y_4755_, v___y_4756_);
lean_dec(v___y_4756_);
lean_dec_ref(v___y_4755_);
lean_dec(v___y_4754_);
lean_dec_ref(v___y_4753_);
lean_dec_ref(v_a_4751_);
return v_res_4758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed(lean_object* v_mvars_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_){
_start:
{
lean_object* v___f_4766_; lean_object* v___x_4767_; 
v___f_4766_ = ((lean_object*)(l_Lean_Elab_WF_assignSubsumed___closed__0));
v___x_4767_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_mvars_4760_, v___f_4766_, v_a_4761_, v_a_4762_, v_a_4763_, v_a_4764_);
return v___x_4767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___boxed(lean_object* v_mvars_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_){
_start:
{
lean_object* v_res_4774_; 
v_res_4774_ = l_Lean_Elab_WF_assignSubsumed(v_mvars_4768_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_);
lean_dec(v_a_4772_);
lean_dec_ref(v_a_4771_);
lean_dec(v_a_4770_);
lean_dec_ref(v_a_4769_);
lean_dec_ref(v_mvars_4768_);
return v_res_4774_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0(lean_object* v_mvarId_4775_, lean_object* v_val_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_){
_start:
{
lean_object* v___x_4782_; 
v___x_4782_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mvarId_4775_, v_val_4776_, v___y_4778_);
return v___x_4782_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___boxed(lean_object* v_mvarId_4783_, lean_object* v_val_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_, lean_object* v___y_4789_){
_start:
{
lean_object* v_res_4790_; 
v_res_4790_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0(v_mvarId_4783_, v_val_4784_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_);
lean_dec(v___y_4788_);
lean_dec_ref(v___y_4787_);
lean_dec(v___y_4786_);
lean_dec_ref(v___y_4785_);
return v_res_4790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1(lean_object* v_00_u03b1_4791_, lean_object* v_a_4792_, lean_object* v_f_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_){
_start:
{
lean_object* v___x_4799_; 
v___x_4799_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_a_4792_, v_f_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_);
return v___x_4799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___boxed(lean_object* v_00_u03b1_4800_, lean_object* v_a_4801_, lean_object* v_f_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_){
_start:
{
lean_object* v_res_4808_; 
v_res_4808_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1(v_00_u03b1_4800_, v_a_4801_, v_f_4802_, v___y_4803_, v___y_4804_, v___y_4805_, v___y_4806_);
lean_dec(v___y_4806_);
lean_dec_ref(v___y_4805_);
lean_dec(v___y_4804_);
lean_dec_ref(v___y_4803_);
lean_dec_ref(v_a_4801_);
return v_res_4808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0(lean_object* v_00_u03b2_4809_, lean_object* v_x_4810_, lean_object* v_x_4811_, lean_object* v_x_4812_){
_start:
{
lean_object* v___x_4813_; 
v___x_4813_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(v_x_4810_, v_x_4811_, v_x_4812_);
return v___x_4813_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2(lean_object* v_upperBound_4814_, lean_object* v_00_u03b1_4815_, lean_object* v_a_4816_, lean_object* v_next_4817_, lean_object* v_f_4818_, lean_object* v_inst_4819_, lean_object* v_R_4820_, lean_object* v_a_4821_, lean_object* v_b_4822_, lean_object* v_c_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_){
_start:
{
lean_object* v___x_4829_; 
v___x_4829_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v_upperBound_4814_, v_a_4816_, v_next_4817_, v_f_4818_, v_a_4821_, v_b_4822_, v___y_4824_, v___y_4825_, v___y_4826_, v___y_4827_);
return v___x_4829_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___boxed(lean_object* v_upperBound_4830_, lean_object* v_00_u03b1_4831_, lean_object* v_a_4832_, lean_object* v_next_4833_, lean_object* v_f_4834_, lean_object* v_inst_4835_, lean_object* v_R_4836_, lean_object* v_a_4837_, lean_object* v_b_4838_, lean_object* v_c_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_){
_start:
{
lean_object* v_res_4845_; 
v_res_4845_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2(v_upperBound_4830_, v_00_u03b1_4831_, v_a_4832_, v_next_4833_, v_f_4834_, v_inst_4835_, v_R_4836_, v_a_4837_, v_b_4838_, v_c_4839_, v___y_4840_, v___y_4841_, v___y_4842_, v___y_4843_);
lean_dec(v___y_4843_);
lean_dec_ref(v___y_4842_);
lean_dec(v___y_4841_);
lean_dec_ref(v___y_4840_);
lean_dec_ref(v_a_4832_);
lean_dec(v_upperBound_4830_);
return v_res_4845_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3(lean_object* v_00_u03b1_4846_, lean_object* v_upperBound_4847_, lean_object* v_removed_4848_, lean_object* v_a_4849_, lean_object* v_inst_4850_, lean_object* v_R_4851_, lean_object* v_a_4852_, lean_object* v_b_4853_, lean_object* v_c_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_){
_start:
{
lean_object* v___x_4860_; 
v___x_4860_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v_upperBound_4847_, v_removed_4848_, v_a_4849_, v_a_4852_, v_b_4853_, v___y_4855_, v___y_4856_, v___y_4857_, v___y_4858_);
return v___x_4860_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___boxed(lean_object* v_00_u03b1_4861_, lean_object* v_upperBound_4862_, lean_object* v_removed_4863_, lean_object* v_a_4864_, lean_object* v_inst_4865_, lean_object* v_R_4866_, lean_object* v_a_4867_, lean_object* v_b_4868_, lean_object* v_c_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_){
_start:
{
lean_object* v_res_4875_; 
v_res_4875_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3(v_00_u03b1_4861_, v_upperBound_4862_, v_removed_4863_, v_a_4864_, v_inst_4865_, v_R_4866_, v_a_4867_, v_b_4868_, v_c_4869_, v___y_4870_, v___y_4871_, v___y_4872_, v___y_4873_);
lean_dec(v___y_4873_);
lean_dec_ref(v___y_4872_);
lean_dec(v___y_4871_);
lean_dec_ref(v___y_4870_);
lean_dec_ref(v_a_4864_);
lean_dec_ref(v_removed_4863_);
lean_dec(v_upperBound_4862_);
return v_res_4875_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4(lean_object* v_upperBound_4876_, lean_object* v___x_4877_, lean_object* v_00_u03b1_4878_, lean_object* v_a_4879_, lean_object* v_f_4880_, lean_object* v_inst_4881_, lean_object* v_R_4882_, lean_object* v_a_4883_, lean_object* v_b_4884_, lean_object* v_c_4885_, lean_object* v___y_4886_, lean_object* v___y_4887_, lean_object* v___y_4888_, lean_object* v___y_4889_){
_start:
{
lean_object* v___x_4891_; 
v___x_4891_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v_upperBound_4876_, v___x_4877_, v_a_4879_, v_f_4880_, v_a_4883_, v_b_4884_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_);
return v___x_4891_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___boxed(lean_object* v_upperBound_4892_, lean_object* v___x_4893_, lean_object* v_00_u03b1_4894_, lean_object* v_a_4895_, lean_object* v_f_4896_, lean_object* v_inst_4897_, lean_object* v_R_4898_, lean_object* v_a_4899_, lean_object* v_b_4900_, lean_object* v_c_4901_, lean_object* v___y_4902_, lean_object* v___y_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_){
_start:
{
lean_object* v_res_4907_; 
v_res_4907_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4(v_upperBound_4892_, v___x_4893_, v_00_u03b1_4894_, v_a_4895_, v_f_4896_, v_inst_4897_, v_R_4898_, v_a_4899_, v_b_4900_, v_c_4901_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_);
lean_dec(v___y_4905_);
lean_dec_ref(v___y_4904_);
lean_dec(v___y_4903_);
lean_dec_ref(v___y_4902_);
lean_dec_ref(v_a_4895_);
lean_dec(v___x_4893_);
lean_dec(v_upperBound_4892_);
return v_res_4907_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4908_, lean_object* v_x_4909_, size_t v_x_4910_, size_t v_x_4911_, lean_object* v_x_4912_, lean_object* v_x_4913_){
_start:
{
lean_object* v___x_4914_; 
v___x_4914_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4909_, v_x_4910_, v_x_4911_, v_x_4912_, v_x_4913_);
return v___x_4914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4915_, lean_object* v_x_4916_, lean_object* v_x_4917_, lean_object* v_x_4918_, lean_object* v_x_4919_, lean_object* v_x_4920_){
_start:
{
size_t v_x_4925__boxed_4921_; size_t v_x_4926__boxed_4922_; lean_object* v_res_4923_; 
v_x_4925__boxed_4921_ = lean_unbox_usize(v_x_4917_);
lean_dec(v_x_4917_);
v_x_4926__boxed_4922_ = lean_unbox_usize(v_x_4918_);
lean_dec(v_x_4918_);
v_res_4923_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1(v_00_u03b2_4915_, v_x_4916_, v_x_4925__boxed_4921_, v_x_4926__boxed_4922_, v_x_4919_, v_x_4920_);
return v_res_4923_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_4924_, lean_object* v_n_4925_, lean_object* v_k_4926_, lean_object* v_v_4927_){
_start:
{
lean_object* v___x_4928_; 
v___x_4928_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(v_n_4925_, v_k_4926_, v_v_4927_);
return v___x_4928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_4929_, size_t v_depth_4930_, lean_object* v_keys_4931_, lean_object* v_vals_4932_, lean_object* v_heq_4933_, lean_object* v_i_4934_, lean_object* v_entries_4935_){
_start:
{
lean_object* v___x_4936_; 
v___x_4936_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_4930_, v_keys_4931_, v_vals_4932_, v_i_4934_, v_entries_4935_);
return v___x_4936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_4937_, lean_object* v_depth_4938_, lean_object* v_keys_4939_, lean_object* v_vals_4940_, lean_object* v_heq_4941_, lean_object* v_i_4942_, lean_object* v_entries_4943_){
_start:
{
size_t v_depth_boxed_4944_; lean_object* v_res_4945_; 
v_depth_boxed_4944_ = lean_unbox_usize(v_depth_4938_);
lean_dec(v_depth_4938_);
v_res_4945_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_4937_, v_depth_boxed_4944_, v_keys_4939_, v_vals_4940_, v_heq_4941_, v_i_4942_, v_entries_4943_);
lean_dec_ref(v_vals_4940_);
lean_dec_ref(v_keys_4939_);
return v_res_4945_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_4946_, lean_object* v_x_4947_, lean_object* v_x_4948_, lean_object* v_x_4949_, lean_object* v_x_4950_){
_start:
{
lean_object* v___x_4951_; 
v___x_4951_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_x_4947_, v_x_4948_, v_x_4949_, v_x_4950_);
return v___x_4951_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4953_; lean_object* v___x_4954_; 
v___x_4953_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__0));
v___x_4954_ = l_Lean_stringToMessageData(v___x_4953_);
return v___x_4954_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4956_; lean_object* v___x_4957_; 
v___x_4956_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__2));
v___x_4957_ = l_Lean_stringToMessageData(v___x_4956_);
return v___x_4957_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(lean_object* v_argsPacker_4958_, lean_object* v_as_4959_, size_t v_sz_4960_, size_t v_i_4961_, lean_object* v_b_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_){
_start:
{
lean_object* v_a_4969_; uint8_t v___x_4973_; 
v___x_4973_ = lean_usize_dec_lt(v_i_4961_, v_sz_4960_);
if (v___x_4973_ == 0)
{
lean_object* v___x_4974_; 
v___x_4974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4974_, 0, v_b_4962_);
return v___x_4974_;
}
else
{
lean_object* v_a_4975_; lean_object* v___x_4976_; 
v_a_4975_ = lean_array_uget_borrowed(v_as_4959_, v_i_4961_);
lean_inc(v_a_4975_);
v___x_4976_ = l_Lean_MVarId_getType(v_a_4975_, v___y_4963_, v___y_4964_, v___y_4965_, v___y_4966_);
if (lean_obj_tag(v___x_4976_) == 0)
{
lean_object* v_a_4977_; lean_object* v___y_4979_; lean_object* v___y_4980_; lean_object* v___y_4981_; lean_object* v___y_4982_; 
v_a_4977_ = lean_ctor_get(v___x_4976_, 0);
lean_inc(v_a_4977_);
lean_dec_ref_known(v___x_4976_, 1);
if (lean_obj_tag(v_a_4977_) == 10)
{
lean_object* v_expr_4995_; 
v_expr_4995_ = lean_ctor_get(v_a_4977_, 1);
if (lean_obj_tag(v_expr_4995_) == 5)
{
lean_object* v_arg_4996_; lean_object* v___x_4997_; 
lean_inc_ref(v_expr_4995_);
lean_dec_ref_known(v_a_4977_, 2);
v_arg_4996_ = lean_ctor_get(v_expr_4995_, 1);
lean_inc_ref_n(v_arg_4996_, 2);
lean_dec_ref_known(v_expr_4995_, 2);
v___x_4997_ = l_Lean_Meta_ArgsPacker_unpack(v_argsPacker_4958_, v_arg_4996_);
if (lean_obj_tag(v___x_4997_) == 1)
{
lean_object* v_val_4998_; lean_object* v_fst_4999_; lean_object* v___x_5000_; uint8_t v___x_5001_; 
lean_dec_ref(v_arg_4996_);
v_val_4998_ = lean_ctor_get(v___x_4997_, 0);
lean_inc(v_val_4998_);
lean_dec_ref_known(v___x_4997_, 1);
v_fst_4999_ = lean_ctor_get(v_val_4998_, 0);
lean_inc(v_fst_4999_);
lean_dec(v_val_4998_);
v___x_5000_ = lean_array_get_size(v_b_4962_);
v___x_5001_ = lean_nat_dec_lt(v_fst_4999_, v___x_5000_);
if (v___x_5001_ == 0)
{
lean_dec(v_fst_4999_);
v_a_4969_ = v_b_4962_;
goto v___jp_4968_;
}
else
{
lean_object* v_v_5002_; lean_object* v___x_5003_; lean_object* v_xs_x27_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; 
v_v_5002_ = lean_array_fget(v_b_4962_, v_fst_4999_);
v___x_5003_ = lean_box(0);
v_xs_x27_5004_ = lean_array_fset(v_b_4962_, v_fst_4999_, v___x_5003_);
lean_inc(v_a_4975_);
v___x_5005_ = lean_array_push(v_v_5002_, v_a_4975_);
v___x_5006_ = lean_array_fset(v_xs_x27_5004_, v_fst_4999_, v___x_5005_);
lean_dec(v_fst_4999_);
v_a_4969_ = v___x_5006_;
goto v___jp_4968_;
}
}
else
{
lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; 
lean_dec(v___x_4997_);
v___x_5007_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3);
v___x_5008_ = l_Lean_indentExpr(v_arg_4996_);
v___x_5009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5009_, 0, v___x_5007_);
lean_ctor_set(v___x_5009_, 1, v___x_5008_);
v___x_5010_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v___x_5009_, v___y_4963_, v___y_4964_, v___y_4965_, v___y_4966_);
if (lean_obj_tag(v___x_5010_) == 0)
{
lean_dec_ref_known(v___x_5010_, 1);
v_a_4969_ = v_b_4962_;
goto v___jp_4968_;
}
else
{
lean_object* v_a_5011_; lean_object* v___x_5013_; uint8_t v_isShared_5014_; uint8_t v_isSharedCheck_5018_; 
lean_dec_ref(v_b_4962_);
v_a_5011_ = lean_ctor_get(v___x_5010_, 0);
v_isSharedCheck_5018_ = !lean_is_exclusive(v___x_5010_);
if (v_isSharedCheck_5018_ == 0)
{
v___x_5013_ = v___x_5010_;
v_isShared_5014_ = v_isSharedCheck_5018_;
goto v_resetjp_5012_;
}
else
{
lean_inc(v_a_5011_);
lean_dec(v___x_5010_);
v___x_5013_ = lean_box(0);
v_isShared_5014_ = v_isSharedCheck_5018_;
goto v_resetjp_5012_;
}
v_resetjp_5012_:
{
lean_object* v___x_5016_; 
if (v_isShared_5014_ == 0)
{
v___x_5016_ = v___x_5013_;
goto v_reusejp_5015_;
}
else
{
lean_object* v_reuseFailAlloc_5017_; 
v_reuseFailAlloc_5017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5017_, 0, v_a_5011_);
v___x_5016_ = v_reuseFailAlloc_5017_;
goto v_reusejp_5015_;
}
v_reusejp_5015_:
{
return v___x_5016_;
}
}
}
}
}
else
{
v___y_4979_ = v___y_4963_;
v___y_4980_ = v___y_4964_;
v___y_4981_ = v___y_4965_;
v___y_4982_ = v___y_4966_;
goto v___jp_4978_;
}
}
else
{
v___y_4979_ = v___y_4963_;
v___y_4980_ = v___y_4964_;
v___y_4981_ = v___y_4965_;
v___y_4982_ = v___y_4966_;
goto v___jp_4978_;
}
v___jp_4978_:
{
lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; 
v___x_4983_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1);
v___x_4984_ = l_Lean_indentExpr(v_a_4977_);
v___x_4985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4985_, 0, v___x_4983_);
lean_ctor_set(v___x_4985_, 1, v___x_4984_);
v___x_4986_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v___x_4985_, v___y_4979_, v___y_4980_, v___y_4981_, v___y_4982_);
if (lean_obj_tag(v___x_4986_) == 0)
{
lean_dec_ref_known(v___x_4986_, 1);
v_a_4969_ = v_b_4962_;
goto v___jp_4968_;
}
else
{
lean_object* v_a_4987_; lean_object* v___x_4989_; uint8_t v_isShared_4990_; uint8_t v_isSharedCheck_4994_; 
lean_dec_ref(v_b_4962_);
v_a_4987_ = lean_ctor_get(v___x_4986_, 0);
v_isSharedCheck_4994_ = !lean_is_exclusive(v___x_4986_);
if (v_isSharedCheck_4994_ == 0)
{
v___x_4989_ = v___x_4986_;
v_isShared_4990_ = v_isSharedCheck_4994_;
goto v_resetjp_4988_;
}
else
{
lean_inc(v_a_4987_);
lean_dec(v___x_4986_);
v___x_4989_ = lean_box(0);
v_isShared_4990_ = v_isSharedCheck_4994_;
goto v_resetjp_4988_;
}
v_resetjp_4988_:
{
lean_object* v___x_4992_; 
if (v_isShared_4990_ == 0)
{
v___x_4992_ = v___x_4989_;
goto v_reusejp_4991_;
}
else
{
lean_object* v_reuseFailAlloc_4993_; 
v_reuseFailAlloc_4993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4993_, 0, v_a_4987_);
v___x_4992_ = v_reuseFailAlloc_4993_;
goto v_reusejp_4991_;
}
v_reusejp_4991_:
{
return v___x_4992_;
}
}
}
}
}
else
{
lean_object* v_a_5019_; lean_object* v___x_5021_; uint8_t v_isShared_5022_; uint8_t v_isSharedCheck_5026_; 
lean_dec_ref(v_b_4962_);
v_a_5019_ = lean_ctor_get(v___x_4976_, 0);
v_isSharedCheck_5026_ = !lean_is_exclusive(v___x_4976_);
if (v_isSharedCheck_5026_ == 0)
{
v___x_5021_ = v___x_4976_;
v_isShared_5022_ = v_isSharedCheck_5026_;
goto v_resetjp_5020_;
}
else
{
lean_inc(v_a_5019_);
lean_dec(v___x_4976_);
v___x_5021_ = lean_box(0);
v_isShared_5022_ = v_isSharedCheck_5026_;
goto v_resetjp_5020_;
}
v_resetjp_5020_:
{
lean_object* v___x_5024_; 
if (v_isShared_5022_ == 0)
{
v___x_5024_ = v___x_5021_;
goto v_reusejp_5023_;
}
else
{
lean_object* v_reuseFailAlloc_5025_; 
v_reuseFailAlloc_5025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5025_, 0, v_a_5019_);
v___x_5024_ = v_reuseFailAlloc_5025_;
goto v_reusejp_5023_;
}
v_reusejp_5023_:
{
return v___x_5024_;
}
}
}
}
v___jp_4968_:
{
size_t v___x_4970_; size_t v___x_4971_; 
v___x_4970_ = ((size_t)1ULL);
v___x_4971_ = lean_usize_add(v_i_4961_, v___x_4970_);
v_i_4961_ = v___x_4971_;
v_b_4962_ = v_a_4969_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___boxed(lean_object* v_argsPacker_5027_, lean_object* v_as_5028_, lean_object* v_sz_5029_, lean_object* v_i_5030_, lean_object* v_b_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_, lean_object* v___y_5036_){
_start:
{
size_t v_sz_boxed_5037_; size_t v_i_boxed_5038_; lean_object* v_res_5039_; 
v_sz_boxed_5037_ = lean_unbox_usize(v_sz_5029_);
lean_dec(v_sz_5029_);
v_i_boxed_5038_ = lean_unbox_usize(v_i_5030_);
lean_dec(v_i_5030_);
v_res_5039_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(v_argsPacker_5027_, v_as_5028_, v_sz_boxed_5037_, v_i_boxed_5038_, v_b_5031_, v___y_5032_, v___y_5033_, v___y_5034_, v___y_5035_);
lean_dec(v___y_5035_);
lean_dec_ref(v___y_5034_);
lean_dec(v___y_5033_);
lean_dec_ref(v___y_5032_);
lean_dec_ref(v_as_5028_);
lean_dec_ref(v_argsPacker_5027_);
return v_res_5039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_groupGoalsByFunction(lean_object* v_argsPacker_5040_, lean_object* v_numFuncs_5041_, lean_object* v_goals_5042_, lean_object* v_a_5043_, lean_object* v_a_5044_, lean_object* v_a_5045_, lean_object* v_a_5046_){
_start:
{
lean_object* v___x_5048_; lean_object* v_r_5049_; size_t v_sz_5050_; size_t v___x_5051_; lean_object* v___x_5052_; 
v___x_5048_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg___closed__0));
v_r_5049_ = lean_mk_array(v_numFuncs_5041_, v___x_5048_);
v_sz_5050_ = lean_array_size(v_goals_5042_);
v___x_5051_ = ((size_t)0ULL);
v___x_5052_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(v_argsPacker_5040_, v_goals_5042_, v_sz_5050_, v___x_5051_, v_r_5049_, v_a_5043_, v_a_5044_, v_a_5045_, v_a_5046_);
return v___x_5052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_groupGoalsByFunction___boxed(lean_object* v_argsPacker_5053_, lean_object* v_numFuncs_5054_, lean_object* v_goals_5055_, lean_object* v_a_5056_, lean_object* v_a_5057_, lean_object* v_a_5058_, lean_object* v_a_5059_, lean_object* v_a_5060_){
_start:
{
lean_object* v_res_5061_; 
v_res_5061_ = l_Lean_Elab_WF_groupGoalsByFunction(v_argsPacker_5053_, v_numFuncs_5054_, v_goals_5055_, v_a_5056_, v_a_5057_, v_a_5058_, v_a_5059_);
lean_dec(v_a_5059_);
lean_dec_ref(v_a_5058_);
lean_dec(v_a_5057_);
lean_dec_ref(v_a_5056_);
lean_dec_ref(v_goals_5055_);
lean_dec_ref(v_argsPacker_5053_);
return v_res_5061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(lean_object* v_t_5062_, lean_object* v___y_5063_){
_start:
{
lean_object* v___x_5065_; lean_object* v_infoState_5066_; uint8_t v_enabled_5067_; 
v___x_5065_ = lean_st_ref_get(v___y_5063_);
v_infoState_5066_ = lean_ctor_get(v___x_5065_, 7);
lean_inc_ref(v_infoState_5066_);
lean_dec(v___x_5065_);
v_enabled_5067_ = lean_ctor_get_uint8(v_infoState_5066_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5066_);
if (v_enabled_5067_ == 0)
{
lean_object* v___x_5068_; lean_object* v___x_5069_; 
lean_dec_ref(v_t_5062_);
v___x_5068_ = lean_box(0);
v___x_5069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5069_, 0, v___x_5068_);
return v___x_5069_;
}
else
{
lean_object* v___x_5070_; lean_object* v_infoState_5071_; lean_object* v_env_5072_; lean_object* v_nextMacroScope_5073_; lean_object* v_ngen_5074_; lean_object* v_auxDeclNGen_5075_; lean_object* v_traceState_5076_; lean_object* v_cache_5077_; lean_object* v_messages_5078_; lean_object* v_snapshotTasks_5079_; lean_object* v___x_5081_; uint8_t v_isShared_5082_; uint8_t v_isSharedCheck_5101_; 
v___x_5070_ = lean_st_ref_take(v___y_5063_);
v_infoState_5071_ = lean_ctor_get(v___x_5070_, 7);
v_env_5072_ = lean_ctor_get(v___x_5070_, 0);
v_nextMacroScope_5073_ = lean_ctor_get(v___x_5070_, 1);
v_ngen_5074_ = lean_ctor_get(v___x_5070_, 2);
v_auxDeclNGen_5075_ = lean_ctor_get(v___x_5070_, 3);
v_traceState_5076_ = lean_ctor_get(v___x_5070_, 4);
v_cache_5077_ = lean_ctor_get(v___x_5070_, 5);
v_messages_5078_ = lean_ctor_get(v___x_5070_, 6);
v_snapshotTasks_5079_ = lean_ctor_get(v___x_5070_, 8);
v_isSharedCheck_5101_ = !lean_is_exclusive(v___x_5070_);
if (v_isSharedCheck_5101_ == 0)
{
v___x_5081_ = v___x_5070_;
v_isShared_5082_ = v_isSharedCheck_5101_;
goto v_resetjp_5080_;
}
else
{
lean_inc(v_snapshotTasks_5079_);
lean_inc(v_infoState_5071_);
lean_inc(v_messages_5078_);
lean_inc(v_cache_5077_);
lean_inc(v_traceState_5076_);
lean_inc(v_auxDeclNGen_5075_);
lean_inc(v_ngen_5074_);
lean_inc(v_nextMacroScope_5073_);
lean_inc(v_env_5072_);
lean_dec(v___x_5070_);
v___x_5081_ = lean_box(0);
v_isShared_5082_ = v_isSharedCheck_5101_;
goto v_resetjp_5080_;
}
v_resetjp_5080_:
{
uint8_t v_enabled_5083_; lean_object* v_assignment_5084_; lean_object* v_lazyAssignment_5085_; lean_object* v_trees_5086_; lean_object* v___x_5088_; uint8_t v_isShared_5089_; uint8_t v_isSharedCheck_5100_; 
v_enabled_5083_ = lean_ctor_get_uint8(v_infoState_5071_, sizeof(void*)*3);
v_assignment_5084_ = lean_ctor_get(v_infoState_5071_, 0);
v_lazyAssignment_5085_ = lean_ctor_get(v_infoState_5071_, 1);
v_trees_5086_ = lean_ctor_get(v_infoState_5071_, 2);
v_isSharedCheck_5100_ = !lean_is_exclusive(v_infoState_5071_);
if (v_isSharedCheck_5100_ == 0)
{
v___x_5088_ = v_infoState_5071_;
v_isShared_5089_ = v_isSharedCheck_5100_;
goto v_resetjp_5087_;
}
else
{
lean_inc(v_trees_5086_);
lean_inc(v_lazyAssignment_5085_);
lean_inc(v_assignment_5084_);
lean_dec(v_infoState_5071_);
v___x_5088_ = lean_box(0);
v_isShared_5089_ = v_isSharedCheck_5100_;
goto v_resetjp_5087_;
}
v_resetjp_5087_:
{
lean_object* v___x_5090_; lean_object* v___x_5092_; 
v___x_5090_ = l_Lean_PersistentArray_push___redArg(v_trees_5086_, v_t_5062_);
if (v_isShared_5089_ == 0)
{
lean_ctor_set(v___x_5088_, 2, v___x_5090_);
v___x_5092_ = v___x_5088_;
goto v_reusejp_5091_;
}
else
{
lean_object* v_reuseFailAlloc_5099_; 
v_reuseFailAlloc_5099_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5099_, 0, v_assignment_5084_);
lean_ctor_set(v_reuseFailAlloc_5099_, 1, v_lazyAssignment_5085_);
lean_ctor_set(v_reuseFailAlloc_5099_, 2, v___x_5090_);
lean_ctor_set_uint8(v_reuseFailAlloc_5099_, sizeof(void*)*3, v_enabled_5083_);
v___x_5092_ = v_reuseFailAlloc_5099_;
goto v_reusejp_5091_;
}
v_reusejp_5091_:
{
lean_object* v___x_5094_; 
if (v_isShared_5082_ == 0)
{
lean_ctor_set(v___x_5081_, 7, v___x_5092_);
v___x_5094_ = v___x_5081_;
goto v_reusejp_5093_;
}
else
{
lean_object* v_reuseFailAlloc_5098_; 
v_reuseFailAlloc_5098_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5098_, 0, v_env_5072_);
lean_ctor_set(v_reuseFailAlloc_5098_, 1, v_nextMacroScope_5073_);
lean_ctor_set(v_reuseFailAlloc_5098_, 2, v_ngen_5074_);
lean_ctor_set(v_reuseFailAlloc_5098_, 3, v_auxDeclNGen_5075_);
lean_ctor_set(v_reuseFailAlloc_5098_, 4, v_traceState_5076_);
lean_ctor_set(v_reuseFailAlloc_5098_, 5, v_cache_5077_);
lean_ctor_set(v_reuseFailAlloc_5098_, 6, v_messages_5078_);
lean_ctor_set(v_reuseFailAlloc_5098_, 7, v___x_5092_);
lean_ctor_set(v_reuseFailAlloc_5098_, 8, v_snapshotTasks_5079_);
v___x_5094_ = v_reuseFailAlloc_5098_;
goto v_reusejp_5093_;
}
v_reusejp_5093_:
{
lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; 
v___x_5095_ = lean_st_ref_put(v___y_5063_, v___x_5094_);
v___x_5096_ = lean_box(0);
v___x_5097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5097_, 0, v___x_5096_);
return v___x_5097_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg___boxed(lean_object* v_t_5102_, lean_object* v___y_5103_, lean_object* v___y_5104_){
_start:
{
lean_object* v_res_5105_; 
v_res_5105_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v_t_5102_, v___y_5103_);
lean_dec(v___y_5103_);
return v_res_5105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0(lean_object* v_t_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_){
_start:
{
lean_object* v___x_5114_; 
v___x_5114_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v_t_5106_, v___y_5112_);
return v___x_5114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___boxed(lean_object* v_t_5115_, lean_object* v___y_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_){
_start:
{
lean_object* v_res_5123_; 
v_res_5123_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0(v_t_5115_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_);
lean_dec(v___y_5121_);
lean_dec_ref(v___y_5120_);
lean_dec(v___y_5119_);
lean_dec_ref(v___y_5118_);
lean_dec(v___y_5117_);
lean_dec_ref(v___y_5116_);
return v_res_5123_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(lean_object* v_e_5124_, lean_object* v___y_5125_){
_start:
{
uint8_t v___x_5127_; 
v___x_5127_ = l_Lean_Expr_hasMVar(v_e_5124_);
if (v___x_5127_ == 0)
{
lean_object* v___x_5128_; 
v___x_5128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5128_, 0, v_e_5124_);
return v___x_5128_;
}
else
{
lean_object* v___x_5129_; lean_object* v_mctx_5130_; lean_object* v___x_5131_; lean_object* v_fst_5132_; lean_object* v_snd_5133_; lean_object* v___x_5134_; lean_object* v_cache_5135_; lean_object* v_zetaDeltaFVarIds_5136_; lean_object* v_postponed_5137_; lean_object* v_diag_5138_; lean_object* v___x_5140_; uint8_t v_isShared_5141_; uint8_t v_isSharedCheck_5147_; 
v___x_5129_ = lean_st_ref_get(v___y_5125_);
v_mctx_5130_ = lean_ctor_get(v___x_5129_, 0);
lean_inc_ref(v_mctx_5130_);
lean_dec(v___x_5129_);
v___x_5131_ = l_Lean_instantiateMVarsCore(v_mctx_5130_, v_e_5124_);
v_fst_5132_ = lean_ctor_get(v___x_5131_, 0);
lean_inc(v_fst_5132_);
v_snd_5133_ = lean_ctor_get(v___x_5131_, 1);
lean_inc(v_snd_5133_);
lean_dec_ref(v___x_5131_);
v___x_5134_ = lean_st_ref_take(v___y_5125_);
v_cache_5135_ = lean_ctor_get(v___x_5134_, 1);
v_zetaDeltaFVarIds_5136_ = lean_ctor_get(v___x_5134_, 2);
v_postponed_5137_ = lean_ctor_get(v___x_5134_, 3);
v_diag_5138_ = lean_ctor_get(v___x_5134_, 4);
v_isSharedCheck_5147_ = !lean_is_exclusive(v___x_5134_);
if (v_isSharedCheck_5147_ == 0)
{
lean_object* v_unused_5148_; 
v_unused_5148_ = lean_ctor_get(v___x_5134_, 0);
lean_dec(v_unused_5148_);
v___x_5140_ = v___x_5134_;
v_isShared_5141_ = v_isSharedCheck_5147_;
goto v_resetjp_5139_;
}
else
{
lean_inc(v_diag_5138_);
lean_inc(v_postponed_5137_);
lean_inc(v_zetaDeltaFVarIds_5136_);
lean_inc(v_cache_5135_);
lean_dec(v___x_5134_);
v___x_5140_ = lean_box(0);
v_isShared_5141_ = v_isSharedCheck_5147_;
goto v_resetjp_5139_;
}
v_resetjp_5139_:
{
lean_object* v___x_5143_; 
if (v_isShared_5141_ == 0)
{
lean_ctor_set(v___x_5140_, 0, v_snd_5133_);
v___x_5143_ = v___x_5140_;
goto v_reusejp_5142_;
}
else
{
lean_object* v_reuseFailAlloc_5146_; 
v_reuseFailAlloc_5146_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5146_, 0, v_snd_5133_);
lean_ctor_set(v_reuseFailAlloc_5146_, 1, v_cache_5135_);
lean_ctor_set(v_reuseFailAlloc_5146_, 2, v_zetaDeltaFVarIds_5136_);
lean_ctor_set(v_reuseFailAlloc_5146_, 3, v_postponed_5137_);
lean_ctor_set(v_reuseFailAlloc_5146_, 4, v_diag_5138_);
v___x_5143_ = v_reuseFailAlloc_5146_;
goto v_reusejp_5142_;
}
v_reusejp_5142_:
{
lean_object* v___x_5144_; lean_object* v___x_5145_; 
v___x_5144_ = lean_st_ref_put(v___y_5125_, v___x_5143_);
v___x_5145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5145_, 0, v_fst_5132_);
return v___x_5145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg___boxed(lean_object* v_e_5149_, lean_object* v___y_5150_, lean_object* v___y_5151_){
_start:
{
lean_object* v_res_5152_; 
v_res_5152_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_e_5149_, v___y_5150_);
lean_dec(v___y_5150_);
return v_res_5152_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7(lean_object* v_e_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_){
_start:
{
lean_object* v___x_5159_; 
v___x_5159_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_e_5153_, v___y_5155_);
return v___x_5159_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___boxed(lean_object* v_e_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_, lean_object* v___y_5165_){
_start:
{
lean_object* v_res_5166_; 
v_res_5166_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7(v_e_5160_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_);
lean_dec(v___y_5164_);
lean_dec_ref(v___y_5163_);
lean_dec(v___y_5162_);
lean_dec_ref(v___y_5161_);
return v_res_5166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(lean_object* v_as_5167_, size_t v_i_5168_, size_t v_stop_5169_, lean_object* v_b_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_, lean_object* v___y_5174_, lean_object* v___y_5175_, lean_object* v___y_5176_){
_start:
{
uint8_t v___x_5178_; 
v___x_5178_ = lean_usize_dec_eq(v_i_5168_, v_stop_5169_);
if (v___x_5178_ == 0)
{
lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; 
v___x_5179_ = lean_array_uget_borrowed(v_as_5167_, v_i_5168_);
lean_inc(v___x_5179_);
v___x_5180_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_5180_, 0, v___x_5179_);
v___x_5181_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v___x_5180_, v___y_5176_);
if (lean_obj_tag(v___x_5181_) == 0)
{
lean_object* v_a_5182_; size_t v___x_5183_; size_t v___x_5184_; 
v_a_5182_ = lean_ctor_get(v___x_5181_, 0);
lean_inc(v_a_5182_);
lean_dec_ref_known(v___x_5181_, 1);
v___x_5183_ = ((size_t)1ULL);
v___x_5184_ = lean_usize_add(v_i_5168_, v___x_5183_);
v_i_5168_ = v___x_5184_;
v_b_5170_ = v_a_5182_;
goto _start;
}
else
{
return v___x_5181_;
}
}
else
{
lean_object* v___x_5186_; 
v___x_5186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5186_, 0, v_b_5170_);
return v___x_5186_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4___boxed(lean_object* v_as_5187_, lean_object* v_i_5188_, lean_object* v_stop_5189_, lean_object* v_b_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_, lean_object* v___y_5194_, lean_object* v___y_5195_, lean_object* v___y_5196_, lean_object* v___y_5197_){
_start:
{
size_t v_i_boxed_5198_; size_t v_stop_boxed_5199_; lean_object* v_res_5200_; 
v_i_boxed_5198_ = lean_unbox_usize(v_i_5188_);
lean_dec(v_i_5188_);
v_stop_boxed_5199_ = lean_unbox_usize(v_stop_5189_);
lean_dec(v_stop_5189_);
v_res_5200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v_as_5187_, v_i_boxed_5198_, v_stop_boxed_5199_, v_b_5190_, v___y_5191_, v___y_5192_, v___y_5193_, v___y_5194_, v___y_5195_, v___y_5196_);
lean_dec(v___y_5196_);
lean_dec_ref(v___y_5195_);
lean_dec(v___y_5194_);
lean_dec_ref(v___y_5193_);
lean_dec(v___y_5192_);
lean_dec_ref(v___y_5191_);
lean_dec_ref(v_as_5187_);
return v_res_5200_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v___x_5203_; 
v___x_5201_ = lean_unsigned_to_nat(32u);
v___x_5202_ = lean_mk_empty_array_with_capacity(v___x_5201_);
v___x_5203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5203_, 0, v___x_5202_);
return v___x_5203_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_5204_; lean_object* v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; lean_object* v___x_5209_; 
v___x_5204_ = ((size_t)5ULL);
v___x_5205_ = lean_unsigned_to_nat(0u);
v___x_5206_ = lean_unsigned_to_nat(32u);
v___x_5207_ = lean_mk_empty_array_with_capacity(v___x_5206_);
v___x_5208_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0);
v___x_5209_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5209_, 0, v___x_5208_);
lean_ctor_set(v___x_5209_, 1, v___x_5207_);
lean_ctor_set(v___x_5209_, 2, v___x_5205_);
lean_ctor_set(v___x_5209_, 3, v___x_5205_);
lean_ctor_set_usize(v___x_5209_, 4, v___x_5204_);
return v___x_5209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(lean_object* v___y_5210_){
_start:
{
lean_object* v___x_5212_; lean_object* v_infoState_5213_; lean_object* v_trees_5214_; lean_object* v___x_5215_; lean_object* v_infoState_5216_; lean_object* v_env_5217_; lean_object* v_nextMacroScope_5218_; lean_object* v_ngen_5219_; lean_object* v_auxDeclNGen_5220_; lean_object* v_traceState_5221_; lean_object* v_cache_5222_; lean_object* v_messages_5223_; lean_object* v_snapshotTasks_5224_; lean_object* v___x_5226_; uint8_t v_isShared_5227_; uint8_t v_isSharedCheck_5245_; 
v___x_5212_ = lean_st_ref_get(v___y_5210_);
v_infoState_5213_ = lean_ctor_get(v___x_5212_, 7);
lean_inc_ref(v_infoState_5213_);
lean_dec(v___x_5212_);
v_trees_5214_ = lean_ctor_get(v_infoState_5213_, 2);
lean_inc_ref(v_trees_5214_);
lean_dec_ref(v_infoState_5213_);
v___x_5215_ = lean_st_ref_take(v___y_5210_);
v_infoState_5216_ = lean_ctor_get(v___x_5215_, 7);
v_env_5217_ = lean_ctor_get(v___x_5215_, 0);
v_nextMacroScope_5218_ = lean_ctor_get(v___x_5215_, 1);
v_ngen_5219_ = lean_ctor_get(v___x_5215_, 2);
v_auxDeclNGen_5220_ = lean_ctor_get(v___x_5215_, 3);
v_traceState_5221_ = lean_ctor_get(v___x_5215_, 4);
v_cache_5222_ = lean_ctor_get(v___x_5215_, 5);
v_messages_5223_ = lean_ctor_get(v___x_5215_, 6);
v_snapshotTasks_5224_ = lean_ctor_get(v___x_5215_, 8);
v_isSharedCheck_5245_ = !lean_is_exclusive(v___x_5215_);
if (v_isSharedCheck_5245_ == 0)
{
v___x_5226_ = v___x_5215_;
v_isShared_5227_ = v_isSharedCheck_5245_;
goto v_resetjp_5225_;
}
else
{
lean_inc(v_snapshotTasks_5224_);
lean_inc(v_infoState_5216_);
lean_inc(v_messages_5223_);
lean_inc(v_cache_5222_);
lean_inc(v_traceState_5221_);
lean_inc(v_auxDeclNGen_5220_);
lean_inc(v_ngen_5219_);
lean_inc(v_nextMacroScope_5218_);
lean_inc(v_env_5217_);
lean_dec(v___x_5215_);
v___x_5226_ = lean_box(0);
v_isShared_5227_ = v_isSharedCheck_5245_;
goto v_resetjp_5225_;
}
v_resetjp_5225_:
{
uint8_t v_enabled_5228_; lean_object* v_assignment_5229_; lean_object* v_lazyAssignment_5230_; lean_object* v___x_5232_; uint8_t v_isShared_5233_; uint8_t v_isSharedCheck_5243_; 
v_enabled_5228_ = lean_ctor_get_uint8(v_infoState_5216_, sizeof(void*)*3);
v_assignment_5229_ = lean_ctor_get(v_infoState_5216_, 0);
v_lazyAssignment_5230_ = lean_ctor_get(v_infoState_5216_, 1);
v_isSharedCheck_5243_ = !lean_is_exclusive(v_infoState_5216_);
if (v_isSharedCheck_5243_ == 0)
{
lean_object* v_unused_5244_; 
v_unused_5244_ = lean_ctor_get(v_infoState_5216_, 2);
lean_dec(v_unused_5244_);
v___x_5232_ = v_infoState_5216_;
v_isShared_5233_ = v_isSharedCheck_5243_;
goto v_resetjp_5231_;
}
else
{
lean_inc(v_lazyAssignment_5230_);
lean_inc(v_assignment_5229_);
lean_dec(v_infoState_5216_);
v___x_5232_ = lean_box(0);
v_isShared_5233_ = v_isSharedCheck_5243_;
goto v_resetjp_5231_;
}
v_resetjp_5231_:
{
lean_object* v___x_5234_; lean_object* v___x_5236_; 
v___x_5234_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1);
if (v_isShared_5233_ == 0)
{
lean_ctor_set(v___x_5232_, 2, v___x_5234_);
v___x_5236_ = v___x_5232_;
goto v_reusejp_5235_;
}
else
{
lean_object* v_reuseFailAlloc_5242_; 
v_reuseFailAlloc_5242_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5242_, 0, v_assignment_5229_);
lean_ctor_set(v_reuseFailAlloc_5242_, 1, v_lazyAssignment_5230_);
lean_ctor_set(v_reuseFailAlloc_5242_, 2, v___x_5234_);
lean_ctor_set_uint8(v_reuseFailAlloc_5242_, sizeof(void*)*3, v_enabled_5228_);
v___x_5236_ = v_reuseFailAlloc_5242_;
goto v_reusejp_5235_;
}
v_reusejp_5235_:
{
lean_object* v___x_5238_; 
if (v_isShared_5227_ == 0)
{
lean_ctor_set(v___x_5226_, 7, v___x_5236_);
v___x_5238_ = v___x_5226_;
goto v_reusejp_5237_;
}
else
{
lean_object* v_reuseFailAlloc_5241_; 
v_reuseFailAlloc_5241_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5241_, 0, v_env_5217_);
lean_ctor_set(v_reuseFailAlloc_5241_, 1, v_nextMacroScope_5218_);
lean_ctor_set(v_reuseFailAlloc_5241_, 2, v_ngen_5219_);
lean_ctor_set(v_reuseFailAlloc_5241_, 3, v_auxDeclNGen_5220_);
lean_ctor_set(v_reuseFailAlloc_5241_, 4, v_traceState_5221_);
lean_ctor_set(v_reuseFailAlloc_5241_, 5, v_cache_5222_);
lean_ctor_set(v_reuseFailAlloc_5241_, 6, v_messages_5223_);
lean_ctor_set(v_reuseFailAlloc_5241_, 7, v___x_5236_);
lean_ctor_set(v_reuseFailAlloc_5241_, 8, v_snapshotTasks_5224_);
v___x_5238_ = v_reuseFailAlloc_5241_;
goto v_reusejp_5237_;
}
v_reusejp_5237_:
{
lean_object* v___x_5239_; lean_object* v___x_5240_; 
v___x_5239_ = lean_st_ref_put(v___y_5210_, v___x_5238_);
v___x_5240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5240_, 0, v_trees_5214_);
return v___x_5240_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___boxed(lean_object* v___y_5246_, lean_object* v___y_5247_){
_start:
{
lean_object* v_res_5248_; 
v_res_5248_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_5246_);
lean_dec(v___y_5246_);
return v_res_5248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(lean_object* v___y_5249_, lean_object* v_mkInfoTree_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_, lean_object* v_a_5258_, lean_object* v_a_x3f_5259_){
_start:
{
lean_object* v___x_5261_; lean_object* v_infoState_5262_; lean_object* v_trees_5263_; lean_object* v___x_5264_; 
v___x_5261_ = lean_st_ref_get(v___y_5249_);
v_infoState_5262_ = lean_ctor_get(v___x_5261_, 7);
lean_inc_ref(v_infoState_5262_);
lean_dec(v___x_5261_);
v_trees_5263_ = lean_ctor_get(v_infoState_5262_, 2);
lean_inc_ref(v_trees_5263_);
lean_dec_ref(v_infoState_5262_);
lean_inc(v___y_5249_);
lean_inc_ref(v___y_5257_);
lean_inc(v___y_5256_);
lean_inc_ref(v___y_5255_);
lean_inc(v___y_5254_);
lean_inc_ref(v___y_5253_);
lean_inc(v___y_5252_);
lean_inc_ref(v___y_5251_);
v___x_5264_ = lean_apply_10(v_mkInfoTree_5250_, v_trees_5263_, v___y_5251_, v___y_5252_, v___y_5253_, v___y_5254_, v___y_5255_, v___y_5256_, v___y_5257_, v___y_5249_, lean_box(0));
if (lean_obj_tag(v___x_5264_) == 0)
{
lean_object* v_a_5265_; lean_object* v___x_5267_; uint8_t v_isShared_5268_; uint8_t v_isSharedCheck_5303_; 
v_a_5265_ = lean_ctor_get(v___x_5264_, 0);
v_isSharedCheck_5303_ = !lean_is_exclusive(v___x_5264_);
if (v_isSharedCheck_5303_ == 0)
{
v___x_5267_ = v___x_5264_;
v_isShared_5268_ = v_isSharedCheck_5303_;
goto v_resetjp_5266_;
}
else
{
lean_inc(v_a_5265_);
lean_dec(v___x_5264_);
v___x_5267_ = lean_box(0);
v_isShared_5268_ = v_isSharedCheck_5303_;
goto v_resetjp_5266_;
}
v_resetjp_5266_:
{
lean_object* v___x_5269_; lean_object* v_infoState_5270_; lean_object* v_env_5271_; lean_object* v_nextMacroScope_5272_; lean_object* v_ngen_5273_; lean_object* v_auxDeclNGen_5274_; lean_object* v_traceState_5275_; lean_object* v_cache_5276_; lean_object* v_messages_5277_; lean_object* v_snapshotTasks_5278_; lean_object* v___x_5280_; uint8_t v_isShared_5281_; uint8_t v_isSharedCheck_5302_; 
v___x_5269_ = lean_st_ref_take(v___y_5249_);
v_infoState_5270_ = lean_ctor_get(v___x_5269_, 7);
v_env_5271_ = lean_ctor_get(v___x_5269_, 0);
v_nextMacroScope_5272_ = lean_ctor_get(v___x_5269_, 1);
v_ngen_5273_ = lean_ctor_get(v___x_5269_, 2);
v_auxDeclNGen_5274_ = lean_ctor_get(v___x_5269_, 3);
v_traceState_5275_ = lean_ctor_get(v___x_5269_, 4);
v_cache_5276_ = lean_ctor_get(v___x_5269_, 5);
v_messages_5277_ = lean_ctor_get(v___x_5269_, 6);
v_snapshotTasks_5278_ = lean_ctor_get(v___x_5269_, 8);
v_isSharedCheck_5302_ = !lean_is_exclusive(v___x_5269_);
if (v_isSharedCheck_5302_ == 0)
{
v___x_5280_ = v___x_5269_;
v_isShared_5281_ = v_isSharedCheck_5302_;
goto v_resetjp_5279_;
}
else
{
lean_inc(v_snapshotTasks_5278_);
lean_inc(v_infoState_5270_);
lean_inc(v_messages_5277_);
lean_inc(v_cache_5276_);
lean_inc(v_traceState_5275_);
lean_inc(v_auxDeclNGen_5274_);
lean_inc(v_ngen_5273_);
lean_inc(v_nextMacroScope_5272_);
lean_inc(v_env_5271_);
lean_dec(v___x_5269_);
v___x_5280_ = lean_box(0);
v_isShared_5281_ = v_isSharedCheck_5302_;
goto v_resetjp_5279_;
}
v_resetjp_5279_:
{
uint8_t v_enabled_5282_; lean_object* v_assignment_5283_; lean_object* v_lazyAssignment_5284_; lean_object* v___x_5286_; uint8_t v_isShared_5287_; uint8_t v_isSharedCheck_5300_; 
v_enabled_5282_ = lean_ctor_get_uint8(v_infoState_5270_, sizeof(void*)*3);
v_assignment_5283_ = lean_ctor_get(v_infoState_5270_, 0);
v_lazyAssignment_5284_ = lean_ctor_get(v_infoState_5270_, 1);
v_isSharedCheck_5300_ = !lean_is_exclusive(v_infoState_5270_);
if (v_isSharedCheck_5300_ == 0)
{
lean_object* v_unused_5301_; 
v_unused_5301_ = lean_ctor_get(v_infoState_5270_, 2);
lean_dec(v_unused_5301_);
v___x_5286_ = v_infoState_5270_;
v_isShared_5287_ = v_isSharedCheck_5300_;
goto v_resetjp_5285_;
}
else
{
lean_inc(v_lazyAssignment_5284_);
lean_inc(v_assignment_5283_);
lean_dec(v_infoState_5270_);
v___x_5286_ = lean_box(0);
v_isShared_5287_ = v_isSharedCheck_5300_;
goto v_resetjp_5285_;
}
v_resetjp_5285_:
{
lean_object* v___x_5288_; lean_object* v___x_5290_; 
v___x_5288_ = l_Lean_PersistentArray_push___redArg(v_a_5258_, v_a_5265_);
if (v_isShared_5287_ == 0)
{
lean_ctor_set(v___x_5286_, 2, v___x_5288_);
v___x_5290_ = v___x_5286_;
goto v_reusejp_5289_;
}
else
{
lean_object* v_reuseFailAlloc_5299_; 
v_reuseFailAlloc_5299_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5299_, 0, v_assignment_5283_);
lean_ctor_set(v_reuseFailAlloc_5299_, 1, v_lazyAssignment_5284_);
lean_ctor_set(v_reuseFailAlloc_5299_, 2, v___x_5288_);
lean_ctor_set_uint8(v_reuseFailAlloc_5299_, sizeof(void*)*3, v_enabled_5282_);
v___x_5290_ = v_reuseFailAlloc_5299_;
goto v_reusejp_5289_;
}
v_reusejp_5289_:
{
lean_object* v___x_5292_; 
if (v_isShared_5281_ == 0)
{
lean_ctor_set(v___x_5280_, 7, v___x_5290_);
v___x_5292_ = v___x_5280_;
goto v_reusejp_5291_;
}
else
{
lean_object* v_reuseFailAlloc_5298_; 
v_reuseFailAlloc_5298_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5298_, 0, v_env_5271_);
lean_ctor_set(v_reuseFailAlloc_5298_, 1, v_nextMacroScope_5272_);
lean_ctor_set(v_reuseFailAlloc_5298_, 2, v_ngen_5273_);
lean_ctor_set(v_reuseFailAlloc_5298_, 3, v_auxDeclNGen_5274_);
lean_ctor_set(v_reuseFailAlloc_5298_, 4, v_traceState_5275_);
lean_ctor_set(v_reuseFailAlloc_5298_, 5, v_cache_5276_);
lean_ctor_set(v_reuseFailAlloc_5298_, 6, v_messages_5277_);
lean_ctor_set(v_reuseFailAlloc_5298_, 7, v___x_5290_);
lean_ctor_set(v_reuseFailAlloc_5298_, 8, v_snapshotTasks_5278_);
v___x_5292_ = v_reuseFailAlloc_5298_;
goto v_reusejp_5291_;
}
v_reusejp_5291_:
{
lean_object* v___x_5293_; lean_object* v___x_5294_; lean_object* v___x_5296_; 
v___x_5293_ = lean_st_ref_put(v___y_5249_, v___x_5292_);
v___x_5294_ = lean_box(0);
if (v_isShared_5268_ == 0)
{
lean_ctor_set(v___x_5267_, 0, v___x_5294_);
v___x_5296_ = v___x_5267_;
goto v_reusejp_5295_;
}
else
{
lean_object* v_reuseFailAlloc_5297_; 
v_reuseFailAlloc_5297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5297_, 0, v___x_5294_);
v___x_5296_ = v_reuseFailAlloc_5297_;
goto v_reusejp_5295_;
}
v_reusejp_5295_:
{
return v___x_5296_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5304_; lean_object* v___x_5306_; uint8_t v_isShared_5307_; uint8_t v_isSharedCheck_5311_; 
lean_dec_ref(v_a_5258_);
v_a_5304_ = lean_ctor_get(v___x_5264_, 0);
v_isSharedCheck_5311_ = !lean_is_exclusive(v___x_5264_);
if (v_isSharedCheck_5311_ == 0)
{
v___x_5306_ = v___x_5264_;
v_isShared_5307_ = v_isSharedCheck_5311_;
goto v_resetjp_5305_;
}
else
{
lean_inc(v_a_5304_);
lean_dec(v___x_5264_);
v___x_5306_ = lean_box(0);
v_isShared_5307_ = v_isSharedCheck_5311_;
goto v_resetjp_5305_;
}
v_resetjp_5305_:
{
lean_object* v___x_5309_; 
if (v_isShared_5307_ == 0)
{
v___x_5309_ = v___x_5306_;
goto v_reusejp_5308_;
}
else
{
lean_object* v_reuseFailAlloc_5310_; 
v_reuseFailAlloc_5310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5310_, 0, v_a_5304_);
v___x_5309_ = v_reuseFailAlloc_5310_;
goto v_reusejp_5308_;
}
v_reusejp_5308_:
{
return v___x_5309_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0___boxed(lean_object* v___y_5312_, lean_object* v_mkInfoTree_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v_a_5321_, lean_object* v_a_x3f_5322_, lean_object* v___y_5323_){
_start:
{
lean_object* v_res_5324_; 
v_res_5324_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5312_, v_mkInfoTree_5313_, v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v_a_5321_, v_a_x3f_5322_);
lean_dec(v_a_x3f_5322_);
lean_dec_ref(v___y_5320_);
lean_dec(v___y_5319_);
lean_dec_ref(v___y_5318_);
lean_dec(v___y_5317_);
lean_dec_ref(v___y_5316_);
lean_dec(v___y_5315_);
lean_dec_ref(v___y_5314_);
lean_dec(v___y_5312_);
return v_res_5324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(lean_object* v_x_5325_, lean_object* v_mkInfoTree_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_){
_start:
{
lean_object* v___x_5336_; lean_object* v_infoState_5337_; uint8_t v_enabled_5338_; 
v___x_5336_ = lean_st_ref_get(v___y_5334_);
v_infoState_5337_ = lean_ctor_get(v___x_5336_, 7);
lean_inc_ref(v_infoState_5337_);
lean_dec(v___x_5336_);
v_enabled_5338_ = lean_ctor_get_uint8(v_infoState_5337_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5337_);
if (v_enabled_5338_ == 0)
{
lean_object* v___x_5339_; 
lean_dec_ref(v_mkInfoTree_5326_);
lean_inc(v___y_5334_);
lean_inc_ref(v___y_5333_);
lean_inc(v___y_5332_);
lean_inc_ref(v___y_5331_);
lean_inc(v___y_5330_);
lean_inc_ref(v___y_5329_);
lean_inc(v___y_5328_);
lean_inc_ref(v___y_5327_);
v___x_5339_ = lean_apply_9(v_x_5325_, v___y_5327_, v___y_5328_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_, v___y_5334_, lean_box(0));
return v___x_5339_;
}
else
{
lean_object* v___x_5340_; lean_object* v_a_5341_; lean_object* v_r_5342_; 
v___x_5340_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_5334_);
v_a_5341_ = lean_ctor_get(v___x_5340_, 0);
lean_inc(v_a_5341_);
lean_dec_ref(v___x_5340_);
lean_inc(v___y_5334_);
lean_inc_ref(v___y_5333_);
lean_inc(v___y_5332_);
lean_inc_ref(v___y_5331_);
lean_inc(v___y_5330_);
lean_inc_ref(v___y_5329_);
lean_inc(v___y_5328_);
lean_inc_ref(v___y_5327_);
v_r_5342_ = lean_apply_9(v_x_5325_, v___y_5327_, v___y_5328_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_, v___y_5334_, lean_box(0));
if (lean_obj_tag(v_r_5342_) == 0)
{
lean_object* v_a_5343_; lean_object* v___x_5345_; uint8_t v_isShared_5346_; uint8_t v_isSharedCheck_5367_; 
v_a_5343_ = lean_ctor_get(v_r_5342_, 0);
v_isSharedCheck_5367_ = !lean_is_exclusive(v_r_5342_);
if (v_isSharedCheck_5367_ == 0)
{
v___x_5345_ = v_r_5342_;
v_isShared_5346_ = v_isSharedCheck_5367_;
goto v_resetjp_5344_;
}
else
{
lean_inc(v_a_5343_);
lean_dec(v_r_5342_);
v___x_5345_ = lean_box(0);
v_isShared_5346_ = v_isSharedCheck_5367_;
goto v_resetjp_5344_;
}
v_resetjp_5344_:
{
lean_object* v___x_5348_; 
lean_inc(v_a_5343_);
if (v_isShared_5346_ == 0)
{
lean_ctor_set_tag(v___x_5345_, 1);
v___x_5348_ = v___x_5345_;
goto v_reusejp_5347_;
}
else
{
lean_object* v_reuseFailAlloc_5366_; 
v_reuseFailAlloc_5366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5366_, 0, v_a_5343_);
v___x_5348_ = v_reuseFailAlloc_5366_;
goto v_reusejp_5347_;
}
v_reusejp_5347_:
{
lean_object* v___x_5349_; 
v___x_5349_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5334_, v_mkInfoTree_5326_, v___y_5327_, v___y_5328_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_, v_a_5341_, v___x_5348_);
lean_dec_ref(v___x_5348_);
if (lean_obj_tag(v___x_5349_) == 0)
{
lean_object* v___x_5351_; uint8_t v_isShared_5352_; uint8_t v_isSharedCheck_5356_; 
v_isSharedCheck_5356_ = !lean_is_exclusive(v___x_5349_);
if (v_isSharedCheck_5356_ == 0)
{
lean_object* v_unused_5357_; 
v_unused_5357_ = lean_ctor_get(v___x_5349_, 0);
lean_dec(v_unused_5357_);
v___x_5351_ = v___x_5349_;
v_isShared_5352_ = v_isSharedCheck_5356_;
goto v_resetjp_5350_;
}
else
{
lean_dec(v___x_5349_);
v___x_5351_ = lean_box(0);
v_isShared_5352_ = v_isSharedCheck_5356_;
goto v_resetjp_5350_;
}
v_resetjp_5350_:
{
lean_object* v___x_5354_; 
if (v_isShared_5352_ == 0)
{
lean_ctor_set(v___x_5351_, 0, v_a_5343_);
v___x_5354_ = v___x_5351_;
goto v_reusejp_5353_;
}
else
{
lean_object* v_reuseFailAlloc_5355_; 
v_reuseFailAlloc_5355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5355_, 0, v_a_5343_);
v___x_5354_ = v_reuseFailAlloc_5355_;
goto v_reusejp_5353_;
}
v_reusejp_5353_:
{
return v___x_5354_;
}
}
}
else
{
lean_object* v_a_5358_; lean_object* v___x_5360_; uint8_t v_isShared_5361_; uint8_t v_isSharedCheck_5365_; 
lean_dec(v_a_5343_);
v_a_5358_ = lean_ctor_get(v___x_5349_, 0);
v_isSharedCheck_5365_ = !lean_is_exclusive(v___x_5349_);
if (v_isSharedCheck_5365_ == 0)
{
v___x_5360_ = v___x_5349_;
v_isShared_5361_ = v_isSharedCheck_5365_;
goto v_resetjp_5359_;
}
else
{
lean_inc(v_a_5358_);
lean_dec(v___x_5349_);
v___x_5360_ = lean_box(0);
v_isShared_5361_ = v_isSharedCheck_5365_;
goto v_resetjp_5359_;
}
v_resetjp_5359_:
{
lean_object* v___x_5363_; 
if (v_isShared_5361_ == 0)
{
v___x_5363_ = v___x_5360_;
goto v_reusejp_5362_;
}
else
{
lean_object* v_reuseFailAlloc_5364_; 
v_reuseFailAlloc_5364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5364_, 0, v_a_5358_);
v___x_5363_ = v_reuseFailAlloc_5364_;
goto v_reusejp_5362_;
}
v_reusejp_5362_:
{
return v___x_5363_;
}
}
}
}
}
}
else
{
lean_object* v_a_5368_; lean_object* v___x_5369_; lean_object* v___x_5370_; 
v_a_5368_ = lean_ctor_get(v_r_5342_, 0);
lean_inc(v_a_5368_);
lean_dec_ref_known(v_r_5342_, 1);
v___x_5369_ = lean_box(0);
v___x_5370_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5334_, v_mkInfoTree_5326_, v___y_5327_, v___y_5328_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_, v_a_5341_, v___x_5369_);
if (lean_obj_tag(v___x_5370_) == 0)
{
lean_object* v___x_5372_; uint8_t v_isShared_5373_; uint8_t v_isSharedCheck_5377_; 
v_isSharedCheck_5377_ = !lean_is_exclusive(v___x_5370_);
if (v_isSharedCheck_5377_ == 0)
{
lean_object* v_unused_5378_; 
v_unused_5378_ = lean_ctor_get(v___x_5370_, 0);
lean_dec(v_unused_5378_);
v___x_5372_ = v___x_5370_;
v_isShared_5373_ = v_isSharedCheck_5377_;
goto v_resetjp_5371_;
}
else
{
lean_dec(v___x_5370_);
v___x_5372_ = lean_box(0);
v_isShared_5373_ = v_isSharedCheck_5377_;
goto v_resetjp_5371_;
}
v_resetjp_5371_:
{
lean_object* v___x_5375_; 
if (v_isShared_5373_ == 0)
{
lean_ctor_set_tag(v___x_5372_, 1);
lean_ctor_set(v___x_5372_, 0, v_a_5368_);
v___x_5375_ = v___x_5372_;
goto v_reusejp_5374_;
}
else
{
lean_object* v_reuseFailAlloc_5376_; 
v_reuseFailAlloc_5376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5376_, 0, v_a_5368_);
v___x_5375_ = v_reuseFailAlloc_5376_;
goto v_reusejp_5374_;
}
v_reusejp_5374_:
{
return v___x_5375_;
}
}
}
else
{
lean_object* v_a_5379_; lean_object* v___x_5381_; uint8_t v_isShared_5382_; uint8_t v_isSharedCheck_5386_; 
lean_dec(v_a_5368_);
v_a_5379_ = lean_ctor_get(v___x_5370_, 0);
v_isSharedCheck_5386_ = !lean_is_exclusive(v___x_5370_);
if (v_isSharedCheck_5386_ == 0)
{
v___x_5381_ = v___x_5370_;
v_isShared_5382_ = v_isSharedCheck_5386_;
goto v_resetjp_5380_;
}
else
{
lean_inc(v_a_5379_);
lean_dec(v___x_5370_);
v___x_5381_ = lean_box(0);
v_isShared_5382_ = v_isSharedCheck_5386_;
goto v_resetjp_5380_;
}
v_resetjp_5380_:
{
lean_object* v___x_5384_; 
if (v_isShared_5382_ == 0)
{
v___x_5384_ = v___x_5381_;
goto v_reusejp_5383_;
}
else
{
lean_object* v_reuseFailAlloc_5385_; 
v_reuseFailAlloc_5385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5385_, 0, v_a_5379_);
v___x_5384_ = v_reuseFailAlloc_5385_;
goto v_reusejp_5383_;
}
v_reusejp_5383_:
{
return v___x_5384_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___boxed(lean_object* v_x_5387_, lean_object* v_mkInfoTree_5388_, lean_object* v___y_5389_, lean_object* v___y_5390_, lean_object* v___y_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_, lean_object* v___y_5394_, lean_object* v___y_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_){
_start:
{
lean_object* v_res_5398_; 
v_res_5398_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v_x_5387_, v_mkInfoTree_5388_, v___y_5389_, v___y_5390_, v___y_5391_, v___y_5392_, v___y_5393_, v___y_5394_, v___y_5395_, v___y_5396_);
lean_dec(v___y_5396_);
lean_dec_ref(v___y_5395_);
lean_dec(v___y_5394_);
lean_dec_ref(v___y_5393_);
lean_dec(v___y_5392_);
lean_dec_ref(v___y_5391_);
lean_dec(v___y_5390_);
lean_dec_ref(v___y_5389_);
return v_res_5398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1(lean_object* v_a_5399_, lean_object* v_trees_5400_, lean_object* v___y_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_, lean_object* v___y_5405_, lean_object* v___y_5406_, lean_object* v___y_5407_, lean_object* v___y_5408_){
_start:
{
lean_object* v___x_5410_; 
lean_inc(v___y_5408_);
lean_inc_ref(v___y_5407_);
lean_inc(v___y_5406_);
lean_inc_ref(v___y_5405_);
lean_inc(v___y_5404_);
lean_inc_ref(v___y_5403_);
lean_inc(v___y_5402_);
lean_inc_ref(v___y_5401_);
v___x_5410_ = lean_apply_9(v_a_5399_, v___y_5401_, v___y_5402_, v___y_5403_, v___y_5404_, v___y_5405_, v___y_5406_, v___y_5407_, v___y_5408_, lean_box(0));
if (lean_obj_tag(v___x_5410_) == 0)
{
lean_object* v_a_5411_; lean_object* v___x_5413_; uint8_t v_isShared_5414_; uint8_t v_isSharedCheck_5419_; 
v_a_5411_ = lean_ctor_get(v___x_5410_, 0);
v_isSharedCheck_5419_ = !lean_is_exclusive(v___x_5410_);
if (v_isSharedCheck_5419_ == 0)
{
v___x_5413_ = v___x_5410_;
v_isShared_5414_ = v_isSharedCheck_5419_;
goto v_resetjp_5412_;
}
else
{
lean_inc(v_a_5411_);
lean_dec(v___x_5410_);
v___x_5413_ = lean_box(0);
v_isShared_5414_ = v_isSharedCheck_5419_;
goto v_resetjp_5412_;
}
v_resetjp_5412_:
{
lean_object* v___x_5415_; lean_object* v___x_5417_; 
v___x_5415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5415_, 0, v_a_5411_);
lean_ctor_set(v___x_5415_, 1, v_trees_5400_);
if (v_isShared_5414_ == 0)
{
lean_ctor_set(v___x_5413_, 0, v___x_5415_);
v___x_5417_ = v___x_5413_;
goto v_reusejp_5416_;
}
else
{
lean_object* v_reuseFailAlloc_5418_; 
v_reuseFailAlloc_5418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5418_, 0, v___x_5415_);
v___x_5417_ = v_reuseFailAlloc_5418_;
goto v_reusejp_5416_;
}
v_reusejp_5416_:
{
return v___x_5417_;
}
}
}
else
{
lean_object* v_a_5420_; lean_object* v___x_5422_; uint8_t v_isShared_5423_; uint8_t v_isSharedCheck_5427_; 
lean_dec_ref(v_trees_5400_);
v_a_5420_ = lean_ctor_get(v___x_5410_, 0);
v_isSharedCheck_5427_ = !lean_is_exclusive(v___x_5410_);
if (v_isSharedCheck_5427_ == 0)
{
v___x_5422_ = v___x_5410_;
v_isShared_5423_ = v_isSharedCheck_5427_;
goto v_resetjp_5421_;
}
else
{
lean_inc(v_a_5420_);
lean_dec(v___x_5410_);
v___x_5422_ = lean_box(0);
v_isShared_5423_ = v_isSharedCheck_5427_;
goto v_resetjp_5421_;
}
v_resetjp_5421_:
{
lean_object* v___x_5425_; 
if (v_isShared_5423_ == 0)
{
v___x_5425_ = v___x_5422_;
goto v_reusejp_5424_;
}
else
{
lean_object* v_reuseFailAlloc_5426_; 
v_reuseFailAlloc_5426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5426_, 0, v_a_5420_);
v___x_5425_ = v_reuseFailAlloc_5426_;
goto v_reusejp_5424_;
}
v_reusejp_5424_:
{
return v___x_5425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1___boxed(lean_object* v_a_5428_, lean_object* v_trees_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_, lean_object* v___y_5434_, lean_object* v___y_5435_, lean_object* v___y_5436_, lean_object* v___y_5437_, lean_object* v___y_5438_){
_start:
{
lean_object* v_res_5439_; 
v_res_5439_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1(v_a_5428_, v_trees_5429_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_, v___y_5436_, v___y_5437_);
lean_dec(v___y_5437_);
lean_dec_ref(v___y_5436_);
lean_dec(v___y_5435_);
lean_dec_ref(v___y_5434_);
lean_dec(v___y_5433_);
lean_dec_ref(v___y_5432_);
lean_dec(v___y_5431_);
lean_dec_ref(v___y_5430_);
return v_res_5439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2(lean_object* v___x_5440_, lean_object* v_ref_5441_, lean_object* v_tactic_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_, lean_object* v___y_5446_, lean_object* v___y_5447_, lean_object* v___y_5448_, lean_object* v___y_5449_, lean_object* v___y_5450_){
_start:
{
lean_object* v___x_5452_; 
v___x_5452_ = l_Lean_Elab_Tactic_setGoals___redArg(v___x_5440_, v___y_5444_);
if (lean_obj_tag(v___x_5452_) == 0)
{
lean_object* v___x_5453_; 
lean_dec_ref_known(v___x_5452_, 1);
v___x_5453_ = l_Lean_Elab_WF_applyCleanWfTactic(v___y_5443_, v___y_5444_, v___y_5445_, v___y_5446_, v___y_5447_, v___y_5448_, v___y_5449_, v___y_5450_);
if (lean_obj_tag(v___x_5453_) == 0)
{
lean_object* v___x_5454_; 
lean_dec_ref_known(v___x_5453_, 1);
v___x_5454_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v_ref_5441_, v___y_5443_, v___y_5444_, v___y_5445_, v___y_5446_, v___y_5447_, v___y_5448_, v___y_5449_, v___y_5450_);
if (lean_obj_tag(v___x_5454_) == 0)
{
lean_object* v_a_5455_; lean_object* v___f_5456_; lean_object* v___x_5457_; lean_object* v___x_5458_; 
v_a_5455_ = lean_ctor_get(v___x_5454_, 0);
lean_inc(v_a_5455_);
lean_dec_ref_known(v___x_5454_, 1);
v___f_5456_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1___boxed), 11, 1);
lean_closure_set(v___f_5456_, 0, v_a_5455_);
v___x_5457_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_5457_, 0, v_tactic_5442_);
v___x_5458_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v___x_5457_, v___f_5456_, v___y_5443_, v___y_5444_, v___y_5445_, v___y_5446_, v___y_5447_, v___y_5448_, v___y_5449_, v___y_5450_);
return v___x_5458_;
}
else
{
lean_object* v_a_5459_; lean_object* v___x_5461_; uint8_t v_isShared_5462_; uint8_t v_isSharedCheck_5466_; 
lean_dec(v_tactic_5442_);
v_a_5459_ = lean_ctor_get(v___x_5454_, 0);
v_isSharedCheck_5466_ = !lean_is_exclusive(v___x_5454_);
if (v_isSharedCheck_5466_ == 0)
{
v___x_5461_ = v___x_5454_;
v_isShared_5462_ = v_isSharedCheck_5466_;
goto v_resetjp_5460_;
}
else
{
lean_inc(v_a_5459_);
lean_dec(v___x_5454_);
v___x_5461_ = lean_box(0);
v_isShared_5462_ = v_isSharedCheck_5466_;
goto v_resetjp_5460_;
}
v_resetjp_5460_:
{
lean_object* v___x_5464_; 
if (v_isShared_5462_ == 0)
{
v___x_5464_ = v___x_5461_;
goto v_reusejp_5463_;
}
else
{
lean_object* v_reuseFailAlloc_5465_; 
v_reuseFailAlloc_5465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5465_, 0, v_a_5459_);
v___x_5464_ = v_reuseFailAlloc_5465_;
goto v_reusejp_5463_;
}
v_reusejp_5463_:
{
return v___x_5464_;
}
}
}
}
else
{
lean_dec(v_tactic_5442_);
lean_dec(v_ref_5441_);
return v___x_5453_;
}
}
else
{
lean_dec(v_tactic_5442_);
lean_dec(v_ref_5441_);
return v___x_5452_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2___boxed(lean_object* v___x_5467_, lean_object* v_ref_5468_, lean_object* v_tactic_5469_, lean_object* v___y_5470_, lean_object* v___y_5471_, lean_object* v___y_5472_, lean_object* v___y_5473_, lean_object* v___y_5474_, lean_object* v___y_5475_, lean_object* v___y_5476_, lean_object* v___y_5477_, lean_object* v___y_5478_){
_start:
{
lean_object* v_res_5479_; 
v_res_5479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2(v___x_5467_, v_ref_5468_, v_tactic_5469_, v___y_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_, v___y_5476_, v___y_5477_);
lean_dec(v___y_5477_);
lean_dec_ref(v___y_5476_);
lean_dec(v___y_5475_);
lean_dec_ref(v___y_5474_);
lean_dec(v___y_5473_);
lean_dec_ref(v___y_5472_);
lean_dec(v___y_5471_);
lean_dec_ref(v___y_5470_);
return v_res_5479_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5480_; lean_object* v___x_5481_; 
v___x_5480_ = lean_box(1);
v___x_5481_ = l_Lean_MessageData_ofFormat(v___x_5480_);
return v___x_5481_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5485_; lean_object* v___x_5486_; 
v___x_5485_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__2));
v___x_5486_ = l_Lean_MessageData_ofFormat(v___x_5485_);
return v___x_5486_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3(lean_object* v_x_5487_, lean_object* v_x_5488_){
_start:
{
if (lean_obj_tag(v_x_5488_) == 0)
{
return v_x_5487_;
}
else
{
lean_object* v_head_5489_; lean_object* v_tail_5490_; lean_object* v___x_5492_; uint8_t v_isShared_5493_; uint8_t v_isSharedCheck_5512_; 
v_head_5489_ = lean_ctor_get(v_x_5488_, 0);
v_tail_5490_ = lean_ctor_get(v_x_5488_, 1);
v_isSharedCheck_5512_ = !lean_is_exclusive(v_x_5488_);
if (v_isSharedCheck_5512_ == 0)
{
v___x_5492_ = v_x_5488_;
v_isShared_5493_ = v_isSharedCheck_5512_;
goto v_resetjp_5491_;
}
else
{
lean_inc(v_tail_5490_);
lean_inc(v_head_5489_);
lean_dec(v_x_5488_);
v___x_5492_ = lean_box(0);
v_isShared_5493_ = v_isSharedCheck_5512_;
goto v_resetjp_5491_;
}
v_resetjp_5491_:
{
lean_object* v_before_5494_; lean_object* v___x_5496_; uint8_t v_isShared_5497_; uint8_t v_isSharedCheck_5510_; 
v_before_5494_ = lean_ctor_get(v_head_5489_, 0);
v_isSharedCheck_5510_ = !lean_is_exclusive(v_head_5489_);
if (v_isSharedCheck_5510_ == 0)
{
lean_object* v_unused_5511_; 
v_unused_5511_ = lean_ctor_get(v_head_5489_, 1);
lean_dec(v_unused_5511_);
v___x_5496_ = v_head_5489_;
v_isShared_5497_ = v_isSharedCheck_5510_;
goto v_resetjp_5495_;
}
else
{
lean_inc(v_before_5494_);
lean_dec(v_head_5489_);
v___x_5496_ = lean_box(0);
v_isShared_5497_ = v_isSharedCheck_5510_;
goto v_resetjp_5495_;
}
v_resetjp_5495_:
{
lean_object* v___x_5498_; lean_object* v___x_5500_; 
v___x_5498_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_5497_ == 0)
{
lean_ctor_set_tag(v___x_5496_, 7);
lean_ctor_set(v___x_5496_, 1, v___x_5498_);
lean_ctor_set(v___x_5496_, 0, v_x_5487_);
v___x_5500_ = v___x_5496_;
goto v_reusejp_5499_;
}
else
{
lean_object* v_reuseFailAlloc_5509_; 
v_reuseFailAlloc_5509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5509_, 0, v_x_5487_);
lean_ctor_set(v_reuseFailAlloc_5509_, 1, v___x_5498_);
v___x_5500_ = v_reuseFailAlloc_5509_;
goto v_reusejp_5499_;
}
v_reusejp_5499_:
{
lean_object* v___x_5501_; lean_object* v___x_5503_; 
v___x_5501_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3);
if (v_isShared_5493_ == 0)
{
lean_ctor_set_tag(v___x_5492_, 7);
lean_ctor_set(v___x_5492_, 1, v___x_5501_);
lean_ctor_set(v___x_5492_, 0, v___x_5500_);
v___x_5503_ = v___x_5492_;
goto v_reusejp_5502_;
}
else
{
lean_object* v_reuseFailAlloc_5508_; 
v_reuseFailAlloc_5508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5508_, 0, v___x_5500_);
lean_ctor_set(v_reuseFailAlloc_5508_, 1, v___x_5501_);
v___x_5503_ = v_reuseFailAlloc_5508_;
goto v_reusejp_5502_;
}
v_reusejp_5502_:
{
lean_object* v___x_5504_; lean_object* v___x_5505_; lean_object* v___x_5506_; 
v___x_5504_ = l_Lean_MessageData_ofSyntax(v_before_5494_);
v___x_5505_ = l_Lean_indentD(v___x_5504_);
v___x_5506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5506_, 0, v___x_5503_);
lean_ctor_set(v___x_5506_, 1, v___x_5505_);
v_x_5487_ = v___x_5506_;
v_x_5488_ = v_tail_5490_;
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
lean_object* v___x_5516_; lean_object* v___x_5517_; 
v___x_5516_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__1));
v___x_5517_ = l_Lean_MessageData_ofFormat(v___x_5516_);
return v___x_5517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(lean_object* v_msgData_5518_, lean_object* v_macroStack_5519_, lean_object* v___y_5520_){
_start:
{
lean_object* v_options_5522_; lean_object* v___x_5523_; uint8_t v___x_5524_; 
v_options_5522_ = lean_ctor_get(v___y_5520_, 1);
v___x_5523_ = l_Lean_Elab_pp_macroStack;
v___x_5524_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v_options_5522_, v___x_5523_);
if (v___x_5524_ == 0)
{
lean_object* v___x_5525_; 
lean_dec(v_macroStack_5519_);
v___x_5525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5525_, 0, v_msgData_5518_);
return v___x_5525_;
}
else
{
if (lean_obj_tag(v_macroStack_5519_) == 0)
{
lean_object* v___x_5526_; 
v___x_5526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5526_, 0, v_msgData_5518_);
return v___x_5526_;
}
else
{
lean_object* v_head_5527_; lean_object* v_after_5528_; lean_object* v___x_5530_; uint8_t v_isShared_5531_; uint8_t v_isSharedCheck_5543_; 
v_head_5527_ = lean_ctor_get(v_macroStack_5519_, 0);
lean_inc(v_head_5527_);
v_after_5528_ = lean_ctor_get(v_head_5527_, 1);
v_isSharedCheck_5543_ = !lean_is_exclusive(v_head_5527_);
if (v_isSharedCheck_5543_ == 0)
{
lean_object* v_unused_5544_; 
v_unused_5544_ = lean_ctor_get(v_head_5527_, 0);
lean_dec(v_unused_5544_);
v___x_5530_ = v_head_5527_;
v_isShared_5531_ = v_isSharedCheck_5543_;
goto v_resetjp_5529_;
}
else
{
lean_inc(v_after_5528_);
lean_dec(v_head_5527_);
v___x_5530_ = lean_box(0);
v_isShared_5531_ = v_isSharedCheck_5543_;
goto v_resetjp_5529_;
}
v_resetjp_5529_:
{
lean_object* v___x_5532_; lean_object* v___x_5534_; 
v___x_5532_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_5531_ == 0)
{
lean_ctor_set_tag(v___x_5530_, 7);
lean_ctor_set(v___x_5530_, 1, v___x_5532_);
lean_ctor_set(v___x_5530_, 0, v_msgData_5518_);
v___x_5534_ = v___x_5530_;
goto v_reusejp_5533_;
}
else
{
lean_object* v_reuseFailAlloc_5542_; 
v_reuseFailAlloc_5542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5542_, 0, v_msgData_5518_);
lean_ctor_set(v_reuseFailAlloc_5542_, 1, v___x_5532_);
v___x_5534_ = v_reuseFailAlloc_5542_;
goto v_reusejp_5533_;
}
v_reusejp_5533_:
{
lean_object* v___x_5535_; lean_object* v___x_5536_; lean_object* v___x_5537_; lean_object* v___x_5538_; lean_object* v_msgData_5539_; lean_object* v___x_5540_; lean_object* v___x_5541_; 
v___x_5535_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2);
v___x_5536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5536_, 0, v___x_5534_);
lean_ctor_set(v___x_5536_, 1, v___x_5535_);
v___x_5537_ = l_Lean_MessageData_ofSyntax(v_after_5528_);
v___x_5538_ = l_Lean_indentD(v___x_5537_);
v_msgData_5539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_5539_, 0, v___x_5536_);
lean_ctor_set(v_msgData_5539_, 1, v___x_5538_);
v___x_5540_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3(v_msgData_5539_, v_macroStack_5519_);
v___x_5541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5541_, 0, v___x_5540_);
return v___x_5541_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_5545_, lean_object* v_macroStack_5546_, lean_object* v___y_5547_, lean_object* v___y_5548_){
_start:
{
lean_object* v_res_5549_; 
v_res_5549_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_msgData_5545_, v_macroStack_5546_, v___y_5547_);
lean_dec_ref(v___y_5547_);
return v_res_5549_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(lean_object* v_msg_5550_, lean_object* v___y_5551_, lean_object* v___y_5552_, lean_object* v___y_5553_, lean_object* v___y_5554_, lean_object* v___y_5555_, lean_object* v___y_5556_){
_start:
{
lean_object* v_ref_5558_; lean_object* v___x_5559_; lean_object* v_a_5560_; lean_object* v_macroStack_5561_; lean_object* v___x_5562_; lean_object* v___x_5563_; lean_object* v_a_5564_; lean_object* v___x_5566_; uint8_t v_isShared_5567_; uint8_t v_isSharedCheck_5572_; 
v_ref_5558_ = lean_ctor_get(v___y_5555_, 4);
v___x_5559_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_5550_, v___y_5553_, v___y_5554_, v___y_5555_, v___y_5556_);
v_a_5560_ = lean_ctor_get(v___x_5559_, 0);
lean_inc(v_a_5560_);
lean_dec_ref(v___x_5559_);
v_macroStack_5561_ = lean_ctor_get(v___y_5551_, 1);
v___x_5562_ = l_Lean_Elab_getBetterRef(v_ref_5558_, v_macroStack_5561_);
lean_inc(v_macroStack_5561_);
v___x_5563_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_a_5560_, v_macroStack_5561_, v___y_5555_);
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
v___x_5568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5568_, 0, v___x_5562_);
lean_ctor_set(v___x_5568_, 1, v_a_5564_);
if (v_isShared_5567_ == 0)
{
lean_ctor_set_tag(v___x_5566_, 1);
lean_ctor_set(v___x_5566_, 0, v___x_5568_);
v___x_5570_ = v___x_5566_;
goto v_reusejp_5569_;
}
else
{
lean_object* v_reuseFailAlloc_5571_; 
v_reuseFailAlloc_5571_ = lean_alloc_ctor(1, 1, 0);
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
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg___boxed(lean_object* v_msg_5573_, lean_object* v___y_5574_, lean_object* v___y_5575_, lean_object* v___y_5576_, lean_object* v___y_5577_, lean_object* v___y_5578_, lean_object* v___y_5579_, lean_object* v___y_5580_){
_start:
{
lean_object* v_res_5581_; 
v_res_5581_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v_msg_5573_, v___y_5574_, v___y_5575_, v___y_5576_, v___y_5577_, v___y_5578_, v___y_5579_);
lean_dec(v___y_5579_);
lean_dec_ref(v___y_5578_);
lean_dec(v___y_5577_);
lean_dec_ref(v___y_5576_);
lean_dec(v___y_5575_);
lean_dec_ref(v___y_5574_);
return v_res_5581_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1(void){
_start:
{
lean_object* v___x_5583_; lean_object* v___x_5584_; 
v___x_5583_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__0));
v___x_5584_ = l_Lean_stringToMessageData(v___x_5583_);
return v___x_5584_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(lean_object* v_as_5585_, size_t v_sz_5586_, size_t v_i_5587_, lean_object* v_b_5588_, lean_object* v___y_5589_, lean_object* v___y_5590_, lean_object* v___y_5591_, lean_object* v___y_5592_, lean_object* v___y_5593_, lean_object* v___y_5594_){
_start:
{
lean_object* v_a_5597_; uint8_t v___x_5601_; 
v___x_5601_ = lean_usize_dec_lt(v_i_5587_, v_sz_5586_);
if (v___x_5601_ == 0)
{
lean_object* v___x_5602_; 
v___x_5602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5602_, 0, v_b_5588_);
return v___x_5602_;
}
else
{
lean_object* v_a_5603_; lean_object* v___x_5604_; 
v_a_5603_ = lean_array_uget_borrowed(v_as_5585_, v_i_5587_);
lean_inc(v_a_5603_);
v___x_5604_ = l_Lean_MVarId_getType(v_a_5603_, v___y_5591_, v___y_5592_, v___y_5593_, v___y_5594_);
if (lean_obj_tag(v___x_5604_) == 0)
{
lean_object* v_a_5605_; lean_object* v___x_5606_; 
v_a_5605_ = lean_ctor_get(v___x_5604_, 0);
lean_inc(v_a_5605_);
lean_dec_ref_known(v___x_5604_, 1);
lean_inc(v_a_5603_);
v___x_5606_ = l_Lean_MVarId_getType(v_a_5603_, v___y_5591_, v___y_5592_, v___y_5593_, v___y_5594_);
if (lean_obj_tag(v___x_5606_) == 0)
{
lean_object* v_a_5607_; lean_object* v___x_5608_; lean_object* v___x_5609_; 
v_a_5607_ = lean_ctor_get(v___x_5606_, 0);
lean_inc(v_a_5607_);
lean_dec_ref_known(v___x_5606_, 1);
v___x_5608_ = lean_box(0);
v___x_5609_ = l_Lean_getRecAppSyntax_x3f(v_a_5607_);
lean_dec(v_a_5607_);
if (lean_obj_tag(v___x_5609_) == 1)
{
lean_object* v_val_5610_; lean_object* v___x_5611_; lean_object* v___x_5612_; 
v_val_5610_ = lean_ctor_get(v___x_5609_, 0);
lean_inc(v_val_5610_);
lean_dec_ref_known(v___x_5609_, 1);
v___x_5611_ = l_Lean_Expr_mdataExpr_x21(v_a_5605_);
lean_dec(v_a_5605_);
lean_inc(v_a_5603_);
v___x_5612_ = l_Lean_MVarId_setType___redArg(v_a_5603_, v___x_5611_, v___y_5592_);
if (lean_obj_tag(v___x_5612_) == 0)
{
lean_object* v_toCold_5613_; lean_object* v_options_5614_; lean_object* v_currRecDepth_5615_; lean_object* v_maxRecDepth_5616_; lean_object* v_ref_5617_; lean_object* v_currNamespace_5618_; lean_object* v_openDecls_5619_; lean_object* v_initHeartbeats_5620_; lean_object* v_maxHeartbeats_5621_; lean_object* v_currMacroScope_5622_; uint8_t v_diag_5623_; uint8_t v_suppressElabErrors_5624_; lean_object* v_ref_5625_; lean_object* v___x_5626_; lean_object* v___x_5627_; 
lean_dec_ref_known(v___x_5612_, 1);
v_toCold_5613_ = lean_ctor_get(v___y_5593_, 0);
v_options_5614_ = lean_ctor_get(v___y_5593_, 1);
v_currRecDepth_5615_ = lean_ctor_get(v___y_5593_, 2);
v_maxRecDepth_5616_ = lean_ctor_get(v___y_5593_, 3);
v_ref_5617_ = lean_ctor_get(v___y_5593_, 4);
v_currNamespace_5618_ = lean_ctor_get(v___y_5593_, 5);
v_openDecls_5619_ = lean_ctor_get(v___y_5593_, 6);
v_initHeartbeats_5620_ = lean_ctor_get(v___y_5593_, 7);
v_maxHeartbeats_5621_ = lean_ctor_get(v___y_5593_, 8);
v_currMacroScope_5622_ = lean_ctor_get(v___y_5593_, 9);
v_diag_5623_ = lean_ctor_get_uint8(v___y_5593_, sizeof(void*)*10);
v_suppressElabErrors_5624_ = lean_ctor_get_uint8(v___y_5593_, sizeof(void*)*10 + 1);
v_ref_5625_ = l_Lean_replaceRef(v_val_5610_, v_ref_5617_);
lean_dec(v_val_5610_);
lean_inc(v_currMacroScope_5622_);
lean_inc(v_maxHeartbeats_5621_);
lean_inc(v_initHeartbeats_5620_);
lean_inc(v_openDecls_5619_);
lean_inc(v_currNamespace_5618_);
lean_inc(v_maxRecDepth_5616_);
lean_inc(v_currRecDepth_5615_);
lean_inc_ref(v_options_5614_);
lean_inc_ref(v_toCold_5613_);
v___x_5626_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_5626_, 0, v_toCold_5613_);
lean_ctor_set(v___x_5626_, 1, v_options_5614_);
lean_ctor_set(v___x_5626_, 2, v_currRecDepth_5615_);
lean_ctor_set(v___x_5626_, 3, v_maxRecDepth_5616_);
lean_ctor_set(v___x_5626_, 4, v_ref_5625_);
lean_ctor_set(v___x_5626_, 5, v_currNamespace_5618_);
lean_ctor_set(v___x_5626_, 6, v_openDecls_5619_);
lean_ctor_set(v___x_5626_, 7, v_initHeartbeats_5620_);
lean_ctor_set(v___x_5626_, 8, v_maxHeartbeats_5621_);
lean_ctor_set(v___x_5626_, 9, v_currMacroScope_5622_);
lean_ctor_set_uint8(v___x_5626_, sizeof(void*)*10, v_diag_5623_);
lean_ctor_set_uint8(v___x_5626_, sizeof(void*)*10 + 1, v_suppressElabErrors_5624_);
lean_inc(v_a_5603_);
v___x_5627_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(v_a_5603_, v___y_5589_, v___y_5590_, v___y_5591_, v___y_5592_, v___x_5626_, v___y_5594_);
lean_dec_ref_known(v___x_5626_, 10);
if (lean_obj_tag(v___x_5627_) == 0)
{
lean_dec_ref_known(v___x_5627_, 1);
v_a_5597_ = v___x_5608_;
goto v___jp_5596_;
}
else
{
return v___x_5627_;
}
}
else
{
lean_dec(v_val_5610_);
return v___x_5612_;
}
}
else
{
lean_object* v___x_5628_; lean_object* v___x_5629_; lean_object* v___x_5630_; lean_object* v___x_5631_; 
lean_dec(v___x_5609_);
v___x_5628_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1);
v___x_5629_ = l_Lean_indentExpr(v_a_5605_);
v___x_5630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5630_, 0, v___x_5628_);
lean_ctor_set(v___x_5630_, 1, v___x_5629_);
v___x_5631_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v___x_5630_, v___y_5589_, v___y_5590_, v___y_5591_, v___y_5592_, v___y_5593_, v___y_5594_);
if (lean_obj_tag(v___x_5631_) == 0)
{
lean_dec_ref_known(v___x_5631_, 1);
v_a_5597_ = v___x_5608_;
goto v___jp_5596_;
}
else
{
return v___x_5631_;
}
}
}
else
{
lean_object* v_a_5632_; lean_object* v___x_5634_; uint8_t v_isShared_5635_; uint8_t v_isSharedCheck_5639_; 
lean_dec(v_a_5605_);
v_a_5632_ = lean_ctor_get(v___x_5606_, 0);
v_isSharedCheck_5639_ = !lean_is_exclusive(v___x_5606_);
if (v_isSharedCheck_5639_ == 0)
{
v___x_5634_ = v___x_5606_;
v_isShared_5635_ = v_isSharedCheck_5639_;
goto v_resetjp_5633_;
}
else
{
lean_inc(v_a_5632_);
lean_dec(v___x_5606_);
v___x_5634_ = lean_box(0);
v_isShared_5635_ = v_isSharedCheck_5639_;
goto v_resetjp_5633_;
}
v_resetjp_5633_:
{
lean_object* v___x_5637_; 
if (v_isShared_5635_ == 0)
{
v___x_5637_ = v___x_5634_;
goto v_reusejp_5636_;
}
else
{
lean_object* v_reuseFailAlloc_5638_; 
v_reuseFailAlloc_5638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5638_, 0, v_a_5632_);
v___x_5637_ = v_reuseFailAlloc_5638_;
goto v_reusejp_5636_;
}
v_reusejp_5636_:
{
return v___x_5637_;
}
}
}
}
else
{
lean_object* v_a_5640_; lean_object* v___x_5642_; uint8_t v_isShared_5643_; uint8_t v_isSharedCheck_5647_; 
v_a_5640_ = lean_ctor_get(v___x_5604_, 0);
v_isSharedCheck_5647_ = !lean_is_exclusive(v___x_5604_);
if (v_isSharedCheck_5647_ == 0)
{
v___x_5642_ = v___x_5604_;
v_isShared_5643_ = v_isSharedCheck_5647_;
goto v_resetjp_5641_;
}
else
{
lean_inc(v_a_5640_);
lean_dec(v___x_5604_);
v___x_5642_ = lean_box(0);
v_isShared_5643_ = v_isSharedCheck_5647_;
goto v_resetjp_5641_;
}
v_resetjp_5641_:
{
lean_object* v___x_5645_; 
if (v_isShared_5643_ == 0)
{
v___x_5645_ = v___x_5642_;
goto v_reusejp_5644_;
}
else
{
lean_object* v_reuseFailAlloc_5646_; 
v_reuseFailAlloc_5646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5646_, 0, v_a_5640_);
v___x_5645_ = v_reuseFailAlloc_5646_;
goto v_reusejp_5644_;
}
v_reusejp_5644_:
{
return v___x_5645_;
}
}
}
}
v___jp_5596_:
{
size_t v___x_5598_; size_t v___x_5599_; 
v___x_5598_ = ((size_t)1ULL);
v___x_5599_ = lean_usize_add(v_i_5587_, v___x_5598_);
v_i_5587_ = v___x_5599_;
v_b_5588_ = v_a_5597_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___boxed(lean_object* v_as_5648_, lean_object* v_sz_5649_, lean_object* v_i_5650_, lean_object* v_b_5651_, lean_object* v___y_5652_, lean_object* v___y_5653_, lean_object* v___y_5654_, lean_object* v___y_5655_, lean_object* v___y_5656_, lean_object* v___y_5657_, lean_object* v___y_5658_){
_start:
{
size_t v_sz_boxed_5659_; size_t v_i_boxed_5660_; lean_object* v_res_5661_; 
v_sz_boxed_5659_ = lean_unbox_usize(v_sz_5649_);
lean_dec(v_sz_5649_);
v_i_boxed_5660_ = lean_unbox_usize(v_i_5650_);
lean_dec(v_i_5650_);
v_res_5661_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(v_as_5648_, v_sz_boxed_5659_, v_i_boxed_5660_, v_b_5651_, v___y_5652_, v___y_5653_, v___y_5654_, v___y_5655_, v___y_5656_, v___y_5657_);
lean_dec(v___y_5657_);
lean_dec_ref(v___y_5656_);
lean_dec(v___y_5655_);
lean_dec_ref(v___y_5654_);
lean_dec(v___y_5653_);
lean_dec_ref(v___y_5652_);
lean_dec_ref(v_as_5648_);
return v_res_5661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(lean_object* v_as_5662_, size_t v_i_5663_, size_t v_stop_5664_, lean_object* v_b_5665_, lean_object* v___y_5666_, lean_object* v___y_5667_, lean_object* v___y_5668_, lean_object* v___y_5669_){
_start:
{
uint8_t v___x_5671_; 
v___x_5671_ = lean_usize_dec_eq(v_i_5663_, v_stop_5664_);
if (v___x_5671_ == 0)
{
lean_object* v___x_5672_; lean_object* v___x_5673_; 
v___x_5672_ = lean_array_uget_borrowed(v_as_5662_, v_i_5663_);
lean_inc(v___x_5672_);
v___x_5673_ = l_Lean_MVarId_getType(v___x_5672_, v___y_5666_, v___y_5667_, v___y_5668_, v___y_5669_);
if (lean_obj_tag(v___x_5673_) == 0)
{
lean_object* v_a_5674_; lean_object* v___x_5675_; lean_object* v___x_5676_; 
v_a_5674_ = lean_ctor_get(v___x_5673_, 0);
lean_inc(v_a_5674_);
lean_dec_ref_known(v___x_5673_, 1);
v___x_5675_ = l_Lean_Expr_mdataExpr_x21(v_a_5674_);
lean_dec(v_a_5674_);
lean_inc(v___x_5672_);
v___x_5676_ = l_Lean_MVarId_setType___redArg(v___x_5672_, v___x_5675_, v___y_5667_);
if (lean_obj_tag(v___x_5676_) == 0)
{
lean_object* v_a_5677_; size_t v___x_5678_; size_t v___x_5679_; 
v_a_5677_ = lean_ctor_get(v___x_5676_, 0);
lean_inc(v_a_5677_);
lean_dec_ref_known(v___x_5676_, 1);
v___x_5678_ = ((size_t)1ULL);
v___x_5679_ = lean_usize_add(v_i_5663_, v___x_5678_);
v_i_5663_ = v___x_5679_;
v_b_5665_ = v_a_5677_;
goto _start;
}
else
{
return v___x_5676_;
}
}
else
{
lean_object* v_a_5681_; lean_object* v___x_5683_; uint8_t v_isShared_5684_; uint8_t v_isSharedCheck_5688_; 
v_a_5681_ = lean_ctor_get(v___x_5673_, 0);
v_isSharedCheck_5688_ = !lean_is_exclusive(v___x_5673_);
if (v_isSharedCheck_5688_ == 0)
{
v___x_5683_ = v___x_5673_;
v_isShared_5684_ = v_isSharedCheck_5688_;
goto v_resetjp_5682_;
}
else
{
lean_inc(v_a_5681_);
lean_dec(v___x_5673_);
v___x_5683_ = lean_box(0);
v_isShared_5684_ = v_isSharedCheck_5688_;
goto v_resetjp_5682_;
}
v_resetjp_5682_:
{
lean_object* v___x_5686_; 
if (v_isShared_5684_ == 0)
{
v___x_5686_ = v___x_5683_;
goto v_reusejp_5685_;
}
else
{
lean_object* v_reuseFailAlloc_5687_; 
v_reuseFailAlloc_5687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5687_, 0, v_a_5681_);
v___x_5686_ = v_reuseFailAlloc_5687_;
goto v_reusejp_5685_;
}
v_reusejp_5685_:
{
return v___x_5686_;
}
}
}
}
else
{
lean_object* v___x_5689_; 
v___x_5689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5689_, 0, v_b_5665_);
return v___x_5689_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg___boxed(lean_object* v_as_5690_, lean_object* v_i_5691_, lean_object* v_stop_5692_, lean_object* v_b_5693_, lean_object* v___y_5694_, lean_object* v___y_5695_, lean_object* v___y_5696_, lean_object* v___y_5697_, lean_object* v___y_5698_){
_start:
{
size_t v_i_boxed_5699_; size_t v_stop_boxed_5700_; lean_object* v_res_5701_; 
v_i_boxed_5699_ = lean_unbox_usize(v_i_5691_);
lean_dec(v_i_5691_);
v_stop_boxed_5700_ = lean_unbox_usize(v_stop_5692_);
lean_dec(v_stop_5692_);
v_res_5701_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v_as_5690_, v_i_boxed_5699_, v_stop_boxed_5700_, v_b_5693_, v___y_5694_, v___y_5695_, v___y_5696_, v___y_5697_);
lean_dec(v___y_5697_);
lean_dec_ref(v___y_5696_);
lean_dec(v___y_5695_);
lean_dec_ref(v___y_5694_);
lean_dec_ref(v_as_5690_);
return v_res_5701_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3(lean_object* v___x_5702_, lean_object* v___x_5703_, lean_object* v___x_5704_, lean_object* v___y_5705_, lean_object* v___y_5706_, lean_object* v___y_5707_, lean_object* v___y_5708_, lean_object* v___y_5709_, lean_object* v___y_5710_){
_start:
{
if (lean_obj_tag(v___x_5702_) == 0)
{
lean_object* v___x_5712_; size_t v_sz_5713_; size_t v___x_5714_; lean_object* v___x_5715_; 
v___x_5712_ = lean_box(0);
v_sz_5713_ = lean_array_size(v___x_5703_);
v___x_5714_ = ((size_t)0ULL);
v___x_5715_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(v___x_5703_, v_sz_5713_, v___x_5714_, v___x_5712_, v___y_5705_, v___y_5706_, v___y_5707_, v___y_5708_, v___y_5709_, v___y_5710_);
lean_dec_ref(v___x_5703_);
if (lean_obj_tag(v___x_5715_) == 0)
{
lean_object* v___x_5717_; uint8_t v_isShared_5718_; uint8_t v_isSharedCheck_5722_; 
v_isSharedCheck_5722_ = !lean_is_exclusive(v___x_5715_);
if (v_isSharedCheck_5722_ == 0)
{
lean_object* v_unused_5723_; 
v_unused_5723_ = lean_ctor_get(v___x_5715_, 0);
lean_dec(v_unused_5723_);
v___x_5717_ = v___x_5715_;
v_isShared_5718_ = v_isSharedCheck_5722_;
goto v_resetjp_5716_;
}
else
{
lean_dec(v___x_5715_);
v___x_5717_ = lean_box(0);
v_isShared_5718_ = v_isSharedCheck_5722_;
goto v_resetjp_5716_;
}
v_resetjp_5716_:
{
lean_object* v___x_5720_; 
if (v_isShared_5718_ == 0)
{
lean_ctor_set(v___x_5717_, 0, v___x_5712_);
v___x_5720_ = v___x_5717_;
goto v_reusejp_5719_;
}
else
{
lean_object* v_reuseFailAlloc_5721_; 
v_reuseFailAlloc_5721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5721_, 0, v___x_5712_);
v___x_5720_ = v_reuseFailAlloc_5721_;
goto v_reusejp_5719_;
}
v_reusejp_5719_:
{
return v___x_5720_;
}
}
}
else
{
return v___x_5715_;
}
}
else
{
lean_object* v_val_5724_; lean_object* v___x_5726_; uint8_t v_isShared_5727_; uint8_t v_isSharedCheck_5798_; 
v_val_5724_ = lean_ctor_get(v___x_5702_, 0);
v_isSharedCheck_5798_ = !lean_is_exclusive(v___x_5702_);
if (v_isSharedCheck_5798_ == 0)
{
v___x_5726_ = v___x_5702_;
v_isShared_5727_ = v_isSharedCheck_5798_;
goto v_resetjp_5725_;
}
else
{
lean_inc(v_val_5724_);
lean_dec(v___x_5702_);
v___x_5726_ = lean_box(0);
v_isShared_5727_ = v_isSharedCheck_5798_;
goto v_resetjp_5725_;
}
v_resetjp_5725_:
{
lean_object* v_ref_5728_; lean_object* v_tactic_5729_; lean_object* v_toCold_5730_; lean_object* v_options_5731_; lean_object* v_currRecDepth_5732_; lean_object* v_maxRecDepth_5733_; lean_object* v_ref_5734_; lean_object* v_currNamespace_5735_; lean_object* v_openDecls_5736_; lean_object* v_initHeartbeats_5737_; lean_object* v_maxHeartbeats_5738_; lean_object* v_currMacroScope_5739_; uint8_t v_diag_5740_; uint8_t v_suppressElabErrors_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; lean_object* v_ref_5744_; lean_object* v___x_5745_; lean_object* v___y_5771_; lean_object* v___y_5788_; uint8_t v___x_5789_; 
v_ref_5728_ = lean_ctor_get(v_val_5724_, 0);
lean_inc(v_ref_5728_);
v_tactic_5729_ = lean_ctor_get(v_val_5724_, 1);
lean_inc(v_tactic_5729_);
lean_dec(v_val_5724_);
v_toCold_5730_ = lean_ctor_get(v___y_5709_, 0);
v_options_5731_ = lean_ctor_get(v___y_5709_, 1);
v_currRecDepth_5732_ = lean_ctor_get(v___y_5709_, 2);
v_maxRecDepth_5733_ = lean_ctor_get(v___y_5709_, 3);
v_ref_5734_ = lean_ctor_get(v___y_5709_, 4);
v_currNamespace_5735_ = lean_ctor_get(v___y_5709_, 5);
v_openDecls_5736_ = lean_ctor_get(v___y_5709_, 6);
v_initHeartbeats_5737_ = lean_ctor_get(v___y_5709_, 7);
v_maxHeartbeats_5738_ = lean_ctor_get(v___y_5709_, 8);
v_currMacroScope_5739_ = lean_ctor_get(v___y_5709_, 9);
v_diag_5740_ = lean_ctor_get_uint8(v___y_5709_, sizeof(void*)*10);
v_suppressElabErrors_5741_ = lean_ctor_get_uint8(v___y_5709_, sizeof(void*)*10 + 1);
v___x_5742_ = lean_unsigned_to_nat(0u);
v___x_5743_ = lean_array_get_size(v___x_5703_);
v_ref_5744_ = l_Lean_replaceRef(v_ref_5728_, v_ref_5734_);
lean_inc(v_currMacroScope_5739_);
lean_inc(v_maxHeartbeats_5738_);
lean_inc(v_initHeartbeats_5737_);
lean_inc(v_openDecls_5736_);
lean_inc(v_currNamespace_5735_);
lean_inc(v_maxRecDepth_5733_);
lean_inc(v_currRecDepth_5732_);
lean_inc_ref(v_options_5731_);
lean_inc_ref(v_toCold_5730_);
v___x_5745_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_5745_, 0, v_toCold_5730_);
lean_ctor_set(v___x_5745_, 1, v_options_5731_);
lean_ctor_set(v___x_5745_, 2, v_currRecDepth_5732_);
lean_ctor_set(v___x_5745_, 3, v_maxRecDepth_5733_);
lean_ctor_set(v___x_5745_, 4, v_ref_5744_);
lean_ctor_set(v___x_5745_, 5, v_currNamespace_5735_);
lean_ctor_set(v___x_5745_, 6, v_openDecls_5736_);
lean_ctor_set(v___x_5745_, 7, v_initHeartbeats_5737_);
lean_ctor_set(v___x_5745_, 8, v_maxHeartbeats_5738_);
lean_ctor_set(v___x_5745_, 9, v_currMacroScope_5739_);
lean_ctor_set_uint8(v___x_5745_, sizeof(void*)*10, v_diag_5740_);
lean_ctor_set_uint8(v___x_5745_, sizeof(void*)*10 + 1, v_suppressElabErrors_5741_);
v___x_5789_ = lean_nat_dec_lt(v___x_5742_, v___x_5743_);
if (v___x_5789_ == 0)
{
goto v___jp_5772_;
}
else
{
lean_object* v___x_5790_; uint8_t v___x_5791_; 
v___x_5790_ = lean_box(0);
v___x_5791_ = lean_nat_dec_le(v___x_5743_, v___x_5743_);
if (v___x_5791_ == 0)
{
if (v___x_5789_ == 0)
{
goto v___jp_5772_;
}
else
{
size_t v___x_5792_; size_t v___x_5793_; lean_object* v___x_5794_; 
v___x_5792_ = ((size_t)0ULL);
v___x_5793_ = lean_usize_of_nat(v___x_5743_);
v___x_5794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v___x_5703_, v___x_5792_, v___x_5793_, v___x_5790_, v___y_5707_, v___y_5708_, v___x_5745_, v___y_5710_);
v___y_5788_ = v___x_5794_;
goto v___jp_5787_;
}
}
else
{
size_t v___x_5795_; size_t v___x_5796_; lean_object* v___x_5797_; 
v___x_5795_ = ((size_t)0ULL);
v___x_5796_ = lean_usize_of_nat(v___x_5743_);
v___x_5797_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v___x_5703_, v___x_5795_, v___x_5796_, v___x_5790_, v___y_5707_, v___y_5708_, v___x_5745_, v___y_5710_);
v___y_5788_ = v___x_5797_;
goto v___jp_5787_;
}
}
v___jp_5746_:
{
lean_object* v___x_5747_; lean_object* v___x_5748_; lean_object* v___f_5749_; lean_object* v___x_5750_; 
v___x_5747_ = lean_array_get(v___x_5704_, v___x_5703_, v___x_5742_);
v___x_5748_ = lean_array_to_list(v___x_5703_);
v___f_5749_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2___boxed), 12, 3);
lean_closure_set(v___f_5749_, 0, v___x_5748_);
lean_closure_set(v___f_5749_, 1, v_ref_5728_);
lean_closure_set(v___f_5749_, 2, v_tactic_5729_);
v___x_5750_ = l_Lean_Elab_Tactic_run(v___x_5747_, v___f_5749_, v___y_5705_, v___y_5706_, v___y_5707_, v___y_5708_, v___x_5745_, v___y_5710_);
if (lean_obj_tag(v___x_5750_) == 0)
{
lean_object* v_a_5751_; lean_object* v___x_5753_; uint8_t v_isShared_5754_; uint8_t v_isSharedCheck_5761_; 
v_a_5751_ = lean_ctor_get(v___x_5750_, 0);
v_isSharedCheck_5761_ = !lean_is_exclusive(v___x_5750_);
if (v_isSharedCheck_5761_ == 0)
{
v___x_5753_ = v___x_5750_;
v_isShared_5754_ = v_isSharedCheck_5761_;
goto v_resetjp_5752_;
}
else
{
lean_inc(v_a_5751_);
lean_dec(v___x_5750_);
v___x_5753_ = lean_box(0);
v_isShared_5754_ = v_isSharedCheck_5761_;
goto v_resetjp_5752_;
}
v_resetjp_5752_:
{
uint8_t v___x_5755_; 
v___x_5755_ = l_List_isEmpty___redArg(v_a_5751_);
if (v___x_5755_ == 0)
{
lean_object* v___x_5756_; 
lean_del_object(v___x_5753_);
v___x_5756_ = l_Lean_Elab_Term_reportUnsolvedGoals(v_a_5751_, v___y_5707_, v___y_5708_, v___x_5745_, v___y_5710_);
lean_dec_ref_known(v___x_5745_, 10);
return v___x_5756_;
}
else
{
lean_object* v___x_5757_; lean_object* v___x_5759_; 
lean_dec(v_a_5751_);
lean_dec_ref_known(v___x_5745_, 10);
v___x_5757_ = lean_box(0);
if (v_isShared_5754_ == 0)
{
lean_ctor_set(v___x_5753_, 0, v___x_5757_);
v___x_5759_ = v___x_5753_;
goto v_reusejp_5758_;
}
else
{
lean_object* v_reuseFailAlloc_5760_; 
v_reuseFailAlloc_5760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5760_, 0, v___x_5757_);
v___x_5759_ = v_reuseFailAlloc_5760_;
goto v_reusejp_5758_;
}
v_reusejp_5758_:
{
return v___x_5759_;
}
}
}
}
else
{
lean_object* v_a_5762_; lean_object* v___x_5764_; uint8_t v_isShared_5765_; uint8_t v_isSharedCheck_5769_; 
lean_dec_ref_known(v___x_5745_, 10);
v_a_5762_ = lean_ctor_get(v___x_5750_, 0);
v_isSharedCheck_5769_ = !lean_is_exclusive(v___x_5750_);
if (v_isSharedCheck_5769_ == 0)
{
v___x_5764_ = v___x_5750_;
v_isShared_5765_ = v_isSharedCheck_5769_;
goto v_resetjp_5763_;
}
else
{
lean_inc(v_a_5762_);
lean_dec(v___x_5750_);
v___x_5764_ = lean_box(0);
v_isShared_5765_ = v_isSharedCheck_5769_;
goto v_resetjp_5763_;
}
v_resetjp_5763_:
{
lean_object* v___x_5767_; 
if (v_isShared_5765_ == 0)
{
v___x_5767_ = v___x_5764_;
goto v_reusejp_5766_;
}
else
{
lean_object* v_reuseFailAlloc_5768_; 
v_reuseFailAlloc_5768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5768_, 0, v_a_5762_);
v___x_5767_ = v_reuseFailAlloc_5768_;
goto v_reusejp_5766_;
}
v_reusejp_5766_:
{
return v___x_5767_;
}
}
}
}
v___jp_5770_:
{
if (lean_obj_tag(v___y_5771_) == 0)
{
lean_dec_ref_known(v___y_5771_, 1);
goto v___jp_5746_;
}
else
{
lean_dec_ref_known(v___x_5745_, 10);
lean_dec(v_tactic_5729_);
lean_dec(v_ref_5728_);
lean_dec_ref(v___x_5703_);
return v___y_5771_;
}
}
v___jp_5772_:
{
uint8_t v___x_5773_; 
v___x_5773_ = lean_nat_dec_eq(v___x_5743_, v___x_5742_);
if (v___x_5773_ == 0)
{
uint8_t v___x_5774_; 
lean_del_object(v___x_5726_);
v___x_5774_ = lean_nat_dec_lt(v___x_5742_, v___x_5743_);
if (v___x_5774_ == 0)
{
goto v___jp_5746_;
}
else
{
lean_object* v___x_5775_; uint8_t v___x_5776_; 
v___x_5775_ = lean_box(0);
v___x_5776_ = lean_nat_dec_le(v___x_5743_, v___x_5743_);
if (v___x_5776_ == 0)
{
if (v___x_5774_ == 0)
{
goto v___jp_5746_;
}
else
{
size_t v___x_5777_; size_t v___x_5778_; lean_object* v___x_5779_; 
v___x_5777_ = ((size_t)0ULL);
v___x_5778_ = lean_usize_of_nat(v___x_5743_);
v___x_5779_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v___x_5703_, v___x_5777_, v___x_5778_, v___x_5775_, v___y_5705_, v___y_5706_, v___y_5707_, v___y_5708_, v___x_5745_, v___y_5710_);
v___y_5771_ = v___x_5779_;
goto v___jp_5770_;
}
}
else
{
size_t v___x_5780_; size_t v___x_5781_; lean_object* v___x_5782_; 
v___x_5780_ = ((size_t)0ULL);
v___x_5781_ = lean_usize_of_nat(v___x_5743_);
v___x_5782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v___x_5703_, v___x_5780_, v___x_5781_, v___x_5775_, v___y_5705_, v___y_5706_, v___y_5707_, v___y_5708_, v___x_5745_, v___y_5710_);
v___y_5771_ = v___x_5782_;
goto v___jp_5770_;
}
}
}
else
{
lean_object* v___x_5783_; lean_object* v___x_5785_; 
lean_dec_ref_known(v___x_5745_, 10);
lean_dec(v_tactic_5729_);
lean_dec(v_ref_5728_);
lean_dec_ref(v___x_5703_);
v___x_5783_ = lean_box(0);
if (v_isShared_5727_ == 0)
{
lean_ctor_set_tag(v___x_5726_, 0);
lean_ctor_set(v___x_5726_, 0, v___x_5783_);
v___x_5785_ = v___x_5726_;
goto v_reusejp_5784_;
}
else
{
lean_object* v_reuseFailAlloc_5786_; 
v_reuseFailAlloc_5786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5786_, 0, v___x_5783_);
v___x_5785_ = v_reuseFailAlloc_5786_;
goto v_reusejp_5784_;
}
v_reusejp_5784_:
{
return v___x_5785_;
}
}
}
v___jp_5787_:
{
if (lean_obj_tag(v___y_5788_) == 0)
{
lean_dec_ref_known(v___y_5788_, 1);
goto v___jp_5772_;
}
else
{
lean_dec_ref_known(v___x_5745_, 10);
lean_dec(v_tactic_5729_);
lean_dec(v_ref_5728_);
lean_del_object(v___x_5726_);
lean_dec_ref(v___x_5703_);
return v___y_5788_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3___boxed(lean_object* v___x_5799_, lean_object* v___x_5800_, lean_object* v___x_5801_, lean_object* v___y_5802_, lean_object* v___y_5803_, lean_object* v___y_5804_, lean_object* v___y_5805_, lean_object* v___y_5806_, lean_object* v___y_5807_, lean_object* v___y_5808_){
_start:
{
lean_object* v_res_5809_; 
v_res_5809_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3(v___x_5799_, v___x_5800_, v___x_5801_, v___y_5802_, v___y_5803_, v___y_5804_, v___y_5805_, v___y_5806_, v___y_5807_);
lean_dec(v___y_5807_);
lean_dec_ref(v___y_5806_);
lean_dec(v___y_5805_);
lean_dec_ref(v___y_5804_);
lean_dec(v___y_5803_);
lean_dec_ref(v___y_5802_);
lean_dec(v___x_5801_);
return v_res_5809_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0(lean_object* v_x_5810_){
_start:
{
uint8_t v___x_5811_; 
v___x_5811_ = 0;
return v___x_5811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0___boxed(lean_object* v_x_5812_){
_start:
{
uint8_t v_res_5813_; lean_object* v_r_5814_; 
v_res_5813_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0(v_x_5812_);
lean_dec(v_x_5812_);
v_r_5814_ = lean_box(v_res_5813_);
return v_r_5814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(lean_object* v_as_5821_, size_t v_sz_5822_, size_t v_i_5823_, lean_object* v_b_5824_, lean_object* v___y_5825_, lean_object* v___y_5826_, lean_object* v___y_5827_, lean_object* v___y_5828_){
_start:
{
uint8_t v___x_5830_; 
v___x_5830_ = lean_usize_dec_lt(v_i_5823_, v_sz_5822_);
if (v___x_5830_ == 0)
{
lean_object* v___x_5831_; 
v___x_5831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5831_, 0, v_b_5824_);
return v___x_5831_;
}
else
{
lean_object* v_snd_5832_; lean_object* v_fst_5833_; lean_object* v___x_5835_; uint8_t v_isShared_5836_; uint8_t v_isSharedCheck_5905_; 
v_snd_5832_ = lean_ctor_get(v_b_5824_, 1);
v_fst_5833_ = lean_ctor_get(v_b_5824_, 0);
v_isSharedCheck_5905_ = !lean_is_exclusive(v_b_5824_);
if (v_isSharedCheck_5905_ == 0)
{
v___x_5835_ = v_b_5824_;
v_isShared_5836_ = v_isSharedCheck_5905_;
goto v_resetjp_5834_;
}
else
{
lean_inc(v_snd_5832_);
lean_inc(v_fst_5833_);
lean_dec(v_b_5824_);
v___x_5835_ = lean_box(0);
v_isShared_5836_ = v_isSharedCheck_5905_;
goto v_resetjp_5834_;
}
v_resetjp_5834_:
{
lean_object* v_array_5837_; lean_object* v_start_5838_; lean_object* v_stop_5839_; uint8_t v___x_5840_; 
v_array_5837_ = lean_ctor_get(v_snd_5832_, 0);
v_start_5838_ = lean_ctor_get(v_snd_5832_, 1);
v_stop_5839_ = lean_ctor_get(v_snd_5832_, 2);
v___x_5840_ = lean_nat_dec_lt(v_start_5838_, v_stop_5839_);
if (v___x_5840_ == 0)
{
lean_object* v___x_5842_; 
if (v_isShared_5836_ == 0)
{
v___x_5842_ = v___x_5835_;
goto v_reusejp_5841_;
}
else
{
lean_object* v_reuseFailAlloc_5844_; 
v_reuseFailAlloc_5844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5844_, 0, v_fst_5833_);
lean_ctor_set(v_reuseFailAlloc_5844_, 1, v_snd_5832_);
v___x_5842_ = v_reuseFailAlloc_5844_;
goto v_reusejp_5841_;
}
v_reusejp_5841_:
{
lean_object* v___x_5843_; 
v___x_5843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5843_, 0, v___x_5842_);
return v___x_5843_;
}
}
else
{
lean_object* v___x_5846_; uint8_t v_isShared_5847_; uint8_t v_isSharedCheck_5901_; 
lean_inc(v_stop_5839_);
lean_inc(v_start_5838_);
lean_inc_ref(v_array_5837_);
v_isSharedCheck_5901_ = !lean_is_exclusive(v_snd_5832_);
if (v_isSharedCheck_5901_ == 0)
{
lean_object* v_unused_5902_; lean_object* v_unused_5903_; lean_object* v_unused_5904_; 
v_unused_5902_ = lean_ctor_get(v_snd_5832_, 2);
lean_dec(v_unused_5902_);
v_unused_5903_ = lean_ctor_get(v_snd_5832_, 1);
lean_dec(v_unused_5903_);
v_unused_5904_ = lean_ctor_get(v_snd_5832_, 0);
lean_dec(v_unused_5904_);
v___x_5846_ = v_snd_5832_;
v_isShared_5847_ = v_isSharedCheck_5901_;
goto v_resetjp_5845_;
}
else
{
lean_dec(v_snd_5832_);
v___x_5846_ = lean_box(0);
v_isShared_5847_ = v_isSharedCheck_5901_;
goto v_resetjp_5845_;
}
v_resetjp_5845_:
{
lean_object* v_array_5848_; lean_object* v_start_5849_; lean_object* v_stop_5850_; lean_object* v___x_5851_; lean_object* v___x_5852_; lean_object* v___x_5853_; lean_object* v___x_5855_; 
v_array_5848_ = lean_ctor_get(v_fst_5833_, 0);
v_start_5849_ = lean_ctor_get(v_fst_5833_, 1);
v_stop_5850_ = lean_ctor_get(v_fst_5833_, 2);
v___x_5851_ = lean_array_fget(v_array_5837_, v_start_5838_);
v___x_5852_ = lean_unsigned_to_nat(1u);
v___x_5853_ = lean_nat_add(v_start_5838_, v___x_5852_);
lean_dec(v_start_5838_);
if (v_isShared_5847_ == 0)
{
lean_ctor_set(v___x_5846_, 1, v___x_5853_);
v___x_5855_ = v___x_5846_;
goto v_reusejp_5854_;
}
else
{
lean_object* v_reuseFailAlloc_5900_; 
v_reuseFailAlloc_5900_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5900_, 0, v_array_5837_);
lean_ctor_set(v_reuseFailAlloc_5900_, 1, v___x_5853_);
lean_ctor_set(v_reuseFailAlloc_5900_, 2, v_stop_5839_);
v___x_5855_ = v_reuseFailAlloc_5900_;
goto v_reusejp_5854_;
}
v_reusejp_5854_:
{
uint8_t v___x_5856_; 
v___x_5856_ = lean_nat_dec_lt(v_start_5849_, v_stop_5850_);
if (v___x_5856_ == 0)
{
lean_object* v___x_5858_; 
lean_dec(v___x_5851_);
if (v_isShared_5836_ == 0)
{
lean_ctor_set(v___x_5835_, 1, v___x_5855_);
v___x_5858_ = v___x_5835_;
goto v_reusejp_5857_;
}
else
{
lean_object* v_reuseFailAlloc_5860_; 
v_reuseFailAlloc_5860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5860_, 0, v_fst_5833_);
lean_ctor_set(v_reuseFailAlloc_5860_, 1, v___x_5855_);
v___x_5858_ = v_reuseFailAlloc_5860_;
goto v_reusejp_5857_;
}
v_reusejp_5857_:
{
lean_object* v___x_5859_; 
v___x_5859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5859_, 0, v___x_5858_);
return v___x_5859_;
}
}
else
{
lean_object* v___x_5862_; uint8_t v_isShared_5863_; uint8_t v_isSharedCheck_5896_; 
lean_inc(v_stop_5850_);
lean_inc(v_start_5849_);
lean_inc_ref(v_array_5848_);
v_isSharedCheck_5896_ = !lean_is_exclusive(v_fst_5833_);
if (v_isSharedCheck_5896_ == 0)
{
lean_object* v_unused_5897_; lean_object* v_unused_5898_; lean_object* v_unused_5899_; 
v_unused_5897_ = lean_ctor_get(v_fst_5833_, 2);
lean_dec(v_unused_5897_);
v_unused_5898_ = lean_ctor_get(v_fst_5833_, 1);
lean_dec(v_unused_5898_);
v_unused_5899_ = lean_ctor_get(v_fst_5833_, 0);
lean_dec(v_unused_5899_);
v___x_5862_ = v_fst_5833_;
v_isShared_5863_ = v_isSharedCheck_5896_;
goto v_resetjp_5861_;
}
else
{
lean_dec(v_fst_5833_);
v___x_5862_ = lean_box(0);
v_isShared_5863_ = v_isSharedCheck_5896_;
goto v_resetjp_5861_;
}
v_resetjp_5861_:
{
lean_object* v___f_5864_; lean_object* v___x_5865_; lean_object* v_a_5866_; lean_object* v___x_5867_; lean_object* v___y_5868_; lean_object* v___x_5869_; lean_object* v___x_5870_; lean_object* v___x_5871_; lean_object* v___x_5872_; uint8_t v___x_5873_; lean_object* v___x_5874_; lean_object* v___x_5875_; lean_object* v___x_5876_; lean_object* v___x_5877_; 
v___f_5864_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__0));
v___x_5865_ = lean_box(0);
v_a_5866_ = lean_array_uget_borrowed(v_as_5821_, v_i_5823_);
v___x_5867_ = lean_array_fget_borrowed(v_array_5848_, v_start_5849_);
lean_inc(v___x_5867_);
v___y_5868_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3___boxed), 10, 3);
lean_closure_set(v___y_5868_, 0, v___x_5851_);
lean_closure_set(v___y_5868_, 1, v___x_5867_);
lean_closure_set(v___y_5868_, 2, v___x_5865_);
lean_inc(v_a_5866_);
v___x_5869_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withDeclName___boxed), 10, 3);
lean_closure_set(v___x_5869_, 0, lean_box(0));
lean_closure_set(v___x_5869_, 1, v_a_5866_);
lean_closure_set(v___x_5869_, 2, v___y_5868_);
v___x_5870_ = lean_box(0);
v___x_5871_ = lean_box(0);
v___x_5872_ = lean_box(1);
v___x_5873_ = 0;
v___x_5874_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__1));
v___x_5875_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_5875_, 0, v___x_5870_);
lean_ctor_set(v___x_5875_, 1, v___x_5871_);
lean_ctor_set(v___x_5875_, 2, v___x_5870_);
lean_ctor_set(v___x_5875_, 3, v___f_5864_);
lean_ctor_set(v___x_5875_, 4, v___x_5872_);
lean_ctor_set(v___x_5875_, 5, v___x_5872_);
lean_ctor_set(v___x_5875_, 6, v___x_5870_);
lean_ctor_set(v___x_5875_, 7, v___x_5874_);
lean_ctor_set_uint8(v___x_5875_, sizeof(void*)*8, v___x_5856_);
lean_ctor_set_uint8(v___x_5875_, sizeof(void*)*8 + 1, v___x_5856_);
lean_ctor_set_uint8(v___x_5875_, sizeof(void*)*8 + 2, v___x_5856_);
lean_ctor_set_uint8(v___x_5875_, sizeof(void*)*8 + 3, v___x_5856_);
lean_ctor_set_uint8(v___x_5875_, sizeof(void*)*8 + 4, v___x_5873_);
lean_ctor_set_uint8(v___x_5875_, sizeof(void*)*8 + 5, v___x_5873_);
lean_ctor_set_uint8(v___x_5875_, sizeof(void*)*8 + 6, v___x_5873_);
lean_ctor_set_uint8(v___x_5875_, sizeof(void*)*8 + 7, v___x_5873_);
lean_ctor_set_uint8(v___x_5875_, sizeof(void*)*8 + 8, v___x_5856_);
lean_ctor_set_uint8(v___x_5875_, sizeof(void*)*8 + 9, v___x_5873_);
lean_ctor_set_uint8(v___x_5875_, sizeof(void*)*8 + 10, v___x_5856_);
v___x_5876_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__2));
v___x_5877_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_5869_, v___x_5875_, v___x_5876_, v___y_5825_, v___y_5826_, v___y_5827_, v___y_5828_);
if (lean_obj_tag(v___x_5877_) == 0)
{
lean_object* v___x_5878_; lean_object* v___x_5880_; 
lean_dec_ref_known(v___x_5877_, 1);
v___x_5878_ = lean_nat_add(v_start_5849_, v___x_5852_);
lean_dec(v_start_5849_);
if (v_isShared_5863_ == 0)
{
lean_ctor_set(v___x_5862_, 1, v___x_5878_);
v___x_5880_ = v___x_5862_;
goto v_reusejp_5879_;
}
else
{
lean_object* v_reuseFailAlloc_5887_; 
v_reuseFailAlloc_5887_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5887_, 0, v_array_5848_);
lean_ctor_set(v_reuseFailAlloc_5887_, 1, v___x_5878_);
lean_ctor_set(v_reuseFailAlloc_5887_, 2, v_stop_5850_);
v___x_5880_ = v_reuseFailAlloc_5887_;
goto v_reusejp_5879_;
}
v_reusejp_5879_:
{
lean_object* v___x_5882_; 
if (v_isShared_5836_ == 0)
{
lean_ctor_set(v___x_5835_, 1, v___x_5855_);
lean_ctor_set(v___x_5835_, 0, v___x_5880_);
v___x_5882_ = v___x_5835_;
goto v_reusejp_5881_;
}
else
{
lean_object* v_reuseFailAlloc_5886_; 
v_reuseFailAlloc_5886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5886_, 0, v___x_5880_);
lean_ctor_set(v_reuseFailAlloc_5886_, 1, v___x_5855_);
v___x_5882_ = v_reuseFailAlloc_5886_;
goto v_reusejp_5881_;
}
v_reusejp_5881_:
{
size_t v___x_5883_; size_t v___x_5884_; 
v___x_5883_ = ((size_t)1ULL);
v___x_5884_ = lean_usize_add(v_i_5823_, v___x_5883_);
v_i_5823_ = v___x_5884_;
v_b_5824_ = v___x_5882_;
goto _start;
}
}
}
else
{
lean_object* v_a_5888_; lean_object* v___x_5890_; uint8_t v_isShared_5891_; uint8_t v_isSharedCheck_5895_; 
lean_del_object(v___x_5862_);
lean_dec_ref(v___x_5855_);
lean_dec(v_stop_5850_);
lean_dec(v_start_5849_);
lean_dec_ref(v_array_5848_);
lean_del_object(v___x_5835_);
v_a_5888_ = lean_ctor_get(v___x_5877_, 0);
v_isSharedCheck_5895_ = !lean_is_exclusive(v___x_5877_);
if (v_isSharedCheck_5895_ == 0)
{
v___x_5890_ = v___x_5877_;
v_isShared_5891_ = v_isSharedCheck_5895_;
goto v_resetjp_5889_;
}
else
{
lean_inc(v_a_5888_);
lean_dec(v___x_5877_);
v___x_5890_ = lean_box(0);
v_isShared_5891_ = v_isSharedCheck_5895_;
goto v_resetjp_5889_;
}
v_resetjp_5889_:
{
lean_object* v___x_5893_; 
if (v_isShared_5891_ == 0)
{
v___x_5893_ = v___x_5890_;
goto v_reusejp_5892_;
}
else
{
lean_object* v_reuseFailAlloc_5894_; 
v_reuseFailAlloc_5894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5894_, 0, v_a_5888_);
v___x_5893_ = v_reuseFailAlloc_5894_;
goto v_reusejp_5892_;
}
v_reusejp_5892_:
{
return v___x_5893_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___boxed(lean_object* v_as_5906_, lean_object* v_sz_5907_, lean_object* v_i_5908_, lean_object* v_b_5909_, lean_object* v___y_5910_, lean_object* v___y_5911_, lean_object* v___y_5912_, lean_object* v___y_5913_, lean_object* v___y_5914_){
_start:
{
size_t v_sz_boxed_5915_; size_t v_i_boxed_5916_; lean_object* v_res_5917_; 
v_sz_boxed_5915_ = lean_unbox_usize(v_sz_5907_);
lean_dec(v_sz_5907_);
v_i_boxed_5916_ = lean_unbox_usize(v_i_5908_);
lean_dec(v_i_5908_);
v_res_5917_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(v_as_5906_, v_sz_boxed_5915_, v_i_boxed_5916_, v_b_5909_, v___y_5910_, v___y_5911_, v___y_5912_, v___y_5913_);
lean_dec(v___y_5913_);
lean_dec_ref(v___y_5912_);
lean_dec(v___y_5911_);
lean_dec_ref(v___y_5910_);
lean_dec_ref(v_as_5906_);
return v_res_5917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___lam__0(lean_object* v_value_5918_, lean_object* v_decrTactics_5919_, lean_object* v_argsPacker_5920_, lean_object* v_funNames_5921_, lean_object* v___y_5922_, lean_object* v___y_5923_, lean_object* v___y_5924_, lean_object* v___y_5925_){
_start:
{
lean_object* v___x_5927_; 
lean_inc_ref(v_value_5918_);
v___x_5927_ = l_Lean_Meta_getMVarsNoDelayed(v_value_5918_, v___y_5922_, v___y_5923_, v___y_5924_, v___y_5925_);
if (lean_obj_tag(v___x_5927_) == 0)
{
lean_object* v_a_5928_; lean_object* v___x_5929_; 
v_a_5928_ = lean_ctor_get(v___x_5927_, 0);
lean_inc(v_a_5928_);
lean_dec_ref_known(v___x_5927_, 1);
v___x_5929_ = l_Lean_Elab_WF_assignSubsumed(v_a_5928_, v___y_5922_, v___y_5923_, v___y_5924_, v___y_5925_);
lean_dec(v_a_5928_);
if (lean_obj_tag(v___x_5929_) == 0)
{
lean_object* v_a_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; 
v_a_5930_ = lean_ctor_get(v___x_5929_, 0);
lean_inc(v_a_5930_);
lean_dec_ref_known(v___x_5929_, 1);
v___x_5931_ = lean_array_get_size(v_decrTactics_5919_);
v___x_5932_ = l_Lean_Elab_WF_groupGoalsByFunction(v_argsPacker_5920_, v___x_5931_, v_a_5930_, v___y_5922_, v___y_5923_, v___y_5924_, v___y_5925_);
lean_dec(v_a_5930_);
if (lean_obj_tag(v___x_5932_) == 0)
{
lean_object* v_a_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; size_t v_sz_5939_; size_t v___x_5940_; lean_object* v___x_5941_; 
v_a_5933_ = lean_ctor_get(v___x_5932_, 0);
lean_inc(v_a_5933_);
lean_dec_ref_known(v___x_5932_, 1);
v___x_5934_ = lean_unsigned_to_nat(0u);
v___x_5935_ = lean_array_get_size(v_a_5933_);
v___x_5936_ = l_Array_toSubarray___redArg(v_a_5933_, v___x_5934_, v___x_5935_);
v___x_5937_ = l_Array_toSubarray___redArg(v_decrTactics_5919_, v___x_5934_, v___x_5931_);
v___x_5938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5938_, 0, v___x_5936_);
lean_ctor_set(v___x_5938_, 1, v___x_5937_);
v_sz_5939_ = lean_array_size(v_funNames_5921_);
v___x_5940_ = ((size_t)0ULL);
v___x_5941_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(v_funNames_5921_, v_sz_5939_, v___x_5940_, v___x_5938_, v___y_5922_, v___y_5923_, v___y_5924_, v___y_5925_);
if (lean_obj_tag(v___x_5941_) == 0)
{
lean_object* v___x_5942_; 
lean_dec_ref_known(v___x_5941_, 1);
v___x_5942_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_value_5918_, v___y_5923_);
return v___x_5942_;
}
else
{
lean_object* v_a_5943_; lean_object* v___x_5945_; uint8_t v_isShared_5946_; uint8_t v_isSharedCheck_5950_; 
lean_dec_ref(v_value_5918_);
v_a_5943_ = lean_ctor_get(v___x_5941_, 0);
v_isSharedCheck_5950_ = !lean_is_exclusive(v___x_5941_);
if (v_isSharedCheck_5950_ == 0)
{
v___x_5945_ = v___x_5941_;
v_isShared_5946_ = v_isSharedCheck_5950_;
goto v_resetjp_5944_;
}
else
{
lean_inc(v_a_5943_);
lean_dec(v___x_5941_);
v___x_5945_ = lean_box(0);
v_isShared_5946_ = v_isSharedCheck_5950_;
goto v_resetjp_5944_;
}
v_resetjp_5944_:
{
lean_object* v___x_5948_; 
if (v_isShared_5946_ == 0)
{
v___x_5948_ = v___x_5945_;
goto v_reusejp_5947_;
}
else
{
lean_object* v_reuseFailAlloc_5949_; 
v_reuseFailAlloc_5949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5949_, 0, v_a_5943_);
v___x_5948_ = v_reuseFailAlloc_5949_;
goto v_reusejp_5947_;
}
v_reusejp_5947_:
{
return v___x_5948_;
}
}
}
}
else
{
lean_object* v_a_5951_; lean_object* v___x_5953_; uint8_t v_isShared_5954_; uint8_t v_isSharedCheck_5958_; 
lean_dec_ref(v_decrTactics_5919_);
lean_dec_ref(v_value_5918_);
v_a_5951_ = lean_ctor_get(v___x_5932_, 0);
v_isSharedCheck_5958_ = !lean_is_exclusive(v___x_5932_);
if (v_isSharedCheck_5958_ == 0)
{
v___x_5953_ = v___x_5932_;
v_isShared_5954_ = v_isSharedCheck_5958_;
goto v_resetjp_5952_;
}
else
{
lean_inc(v_a_5951_);
lean_dec(v___x_5932_);
v___x_5953_ = lean_box(0);
v_isShared_5954_ = v_isSharedCheck_5958_;
goto v_resetjp_5952_;
}
v_resetjp_5952_:
{
lean_object* v___x_5956_; 
if (v_isShared_5954_ == 0)
{
v___x_5956_ = v___x_5953_;
goto v_reusejp_5955_;
}
else
{
lean_object* v_reuseFailAlloc_5957_; 
v_reuseFailAlloc_5957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5957_, 0, v_a_5951_);
v___x_5956_ = v_reuseFailAlloc_5957_;
goto v_reusejp_5955_;
}
v_reusejp_5955_:
{
return v___x_5956_;
}
}
}
}
else
{
lean_object* v_a_5959_; lean_object* v___x_5961_; uint8_t v_isShared_5962_; uint8_t v_isSharedCheck_5966_; 
lean_dec_ref(v_decrTactics_5919_);
lean_dec_ref(v_value_5918_);
v_a_5959_ = lean_ctor_get(v___x_5929_, 0);
v_isSharedCheck_5966_ = !lean_is_exclusive(v___x_5929_);
if (v_isSharedCheck_5966_ == 0)
{
v___x_5961_ = v___x_5929_;
v_isShared_5962_ = v_isSharedCheck_5966_;
goto v_resetjp_5960_;
}
else
{
lean_inc(v_a_5959_);
lean_dec(v___x_5929_);
v___x_5961_ = lean_box(0);
v_isShared_5962_ = v_isSharedCheck_5966_;
goto v_resetjp_5960_;
}
v_resetjp_5960_:
{
lean_object* v___x_5964_; 
if (v_isShared_5962_ == 0)
{
v___x_5964_ = v___x_5961_;
goto v_reusejp_5963_;
}
else
{
lean_object* v_reuseFailAlloc_5965_; 
v_reuseFailAlloc_5965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5965_, 0, v_a_5959_);
v___x_5964_ = v_reuseFailAlloc_5965_;
goto v_reusejp_5963_;
}
v_reusejp_5963_:
{
return v___x_5964_;
}
}
}
}
else
{
lean_object* v_a_5967_; lean_object* v___x_5969_; uint8_t v_isShared_5970_; uint8_t v_isSharedCheck_5974_; 
lean_dec_ref(v_decrTactics_5919_);
lean_dec_ref(v_value_5918_);
v_a_5967_ = lean_ctor_get(v___x_5927_, 0);
v_isSharedCheck_5974_ = !lean_is_exclusive(v___x_5927_);
if (v_isSharedCheck_5974_ == 0)
{
v___x_5969_ = v___x_5927_;
v_isShared_5970_ = v_isSharedCheck_5974_;
goto v_resetjp_5968_;
}
else
{
lean_inc(v_a_5967_);
lean_dec(v___x_5927_);
v___x_5969_ = lean_box(0);
v_isShared_5970_ = v_isSharedCheck_5974_;
goto v_resetjp_5968_;
}
v_resetjp_5968_:
{
lean_object* v___x_5972_; 
if (v_isShared_5970_ == 0)
{
v___x_5972_ = v___x_5969_;
goto v_reusejp_5971_;
}
else
{
lean_object* v_reuseFailAlloc_5973_; 
v_reuseFailAlloc_5973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5973_, 0, v_a_5967_);
v___x_5972_ = v_reuseFailAlloc_5973_;
goto v_reusejp_5971_;
}
v_reusejp_5971_:
{
return v___x_5972_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___lam__0___boxed(lean_object* v_value_5975_, lean_object* v_decrTactics_5976_, lean_object* v_argsPacker_5977_, lean_object* v_funNames_5978_, lean_object* v___y_5979_, lean_object* v___y_5980_, lean_object* v___y_5981_, lean_object* v___y_5982_, lean_object* v___y_5983_){
_start:
{
lean_object* v_res_5984_; 
v_res_5984_ = l_Lean_Elab_WF_solveDecreasingGoals___lam__0(v_value_5975_, v_decrTactics_5976_, v_argsPacker_5977_, v_funNames_5978_, v___y_5979_, v___y_5980_, v___y_5981_, v___y_5982_);
lean_dec(v___y_5982_);
lean_dec_ref(v___y_5981_);
lean_dec(v___y_5980_);
lean_dec_ref(v___y_5979_);
lean_dec_ref(v_funNames_5978_);
lean_dec_ref(v_argsPacker_5977_);
return v_res_5984_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(lean_object* v___y_5985_, uint8_t v_isExporting_5986_, lean_object* v___x_5987_, lean_object* v___y_5988_, lean_object* v___x_5989_, lean_object* v_a_x3f_5990_){
_start:
{
lean_object* v___x_5992_; lean_object* v_env_5993_; lean_object* v_nextMacroScope_5994_; lean_object* v_ngen_5995_; lean_object* v_auxDeclNGen_5996_; lean_object* v_traceState_5997_; lean_object* v_messages_5998_; lean_object* v_infoState_5999_; lean_object* v_snapshotTasks_6000_; lean_object* v___x_6002_; uint8_t v_isShared_6003_; uint8_t v_isSharedCheck_6025_; 
v___x_5992_ = lean_st_ref_take(v___y_5985_);
v_env_5993_ = lean_ctor_get(v___x_5992_, 0);
v_nextMacroScope_5994_ = lean_ctor_get(v___x_5992_, 1);
v_ngen_5995_ = lean_ctor_get(v___x_5992_, 2);
v_auxDeclNGen_5996_ = lean_ctor_get(v___x_5992_, 3);
v_traceState_5997_ = lean_ctor_get(v___x_5992_, 4);
v_messages_5998_ = lean_ctor_get(v___x_5992_, 6);
v_infoState_5999_ = lean_ctor_get(v___x_5992_, 7);
v_snapshotTasks_6000_ = lean_ctor_get(v___x_5992_, 8);
v_isSharedCheck_6025_ = !lean_is_exclusive(v___x_5992_);
if (v_isSharedCheck_6025_ == 0)
{
lean_object* v_unused_6026_; 
v_unused_6026_ = lean_ctor_get(v___x_5992_, 5);
lean_dec(v_unused_6026_);
v___x_6002_ = v___x_5992_;
v_isShared_6003_ = v_isSharedCheck_6025_;
goto v_resetjp_6001_;
}
else
{
lean_inc(v_snapshotTasks_6000_);
lean_inc(v_infoState_5999_);
lean_inc(v_messages_5998_);
lean_inc(v_traceState_5997_);
lean_inc(v_auxDeclNGen_5996_);
lean_inc(v_ngen_5995_);
lean_inc(v_nextMacroScope_5994_);
lean_inc(v_env_5993_);
lean_dec(v___x_5992_);
v___x_6002_ = lean_box(0);
v_isShared_6003_ = v_isSharedCheck_6025_;
goto v_resetjp_6001_;
}
v_resetjp_6001_:
{
lean_object* v___x_6004_; lean_object* v___x_6006_; 
v___x_6004_ = l_Lean_Environment_setExporting(v_env_5993_, v_isExporting_5986_);
if (v_isShared_6003_ == 0)
{
lean_ctor_set(v___x_6002_, 5, v___x_5987_);
lean_ctor_set(v___x_6002_, 0, v___x_6004_);
v___x_6006_ = v___x_6002_;
goto v_reusejp_6005_;
}
else
{
lean_object* v_reuseFailAlloc_6024_; 
v_reuseFailAlloc_6024_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6024_, 0, v___x_6004_);
lean_ctor_set(v_reuseFailAlloc_6024_, 1, v_nextMacroScope_5994_);
lean_ctor_set(v_reuseFailAlloc_6024_, 2, v_ngen_5995_);
lean_ctor_set(v_reuseFailAlloc_6024_, 3, v_auxDeclNGen_5996_);
lean_ctor_set(v_reuseFailAlloc_6024_, 4, v_traceState_5997_);
lean_ctor_set(v_reuseFailAlloc_6024_, 5, v___x_5987_);
lean_ctor_set(v_reuseFailAlloc_6024_, 6, v_messages_5998_);
lean_ctor_set(v_reuseFailAlloc_6024_, 7, v_infoState_5999_);
lean_ctor_set(v_reuseFailAlloc_6024_, 8, v_snapshotTasks_6000_);
v___x_6006_ = v_reuseFailAlloc_6024_;
goto v_reusejp_6005_;
}
v_reusejp_6005_:
{
lean_object* v___x_6007_; lean_object* v___x_6008_; lean_object* v_mctx_6009_; lean_object* v_zetaDeltaFVarIds_6010_; lean_object* v_postponed_6011_; lean_object* v_diag_6012_; lean_object* v___x_6014_; uint8_t v_isShared_6015_; uint8_t v_isSharedCheck_6022_; 
v___x_6007_ = lean_st_ref_put(v___y_5985_, v___x_6006_);
v___x_6008_ = lean_st_ref_take(v___y_5988_);
v_mctx_6009_ = lean_ctor_get(v___x_6008_, 0);
v_zetaDeltaFVarIds_6010_ = lean_ctor_get(v___x_6008_, 2);
v_postponed_6011_ = lean_ctor_get(v___x_6008_, 3);
v_diag_6012_ = lean_ctor_get(v___x_6008_, 4);
v_isSharedCheck_6022_ = !lean_is_exclusive(v___x_6008_);
if (v_isSharedCheck_6022_ == 0)
{
lean_object* v_unused_6023_; 
v_unused_6023_ = lean_ctor_get(v___x_6008_, 1);
lean_dec(v_unused_6023_);
v___x_6014_ = v___x_6008_;
v_isShared_6015_ = v_isSharedCheck_6022_;
goto v_resetjp_6013_;
}
else
{
lean_inc(v_diag_6012_);
lean_inc(v_postponed_6011_);
lean_inc(v_zetaDeltaFVarIds_6010_);
lean_inc(v_mctx_6009_);
lean_dec(v___x_6008_);
v___x_6014_ = lean_box(0);
v_isShared_6015_ = v_isSharedCheck_6022_;
goto v_resetjp_6013_;
}
v_resetjp_6013_:
{
lean_object* v___x_6017_; 
if (v_isShared_6015_ == 0)
{
lean_ctor_set(v___x_6014_, 1, v___x_5989_);
v___x_6017_ = v___x_6014_;
goto v_reusejp_6016_;
}
else
{
lean_object* v_reuseFailAlloc_6021_; 
v_reuseFailAlloc_6021_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6021_, 0, v_mctx_6009_);
lean_ctor_set(v_reuseFailAlloc_6021_, 1, v___x_5989_);
lean_ctor_set(v_reuseFailAlloc_6021_, 2, v_zetaDeltaFVarIds_6010_);
lean_ctor_set(v_reuseFailAlloc_6021_, 3, v_postponed_6011_);
lean_ctor_set(v_reuseFailAlloc_6021_, 4, v_diag_6012_);
v___x_6017_ = v_reuseFailAlloc_6021_;
goto v_reusejp_6016_;
}
v_reusejp_6016_:
{
lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; 
v___x_6018_ = lean_st_ref_put(v___y_5988_, v___x_6017_);
v___x_6019_ = lean_box(0);
v___x_6020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6020_, 0, v___x_6019_);
return v___x_6020_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0___boxed(lean_object* v___y_6027_, lean_object* v_isExporting_6028_, lean_object* v___x_6029_, lean_object* v___y_6030_, lean_object* v___x_6031_, lean_object* v_a_x3f_6032_, lean_object* v___y_6033_){
_start:
{
uint8_t v_isExporting_boxed_6034_; lean_object* v_res_6035_; 
v_isExporting_boxed_6034_ = lean_unbox(v_isExporting_6028_);
v_res_6035_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6027_, v_isExporting_boxed_6034_, v___x_6029_, v___y_6030_, v___x_6031_, v_a_x3f_6032_);
lean_dec(v_a_x3f_6032_);
lean_dec(v___y_6030_);
lean_dec(v___y_6027_);
return v_res_6035_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_6036_; 
v___x_6036_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_6036_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_6037_; lean_object* v___x_6038_; 
v___x_6037_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0);
v___x_6038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6038_, 0, v___x_6037_);
return v___x_6038_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_6039_; lean_object* v___x_6040_; 
v___x_6039_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1);
v___x_6040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6040_, 0, v___x_6039_);
lean_ctor_set(v___x_6040_, 1, v___x_6039_);
return v___x_6040_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_6041_; lean_object* v___x_6042_; 
v___x_6041_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1);
v___x_6042_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6042_, 0, v___x_6041_);
lean_ctor_set(v___x_6042_, 1, v___x_6041_);
lean_ctor_set(v___x_6042_, 2, v___x_6041_);
lean_ctor_set(v___x_6042_, 3, v___x_6041_);
lean_ctor_set(v___x_6042_, 4, v___x_6041_);
lean_ctor_set(v___x_6042_, 5, v___x_6041_);
return v___x_6042_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(lean_object* v_x_6043_, uint8_t v_isExporting_6044_, lean_object* v___y_6045_, lean_object* v___y_6046_, lean_object* v___y_6047_, lean_object* v___y_6048_){
_start:
{
lean_object* v___x_6050_; lean_object* v_env_6051_; lean_object* v___x_6052_; uint8_t v_isModule_6053_; 
v___x_6050_ = lean_st_ref_get(v___y_6048_);
v_env_6051_ = lean_ctor_get(v___x_6050_, 0);
lean_inc_ref(v_env_6051_);
lean_dec(v___x_6050_);
v___x_6052_ = l_Lean_Environment_header(v_env_6051_);
v_isModule_6053_ = lean_ctor_get_uint8(v___x_6052_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_6052_);
if (v_isModule_6053_ == 0)
{
lean_object* v___x_6054_; 
lean_dec_ref(v_env_6051_);
lean_inc(v___y_6048_);
lean_inc_ref(v___y_6047_);
lean_inc(v___y_6046_);
lean_inc_ref(v___y_6045_);
v___x_6054_ = lean_apply_5(v_x_6043_, v___y_6045_, v___y_6046_, v___y_6047_, v___y_6048_, lean_box(0));
return v___x_6054_;
}
else
{
uint8_t v_isExporting_6055_; 
v_isExporting_6055_ = lean_ctor_get_uint8(v_env_6051_, sizeof(void*)*8);
lean_dec_ref(v_env_6051_);
if (v_isExporting_6044_ == 0)
{
if (v_isExporting_6055_ == 0)
{
lean_object* v___x_6121_; 
lean_inc(v___y_6048_);
lean_inc_ref(v___y_6047_);
lean_inc(v___y_6046_);
lean_inc_ref(v___y_6045_);
v___x_6121_ = lean_apply_5(v_x_6043_, v___y_6045_, v___y_6046_, v___y_6047_, v___y_6048_, lean_box(0));
return v___x_6121_;
}
else
{
goto v___jp_6056_;
}
}
else
{
if (v_isExporting_6055_ == 0)
{
goto v___jp_6056_;
}
else
{
lean_object* v___x_6122_; 
lean_inc(v___y_6048_);
lean_inc_ref(v___y_6047_);
lean_inc(v___y_6046_);
lean_inc_ref(v___y_6045_);
v___x_6122_ = lean_apply_5(v_x_6043_, v___y_6045_, v___y_6046_, v___y_6047_, v___y_6048_, lean_box(0));
return v___x_6122_;
}
}
v___jp_6056_:
{
lean_object* v___x_6057_; lean_object* v_env_6058_; lean_object* v_nextMacroScope_6059_; lean_object* v_ngen_6060_; lean_object* v_auxDeclNGen_6061_; lean_object* v_traceState_6062_; lean_object* v_messages_6063_; lean_object* v_infoState_6064_; lean_object* v_snapshotTasks_6065_; lean_object* v___x_6067_; uint8_t v_isShared_6068_; uint8_t v_isSharedCheck_6119_; 
v___x_6057_ = lean_st_ref_take(v___y_6048_);
v_env_6058_ = lean_ctor_get(v___x_6057_, 0);
v_nextMacroScope_6059_ = lean_ctor_get(v___x_6057_, 1);
v_ngen_6060_ = lean_ctor_get(v___x_6057_, 2);
v_auxDeclNGen_6061_ = lean_ctor_get(v___x_6057_, 3);
v_traceState_6062_ = lean_ctor_get(v___x_6057_, 4);
v_messages_6063_ = lean_ctor_get(v___x_6057_, 6);
v_infoState_6064_ = lean_ctor_get(v___x_6057_, 7);
v_snapshotTasks_6065_ = lean_ctor_get(v___x_6057_, 8);
v_isSharedCheck_6119_ = !lean_is_exclusive(v___x_6057_);
if (v_isSharedCheck_6119_ == 0)
{
lean_object* v_unused_6120_; 
v_unused_6120_ = lean_ctor_get(v___x_6057_, 5);
lean_dec(v_unused_6120_);
v___x_6067_ = v___x_6057_;
v_isShared_6068_ = v_isSharedCheck_6119_;
goto v_resetjp_6066_;
}
else
{
lean_inc(v_snapshotTasks_6065_);
lean_inc(v_infoState_6064_);
lean_inc(v_messages_6063_);
lean_inc(v_traceState_6062_);
lean_inc(v_auxDeclNGen_6061_);
lean_inc(v_ngen_6060_);
lean_inc(v_nextMacroScope_6059_);
lean_inc(v_env_6058_);
lean_dec(v___x_6057_);
v___x_6067_ = lean_box(0);
v_isShared_6068_ = v_isSharedCheck_6119_;
goto v_resetjp_6066_;
}
v_resetjp_6066_:
{
lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6072_; 
v___x_6069_ = l_Lean_Environment_setExporting(v_env_6058_, v_isExporting_6044_);
v___x_6070_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2);
if (v_isShared_6068_ == 0)
{
lean_ctor_set(v___x_6067_, 5, v___x_6070_);
lean_ctor_set(v___x_6067_, 0, v___x_6069_);
v___x_6072_ = v___x_6067_;
goto v_reusejp_6071_;
}
else
{
lean_object* v_reuseFailAlloc_6118_; 
v_reuseFailAlloc_6118_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6118_, 0, v___x_6069_);
lean_ctor_set(v_reuseFailAlloc_6118_, 1, v_nextMacroScope_6059_);
lean_ctor_set(v_reuseFailAlloc_6118_, 2, v_ngen_6060_);
lean_ctor_set(v_reuseFailAlloc_6118_, 3, v_auxDeclNGen_6061_);
lean_ctor_set(v_reuseFailAlloc_6118_, 4, v_traceState_6062_);
lean_ctor_set(v_reuseFailAlloc_6118_, 5, v___x_6070_);
lean_ctor_set(v_reuseFailAlloc_6118_, 6, v_messages_6063_);
lean_ctor_set(v_reuseFailAlloc_6118_, 7, v_infoState_6064_);
lean_ctor_set(v_reuseFailAlloc_6118_, 8, v_snapshotTasks_6065_);
v___x_6072_ = v_reuseFailAlloc_6118_;
goto v_reusejp_6071_;
}
v_reusejp_6071_:
{
lean_object* v___x_6073_; lean_object* v___x_6074_; lean_object* v_mctx_6075_; lean_object* v_zetaDeltaFVarIds_6076_; lean_object* v_postponed_6077_; lean_object* v_diag_6078_; lean_object* v___x_6080_; uint8_t v_isShared_6081_; uint8_t v_isSharedCheck_6116_; 
v___x_6073_ = lean_st_ref_put(v___y_6048_, v___x_6072_);
v___x_6074_ = lean_st_ref_take(v___y_6046_);
v_mctx_6075_ = lean_ctor_get(v___x_6074_, 0);
v_zetaDeltaFVarIds_6076_ = lean_ctor_get(v___x_6074_, 2);
v_postponed_6077_ = lean_ctor_get(v___x_6074_, 3);
v_diag_6078_ = lean_ctor_get(v___x_6074_, 4);
v_isSharedCheck_6116_ = !lean_is_exclusive(v___x_6074_);
if (v_isSharedCheck_6116_ == 0)
{
lean_object* v_unused_6117_; 
v_unused_6117_ = lean_ctor_get(v___x_6074_, 1);
lean_dec(v_unused_6117_);
v___x_6080_ = v___x_6074_;
v_isShared_6081_ = v_isSharedCheck_6116_;
goto v_resetjp_6079_;
}
else
{
lean_inc(v_diag_6078_);
lean_inc(v_postponed_6077_);
lean_inc(v_zetaDeltaFVarIds_6076_);
lean_inc(v_mctx_6075_);
lean_dec(v___x_6074_);
v___x_6080_ = lean_box(0);
v_isShared_6081_ = v_isSharedCheck_6116_;
goto v_resetjp_6079_;
}
v_resetjp_6079_:
{
lean_object* v___x_6082_; lean_object* v___x_6084_; 
v___x_6082_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3);
if (v_isShared_6081_ == 0)
{
lean_ctor_set(v___x_6080_, 1, v___x_6082_);
v___x_6084_ = v___x_6080_;
goto v_reusejp_6083_;
}
else
{
lean_object* v_reuseFailAlloc_6115_; 
v_reuseFailAlloc_6115_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6115_, 0, v_mctx_6075_);
lean_ctor_set(v_reuseFailAlloc_6115_, 1, v___x_6082_);
lean_ctor_set(v_reuseFailAlloc_6115_, 2, v_zetaDeltaFVarIds_6076_);
lean_ctor_set(v_reuseFailAlloc_6115_, 3, v_postponed_6077_);
lean_ctor_set(v_reuseFailAlloc_6115_, 4, v_diag_6078_);
v___x_6084_ = v_reuseFailAlloc_6115_;
goto v_reusejp_6083_;
}
v_reusejp_6083_:
{
lean_object* v___x_6085_; lean_object* v_r_6086_; 
v___x_6085_ = lean_st_ref_put(v___y_6046_, v___x_6084_);
lean_inc(v___y_6048_);
lean_inc_ref(v___y_6047_);
lean_inc(v___y_6046_);
lean_inc_ref(v___y_6045_);
v_r_6086_ = lean_apply_5(v_x_6043_, v___y_6045_, v___y_6046_, v___y_6047_, v___y_6048_, lean_box(0));
if (lean_obj_tag(v_r_6086_) == 0)
{
lean_object* v_a_6087_; lean_object* v___x_6089_; uint8_t v_isShared_6090_; uint8_t v_isSharedCheck_6103_; 
v_a_6087_ = lean_ctor_get(v_r_6086_, 0);
v_isSharedCheck_6103_ = !lean_is_exclusive(v_r_6086_);
if (v_isSharedCheck_6103_ == 0)
{
v___x_6089_ = v_r_6086_;
v_isShared_6090_ = v_isSharedCheck_6103_;
goto v_resetjp_6088_;
}
else
{
lean_inc(v_a_6087_);
lean_dec(v_r_6086_);
v___x_6089_ = lean_box(0);
v_isShared_6090_ = v_isSharedCheck_6103_;
goto v_resetjp_6088_;
}
v_resetjp_6088_:
{
lean_object* v___x_6092_; 
lean_inc(v_a_6087_);
if (v_isShared_6090_ == 0)
{
lean_ctor_set_tag(v___x_6089_, 1);
v___x_6092_ = v___x_6089_;
goto v_reusejp_6091_;
}
else
{
lean_object* v_reuseFailAlloc_6102_; 
v_reuseFailAlloc_6102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6102_, 0, v_a_6087_);
v___x_6092_ = v_reuseFailAlloc_6102_;
goto v_reusejp_6091_;
}
v_reusejp_6091_:
{
lean_object* v___x_6093_; lean_object* v___x_6095_; uint8_t v_isShared_6096_; uint8_t v_isSharedCheck_6100_; 
v___x_6093_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6048_, v_isExporting_6055_, v___x_6070_, v___y_6046_, v___x_6082_, v___x_6092_);
lean_dec_ref(v___x_6092_);
v_isSharedCheck_6100_ = !lean_is_exclusive(v___x_6093_);
if (v_isSharedCheck_6100_ == 0)
{
lean_object* v_unused_6101_; 
v_unused_6101_ = lean_ctor_get(v___x_6093_, 0);
lean_dec(v_unused_6101_);
v___x_6095_ = v___x_6093_;
v_isShared_6096_ = v_isSharedCheck_6100_;
goto v_resetjp_6094_;
}
else
{
lean_dec(v___x_6093_);
v___x_6095_ = lean_box(0);
v_isShared_6096_ = v_isSharedCheck_6100_;
goto v_resetjp_6094_;
}
v_resetjp_6094_:
{
lean_object* v___x_6098_; 
if (v_isShared_6096_ == 0)
{
lean_ctor_set(v___x_6095_, 0, v_a_6087_);
v___x_6098_ = v___x_6095_;
goto v_reusejp_6097_;
}
else
{
lean_object* v_reuseFailAlloc_6099_; 
v_reuseFailAlloc_6099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6099_, 0, v_a_6087_);
v___x_6098_ = v_reuseFailAlloc_6099_;
goto v_reusejp_6097_;
}
v_reusejp_6097_:
{
return v___x_6098_;
}
}
}
}
}
else
{
lean_object* v_a_6104_; lean_object* v___x_6105_; lean_object* v___x_6106_; lean_object* v___x_6108_; uint8_t v_isShared_6109_; uint8_t v_isSharedCheck_6113_; 
v_a_6104_ = lean_ctor_get(v_r_6086_, 0);
lean_inc(v_a_6104_);
lean_dec_ref_known(v_r_6086_, 1);
v___x_6105_ = lean_box(0);
v___x_6106_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6048_, v_isExporting_6055_, v___x_6070_, v___y_6046_, v___x_6082_, v___x_6105_);
v_isSharedCheck_6113_ = !lean_is_exclusive(v___x_6106_);
if (v_isSharedCheck_6113_ == 0)
{
lean_object* v_unused_6114_; 
v_unused_6114_ = lean_ctor_get(v___x_6106_, 0);
lean_dec(v_unused_6114_);
v___x_6108_ = v___x_6106_;
v_isShared_6109_ = v_isSharedCheck_6113_;
goto v_resetjp_6107_;
}
else
{
lean_dec(v___x_6106_);
v___x_6108_ = lean_box(0);
v_isShared_6109_ = v_isSharedCheck_6113_;
goto v_resetjp_6107_;
}
v_resetjp_6107_:
{
lean_object* v___x_6111_; 
if (v_isShared_6109_ == 0)
{
lean_ctor_set_tag(v___x_6108_, 1);
lean_ctor_set(v___x_6108_, 0, v_a_6104_);
v___x_6111_ = v___x_6108_;
goto v_reusejp_6110_;
}
else
{
lean_object* v_reuseFailAlloc_6112_; 
v_reuseFailAlloc_6112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6112_, 0, v_a_6104_);
v___x_6111_ = v_reuseFailAlloc_6112_;
goto v_reusejp_6110_;
}
v_reusejp_6110_:
{
return v___x_6111_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___boxed(lean_object* v_x_6123_, lean_object* v_isExporting_6124_, lean_object* v___y_6125_, lean_object* v___y_6126_, lean_object* v___y_6127_, lean_object* v___y_6128_, lean_object* v___y_6129_){
_start:
{
uint8_t v_isExporting_boxed_6130_; lean_object* v_res_6131_; 
v_isExporting_boxed_6130_ = lean_unbox(v_isExporting_6124_);
v_res_6131_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6123_, v_isExporting_boxed_6130_, v___y_6125_, v___y_6126_, v___y_6127_, v___y_6128_);
lean_dec(v___y_6128_);
lean_dec_ref(v___y_6127_);
lean_dec(v___y_6126_);
lean_dec_ref(v___y_6125_);
return v_res_6131_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(lean_object* v_x_6132_, uint8_t v_when_6133_, lean_object* v___y_6134_, lean_object* v___y_6135_, lean_object* v___y_6136_, lean_object* v___y_6137_){
_start:
{
if (v_when_6133_ == 0)
{
lean_object* v___x_6139_; 
lean_inc(v___y_6137_);
lean_inc_ref(v___y_6136_);
lean_inc(v___y_6135_);
lean_inc_ref(v___y_6134_);
v___x_6139_ = lean_apply_5(v_x_6132_, v___y_6134_, v___y_6135_, v___y_6136_, v___y_6137_, lean_box(0));
return v___x_6139_;
}
else
{
uint8_t v___x_6140_; lean_object* v___x_6141_; 
v___x_6140_ = 0;
v___x_6141_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6132_, v___x_6140_, v___y_6134_, v___y_6135_, v___y_6136_, v___y_6137_);
return v___x_6141_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg___boxed(lean_object* v_x_6142_, lean_object* v_when_6143_, lean_object* v___y_6144_, lean_object* v___y_6145_, lean_object* v___y_6146_, lean_object* v___y_6147_, lean_object* v___y_6148_){
_start:
{
uint8_t v_when_boxed_6149_; lean_object* v_res_6150_; 
v_when_boxed_6149_ = lean_unbox(v_when_6143_);
v_res_6150_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v_x_6142_, v_when_boxed_6149_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_);
lean_dec(v___y_6147_);
lean_dec_ref(v___y_6146_);
lean_dec(v___y_6145_);
lean_dec_ref(v___y_6144_);
return v_res_6150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals(lean_object* v_funNames_6151_, lean_object* v_argsPacker_6152_, lean_object* v_decrTactics_6153_, lean_object* v_value_6154_, lean_object* v_a_6155_, lean_object* v_a_6156_, lean_object* v_a_6157_, lean_object* v_a_6158_){
_start:
{
lean_object* v___f_6160_; uint8_t v___x_6161_; lean_object* v___x_6162_; 
v___f_6160_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_solveDecreasingGoals___lam__0___boxed), 9, 4);
lean_closure_set(v___f_6160_, 0, v_value_6154_);
lean_closure_set(v___f_6160_, 1, v_decrTactics_6153_);
lean_closure_set(v___f_6160_, 2, v_argsPacker_6152_);
lean_closure_set(v___f_6160_, 3, v_funNames_6151_);
v___x_6161_ = 1;
v___x_6162_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v___f_6160_, v___x_6161_, v_a_6155_, v_a_6156_, v_a_6157_, v_a_6158_);
return v___x_6162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___boxed(lean_object* v_funNames_6163_, lean_object* v_argsPacker_6164_, lean_object* v_decrTactics_6165_, lean_object* v_value_6166_, lean_object* v_a_6167_, lean_object* v_a_6168_, lean_object* v_a_6169_, lean_object* v_a_6170_, lean_object* v_a_6171_){
_start:
{
lean_object* v_res_6172_; 
v_res_6172_ = l_Lean_Elab_WF_solveDecreasingGoals(v_funNames_6163_, v_argsPacker_6164_, v_decrTactics_6165_, v_value_6166_, v_a_6167_, v_a_6168_, v_a_6169_, v_a_6170_);
lean_dec(v_a_6170_);
lean_dec_ref(v_a_6169_);
lean_dec(v_a_6168_);
lean_dec_ref(v_a_6167_);
return v_res_6172_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1(lean_object* v_00_u03b1_6173_, lean_object* v_msg_6174_, lean_object* v___y_6175_, lean_object* v___y_6176_, lean_object* v___y_6177_, lean_object* v___y_6178_, lean_object* v___y_6179_, lean_object* v___y_6180_){
_start:
{
lean_object* v___x_6182_; 
v___x_6182_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v_msg_6174_, v___y_6175_, v___y_6176_, v___y_6177_, v___y_6178_, v___y_6179_, v___y_6180_);
return v___x_6182_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___boxed(lean_object* v_00_u03b1_6183_, lean_object* v_msg_6184_, lean_object* v___y_6185_, lean_object* v___y_6186_, lean_object* v___y_6187_, lean_object* v___y_6188_, lean_object* v___y_6189_, lean_object* v___y_6190_, lean_object* v___y_6191_){
_start:
{
lean_object* v_res_6192_; 
v_res_6192_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1(v_00_u03b1_6183_, v_msg_6184_, v___y_6185_, v___y_6186_, v___y_6187_, v___y_6188_, v___y_6189_, v___y_6190_);
lean_dec(v___y_6190_);
lean_dec_ref(v___y_6189_);
lean_dec(v___y_6188_);
lean_dec_ref(v___y_6187_);
lean_dec(v___y_6186_);
lean_dec_ref(v___y_6185_);
return v_res_6192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4(lean_object* v___y_6193_, lean_object* v___y_6194_, lean_object* v___y_6195_, lean_object* v___y_6196_, lean_object* v___y_6197_, lean_object* v___y_6198_, lean_object* v___y_6199_, lean_object* v___y_6200_){
_start:
{
lean_object* v___x_6202_; 
v___x_6202_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_6200_);
return v___x_6202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___boxed(lean_object* v___y_6203_, lean_object* v___y_6204_, lean_object* v___y_6205_, lean_object* v___y_6206_, lean_object* v___y_6207_, lean_object* v___y_6208_, lean_object* v___y_6209_, lean_object* v___y_6210_, lean_object* v___y_6211_){
_start:
{
lean_object* v_res_6212_; 
v_res_6212_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4(v___y_6203_, v___y_6204_, v___y_6205_, v___y_6206_, v___y_6207_, v___y_6208_, v___y_6209_, v___y_6210_);
lean_dec(v___y_6210_);
lean_dec_ref(v___y_6209_);
lean_dec(v___y_6208_);
lean_dec_ref(v___y_6207_);
lean_dec(v___y_6206_);
lean_dec_ref(v___y_6205_);
lean_dec(v___y_6204_);
lean_dec_ref(v___y_6203_);
return v_res_6212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3(lean_object* v_00_u03b1_6213_, lean_object* v_x_6214_, lean_object* v_mkInfoTree_6215_, lean_object* v___y_6216_, lean_object* v___y_6217_, lean_object* v___y_6218_, lean_object* v___y_6219_, lean_object* v___y_6220_, lean_object* v___y_6221_, lean_object* v___y_6222_, lean_object* v___y_6223_){
_start:
{
lean_object* v___x_6225_; 
v___x_6225_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v_x_6214_, v_mkInfoTree_6215_, v___y_6216_, v___y_6217_, v___y_6218_, v___y_6219_, v___y_6220_, v___y_6221_, v___y_6222_, v___y_6223_);
return v___x_6225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___boxed(lean_object* v_00_u03b1_6226_, lean_object* v_x_6227_, lean_object* v_mkInfoTree_6228_, lean_object* v___y_6229_, lean_object* v___y_6230_, lean_object* v___y_6231_, lean_object* v___y_6232_, lean_object* v___y_6233_, lean_object* v___y_6234_, lean_object* v___y_6235_, lean_object* v___y_6236_, lean_object* v___y_6237_){
_start:
{
lean_object* v_res_6238_; 
v_res_6238_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3(v_00_u03b1_6226_, v_x_6227_, v_mkInfoTree_6228_, v___y_6229_, v___y_6230_, v___y_6231_, v___y_6232_, v___y_6233_, v___y_6234_, v___y_6235_, v___y_6236_);
lean_dec(v___y_6236_);
lean_dec_ref(v___y_6235_);
lean_dec(v___y_6234_);
lean_dec_ref(v___y_6233_);
lean_dec(v___y_6232_);
lean_dec_ref(v___y_6231_);
lean_dec(v___y_6230_);
lean_dec_ref(v___y_6229_);
return v_res_6238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5(lean_object* v_as_6239_, size_t v_i_6240_, size_t v_stop_6241_, lean_object* v_b_6242_, lean_object* v___y_6243_, lean_object* v___y_6244_, lean_object* v___y_6245_, lean_object* v___y_6246_, lean_object* v___y_6247_, lean_object* v___y_6248_){
_start:
{
lean_object* v___x_6250_; 
v___x_6250_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v_as_6239_, v_i_6240_, v_stop_6241_, v_b_6242_, v___y_6245_, v___y_6246_, v___y_6247_, v___y_6248_);
return v___x_6250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___boxed(lean_object* v_as_6251_, lean_object* v_i_6252_, lean_object* v_stop_6253_, lean_object* v_b_6254_, lean_object* v___y_6255_, lean_object* v___y_6256_, lean_object* v___y_6257_, lean_object* v___y_6258_, lean_object* v___y_6259_, lean_object* v___y_6260_, lean_object* v___y_6261_){
_start:
{
size_t v_i_boxed_6262_; size_t v_stop_boxed_6263_; lean_object* v_res_6264_; 
v_i_boxed_6262_ = lean_unbox_usize(v_i_6252_);
lean_dec(v_i_6252_);
v_stop_boxed_6263_ = lean_unbox_usize(v_stop_6253_);
lean_dec(v_stop_6253_);
v_res_6264_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5(v_as_6251_, v_i_boxed_6262_, v_stop_boxed_6263_, v_b_6254_, v___y_6255_, v___y_6256_, v___y_6257_, v___y_6258_, v___y_6259_, v___y_6260_);
lean_dec(v___y_6260_);
lean_dec_ref(v___y_6259_);
lean_dec(v___y_6258_);
lean_dec_ref(v___y_6257_);
lean_dec(v___y_6256_);
lean_dec_ref(v___y_6255_);
lean_dec_ref(v_as_6251_);
return v_res_6264_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10(lean_object* v_00_u03b1_6265_, lean_object* v_x_6266_, uint8_t v_isExporting_6267_, lean_object* v___y_6268_, lean_object* v___y_6269_, lean_object* v___y_6270_, lean_object* v___y_6271_){
_start:
{
lean_object* v___x_6273_; 
v___x_6273_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6266_, v_isExporting_6267_, v___y_6268_, v___y_6269_, v___y_6270_, v___y_6271_);
return v___x_6273_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___boxed(lean_object* v_00_u03b1_6274_, lean_object* v_x_6275_, lean_object* v_isExporting_6276_, lean_object* v___y_6277_, lean_object* v___y_6278_, lean_object* v___y_6279_, lean_object* v___y_6280_, lean_object* v___y_6281_){
_start:
{
uint8_t v_isExporting_boxed_6282_; lean_object* v_res_6283_; 
v_isExporting_boxed_6282_ = lean_unbox(v_isExporting_6276_);
v_res_6283_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10(v_00_u03b1_6274_, v_x_6275_, v_isExporting_boxed_6282_, v___y_6277_, v___y_6278_, v___y_6279_, v___y_6280_);
lean_dec(v___y_6280_);
lean_dec_ref(v___y_6279_);
lean_dec(v___y_6278_);
lean_dec_ref(v___y_6277_);
return v_res_6283_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8(lean_object* v_00_u03b1_6284_, lean_object* v_x_6285_, uint8_t v_when_6286_, lean_object* v___y_6287_, lean_object* v___y_6288_, lean_object* v___y_6289_, lean_object* v___y_6290_){
_start:
{
lean_object* v___x_6292_; 
v___x_6292_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v_x_6285_, v_when_6286_, v___y_6287_, v___y_6288_, v___y_6289_, v___y_6290_);
return v___x_6292_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___boxed(lean_object* v_00_u03b1_6293_, lean_object* v_x_6294_, lean_object* v_when_6295_, lean_object* v___y_6296_, lean_object* v___y_6297_, lean_object* v___y_6298_, lean_object* v___y_6299_, lean_object* v___y_6300_){
_start:
{
uint8_t v_when_boxed_6301_; lean_object* v_res_6302_; 
v_when_boxed_6301_ = lean_unbox(v_when_6295_);
v_res_6302_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8(v_00_u03b1_6293_, v_x_6294_, v_when_boxed_6301_, v___y_6296_, v___y_6297_, v___y_6298_, v___y_6299_);
lean_dec(v___y_6299_);
lean_dec_ref(v___y_6298_);
lean_dec(v___y_6297_);
lean_dec_ref(v___y_6296_);
return v_res_6302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1(lean_object* v_msgData_6303_, lean_object* v_macroStack_6304_, lean_object* v___y_6305_, lean_object* v___y_6306_, lean_object* v___y_6307_, lean_object* v___y_6308_, lean_object* v___y_6309_, lean_object* v___y_6310_){
_start:
{
lean_object* v___x_6312_; 
v___x_6312_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_msgData_6303_, v_macroStack_6304_, v___y_6309_);
return v___x_6312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___boxed(lean_object* v_msgData_6313_, lean_object* v_macroStack_6314_, lean_object* v___y_6315_, lean_object* v___y_6316_, lean_object* v___y_6317_, lean_object* v___y_6318_, lean_object* v___y_6319_, lean_object* v___y_6320_, lean_object* v___y_6321_){
_start:
{
lean_object* v_res_6322_; 
v_res_6322_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1(v_msgData_6313_, v_macroStack_6314_, v___y_6315_, v___y_6316_, v___y_6317_, v___y_6318_, v___y_6319_, v___y_6320_);
lean_dec(v___y_6320_);
lean_dec_ref(v___y_6319_);
lean_dec(v___y_6318_);
lean_dec_ref(v___y_6317_);
lean_dec(v___y_6316_);
lean_dec_ref(v___y_6315_);
return v_res_6322_;
}
}
static lean_object* _init_l_Lean_Elab_WF_isNatLtWF___closed__4(void){
_start:
{
lean_object* v___x_6329_; lean_object* v___x_6330_; lean_object* v___x_6331_; 
v___x_6329_ = lean_box(0);
v___x_6330_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__3));
v___x_6331_ = l_Lean_mkConst(v___x_6330_, v___x_6329_);
return v___x_6331_;
}
}
static lean_object* _init_l_Lean_Elab_WF_isNatLtWF___closed__7(void){
_start:
{
lean_object* v___x_6336_; lean_object* v___x_6337_; lean_object* v___x_6338_; 
v___x_6336_ = lean_box(0);
v___x_6337_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__6));
v___x_6338_ = l_Lean_mkConst(v___x_6337_, v___x_6336_);
return v___x_6338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isNatLtWF(lean_object* v_wfRel_6339_, lean_object* v_a_6340_, lean_object* v_a_6341_, lean_object* v_a_6342_, lean_object* v_a_6343_){
_start:
{
lean_object* v___x_6345_; 
v___x_6345_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_wfRel_6339_, v_a_6341_);
if (lean_obj_tag(v___x_6345_) == 0)
{
lean_object* v_a_6346_; lean_object* v___x_6348_; uint8_t v_isShared_6349_; uint8_t v_isSharedCheck_6413_; 
v_a_6346_ = lean_ctor_get(v___x_6345_, 0);
v_isSharedCheck_6413_ = !lean_is_exclusive(v___x_6345_);
if (v_isSharedCheck_6413_ == 0)
{
v___x_6348_ = v___x_6345_;
v_isShared_6349_ = v_isSharedCheck_6413_;
goto v_resetjp_6347_;
}
else
{
lean_inc(v_a_6346_);
lean_dec(v___x_6345_);
v___x_6348_ = lean_box(0);
v_isShared_6349_ = v_isSharedCheck_6413_;
goto v_resetjp_6347_;
}
v_resetjp_6347_:
{
lean_object* v___x_6355_; uint8_t v___x_6356_; 
v___x_6355_ = l_Lean_Expr_cleanupAnnotations(v_a_6346_);
v___x_6356_ = l_Lean_Expr_isApp(v___x_6355_);
if (v___x_6356_ == 0)
{
lean_dec_ref(v___x_6355_);
goto v___jp_6350_;
}
else
{
lean_object* v_arg_6357_; lean_object* v___x_6358_; uint8_t v___x_6359_; 
v_arg_6357_ = lean_ctor_get(v___x_6355_, 1);
lean_inc_ref(v_arg_6357_);
v___x_6358_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6355_);
v___x_6359_ = l_Lean_Expr_isApp(v___x_6358_);
if (v___x_6359_ == 0)
{
lean_dec_ref(v___x_6358_);
lean_dec_ref(v_arg_6357_);
goto v___jp_6350_;
}
else
{
lean_object* v_arg_6360_; lean_object* v___x_6361_; uint8_t v___x_6362_; 
v_arg_6360_ = lean_ctor_get(v___x_6358_, 1);
lean_inc_ref(v_arg_6360_);
v___x_6361_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6358_);
v___x_6362_ = l_Lean_Expr_isApp(v___x_6361_);
if (v___x_6362_ == 0)
{
lean_dec_ref(v___x_6361_);
lean_dec_ref(v_arg_6360_);
lean_dec_ref(v_arg_6357_);
goto v___jp_6350_;
}
else
{
lean_object* v_arg_6363_; lean_object* v___x_6364_; uint8_t v___x_6365_; 
v_arg_6363_ = lean_ctor_get(v___x_6361_, 1);
lean_inc_ref(v_arg_6363_);
v___x_6364_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6361_);
v___x_6365_ = l_Lean_Expr_isApp(v___x_6364_);
if (v___x_6365_ == 0)
{
lean_dec_ref(v___x_6364_);
lean_dec_ref(v_arg_6363_);
lean_dec_ref(v_arg_6360_);
lean_dec_ref(v_arg_6357_);
goto v___jp_6350_;
}
else
{
lean_object* v___x_6366_; lean_object* v___x_6367_; uint8_t v___x_6368_; 
v___x_6366_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6364_);
v___x_6367_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__1));
v___x_6368_ = l_Lean_Expr_isConstOf(v___x_6366_, v___x_6367_);
lean_dec_ref(v___x_6366_);
if (v___x_6368_ == 0)
{
lean_dec_ref(v_arg_6363_);
lean_dec_ref(v_arg_6360_);
lean_dec_ref(v_arg_6357_);
goto v___jp_6350_;
}
else
{
lean_object* v___x_6369_; lean_object* v___x_6370_; 
lean_del_object(v___x_6348_);
v___x_6369_ = lean_obj_once(&l_Lean_Elab_WF_isNatLtWF___closed__4, &l_Lean_Elab_WF_isNatLtWF___closed__4_once, _init_l_Lean_Elab_WF_isNatLtWF___closed__4);
v___x_6370_ = l_Lean_Meta_isExprDefEq(v_arg_6363_, v___x_6369_, v_a_6340_, v_a_6341_, v_a_6342_, v_a_6343_);
if (lean_obj_tag(v___x_6370_) == 0)
{
lean_object* v_a_6371_; lean_object* v___x_6373_; uint8_t v_isShared_6374_; uint8_t v_isSharedCheck_6404_; 
v_a_6371_ = lean_ctor_get(v___x_6370_, 0);
v_isSharedCheck_6404_ = !lean_is_exclusive(v___x_6370_);
if (v_isSharedCheck_6404_ == 0)
{
v___x_6373_ = v___x_6370_;
v_isShared_6374_ = v_isSharedCheck_6404_;
goto v_resetjp_6372_;
}
else
{
lean_inc(v_a_6371_);
lean_dec(v___x_6370_);
v___x_6373_ = lean_box(0);
v_isShared_6374_ = v_isSharedCheck_6404_;
goto v_resetjp_6372_;
}
v_resetjp_6372_:
{
uint8_t v___x_6375_; 
v___x_6375_ = lean_unbox(v_a_6371_);
lean_dec(v_a_6371_);
if (v___x_6375_ == 0)
{
lean_object* v___x_6376_; lean_object* v___x_6378_; 
lean_dec_ref(v_arg_6360_);
lean_dec_ref(v_arg_6357_);
v___x_6376_ = lean_box(0);
if (v_isShared_6374_ == 0)
{
lean_ctor_set(v___x_6373_, 0, v___x_6376_);
v___x_6378_ = v___x_6373_;
goto v_reusejp_6377_;
}
else
{
lean_object* v_reuseFailAlloc_6379_; 
v_reuseFailAlloc_6379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6379_, 0, v___x_6376_);
v___x_6378_ = v_reuseFailAlloc_6379_;
goto v_reusejp_6377_;
}
v_reusejp_6377_:
{
return v___x_6378_;
}
}
else
{
lean_object* v___x_6380_; lean_object* v___x_6381_; 
lean_del_object(v___x_6373_);
v___x_6380_ = lean_obj_once(&l_Lean_Elab_WF_isNatLtWF___closed__7, &l_Lean_Elab_WF_isNatLtWF___closed__7_once, _init_l_Lean_Elab_WF_isNatLtWF___closed__7);
v___x_6381_ = l_Lean_Meta_isExprDefEq(v_arg_6357_, v___x_6380_, v_a_6340_, v_a_6341_, v_a_6342_, v_a_6343_);
if (lean_obj_tag(v___x_6381_) == 0)
{
lean_object* v_a_6382_; lean_object* v___x_6384_; uint8_t v_isShared_6385_; uint8_t v_isSharedCheck_6395_; 
v_a_6382_ = lean_ctor_get(v___x_6381_, 0);
v_isSharedCheck_6395_ = !lean_is_exclusive(v___x_6381_);
if (v_isSharedCheck_6395_ == 0)
{
v___x_6384_ = v___x_6381_;
v_isShared_6385_ = v_isSharedCheck_6395_;
goto v_resetjp_6383_;
}
else
{
lean_inc(v_a_6382_);
lean_dec(v___x_6381_);
v___x_6384_ = lean_box(0);
v_isShared_6385_ = v_isSharedCheck_6395_;
goto v_resetjp_6383_;
}
v_resetjp_6383_:
{
uint8_t v___x_6386_; 
v___x_6386_ = lean_unbox(v_a_6382_);
lean_dec(v_a_6382_);
if (v___x_6386_ == 0)
{
lean_object* v___x_6387_; lean_object* v___x_6389_; 
lean_dec_ref(v_arg_6360_);
v___x_6387_ = lean_box(0);
if (v_isShared_6385_ == 0)
{
lean_ctor_set(v___x_6384_, 0, v___x_6387_);
v___x_6389_ = v___x_6384_;
goto v_reusejp_6388_;
}
else
{
lean_object* v_reuseFailAlloc_6390_; 
v_reuseFailAlloc_6390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6390_, 0, v___x_6387_);
v___x_6389_ = v_reuseFailAlloc_6390_;
goto v_reusejp_6388_;
}
v_reusejp_6388_:
{
return v___x_6389_;
}
}
else
{
lean_object* v___x_6391_; lean_object* v___x_6393_; 
v___x_6391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6391_, 0, v_arg_6360_);
if (v_isShared_6385_ == 0)
{
lean_ctor_set(v___x_6384_, 0, v___x_6391_);
v___x_6393_ = v___x_6384_;
goto v_reusejp_6392_;
}
else
{
lean_object* v_reuseFailAlloc_6394_; 
v_reuseFailAlloc_6394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6394_, 0, v___x_6391_);
v___x_6393_ = v_reuseFailAlloc_6394_;
goto v_reusejp_6392_;
}
v_reusejp_6392_:
{
return v___x_6393_;
}
}
}
}
else
{
lean_object* v_a_6396_; lean_object* v___x_6398_; uint8_t v_isShared_6399_; uint8_t v_isSharedCheck_6403_; 
lean_dec_ref(v_arg_6360_);
v_a_6396_ = lean_ctor_get(v___x_6381_, 0);
v_isSharedCheck_6403_ = !lean_is_exclusive(v___x_6381_);
if (v_isSharedCheck_6403_ == 0)
{
v___x_6398_ = v___x_6381_;
v_isShared_6399_ = v_isSharedCheck_6403_;
goto v_resetjp_6397_;
}
else
{
lean_inc(v_a_6396_);
lean_dec(v___x_6381_);
v___x_6398_ = lean_box(0);
v_isShared_6399_ = v_isSharedCheck_6403_;
goto v_resetjp_6397_;
}
v_resetjp_6397_:
{
lean_object* v___x_6401_; 
if (v_isShared_6399_ == 0)
{
v___x_6401_ = v___x_6398_;
goto v_reusejp_6400_;
}
else
{
lean_object* v_reuseFailAlloc_6402_; 
v_reuseFailAlloc_6402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6402_, 0, v_a_6396_);
v___x_6401_ = v_reuseFailAlloc_6402_;
goto v_reusejp_6400_;
}
v_reusejp_6400_:
{
return v___x_6401_;
}
}
}
}
}
}
else
{
lean_object* v_a_6405_; lean_object* v___x_6407_; uint8_t v_isShared_6408_; uint8_t v_isSharedCheck_6412_; 
lean_dec_ref(v_arg_6360_);
lean_dec_ref(v_arg_6357_);
v_a_6405_ = lean_ctor_get(v___x_6370_, 0);
v_isSharedCheck_6412_ = !lean_is_exclusive(v___x_6370_);
if (v_isSharedCheck_6412_ == 0)
{
v___x_6407_ = v___x_6370_;
v_isShared_6408_ = v_isSharedCheck_6412_;
goto v_resetjp_6406_;
}
else
{
lean_inc(v_a_6405_);
lean_dec(v___x_6370_);
v___x_6407_ = lean_box(0);
v_isShared_6408_ = v_isSharedCheck_6412_;
goto v_resetjp_6406_;
}
v_resetjp_6406_:
{
lean_object* v___x_6410_; 
if (v_isShared_6408_ == 0)
{
v___x_6410_ = v___x_6407_;
goto v_reusejp_6409_;
}
else
{
lean_object* v_reuseFailAlloc_6411_; 
v_reuseFailAlloc_6411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6411_, 0, v_a_6405_);
v___x_6410_ = v_reuseFailAlloc_6411_;
goto v_reusejp_6409_;
}
v_reusejp_6409_:
{
return v___x_6410_;
}
}
}
}
}
}
}
}
v___jp_6350_:
{
lean_object* v___x_6351_; lean_object* v___x_6353_; 
v___x_6351_ = lean_box(0);
if (v_isShared_6349_ == 0)
{
lean_ctor_set(v___x_6348_, 0, v___x_6351_);
v___x_6353_ = v___x_6348_;
goto v_reusejp_6352_;
}
else
{
lean_object* v_reuseFailAlloc_6354_; 
v_reuseFailAlloc_6354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6354_, 0, v___x_6351_);
v___x_6353_ = v_reuseFailAlloc_6354_;
goto v_reusejp_6352_;
}
v_reusejp_6352_:
{
return v___x_6353_;
}
}
}
}
else
{
lean_object* v_a_6414_; lean_object* v___x_6416_; uint8_t v_isShared_6417_; uint8_t v_isSharedCheck_6421_; 
v_a_6414_ = lean_ctor_get(v___x_6345_, 0);
v_isSharedCheck_6421_ = !lean_is_exclusive(v___x_6345_);
if (v_isSharedCheck_6421_ == 0)
{
v___x_6416_ = v___x_6345_;
v_isShared_6417_ = v_isSharedCheck_6421_;
goto v_resetjp_6415_;
}
else
{
lean_inc(v_a_6414_);
lean_dec(v___x_6345_);
v___x_6416_ = lean_box(0);
v_isShared_6417_ = v_isSharedCheck_6421_;
goto v_resetjp_6415_;
}
v_resetjp_6415_:
{
lean_object* v___x_6419_; 
if (v_isShared_6417_ == 0)
{
v___x_6419_ = v___x_6416_;
goto v_reusejp_6418_;
}
else
{
lean_object* v_reuseFailAlloc_6420_; 
v_reuseFailAlloc_6420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6420_, 0, v_a_6414_);
v___x_6419_ = v_reuseFailAlloc_6420_;
goto v_reusejp_6418_;
}
v_reusejp_6418_:
{
return v___x_6419_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isNatLtWF___boxed(lean_object* v_wfRel_6422_, lean_object* v_a_6423_, lean_object* v_a_6424_, lean_object* v_a_6425_, lean_object* v_a_6426_, lean_object* v_a_6427_){
_start:
{
lean_object* v_res_6428_; 
v_res_6428_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_6422_, v_a_6423_, v_a_6424_, v_a_6425_, v_a_6426_);
lean_dec(v_a_6426_);
lean_dec_ref(v_a_6425_);
lean_dec(v_a_6424_);
lean_dec_ref(v_a_6423_);
return v_res_6428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(lean_object* v_type_6429_, lean_object* v_maxFVars_x3f_6430_, lean_object* v_k_6431_, uint8_t v_cleanupAnnotations_6432_, uint8_t v_whnfType_6433_, lean_object* v___y_6434_, lean_object* v___y_6435_, lean_object* v___y_6436_, lean_object* v___y_6437_, lean_object* v___y_6438_, lean_object* v___y_6439_){
_start:
{
lean_object* v___f_6441_; lean_object* v___x_6442_; 
lean_inc(v___y_6435_);
lean_inc_ref(v___y_6434_);
v___f_6441_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_6441_, 0, v_k_6431_);
lean_closure_set(v___f_6441_, 1, v___y_6434_);
lean_closure_set(v___f_6441_, 2, v___y_6435_);
v___x_6442_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_6429_, v_maxFVars_x3f_6430_, v___f_6441_, v_cleanupAnnotations_6432_, v_whnfType_6433_, v___y_6436_, v___y_6437_, v___y_6438_, v___y_6439_);
if (lean_obj_tag(v___x_6442_) == 0)
{
return v___x_6442_;
}
else
{
lean_object* v_a_6443_; lean_object* v___x_6445_; uint8_t v_isShared_6446_; uint8_t v_isSharedCheck_6450_; 
v_a_6443_ = lean_ctor_get(v___x_6442_, 0);
v_isSharedCheck_6450_ = !lean_is_exclusive(v___x_6442_);
if (v_isSharedCheck_6450_ == 0)
{
v___x_6445_ = v___x_6442_;
v_isShared_6446_ = v_isSharedCheck_6450_;
goto v_resetjp_6444_;
}
else
{
lean_inc(v_a_6443_);
lean_dec(v___x_6442_);
v___x_6445_ = lean_box(0);
v_isShared_6446_ = v_isSharedCheck_6450_;
goto v_resetjp_6444_;
}
v_resetjp_6444_:
{
lean_object* v___x_6448_; 
if (v_isShared_6446_ == 0)
{
v___x_6448_ = v___x_6445_;
goto v_reusejp_6447_;
}
else
{
lean_object* v_reuseFailAlloc_6449_; 
v_reuseFailAlloc_6449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6449_, 0, v_a_6443_);
v___x_6448_ = v_reuseFailAlloc_6449_;
goto v_reusejp_6447_;
}
v_reusejp_6447_:
{
return v___x_6448_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg___boxed(lean_object* v_type_6451_, lean_object* v_maxFVars_x3f_6452_, lean_object* v_k_6453_, lean_object* v_cleanupAnnotations_6454_, lean_object* v_whnfType_6455_, lean_object* v___y_6456_, lean_object* v___y_6457_, lean_object* v___y_6458_, lean_object* v___y_6459_, lean_object* v___y_6460_, lean_object* v___y_6461_, lean_object* v___y_6462_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_6463_; uint8_t v_whnfType_boxed_6464_; lean_object* v_res_6465_; 
v_cleanupAnnotations_boxed_6463_ = lean_unbox(v_cleanupAnnotations_6454_);
v_whnfType_boxed_6464_ = lean_unbox(v_whnfType_6455_);
v_res_6465_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_type_6451_, v_maxFVars_x3f_6452_, v_k_6453_, v_cleanupAnnotations_boxed_6463_, v_whnfType_boxed_6464_, v___y_6456_, v___y_6457_, v___y_6458_, v___y_6459_, v___y_6460_, v___y_6461_);
lean_dec(v___y_6461_);
lean_dec_ref(v___y_6460_);
lean_dec(v___y_6459_);
lean_dec_ref(v___y_6458_);
lean_dec(v___y_6457_);
lean_dec_ref(v___y_6456_);
return v_res_6465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0(lean_object* v_00_u03b1_6466_, lean_object* v_type_6467_, lean_object* v_maxFVars_x3f_6468_, lean_object* v_k_6469_, uint8_t v_cleanupAnnotations_6470_, uint8_t v_whnfType_6471_, lean_object* v___y_6472_, lean_object* v___y_6473_, lean_object* v___y_6474_, lean_object* v___y_6475_, lean_object* v___y_6476_, lean_object* v___y_6477_){
_start:
{
lean_object* v___x_6479_; 
v___x_6479_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_type_6467_, v_maxFVars_x3f_6468_, v_k_6469_, v_cleanupAnnotations_6470_, v_whnfType_6471_, v___y_6472_, v___y_6473_, v___y_6474_, v___y_6475_, v___y_6476_, v___y_6477_);
return v___x_6479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___boxed(lean_object* v_00_u03b1_6480_, lean_object* v_type_6481_, lean_object* v_maxFVars_x3f_6482_, lean_object* v_k_6483_, lean_object* v_cleanupAnnotations_6484_, lean_object* v_whnfType_6485_, lean_object* v___y_6486_, lean_object* v___y_6487_, lean_object* v___y_6488_, lean_object* v___y_6489_, lean_object* v___y_6490_, lean_object* v___y_6491_, lean_object* v___y_6492_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_6493_; uint8_t v_whnfType_boxed_6494_; lean_object* v_res_6495_; 
v_cleanupAnnotations_boxed_6493_ = lean_unbox(v_cleanupAnnotations_6484_);
v_whnfType_boxed_6494_ = lean_unbox(v_whnfType_6485_);
v_res_6495_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0(v_00_u03b1_6480_, v_type_6481_, v_maxFVars_x3f_6482_, v_k_6483_, v_cleanupAnnotations_boxed_6493_, v_whnfType_boxed_6494_, v___y_6486_, v___y_6487_, v___y_6488_, v___y_6489_, v___y_6490_, v___y_6491_);
lean_dec(v___y_6491_);
lean_dec_ref(v___y_6490_);
lean_dec(v___y_6489_);
lean_dec_ref(v___y_6488_);
lean_dec(v___y_6487_);
lean_dec_ref(v___y_6486_);
return v_res_6495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(lean_object* v_lctx_6496_, lean_object* v_x_6497_, lean_object* v___y_6498_, lean_object* v___y_6499_, lean_object* v___y_6500_, lean_object* v___y_6501_, lean_object* v___y_6502_, lean_object* v___y_6503_){
_start:
{
lean_object* v_keyedConfig_6505_; uint8_t v_trackZetaDelta_6506_; lean_object* v_zetaDeltaSet_6507_; lean_object* v_localInstances_6508_; lean_object* v_defEqCtx_x3f_6509_; lean_object* v_synthPendingDepth_6510_; lean_object* v_customCanUnfoldPredicate_x3f_6511_; uint8_t v_univApprox_6512_; uint8_t v_inTypeClassResolution_6513_; uint8_t v_cacheInferType_6514_; lean_object* v___x_6515_; lean_object* v___x_6516_; 
v_keyedConfig_6505_ = lean_ctor_get(v___y_6500_, 0);
v_trackZetaDelta_6506_ = lean_ctor_get_uint8(v___y_6500_, sizeof(void*)*7);
v_zetaDeltaSet_6507_ = lean_ctor_get(v___y_6500_, 1);
v_localInstances_6508_ = lean_ctor_get(v___y_6500_, 3);
v_defEqCtx_x3f_6509_ = lean_ctor_get(v___y_6500_, 4);
v_synthPendingDepth_6510_ = lean_ctor_get(v___y_6500_, 5);
v_customCanUnfoldPredicate_x3f_6511_ = lean_ctor_get(v___y_6500_, 6);
v_univApprox_6512_ = lean_ctor_get_uint8(v___y_6500_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_6513_ = lean_ctor_get_uint8(v___y_6500_, sizeof(void*)*7 + 2);
v_cacheInferType_6514_ = lean_ctor_get_uint8(v___y_6500_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_6511_);
lean_inc(v_synthPendingDepth_6510_);
lean_inc(v_defEqCtx_x3f_6509_);
lean_inc_ref(v_localInstances_6508_);
lean_inc(v_zetaDeltaSet_6507_);
lean_inc_ref(v_keyedConfig_6505_);
v___x_6515_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6515_, 0, v_keyedConfig_6505_);
lean_ctor_set(v___x_6515_, 1, v_zetaDeltaSet_6507_);
lean_ctor_set(v___x_6515_, 2, v_lctx_6496_);
lean_ctor_set(v___x_6515_, 3, v_localInstances_6508_);
lean_ctor_set(v___x_6515_, 4, v_defEqCtx_x3f_6509_);
lean_ctor_set(v___x_6515_, 5, v_synthPendingDepth_6510_);
lean_ctor_set(v___x_6515_, 6, v_customCanUnfoldPredicate_x3f_6511_);
lean_ctor_set_uint8(v___x_6515_, sizeof(void*)*7, v_trackZetaDelta_6506_);
lean_ctor_set_uint8(v___x_6515_, sizeof(void*)*7 + 1, v_univApprox_6512_);
lean_ctor_set_uint8(v___x_6515_, sizeof(void*)*7 + 2, v_inTypeClassResolution_6513_);
lean_ctor_set_uint8(v___x_6515_, sizeof(void*)*7 + 3, v_cacheInferType_6514_);
lean_inc(v___y_6503_);
lean_inc_ref(v___y_6502_);
lean_inc(v___y_6501_);
lean_inc(v___y_6499_);
lean_inc_ref(v___y_6498_);
v___x_6516_ = lean_apply_7(v_x_6497_, v___y_6498_, v___y_6499_, v___x_6515_, v___y_6501_, v___y_6502_, v___y_6503_, lean_box(0));
if (lean_obj_tag(v___x_6516_) == 0)
{
lean_object* v_a_6517_; lean_object* v___x_6519_; uint8_t v_isShared_6520_; uint8_t v_isSharedCheck_6524_; 
v_a_6517_ = lean_ctor_get(v___x_6516_, 0);
v_isSharedCheck_6524_ = !lean_is_exclusive(v___x_6516_);
if (v_isSharedCheck_6524_ == 0)
{
v___x_6519_ = v___x_6516_;
v_isShared_6520_ = v_isSharedCheck_6524_;
goto v_resetjp_6518_;
}
else
{
lean_inc(v_a_6517_);
lean_dec(v___x_6516_);
v___x_6519_ = lean_box(0);
v_isShared_6520_ = v_isSharedCheck_6524_;
goto v_resetjp_6518_;
}
v_resetjp_6518_:
{
lean_object* v___x_6522_; 
if (v_isShared_6520_ == 0)
{
v___x_6522_ = v___x_6519_;
goto v_reusejp_6521_;
}
else
{
lean_object* v_reuseFailAlloc_6523_; 
v_reuseFailAlloc_6523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6523_, 0, v_a_6517_);
v___x_6522_ = v_reuseFailAlloc_6523_;
goto v_reusejp_6521_;
}
v_reusejp_6521_:
{
return v___x_6522_;
}
}
}
else
{
return v___x_6516_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg___boxed(lean_object* v_lctx_6525_, lean_object* v_x_6526_, lean_object* v___y_6527_, lean_object* v___y_6528_, lean_object* v___y_6529_, lean_object* v___y_6530_, lean_object* v___y_6531_, lean_object* v___y_6532_, lean_object* v___y_6533_){
_start:
{
lean_object* v_res_6534_; 
v_res_6534_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v_lctx_6525_, v_x_6526_, v___y_6527_, v___y_6528_, v___y_6529_, v___y_6530_, v___y_6531_, v___y_6532_);
lean_dec(v___y_6532_);
lean_dec_ref(v___y_6531_);
lean_dec(v___y_6530_);
lean_dec_ref(v___y_6529_);
lean_dec(v___y_6528_);
lean_dec_ref(v___y_6527_);
return v_res_6534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1(lean_object* v_00_u03b1_6535_, lean_object* v_lctx_6536_, lean_object* v_x_6537_, lean_object* v___y_6538_, lean_object* v___y_6539_, lean_object* v___y_6540_, lean_object* v___y_6541_, lean_object* v___y_6542_, lean_object* v___y_6543_){
_start:
{
lean_object* v___x_6545_; 
v___x_6545_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v_lctx_6536_, v_x_6537_, v___y_6538_, v___y_6539_, v___y_6540_, v___y_6541_, v___y_6542_, v___y_6543_);
return v___x_6545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___boxed(lean_object* v_00_u03b1_6546_, lean_object* v_lctx_6547_, lean_object* v_x_6548_, lean_object* v___y_6549_, lean_object* v___y_6550_, lean_object* v___y_6551_, lean_object* v___y_6552_, lean_object* v___y_6553_, lean_object* v___y_6554_, lean_object* v___y_6555_){
_start:
{
lean_object* v_res_6556_; 
v_res_6556_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1(v_00_u03b1_6546_, v_lctx_6547_, v_x_6548_, v___y_6549_, v___y_6550_, v___y_6551_, v___y_6552_, v___y_6553_, v___y_6554_);
lean_dec(v___y_6554_);
lean_dec_ref(v___y_6553_);
lean_dec(v___y_6552_);
lean_dec_ref(v___y_6551_);
lean_dec(v___y_6550_);
lean_dec_ref(v___y_6549_);
return v_res_6556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__0(lean_object* v___x_6573_, lean_object* v___x_6574_, lean_object* v_wfRel_6575_, lean_object* v_x_6576_, lean_object* v_type_6577_, lean_object* v___y_6578_, lean_object* v___y_6579_, lean_object* v___y_6580_, lean_object* v___y_6581_, lean_object* v___y_6582_, lean_object* v___y_6583_){
_start:
{
lean_object* v___x_6585_; lean_object* v___x_6586_; lean_object* v___x_6587_; lean_object* v___x_6588_; 
v___x_6585_ = lean_unsigned_to_nat(0u);
v___x_6586_ = lean_array_get_borrowed(v___x_6573_, v_x_6576_, v___x_6585_);
v___x_6587_ = l_Lean_Expr_fvarId_x21(v___x_6586_);
v___x_6588_ = l_Lean_FVarId_getUserName___redArg(v___x_6587_, v___y_6580_, v___y_6582_, v___y_6583_);
if (lean_obj_tag(v___x_6588_) == 0)
{
lean_object* v_a_6589_; lean_object* v___x_6590_; 
v_a_6589_ = lean_ctor_get(v___x_6588_, 0);
lean_inc(v_a_6589_);
lean_dec_ref_known(v___x_6588_, 1);
lean_inc(v___y_6583_);
lean_inc_ref(v___y_6582_);
lean_inc(v___y_6581_);
lean_inc_ref(v___y_6580_);
lean_inc(v___x_6586_);
v___x_6590_ = lean_infer_type(v___x_6586_, v___y_6580_, v___y_6581_, v___y_6582_, v___y_6583_);
if (lean_obj_tag(v___x_6590_) == 0)
{
lean_object* v_a_6591_; lean_object* v___x_6592_; 
v_a_6591_ = lean_ctor_get(v___x_6590_, 0);
lean_inc_n(v_a_6591_, 2);
lean_dec_ref_known(v___x_6590_, 1);
v___x_6592_ = l_Lean_Meta_getLevel(v_a_6591_, v___y_6580_, v___y_6581_, v___y_6582_, v___y_6583_);
if (lean_obj_tag(v___x_6592_) == 0)
{
lean_object* v_a_6593_; lean_object* v___x_6594_; 
v_a_6593_ = lean_ctor_get(v___x_6592_, 0);
lean_inc(v_a_6593_);
lean_dec_ref_known(v___x_6592_, 1);
lean_inc_ref(v_type_6577_);
v___x_6594_ = l_Lean_Meta_getLevel(v_type_6577_, v___y_6580_, v___y_6581_, v___y_6582_, v___y_6583_);
if (lean_obj_tag(v___x_6594_) == 0)
{
lean_object* v_a_6595_; lean_object* v___x_6596_; lean_object* v___x_6597_; uint8_t v___x_6598_; uint8_t v___x_6599_; uint8_t v___x_6600_; lean_object* v___x_6601_; 
v_a_6595_ = lean_ctor_get(v___x_6594_, 0);
lean_inc(v_a_6595_);
lean_dec_ref_known(v___x_6594_, 1);
v___x_6596_ = lean_mk_empty_array_with_capacity(v___x_6574_);
lean_inc(v___x_6586_);
lean_inc_ref(v___x_6596_);
v___x_6597_ = lean_array_push(v___x_6596_, v___x_6586_);
v___x_6598_ = 0;
v___x_6599_ = 1;
v___x_6600_ = 1;
v___x_6601_ = l_Lean_Meta_mkLambdaFVars(v___x_6597_, v_type_6577_, v___x_6598_, v___x_6599_, v___x_6598_, v___x_6599_, v___x_6600_, v___y_6580_, v___y_6581_, v___y_6582_, v___y_6583_);
lean_dec_ref(v___x_6597_);
if (lean_obj_tag(v___x_6601_) == 0)
{
lean_object* v_a_6602_; lean_object* v___x_6603_; 
v_a_6602_ = lean_ctor_get(v___x_6601_, 0);
lean_inc(v_a_6602_);
lean_dec_ref_known(v___x_6601_, 1);
lean_inc_ref(v_wfRel_6575_);
v___x_6603_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_6575_, v___y_6580_, v___y_6581_, v___y_6582_, v___y_6583_);
if (lean_obj_tag(v___x_6603_) == 0)
{
lean_object* v_a_6604_; lean_object* v___x_6606_; uint8_t v_isShared_6607_; uint8_t v_isSharedCheck_6648_; 
v_a_6604_ = lean_ctor_get(v___x_6603_, 0);
v_isSharedCheck_6648_ = !lean_is_exclusive(v___x_6603_);
if (v_isSharedCheck_6648_ == 0)
{
v___x_6606_ = v___x_6603_;
v_isShared_6607_ = v_isSharedCheck_6648_;
goto v_resetjp_6605_;
}
else
{
lean_inc(v_a_6604_);
lean_dec(v___x_6603_);
v___x_6606_ = lean_box(0);
v_isShared_6607_ = v_isSharedCheck_6648_;
goto v_resetjp_6605_;
}
v_resetjp_6605_:
{
if (lean_obj_tag(v_a_6604_) == 1)
{
lean_object* v_val_6608_; lean_object* v___x_6609_; lean_object* v___x_6610_; lean_object* v___x_6611_; lean_object* v___x_6612_; lean_object* v___x_6613_; lean_object* v___x_6614_; lean_object* v___x_6615_; lean_object* v___x_6617_; 
lean_dec_ref(v___x_6596_);
lean_dec_ref(v_wfRel_6575_);
lean_dec(v___x_6574_);
v_val_6608_ = lean_ctor_get(v_a_6604_, 0);
lean_inc(v_val_6608_);
lean_dec_ref_known(v_a_6604_, 1);
v___x_6609_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__2));
v___x_6610_ = lean_box(0);
v___x_6611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6611_, 0, v_a_6595_);
lean_ctor_set(v___x_6611_, 1, v___x_6610_);
v___x_6612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6612_, 0, v_a_6593_);
lean_ctor_set(v___x_6612_, 1, v___x_6611_);
v___x_6613_ = l_Lean_mkConst(v___x_6609_, v___x_6612_);
v___x_6614_ = l_Lean_mkApp3(v___x_6613_, v_a_6591_, v_a_6602_, v_val_6608_);
v___x_6615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6615_, 0, v___x_6614_);
lean_ctor_set(v___x_6615_, 1, v_a_6589_);
if (v_isShared_6607_ == 0)
{
lean_ctor_set(v___x_6606_, 0, v___x_6615_);
v___x_6617_ = v___x_6606_;
goto v_reusejp_6616_;
}
else
{
lean_object* v_reuseFailAlloc_6618_; 
v_reuseFailAlloc_6618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6618_, 0, v___x_6615_);
v___x_6617_ = v_reuseFailAlloc_6618_;
goto v_reusejp_6616_;
}
v_reusejp_6616_:
{
return v___x_6617_;
}
}
else
{
lean_object* v___x_6619_; lean_object* v___x_6620_; lean_object* v___x_6621_; lean_object* v___x_6622_; lean_object* v___x_6623_; lean_object* v___x_6624_; 
lean_del_object(v___x_6606_);
lean_dec(v_a_6604_);
v___x_6619_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__4));
lean_inc_ref(v_wfRel_6575_);
v___x_6620_ = l_Lean_mkProj(v___x_6619_, v___x_6585_, v_wfRel_6575_);
v___x_6621_ = l_Lean_mkProj(v___x_6619_, v___x_6574_, v_wfRel_6575_);
v___x_6622_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__6));
v___x_6623_ = lean_array_push(v___x_6596_, v___x_6621_);
v___x_6624_ = l_Lean_Meta_mkAppM(v___x_6622_, v___x_6623_, v___y_6580_, v___y_6581_, v___y_6582_, v___y_6583_);
if (lean_obj_tag(v___x_6624_) == 0)
{
lean_object* v_a_6625_; lean_object* v___x_6627_; uint8_t v_isShared_6628_; uint8_t v_isSharedCheck_6639_; 
v_a_6625_ = lean_ctor_get(v___x_6624_, 0);
v_isSharedCheck_6639_ = !lean_is_exclusive(v___x_6624_);
if (v_isSharedCheck_6639_ == 0)
{
v___x_6627_ = v___x_6624_;
v_isShared_6628_ = v_isSharedCheck_6639_;
goto v_resetjp_6626_;
}
else
{
lean_inc(v_a_6625_);
lean_dec(v___x_6624_);
v___x_6627_ = lean_box(0);
v_isShared_6628_ = v_isSharedCheck_6639_;
goto v_resetjp_6626_;
}
v_resetjp_6626_:
{
lean_object* v___x_6629_; lean_object* v___x_6630_; lean_object* v___x_6631_; lean_object* v___x_6632_; lean_object* v___x_6633_; lean_object* v___x_6634_; lean_object* v___x_6635_; lean_object* v___x_6637_; 
v___x_6629_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__7));
v___x_6630_ = lean_box(0);
v___x_6631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6631_, 0, v_a_6595_);
lean_ctor_set(v___x_6631_, 1, v___x_6630_);
v___x_6632_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6632_, 0, v_a_6593_);
lean_ctor_set(v___x_6632_, 1, v___x_6631_);
v___x_6633_ = l_Lean_mkConst(v___x_6629_, v___x_6632_);
v___x_6634_ = l_Lean_mkApp4(v___x_6633_, v_a_6591_, v_a_6602_, v___x_6620_, v_a_6625_);
v___x_6635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6635_, 0, v___x_6634_);
lean_ctor_set(v___x_6635_, 1, v_a_6589_);
if (v_isShared_6628_ == 0)
{
lean_ctor_set(v___x_6627_, 0, v___x_6635_);
v___x_6637_ = v___x_6627_;
goto v_reusejp_6636_;
}
else
{
lean_object* v_reuseFailAlloc_6638_; 
v_reuseFailAlloc_6638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6638_, 0, v___x_6635_);
v___x_6637_ = v_reuseFailAlloc_6638_;
goto v_reusejp_6636_;
}
v_reusejp_6636_:
{
return v___x_6637_;
}
}
}
else
{
lean_object* v_a_6640_; lean_object* v___x_6642_; uint8_t v_isShared_6643_; uint8_t v_isSharedCheck_6647_; 
lean_dec_ref(v___x_6620_);
lean_dec(v_a_6602_);
lean_dec(v_a_6595_);
lean_dec(v_a_6593_);
lean_dec(v_a_6591_);
lean_dec(v_a_6589_);
v_a_6640_ = lean_ctor_get(v___x_6624_, 0);
v_isSharedCheck_6647_ = !lean_is_exclusive(v___x_6624_);
if (v_isSharedCheck_6647_ == 0)
{
v___x_6642_ = v___x_6624_;
v_isShared_6643_ = v_isSharedCheck_6647_;
goto v_resetjp_6641_;
}
else
{
lean_inc(v_a_6640_);
lean_dec(v___x_6624_);
v___x_6642_ = lean_box(0);
v_isShared_6643_ = v_isSharedCheck_6647_;
goto v_resetjp_6641_;
}
v_resetjp_6641_:
{
lean_object* v___x_6645_; 
if (v_isShared_6643_ == 0)
{
v___x_6645_ = v___x_6642_;
goto v_reusejp_6644_;
}
else
{
lean_object* v_reuseFailAlloc_6646_; 
v_reuseFailAlloc_6646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6646_, 0, v_a_6640_);
v___x_6645_ = v_reuseFailAlloc_6646_;
goto v_reusejp_6644_;
}
v_reusejp_6644_:
{
return v___x_6645_;
}
}
}
}
}
}
else
{
lean_object* v_a_6649_; lean_object* v___x_6651_; uint8_t v_isShared_6652_; uint8_t v_isSharedCheck_6656_; 
lean_dec(v_a_6602_);
lean_dec_ref(v___x_6596_);
lean_dec(v_a_6595_);
lean_dec(v_a_6593_);
lean_dec(v_a_6591_);
lean_dec(v_a_6589_);
lean_dec_ref(v_wfRel_6575_);
lean_dec(v___x_6574_);
v_a_6649_ = lean_ctor_get(v___x_6603_, 0);
v_isSharedCheck_6656_ = !lean_is_exclusive(v___x_6603_);
if (v_isSharedCheck_6656_ == 0)
{
v___x_6651_ = v___x_6603_;
v_isShared_6652_ = v_isSharedCheck_6656_;
goto v_resetjp_6650_;
}
else
{
lean_inc(v_a_6649_);
lean_dec(v___x_6603_);
v___x_6651_ = lean_box(0);
v_isShared_6652_ = v_isSharedCheck_6656_;
goto v_resetjp_6650_;
}
v_resetjp_6650_:
{
lean_object* v___x_6654_; 
if (v_isShared_6652_ == 0)
{
v___x_6654_ = v___x_6651_;
goto v_reusejp_6653_;
}
else
{
lean_object* v_reuseFailAlloc_6655_; 
v_reuseFailAlloc_6655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6655_, 0, v_a_6649_);
v___x_6654_ = v_reuseFailAlloc_6655_;
goto v_reusejp_6653_;
}
v_reusejp_6653_:
{
return v___x_6654_;
}
}
}
}
else
{
lean_object* v_a_6657_; lean_object* v___x_6659_; uint8_t v_isShared_6660_; uint8_t v_isSharedCheck_6664_; 
lean_dec_ref(v___x_6596_);
lean_dec(v_a_6595_);
lean_dec(v_a_6593_);
lean_dec(v_a_6591_);
lean_dec(v_a_6589_);
lean_dec_ref(v_wfRel_6575_);
lean_dec(v___x_6574_);
v_a_6657_ = lean_ctor_get(v___x_6601_, 0);
v_isSharedCheck_6664_ = !lean_is_exclusive(v___x_6601_);
if (v_isSharedCheck_6664_ == 0)
{
v___x_6659_ = v___x_6601_;
v_isShared_6660_ = v_isSharedCheck_6664_;
goto v_resetjp_6658_;
}
else
{
lean_inc(v_a_6657_);
lean_dec(v___x_6601_);
v___x_6659_ = lean_box(0);
v_isShared_6660_ = v_isSharedCheck_6664_;
goto v_resetjp_6658_;
}
v_resetjp_6658_:
{
lean_object* v___x_6662_; 
if (v_isShared_6660_ == 0)
{
v___x_6662_ = v___x_6659_;
goto v_reusejp_6661_;
}
else
{
lean_object* v_reuseFailAlloc_6663_; 
v_reuseFailAlloc_6663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6663_, 0, v_a_6657_);
v___x_6662_ = v_reuseFailAlloc_6663_;
goto v_reusejp_6661_;
}
v_reusejp_6661_:
{
return v___x_6662_;
}
}
}
}
else
{
lean_object* v_a_6665_; lean_object* v___x_6667_; uint8_t v_isShared_6668_; uint8_t v_isSharedCheck_6672_; 
lean_dec(v_a_6593_);
lean_dec(v_a_6591_);
lean_dec(v_a_6589_);
lean_dec_ref(v_type_6577_);
lean_dec_ref(v_wfRel_6575_);
lean_dec(v___x_6574_);
v_a_6665_ = lean_ctor_get(v___x_6594_, 0);
v_isSharedCheck_6672_ = !lean_is_exclusive(v___x_6594_);
if (v_isSharedCheck_6672_ == 0)
{
v___x_6667_ = v___x_6594_;
v_isShared_6668_ = v_isSharedCheck_6672_;
goto v_resetjp_6666_;
}
else
{
lean_inc(v_a_6665_);
lean_dec(v___x_6594_);
v___x_6667_ = lean_box(0);
v_isShared_6668_ = v_isSharedCheck_6672_;
goto v_resetjp_6666_;
}
v_resetjp_6666_:
{
lean_object* v___x_6670_; 
if (v_isShared_6668_ == 0)
{
v___x_6670_ = v___x_6667_;
goto v_reusejp_6669_;
}
else
{
lean_object* v_reuseFailAlloc_6671_; 
v_reuseFailAlloc_6671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6671_, 0, v_a_6665_);
v___x_6670_ = v_reuseFailAlloc_6671_;
goto v_reusejp_6669_;
}
v_reusejp_6669_:
{
return v___x_6670_;
}
}
}
}
else
{
lean_object* v_a_6673_; lean_object* v___x_6675_; uint8_t v_isShared_6676_; uint8_t v_isSharedCheck_6680_; 
lean_dec(v_a_6591_);
lean_dec(v_a_6589_);
lean_dec_ref(v_type_6577_);
lean_dec_ref(v_wfRel_6575_);
lean_dec(v___x_6574_);
v_a_6673_ = lean_ctor_get(v___x_6592_, 0);
v_isSharedCheck_6680_ = !lean_is_exclusive(v___x_6592_);
if (v_isSharedCheck_6680_ == 0)
{
v___x_6675_ = v___x_6592_;
v_isShared_6676_ = v_isSharedCheck_6680_;
goto v_resetjp_6674_;
}
else
{
lean_inc(v_a_6673_);
lean_dec(v___x_6592_);
v___x_6675_ = lean_box(0);
v_isShared_6676_ = v_isSharedCheck_6680_;
goto v_resetjp_6674_;
}
v_resetjp_6674_:
{
lean_object* v___x_6678_; 
if (v_isShared_6676_ == 0)
{
v___x_6678_ = v___x_6675_;
goto v_reusejp_6677_;
}
else
{
lean_object* v_reuseFailAlloc_6679_; 
v_reuseFailAlloc_6679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6679_, 0, v_a_6673_);
v___x_6678_ = v_reuseFailAlloc_6679_;
goto v_reusejp_6677_;
}
v_reusejp_6677_:
{
return v___x_6678_;
}
}
}
}
else
{
lean_object* v_a_6681_; lean_object* v___x_6683_; uint8_t v_isShared_6684_; uint8_t v_isSharedCheck_6688_; 
lean_dec(v_a_6589_);
lean_dec_ref(v_type_6577_);
lean_dec_ref(v_wfRel_6575_);
lean_dec(v___x_6574_);
v_a_6681_ = lean_ctor_get(v___x_6590_, 0);
v_isSharedCheck_6688_ = !lean_is_exclusive(v___x_6590_);
if (v_isSharedCheck_6688_ == 0)
{
v___x_6683_ = v___x_6590_;
v_isShared_6684_ = v_isSharedCheck_6688_;
goto v_resetjp_6682_;
}
else
{
lean_inc(v_a_6681_);
lean_dec(v___x_6590_);
v___x_6683_ = lean_box(0);
v_isShared_6684_ = v_isSharedCheck_6688_;
goto v_resetjp_6682_;
}
v_resetjp_6682_:
{
lean_object* v___x_6686_; 
if (v_isShared_6684_ == 0)
{
v___x_6686_ = v___x_6683_;
goto v_reusejp_6685_;
}
else
{
lean_object* v_reuseFailAlloc_6687_; 
v_reuseFailAlloc_6687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6687_, 0, v_a_6681_);
v___x_6686_ = v_reuseFailAlloc_6687_;
goto v_reusejp_6685_;
}
v_reusejp_6685_:
{
return v___x_6686_;
}
}
}
}
else
{
lean_object* v_a_6689_; lean_object* v___x_6691_; uint8_t v_isShared_6692_; uint8_t v_isSharedCheck_6696_; 
lean_dec_ref(v_type_6577_);
lean_dec_ref(v_wfRel_6575_);
lean_dec(v___x_6574_);
v_a_6689_ = lean_ctor_get(v___x_6588_, 0);
v_isSharedCheck_6696_ = !lean_is_exclusive(v___x_6588_);
if (v_isSharedCheck_6696_ == 0)
{
v___x_6691_ = v___x_6588_;
v_isShared_6692_ = v_isSharedCheck_6696_;
goto v_resetjp_6690_;
}
else
{
lean_inc(v_a_6689_);
lean_dec(v___x_6588_);
v___x_6691_ = lean_box(0);
v_isShared_6692_ = v_isSharedCheck_6696_;
goto v_resetjp_6690_;
}
v_resetjp_6690_:
{
lean_object* v___x_6694_; 
if (v_isShared_6692_ == 0)
{
v___x_6694_ = v___x_6691_;
goto v_reusejp_6693_;
}
else
{
lean_object* v_reuseFailAlloc_6695_; 
v_reuseFailAlloc_6695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6695_, 0, v_a_6689_);
v___x_6694_ = v_reuseFailAlloc_6695_;
goto v_reusejp_6693_;
}
v_reusejp_6693_:
{
return v___x_6694_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__0___boxed(lean_object* v___x_6697_, lean_object* v___x_6698_, lean_object* v_wfRel_6699_, lean_object* v_x_6700_, lean_object* v_type_6701_, lean_object* v___y_6702_, lean_object* v___y_6703_, lean_object* v___y_6704_, lean_object* v___y_6705_, lean_object* v___y_6706_, lean_object* v___y_6707_, lean_object* v___y_6708_){
_start:
{
lean_object* v_res_6709_; 
v_res_6709_ = l_Lean_Elab_WF_mkFix___lam__0(v___x_6697_, v___x_6698_, v_wfRel_6699_, v_x_6700_, v_type_6701_, v___y_6702_, v___y_6703_, v___y_6704_, v___y_6705_, v___y_6706_, v___y_6707_);
lean_dec(v___y_6707_);
lean_dec_ref(v___y_6706_);
lean_dec(v___y_6705_);
lean_dec_ref(v___y_6704_);
lean_dec(v___y_6703_);
lean_dec_ref(v___y_6702_);
lean_dec_ref(v_x_6700_);
lean_dec_ref(v___x_6697_);
return v_res_6709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__1(lean_object* v_prefixArgs_6710_, lean_object* v_declName_6711_, lean_object* v_x_6712_, lean_object* v_F_6713_, lean_object* v_val_6714_, lean_object* v___y_6715_, lean_object* v___y_6716_, lean_object* v___y_6717_, lean_object* v___y_6718_, lean_object* v___y_6719_, lean_object* v___y_6720_){
_start:
{
lean_object* v___x_6722_; lean_object* v___x_6723_; lean_object* v___x_6724_; 
v___x_6722_ = lean_array_get_size(v_prefixArgs_6710_);
v___x_6723_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___boxed), 11, 2);
lean_closure_set(v___x_6723_, 0, v_declName_6711_);
lean_closure_set(v___x_6723_, 1, v___x_6722_);
v___x_6724_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v_x_6712_, v_F_6713_, v_val_6714_, v___x_6723_, v___y_6715_, v___y_6716_, v___y_6717_, v___y_6718_, v___y_6719_, v___y_6720_);
return v___x_6724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__1___boxed(lean_object* v_prefixArgs_6725_, lean_object* v_declName_6726_, lean_object* v_x_6727_, lean_object* v_F_6728_, lean_object* v_val_6729_, lean_object* v___y_6730_, lean_object* v___y_6731_, lean_object* v___y_6732_, lean_object* v___y_6733_, lean_object* v___y_6734_, lean_object* v___y_6735_, lean_object* v___y_6736_){
_start:
{
lean_object* v_res_6737_; 
v_res_6737_ = l_Lean_Elab_WF_mkFix___lam__1(v_prefixArgs_6725_, v_declName_6726_, v_x_6727_, v_F_6728_, v_val_6729_, v___y_6730_, v___y_6731_, v___y_6732_, v___y_6733_, v___y_6734_, v___y_6735_);
lean_dec(v___y_6735_);
lean_dec_ref(v___y_6734_);
lean_dec(v___y_6733_);
lean_dec_ref(v___y_6732_);
lean_dec(v___y_6731_);
lean_dec_ref(v___y_6730_);
lean_dec_ref(v_prefixArgs_6725_);
return v_res_6737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__2(lean_object* v___x_6738_, lean_object* v___x_6739_, lean_object* v___x_6740_, lean_object* v___f_6741_, lean_object* v_funNames_6742_, lean_object* v_argsPacker_6743_, lean_object* v_decrTactics_6744_, uint8_t v___x_6745_, lean_object* v_fst_6746_, lean_object* v_prefixArgs_6747_, lean_object* v___y_6748_, lean_object* v___y_6749_, lean_object* v___y_6750_, lean_object* v___y_6751_, lean_object* v___y_6752_, lean_object* v___y_6753_){
_start:
{
lean_object* v___x_6755_; 
lean_inc_ref(v___x_6739_);
lean_inc_ref(v___x_6738_);
v___x_6755_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v___x_6738_, v___x_6739_, v___x_6740_, v___f_6741_, v___y_6748_, v___y_6749_, v___y_6750_, v___y_6751_, v___y_6752_, v___y_6753_);
if (lean_obj_tag(v___x_6755_) == 0)
{
lean_object* v_a_6756_; lean_object* v___x_6757_; 
v_a_6756_ = lean_ctor_get(v___x_6755_, 0);
lean_inc(v_a_6756_);
lean_dec_ref_known(v___x_6755_, 1);
v___x_6757_ = l_Lean_Elab_WF_solveDecreasingGoals(v_funNames_6742_, v_argsPacker_6743_, v_decrTactics_6744_, v_a_6756_, v___y_6750_, v___y_6751_, v___y_6752_, v___y_6753_);
if (lean_obj_tag(v___x_6757_) == 0)
{
lean_object* v_a_6758_; lean_object* v___x_6759_; lean_object* v___x_6760_; lean_object* v___x_6761_; lean_object* v___x_6762_; uint8_t v___x_6763_; uint8_t v___x_6764_; lean_object* v___x_6765_; 
v_a_6758_ = lean_ctor_get(v___x_6757_, 0);
lean_inc(v_a_6758_);
lean_dec_ref_known(v___x_6757_, 1);
v___x_6759_ = lean_unsigned_to_nat(2u);
v___x_6760_ = lean_mk_empty_array_with_capacity(v___x_6759_);
v___x_6761_ = lean_array_push(v___x_6760_, v___x_6738_);
v___x_6762_ = lean_array_push(v___x_6761_, v___x_6739_);
v___x_6763_ = 1;
v___x_6764_ = 1;
v___x_6765_ = l_Lean_Meta_mkLambdaFVars(v___x_6762_, v_a_6758_, v___x_6745_, v___x_6763_, v___x_6745_, v___x_6763_, v___x_6764_, v___y_6750_, v___y_6751_, v___y_6752_, v___y_6753_);
lean_dec_ref(v___x_6762_);
if (lean_obj_tag(v___x_6765_) == 0)
{
lean_object* v_a_6766_; lean_object* v___x_6767_; lean_object* v___x_6768_; 
v_a_6766_ = lean_ctor_get(v___x_6765_, 0);
lean_inc(v_a_6766_);
lean_dec_ref_known(v___x_6765_, 1);
v___x_6767_ = l_Lean_Expr_app___override(v_fst_6746_, v_a_6766_);
v___x_6768_ = l_Lean_Meta_mkLambdaFVars(v_prefixArgs_6747_, v___x_6767_, v___x_6745_, v___x_6763_, v___x_6745_, v___x_6763_, v___x_6764_, v___y_6750_, v___y_6751_, v___y_6752_, v___y_6753_);
return v___x_6768_;
}
else
{
lean_dec_ref(v_fst_6746_);
return v___x_6765_;
}
}
else
{
lean_dec_ref(v_fst_6746_);
lean_dec_ref(v___x_6739_);
lean_dec_ref(v___x_6738_);
return v___x_6757_;
}
}
else
{
lean_dec_ref(v_fst_6746_);
lean_dec_ref(v_decrTactics_6744_);
lean_dec_ref(v_argsPacker_6743_);
lean_dec_ref(v_funNames_6742_);
lean_dec_ref(v___x_6739_);
lean_dec_ref(v___x_6738_);
return v___x_6755_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__2___boxed(lean_object** _args){
lean_object* v___x_6769_ = _args[0];
lean_object* v___x_6770_ = _args[1];
lean_object* v___x_6771_ = _args[2];
lean_object* v___f_6772_ = _args[3];
lean_object* v_funNames_6773_ = _args[4];
lean_object* v_argsPacker_6774_ = _args[5];
lean_object* v_decrTactics_6775_ = _args[6];
lean_object* v___x_6776_ = _args[7];
lean_object* v_fst_6777_ = _args[8];
lean_object* v_prefixArgs_6778_ = _args[9];
lean_object* v___y_6779_ = _args[10];
lean_object* v___y_6780_ = _args[11];
lean_object* v___y_6781_ = _args[12];
lean_object* v___y_6782_ = _args[13];
lean_object* v___y_6783_ = _args[14];
lean_object* v___y_6784_ = _args[15];
lean_object* v___y_6785_ = _args[16];
_start:
{
uint8_t v___x_5938__boxed_6786_; lean_object* v_res_6787_; 
v___x_5938__boxed_6786_ = lean_unbox(v___x_6776_);
v_res_6787_ = l_Lean_Elab_WF_mkFix___lam__2(v___x_6769_, v___x_6770_, v___x_6771_, v___f_6772_, v_funNames_6773_, v_argsPacker_6774_, v_decrTactics_6775_, v___x_5938__boxed_6786_, v_fst_6777_, v_prefixArgs_6778_, v___y_6779_, v___y_6780_, v___y_6781_, v___y_6782_, v___y_6783_, v___y_6784_);
lean_dec(v___y_6784_);
lean_dec_ref(v___y_6783_);
lean_dec(v___y_6782_);
lean_dec_ref(v___y_6781_);
lean_dec(v___y_6780_);
lean_dec_ref(v___y_6779_);
lean_dec_ref(v_prefixArgs_6778_);
return v_res_6787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__3(lean_object* v___x_6788_, lean_object* v_snd_6789_, lean_object* v___x_6790_, lean_object* v_prefixArgs_6791_, lean_object* v_value_6792_, lean_object* v___f_6793_, lean_object* v_funNames_6794_, lean_object* v_argsPacker_6795_, lean_object* v_decrTactics_6796_, uint8_t v___x_6797_, lean_object* v_fst_6798_, lean_object* v_xs_6799_, lean_object* v_x_6800_, lean_object* v___y_6801_, lean_object* v___y_6802_, lean_object* v___y_6803_, lean_object* v___y_6804_, lean_object* v___y_6805_, lean_object* v___y_6806_){
_start:
{
lean_object* v_lctx_6808_; lean_object* v___x_6809_; lean_object* v___x_6810_; lean_object* v___x_6811_; lean_object* v___x_6812_; lean_object* v___x_6813_; lean_object* v___x_6814_; lean_object* v___x_6815_; lean_object* v___x_6816_; lean_object* v___f_6817_; lean_object* v___x_6818_; 
v_lctx_6808_ = lean_ctor_get(v___y_6803_, 2);
v___x_6809_ = lean_unsigned_to_nat(0u);
v___x_6810_ = lean_array_get_borrowed(v___x_6788_, v_xs_6799_, v___x_6809_);
v___x_6811_ = l_Lean_Expr_fvarId_x21(v___x_6810_);
lean_inc_ref(v_lctx_6808_);
v___x_6812_ = l_Lean_LocalContext_setUserName(v_lctx_6808_, v___x_6811_, v_snd_6789_);
v___x_6813_ = lean_array_get_borrowed(v___x_6788_, v_xs_6799_, v___x_6790_);
lean_inc_n(v___x_6810_, 2);
lean_inc_ref(v_prefixArgs_6791_);
v___x_6814_ = lean_array_push(v_prefixArgs_6791_, v___x_6810_);
v___x_6815_ = l_Lean_Expr_beta(v_value_6792_, v___x_6814_);
v___x_6816_ = lean_box(v___x_6797_);
lean_inc(v___x_6813_);
v___f_6817_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__2___boxed), 17, 10);
lean_closure_set(v___f_6817_, 0, v___x_6810_);
lean_closure_set(v___f_6817_, 1, v___x_6813_);
lean_closure_set(v___f_6817_, 2, v___x_6815_);
lean_closure_set(v___f_6817_, 3, v___f_6793_);
lean_closure_set(v___f_6817_, 4, v_funNames_6794_);
lean_closure_set(v___f_6817_, 5, v_argsPacker_6795_);
lean_closure_set(v___f_6817_, 6, v_decrTactics_6796_);
lean_closure_set(v___f_6817_, 7, v___x_6816_);
lean_closure_set(v___f_6817_, 8, v_fst_6798_);
lean_closure_set(v___f_6817_, 9, v_prefixArgs_6791_);
v___x_6818_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v___x_6812_, v___f_6817_, v___y_6801_, v___y_6802_, v___y_6803_, v___y_6804_, v___y_6805_, v___y_6806_);
return v___x_6818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__3___boxed(lean_object** _args){
lean_object* v___x_6819_ = _args[0];
lean_object* v_snd_6820_ = _args[1];
lean_object* v___x_6821_ = _args[2];
lean_object* v_prefixArgs_6822_ = _args[3];
lean_object* v_value_6823_ = _args[4];
lean_object* v___f_6824_ = _args[5];
lean_object* v_funNames_6825_ = _args[6];
lean_object* v_argsPacker_6826_ = _args[7];
lean_object* v_decrTactics_6827_ = _args[8];
lean_object* v___x_6828_ = _args[9];
lean_object* v_fst_6829_ = _args[10];
lean_object* v_xs_6830_ = _args[11];
lean_object* v_x_6831_ = _args[12];
lean_object* v___y_6832_ = _args[13];
lean_object* v___y_6833_ = _args[14];
lean_object* v___y_6834_ = _args[15];
lean_object* v___y_6835_ = _args[16];
lean_object* v___y_6836_ = _args[17];
lean_object* v___y_6837_ = _args[18];
lean_object* v___y_6838_ = _args[19];
_start:
{
uint8_t v___x_6008__boxed_6839_; lean_object* v_res_6840_; 
v___x_6008__boxed_6839_ = lean_unbox(v___x_6828_);
v_res_6840_ = l_Lean_Elab_WF_mkFix___lam__3(v___x_6819_, v_snd_6820_, v___x_6821_, v_prefixArgs_6822_, v_value_6823_, v___f_6824_, v_funNames_6825_, v_argsPacker_6826_, v_decrTactics_6827_, v___x_6008__boxed_6839_, v_fst_6829_, v_xs_6830_, v_x_6831_, v___y_6832_, v___y_6833_, v___y_6834_, v___y_6835_, v___y_6836_, v___y_6837_);
lean_dec(v___y_6837_);
lean_dec_ref(v___y_6836_);
lean_dec(v___y_6835_);
lean_dec_ref(v___y_6834_);
lean_dec(v___y_6833_);
lean_dec_ref(v___y_6832_);
lean_dec_ref(v_x_6831_);
lean_dec_ref(v_xs_6830_);
lean_dec(v___x_6821_);
lean_dec_ref(v___x_6819_);
return v_res_6840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix(lean_object* v_preDef_6845_, lean_object* v_prefixArgs_6846_, lean_object* v_argsPacker_6847_, lean_object* v_wfRel_6848_, lean_object* v_funNames_6849_, lean_object* v_decrTactics_6850_, lean_object* v_a_6851_, lean_object* v_a_6852_, lean_object* v_a_6853_, lean_object* v_a_6854_, lean_object* v_a_6855_, lean_object* v_a_6856_){
_start:
{
lean_object* v_declName_6858_; lean_object* v_type_6859_; lean_object* v_value_6860_; lean_object* v___x_6861_; 
v_declName_6858_ = lean_ctor_get(v_preDef_6845_, 3);
lean_inc(v_declName_6858_);
v_type_6859_ = lean_ctor_get(v_preDef_6845_, 6);
lean_inc_ref(v_type_6859_);
v_value_6860_ = lean_ctor_get(v_preDef_6845_, 7);
lean_inc_ref(v_value_6860_);
lean_dec_ref(v_preDef_6845_);
v___x_6861_ = l_Lean_Meta_instantiateForall(v_type_6859_, v_prefixArgs_6846_, v_a_6853_, v_a_6854_, v_a_6855_, v_a_6856_);
if (lean_obj_tag(v___x_6861_) == 0)
{
lean_object* v_a_6862_; lean_object* v___x_6863_; lean_object* v___x_6864_; lean_object* v___f_6865_; lean_object* v___x_6866_; uint8_t v___x_6867_; lean_object* v___x_6868_; 
v_a_6862_ = lean_ctor_get(v___x_6861_, 0);
lean_inc(v_a_6862_);
lean_dec_ref_known(v___x_6861_, 1);
v___x_6863_ = l_Lean_instInhabitedExpr;
v___x_6864_ = lean_unsigned_to_nat(1u);
v___f_6865_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__0___boxed), 12, 3);
lean_closure_set(v___f_6865_, 0, v___x_6863_);
lean_closure_set(v___f_6865_, 1, v___x_6864_);
lean_closure_set(v___f_6865_, 2, v_wfRel_6848_);
v___x_6866_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___closed__0));
v___x_6867_ = 0;
v___x_6868_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_a_6862_, v___x_6866_, v___f_6865_, v___x_6867_, v___x_6867_, v_a_6851_, v_a_6852_, v_a_6853_, v_a_6854_, v_a_6855_, v_a_6856_);
if (lean_obj_tag(v___x_6868_) == 0)
{
lean_object* v_a_6869_; lean_object* v_fst_6870_; lean_object* v_snd_6871_; lean_object* v___x_6872_; 
v_a_6869_ = lean_ctor_get(v___x_6868_, 0);
lean_inc(v_a_6869_);
lean_dec_ref_known(v___x_6868_, 1);
v_fst_6870_ = lean_ctor_get(v_a_6869_, 0);
lean_inc_n(v_fst_6870_, 2);
v_snd_6871_ = lean_ctor_get(v_a_6869_, 1);
lean_inc(v_snd_6871_);
lean_dec(v_a_6869_);
lean_inc(v_a_6856_);
lean_inc_ref(v_a_6855_);
lean_inc(v_a_6854_);
lean_inc_ref(v_a_6853_);
v___x_6872_ = lean_infer_type(v_fst_6870_, v_a_6853_, v_a_6854_, v_a_6855_, v_a_6856_);
if (lean_obj_tag(v___x_6872_) == 0)
{
lean_object* v_a_6873_; lean_object* v___x_6874_; 
v_a_6873_ = lean_ctor_get(v___x_6872_, 0);
lean_inc(v_a_6873_);
lean_dec_ref_known(v___x_6872_, 1);
lean_inc(v_a_6856_);
lean_inc_ref(v_a_6855_);
lean_inc(v_a_6854_);
lean_inc_ref(v_a_6853_);
v___x_6874_ = lean_whnf(v_a_6873_, v_a_6853_, v_a_6854_, v_a_6855_, v_a_6856_);
if (lean_obj_tag(v___x_6874_) == 0)
{
lean_object* v_a_6875_; lean_object* v___f_6876_; lean_object* v___x_6877_; lean_object* v___f_6878_; lean_object* v___x_6879_; lean_object* v___x_6880_; lean_object* v___x_6881_; 
v_a_6875_ = lean_ctor_get(v___x_6874_, 0);
lean_inc(v_a_6875_);
lean_dec_ref_known(v___x_6874_, 1);
lean_inc_ref(v_prefixArgs_6846_);
v___f_6876_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__1___boxed), 12, 2);
lean_closure_set(v___f_6876_, 0, v_prefixArgs_6846_);
lean_closure_set(v___f_6876_, 1, v_declName_6858_);
v___x_6877_ = lean_box(v___x_6867_);
v___f_6878_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__3___boxed), 20, 11);
lean_closure_set(v___f_6878_, 0, v___x_6863_);
lean_closure_set(v___f_6878_, 1, v_snd_6871_);
lean_closure_set(v___f_6878_, 2, v___x_6864_);
lean_closure_set(v___f_6878_, 3, v_prefixArgs_6846_);
lean_closure_set(v___f_6878_, 4, v_value_6860_);
lean_closure_set(v___f_6878_, 5, v___f_6876_);
lean_closure_set(v___f_6878_, 6, v_funNames_6849_);
lean_closure_set(v___f_6878_, 7, v_argsPacker_6847_);
lean_closure_set(v___f_6878_, 8, v_decrTactics_6850_);
lean_closure_set(v___f_6878_, 9, v___x_6877_);
lean_closure_set(v___f_6878_, 10, v_fst_6870_);
v___x_6879_ = l_Lean_Expr_bindingDomain_x21(v_a_6875_);
lean_dec(v_a_6875_);
v___x_6880_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___closed__1));
v___x_6881_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v___x_6879_, v___x_6880_, v___f_6878_, v___x_6867_, v___x_6867_, v_a_6851_, v_a_6852_, v_a_6853_, v_a_6854_, v_a_6855_, v_a_6856_);
return v___x_6881_;
}
else
{
lean_dec(v_snd_6871_);
lean_dec(v_fst_6870_);
lean_dec_ref(v_value_6860_);
lean_dec(v_declName_6858_);
lean_dec_ref(v_decrTactics_6850_);
lean_dec_ref(v_funNames_6849_);
lean_dec_ref(v_argsPacker_6847_);
lean_dec_ref(v_prefixArgs_6846_);
return v___x_6874_;
}
}
else
{
lean_dec(v_snd_6871_);
lean_dec(v_fst_6870_);
lean_dec_ref(v_value_6860_);
lean_dec(v_declName_6858_);
lean_dec_ref(v_decrTactics_6850_);
lean_dec_ref(v_funNames_6849_);
lean_dec_ref(v_argsPacker_6847_);
lean_dec_ref(v_prefixArgs_6846_);
return v___x_6872_;
}
}
else
{
lean_object* v_a_6882_; lean_object* v___x_6884_; uint8_t v_isShared_6885_; uint8_t v_isSharedCheck_6889_; 
lean_dec_ref(v_value_6860_);
lean_dec(v_declName_6858_);
lean_dec_ref(v_decrTactics_6850_);
lean_dec_ref(v_funNames_6849_);
lean_dec_ref(v_argsPacker_6847_);
lean_dec_ref(v_prefixArgs_6846_);
v_a_6882_ = lean_ctor_get(v___x_6868_, 0);
v_isSharedCheck_6889_ = !lean_is_exclusive(v___x_6868_);
if (v_isSharedCheck_6889_ == 0)
{
v___x_6884_ = v___x_6868_;
v_isShared_6885_ = v_isSharedCheck_6889_;
goto v_resetjp_6883_;
}
else
{
lean_inc(v_a_6882_);
lean_dec(v___x_6868_);
v___x_6884_ = lean_box(0);
v_isShared_6885_ = v_isSharedCheck_6889_;
goto v_resetjp_6883_;
}
v_resetjp_6883_:
{
lean_object* v___x_6887_; 
if (v_isShared_6885_ == 0)
{
v___x_6887_ = v___x_6884_;
goto v_reusejp_6886_;
}
else
{
lean_object* v_reuseFailAlloc_6888_; 
v_reuseFailAlloc_6888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6888_, 0, v_a_6882_);
v___x_6887_ = v_reuseFailAlloc_6888_;
goto v_reusejp_6886_;
}
v_reusejp_6886_:
{
return v___x_6887_;
}
}
}
}
else
{
lean_dec_ref(v_value_6860_);
lean_dec(v_declName_6858_);
lean_dec_ref(v_decrTactics_6850_);
lean_dec_ref(v_funNames_6849_);
lean_dec_ref(v_wfRel_6848_);
lean_dec_ref(v_argsPacker_6847_);
lean_dec_ref(v_prefixArgs_6846_);
return v___x_6861_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___boxed(lean_object* v_preDef_6890_, lean_object* v_prefixArgs_6891_, lean_object* v_argsPacker_6892_, lean_object* v_wfRel_6893_, lean_object* v_funNames_6894_, lean_object* v_decrTactics_6895_, lean_object* v_a_6896_, lean_object* v_a_6897_, lean_object* v_a_6898_, lean_object* v_a_6899_, lean_object* v_a_6900_, lean_object* v_a_6901_, lean_object* v_a_6902_){
_start:
{
lean_object* v_res_6903_; 
v_res_6903_ = l_Lean_Elab_WF_mkFix(v_preDef_6890_, v_prefixArgs_6891_, v_argsPacker_6892_, v_wfRel_6893_, v_funNames_6894_, v_decrTactics_6895_, v_a_6896_, v_a_6897_, v_a_6898_, v_a_6899_, v_a_6900_, v_a_6901_);
lean_dec(v_a_6901_);
lean_dec_ref(v_a_6900_);
lean_dec(v_a_6899_);
lean_dec_ref(v_a_6898_);
lean_dec(v_a_6897_);
lean_dec_ref(v_a_6896_);
return v_res_6903_;
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
