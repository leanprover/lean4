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
v___x_274_ = lean_st_ref_take(v_a_272_);
v___x_275_ = lean_unsigned_to_nat(1u);
v___x_276_ = lean_mk_empty_array_with_capacity(v___x_275_);
v___x_277_ = lean_array_push(v___x_276_, v_recFnName_270_);
v___x_278_ = l_Lean_HasConstCache_containsUnsafe(v___x_277_, v_e_271_, v___x_274_);
lean_dec_ref(v___x_277_);
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
lean_object* v___x_348_; double v___x_349_; uint8_t v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_358_; 
v___x_348_ = lean_box(0);
v___x_349_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0);
v___x_350_ = 0;
v___x_351_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__1));
v___x_352_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_352_, 0, v_cls_317_);
lean_ctor_set(v___x_352_, 1, v___x_348_);
lean_ctor_set(v___x_352_, 2, v___x_351_);
lean_ctor_set_float(v___x_352_, sizeof(void*)*3, v___x_349_);
lean_ctor_set_float(v___x_352_, sizeof(void*)*3 + 8, v___x_349_);
lean_ctor_set_uint8(v___x_352_, sizeof(void*)*3 + 16, v___x_350_);
v___x_353_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__2));
v___x_354_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_354_, 0, v___x_352_);
lean_ctor_set(v___x_354_, 1, v_a_326_);
lean_ctor_set(v___x_354_, 2, v___x_353_);
lean_inc(v_ref_324_);
v___x_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_355_, 0, v_ref_324_);
lean_ctor_set(v___x_355_, 1, v___x_354_);
v___x_356_ = l_Lean_PersistentArray_push___redArg(v_traces_344_, v___x_355_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 0, v___x_356_);
v___x_358_ = v___x_346_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v___x_356_);
lean_ctor_set_uint64(v_reuseFailAlloc_367_, sizeof(void*)*1, v_tid_343_);
v___x_358_ = v_reuseFailAlloc_367_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
lean_object* v___x_360_; 
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 4, v___x_358_);
v___x_360_ = v___x_341_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_env_332_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v_nextMacroScope_333_);
lean_ctor_set(v_reuseFailAlloc_366_, 2, v_ngen_334_);
lean_ctor_set(v_reuseFailAlloc_366_, 3, v_auxDeclNGen_335_);
lean_ctor_set(v_reuseFailAlloc_366_, 4, v___x_358_);
lean_ctor_set(v_reuseFailAlloc_366_, 5, v_cache_336_);
lean_ctor_set(v_reuseFailAlloc_366_, 6, v_messages_337_);
lean_ctor_set(v_reuseFailAlloc_366_, 7, v_infoState_338_);
lean_ctor_set(v_reuseFailAlloc_366_, 8, v_snapshotTasks_339_);
v___x_360_ = v_reuseFailAlloc_366_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_364_; 
v___x_361_ = lean_st_ref_put(v___y_322_, v___x_360_);
v___x_362_ = lean_box(0);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 0, v___x_362_);
v___x_364_ = v___x_328_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_362_);
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
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v_nbuckets_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_420_ = lean_array_get_size(v_data_419_);
v___x_421_ = lean_unsigned_to_nat(2u);
v_nbuckets_422_ = lean_nat_mul(v___x_420_, v___x_421_);
v___x_423_ = lean_unsigned_to_nat(0u);
v___x_424_ = lean_box(0);
v___x_425_ = lean_mk_array(v_nbuckets_422_, v___x_424_);
v___x_426_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12___redArg(v___x_423_, v_data_419_, v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg(lean_object* v_a_427_, lean_object* v_x_428_){
_start:
{
if (lean_obj_tag(v_x_428_) == 0)
{
uint8_t v___x_429_; 
v___x_429_ = 0;
return v___x_429_;
}
else
{
lean_object* v_key_430_; lean_object* v_tail_431_; uint8_t v___x_432_; 
v_key_430_ = lean_ctor_get(v_x_428_, 0);
v_tail_431_ = lean_ctor_get(v_x_428_, 2);
v___x_432_ = lean_expr_eqv(v_key_430_, v_a_427_);
if (v___x_432_ == 0)
{
v_x_428_ = v_tail_431_;
goto _start;
}
else
{
return v___x_432_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg___boxed(lean_object* v_a_434_, lean_object* v_x_435_){
_start:
{
uint8_t v_res_436_; lean_object* v_r_437_; 
v_res_436_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg(v_a_434_, v_x_435_);
lean_dec(v_x_435_);
lean_dec_ref(v_a_434_);
v_r_437_ = lean_box(v_res_436_);
return v_r_437_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6___redArg(lean_object* v_a_438_, lean_object* v_b_439_, lean_object* v_x_440_){
_start:
{
if (lean_obj_tag(v_x_440_) == 0)
{
lean_dec(v_b_439_);
lean_dec_ref(v_a_438_);
return v_x_440_;
}
else
{
lean_object* v_key_441_; lean_object* v_value_442_; lean_object* v_tail_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_455_; 
v_key_441_ = lean_ctor_get(v_x_440_, 0);
v_value_442_ = lean_ctor_get(v_x_440_, 1);
v_tail_443_ = lean_ctor_get(v_x_440_, 2);
v_isSharedCheck_455_ = !lean_is_exclusive(v_x_440_);
if (v_isSharedCheck_455_ == 0)
{
v___x_445_ = v_x_440_;
v_isShared_446_ = v_isSharedCheck_455_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_tail_443_);
lean_inc(v_value_442_);
lean_inc(v_key_441_);
lean_dec(v_x_440_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_455_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
uint8_t v___x_447_; 
v___x_447_ = lean_expr_eqv(v_key_441_, v_a_438_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; lean_object* v___x_450_; 
v___x_448_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6___redArg(v_a_438_, v_b_439_, v_tail_443_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 2, v___x_448_);
v___x_450_ = v___x_445_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_key_441_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v_value_442_);
lean_ctor_set(v_reuseFailAlloc_451_, 2, v___x_448_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
else
{
lean_object* v___x_453_; 
lean_dec(v_value_442_);
lean_dec(v_key_441_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 1, v_b_439_);
lean_ctor_set(v___x_445_, 0, v_a_438_);
v___x_453_ = v___x_445_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_438_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_b_439_);
lean_ctor_set(v_reuseFailAlloc_454_, 2, v_tail_443_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4___redArg(lean_object* v_m_456_, lean_object* v_a_457_, lean_object* v_b_458_){
_start:
{
lean_object* v_size_459_; lean_object* v_buckets_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_503_; 
v_size_459_ = lean_ctor_get(v_m_456_, 0);
v_buckets_460_ = lean_ctor_get(v_m_456_, 1);
v_isSharedCheck_503_ = !lean_is_exclusive(v_m_456_);
if (v_isSharedCheck_503_ == 0)
{
v___x_462_ = v_m_456_;
v_isShared_463_ = v_isSharedCheck_503_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_buckets_460_);
lean_inc(v_size_459_);
lean_dec(v_m_456_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_503_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_464_; uint64_t v___x_465_; uint64_t v___x_466_; uint64_t v___x_467_; uint64_t v_fold_468_; uint64_t v___x_469_; uint64_t v___x_470_; uint64_t v___x_471_; size_t v___x_472_; size_t v___x_473_; size_t v___x_474_; size_t v___x_475_; size_t v___x_476_; lean_object* v_bkt_477_; uint8_t v___x_478_; 
v___x_464_ = lean_array_get_size(v_buckets_460_);
v___x_465_ = l_Lean_Expr_hash(v_a_457_);
v___x_466_ = 32ULL;
v___x_467_ = lean_uint64_shift_right(v___x_465_, v___x_466_);
v_fold_468_ = lean_uint64_xor(v___x_465_, v___x_467_);
v___x_469_ = 16ULL;
v___x_470_ = lean_uint64_shift_right(v_fold_468_, v___x_469_);
v___x_471_ = lean_uint64_xor(v_fold_468_, v___x_470_);
v___x_472_ = lean_uint64_to_usize(v___x_471_);
v___x_473_ = lean_usize_of_nat(v___x_464_);
v___x_474_ = ((size_t)1ULL);
v___x_475_ = lean_usize_sub(v___x_473_, v___x_474_);
v___x_476_ = lean_usize_land(v___x_472_, v___x_475_);
v_bkt_477_ = lean_array_uget_borrowed(v_buckets_460_, v___x_476_);
v___x_478_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg(v_a_457_, v_bkt_477_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; lean_object* v_size_x27_480_; lean_object* v___x_481_; lean_object* v_buckets_x27_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_479_ = lean_unsigned_to_nat(1u);
v_size_x27_480_ = lean_nat_add(v_size_459_, v___x_479_);
lean_dec(v_size_459_);
lean_inc(v_bkt_477_);
v___x_481_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_481_, 0, v_a_457_);
lean_ctor_set(v___x_481_, 1, v_b_458_);
lean_ctor_set(v___x_481_, 2, v_bkt_477_);
v_buckets_x27_482_ = lean_array_uset(v_buckets_460_, v___x_476_, v___x_481_);
v___x_483_ = lean_unsigned_to_nat(4u);
v___x_484_ = lean_nat_mul(v_size_x27_480_, v___x_483_);
v___x_485_ = lean_unsigned_to_nat(3u);
v___x_486_ = lean_nat_div(v___x_484_, v___x_485_);
lean_dec(v___x_484_);
v___x_487_ = lean_array_get_size(v_buckets_x27_482_);
v___x_488_ = lean_nat_dec_le(v___x_486_, v___x_487_);
lean_dec(v___x_486_);
if (v___x_488_ == 0)
{
lean_object* v_val_489_; lean_object* v___x_491_; 
v_val_489_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5___redArg(v_buckets_x27_482_);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 1, v_val_489_);
lean_ctor_set(v___x_462_, 0, v_size_x27_480_);
v___x_491_ = v___x_462_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_size_x27_480_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_val_489_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
else
{
lean_object* v___x_494_; 
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 1, v_buckets_x27_482_);
lean_ctor_set(v___x_462_, 0, v_size_x27_480_);
v___x_494_ = v___x_462_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_size_x27_480_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_buckets_x27_482_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
else
{
lean_object* v___x_496_; lean_object* v_buckets_x27_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_501_; 
lean_inc(v_bkt_477_);
v___x_496_ = lean_box(0);
v_buckets_x27_497_ = lean_array_uset(v_buckets_460_, v___x_476_, v___x_496_);
v___x_498_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6___redArg(v_a_457_, v_b_458_, v_bkt_477_);
v___x_499_ = lean_array_uset(v_buckets_x27_497_, v___x_476_, v___x_498_);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 1, v___x_499_);
v___x_501_ = v___x_462_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_size_459_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v___x_499_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(lean_object* v_msg_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v_ref_510_; lean_object* v___x_511_; lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_520_; 
v_ref_510_ = lean_ctor_get(v___y_507_, 2);
v___x_511_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
v_a_512_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_520_ == 0)
{
v___x_514_ = v___x_511_;
v_isShared_515_ = v_isSharedCheck_520_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_511_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_520_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_516_; lean_object* v___x_518_; 
lean_inc(v_ref_510_);
v___x_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_516_, 0, v_ref_510_);
lean_ctor_set(v___x_516_, 1, v_a_512_);
if (v_isShared_515_ == 0)
{
lean_ctor_set_tag(v___x_514_, 1);
lean_ctor_set(v___x_514_, 0, v___x_516_);
v___x_518_ = v___x_514_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_516_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg___boxed(lean_object* v_msg_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v_msg_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
return v_res_527_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__1(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__0));
v___x_530_ = l_Lean_stringToMessageData(v___x_529_);
return v___x_530_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__2));
v___x_533_ = l_Lean_stringToMessageData(v___x_532_);
return v___x_533_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__5(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__4));
v___x_536_ = l_Lean_stringToMessageData(v___x_535_);
return v___x_536_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__7(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__6));
v___x_539_ = l_Lean_stringToMessageData(v___x_538_);
return v___x_539_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__9(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__8));
v___x_542_ = l_Lean_stringToMessageData(v___x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0(lean_object* v_a_543_, lean_object* v_e_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v___y_562_; lean_object* v___x_636_; 
lean_inc_ref(v_a_543_);
v___x_636_ = l_Lean_Meta_isTypeCorrect(v_a_543_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; uint8_t v___x_638_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_a_637_);
lean_dec_ref_known(v___x_636_, 1);
v___x_638_ = lean_unbox(v_a_637_);
lean_dec(v_a_637_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_639_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__9, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__9);
lean_inc_ref(v_e_544_);
v___x_640_ = l_Lean_indentExpr(v_e_544_);
v___x_641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_639_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3);
v___x_643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_641_);
lean_ctor_set(v___x_643_, 1, v___x_642_);
lean_inc_ref(v_a_543_);
v___x_644_ = l_Lean_indentExpr(v_a_543_);
v___x_645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_645_, 0, v___x_643_);
lean_ctor_set(v___x_645_, 1, v___x_644_);
v___x_646_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v___x_645_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_dec_ref_known(v___x_646_, 1);
v___y_555_ = v___y_545_;
v___y_556_ = v___y_546_;
v___y_557_ = v___y_547_;
v___y_558_ = v___y_548_;
v___y_559_ = v___y_549_;
v___y_560_ = v___y_550_;
v___y_561_ = v___y_551_;
v___y_562_ = v___y_552_;
goto v___jp_554_;
}
else
{
lean_dec_ref(v_e_544_);
lean_dec_ref(v_a_543_);
return v___x_646_;
}
}
else
{
v___y_555_ = v___y_545_;
v___y_556_ = v___y_546_;
v___y_557_ = v___y_547_;
v___y_558_ = v___y_548_;
v___y_559_ = v___y_549_;
v___y_560_ = v___y_550_;
v___y_561_ = v___y_551_;
v___y_562_ = v___y_552_;
goto v___jp_554_;
}
}
else
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
lean_dec_ref(v_e_544_);
lean_dec_ref(v_a_543_);
v_a_647_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_636_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_636_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_647_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
v___jp_554_:
{
lean_object* v___x_563_; 
lean_inc(v___y_562_);
lean_inc_ref(v___y_561_);
lean_inc(v___y_560_);
lean_inc_ref(v___y_559_);
lean_inc_ref(v_e_544_);
v___x_563_ = lean_infer_type(v_e_544_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_564_; lean_object* v___x_565_; 
v_a_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_a_564_);
lean_dec_ref_known(v___x_563_, 1);
lean_inc(v___y_562_);
lean_inc_ref(v___y_561_);
lean_inc(v___y_560_);
lean_inc_ref(v___y_559_);
lean_inc_ref(v_a_543_);
v___x_565_ = lean_infer_type(v_a_543_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_a_566_; lean_object* v___x_567_; 
v_a_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc_n(v_a_566_, 2);
lean_dec_ref_known(v___x_565_, 1);
lean_inc(v_a_564_);
v___x_567_ = l_Lean_Meta_isExprDefEq(v_a_564_, v_a_566_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_611_; 
v_a_568_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_611_ == 0)
{
v___x_570_ = v___x_567_;
v_isShared_571_ = v_isSharedCheck_611_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_567_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_611_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
uint8_t v___x_572_; 
v___x_572_ = lean_unbox(v_a_568_);
lean_dec(v_a_568_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; 
lean_del_object(v___x_570_);
v___x_573_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_a_564_, v_a_566_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_a_574_; lean_object* v_fst_575_; lean_object* v_snd_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_598_; 
v_a_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc(v_a_574_);
lean_dec_ref_known(v___x_573_, 1);
v_fst_575_ = lean_ctor_get(v_a_574_, 0);
v_snd_576_ = lean_ctor_get(v_a_574_, 1);
v_isSharedCheck_598_ = !lean_is_exclusive(v_a_574_);
if (v_isSharedCheck_598_ == 0)
{
v___x_578_ = v_a_574_;
v_isShared_579_ = v_isSharedCheck_598_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_snd_576_);
lean_inc(v_fst_575_);
lean_dec(v_a_574_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_598_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_583_; 
v___x_580_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__1);
v___x_581_ = l_Lean_indentExpr(v_e_544_);
if (v_isShared_579_ == 0)
{
lean_ctor_set_tag(v___x_578_, 7);
lean_ctor_set(v___x_578_, 1, v___x_581_);
lean_ctor_set(v___x_578_, 0, v___x_580_);
v___x_583_ = v___x_578_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_580_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v___x_581_);
v___x_583_ = v_reuseFailAlloc_597_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_584_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3);
v___x_585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_583_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
v___x_586_ = l_Lean_indentExpr(v_a_543_);
v___x_587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_585_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
v___x_588_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__5);
v___x_589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_587_);
lean_ctor_set(v___x_589_, 1, v___x_588_);
v___x_590_ = l_Lean_indentExpr(v_fst_575_);
v___x_591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_589_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
v___x_592_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__7, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__7);
v___x_593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_591_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
v___x_594_ = l_Lean_indentExpr(v_snd_576_);
v___x_595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_593_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
v___x_596_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v___x_595_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
return v___x_596_;
}
}
}
else
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_606_; 
lean_dec_ref(v_e_544_);
lean_dec_ref(v_a_543_);
v_a_599_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_606_ == 0)
{
v___x_601_ = v___x_573_;
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_573_);
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
lean_object* v___x_607_; lean_object* v___x_609_; 
lean_dec(v_a_566_);
lean_dec(v_a_564_);
lean_dec_ref(v_e_544_);
lean_dec_ref(v_a_543_);
v___x_607_ = lean_box(0);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v___x_607_);
v___x_609_ = v___x_570_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_607_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
else
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_619_; 
lean_dec(v_a_566_);
lean_dec(v_a_564_);
lean_dec_ref(v_e_544_);
lean_dec_ref(v_a_543_);
v_a_612_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_619_ == 0)
{
v___x_614_ = v___x_567_;
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_567_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_617_; 
if (v_isShared_615_ == 0)
{
v___x_617_ = v___x_614_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
else
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
lean_dec(v_a_564_);
lean_dec_ref(v_e_544_);
lean_dec_ref(v_a_543_);
v_a_620_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_627_ == 0)
{
v___x_622_ = v___x_565_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_565_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
else
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
lean_dec_ref(v_e_544_);
lean_dec_ref(v_a_543_);
v_a_628_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_635_ == 0)
{
v___x_630_ = v___x_563_;
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_563_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
if (v_isShared_631_ == 0)
{
v___x_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_628_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___boxed(lean_object* v_a_655_, lean_object* v_e_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0(v_a_655_, v_e_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec(v___y_657_);
return v_res_666_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0(void){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_667_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0);
v___x_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
return v___x_669_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__2(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_670_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1);
v___x_671_ = lean_unsigned_to_nat(0u);
v___x_672_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
lean_ctor_set(v___x_672_, 1, v___x_671_);
lean_ctor_set(v___x_672_, 2, v___x_671_);
lean_ctor_set(v___x_672_, 3, v___x_671_);
lean_ctor_set(v___x_672_, 4, v___x_670_);
lean_ctor_set(v___x_672_, 5, v___x_670_);
lean_ctor_set(v___x_672_, 6, v___x_670_);
lean_ctor_set(v___x_672_, 7, v___x_670_);
lean_ctor_set(v___x_672_, 8, v___x_670_);
lean_ctor_set(v___x_672_, 9, v___x_670_);
lean_ctor_set(v___x_672_, 10, v___x_670_);
return v___x_672_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__3(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_673_ = lean_unsigned_to_nat(32u);
v___x_674_ = lean_mk_empty_array_with_capacity(v___x_673_);
v___x_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
return v___x_675_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__4(void){
_start:
{
size_t v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_676_ = ((size_t)5ULL);
v___x_677_ = lean_unsigned_to_nat(0u);
v___x_678_ = lean_unsigned_to_nat(32u);
v___x_679_ = lean_mk_empty_array_with_capacity(v___x_678_);
v___x_680_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__3);
v___x_681_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_681_, 0, v___x_680_);
lean_ctor_set(v___x_681_, 1, v___x_679_);
lean_ctor_set(v___x_681_, 2, v___x_677_);
lean_ctor_set(v___x_681_, 3, v___x_677_);
lean_ctor_set_usize(v___x_681_, 4, v___x_676_);
return v___x_681_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__5(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_682_ = lean_box(1);
v___x_683_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__4);
v___x_684_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1);
v___x_685_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_685_, 0, v___x_684_);
lean_ctor_set(v___x_685_, 1, v___x_683_);
lean_ctor_set(v___x_685_, 2, v___x_682_);
return v___x_685_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__6));
v___x_688_ = l_Lean_stringToMessageData(v___x_687_);
return v___x_688_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__9(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__8));
v___x_691_ = l_Lean_stringToMessageData(v___x_690_);
return v___x_691_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__11(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__10));
v___x_694_ = l_Lean_stringToMessageData(v___x_693_);
return v___x_694_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__13(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__12));
v___x_697_ = l_Lean_stringToMessageData(v___x_696_);
return v___x_697_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__15(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__14));
v___x_700_ = l_Lean_stringToMessageData(v___x_699_);
return v___x_700_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__17(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__16));
v___x_703_ = l_Lean_stringToMessageData(v___x_702_);
return v___x_703_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__19(void){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__18));
v___x_706_ = l_Lean_stringToMessageData(v___x_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(lean_object* v_msg_707_, lean_object* v_declHint_708_, lean_object* v___y_709_){
_start:
{
lean_object* v___x_711_; lean_object* v_env_712_; uint8_t v___x_713_; 
v___x_711_ = lean_st_ref_get(v___y_709_);
v_env_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc_ref(v_env_712_);
lean_dec(v___x_711_);
v___x_713_ = l_Lean_Name_isAnonymous(v_declHint_708_);
if (v___x_713_ == 0)
{
uint8_t v_isExporting_714_; 
v_isExporting_714_ = lean_ctor_get_uint8(v_env_712_, sizeof(void*)*8);
if (v_isExporting_714_ == 0)
{
lean_object* v___x_715_; 
lean_dec_ref(v_env_712_);
lean_dec(v_declHint_708_);
v___x_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_715_, 0, v_msg_707_);
return v___x_715_;
}
else
{
lean_object* v___x_716_; uint8_t v___x_717_; 
lean_inc_ref(v_env_712_);
v___x_716_ = l_Lean_Environment_setExporting(v_env_712_, v___x_713_);
lean_inc(v_declHint_708_);
lean_inc_ref(v___x_716_);
v___x_717_ = l_Lean_Environment_contains(v___x_716_, v_declHint_708_, v_isExporting_714_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; 
lean_dec_ref(v___x_716_);
lean_dec_ref(v_env_712_);
lean_dec(v_declHint_708_);
v___x_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_718_, 0, v_msg_707_);
return v___x_718_;
}
else
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v_c_724_; lean_object* v___x_725_; 
v___x_719_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__2);
v___x_720_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__5);
v___x_721_ = l_Lean_Options_empty;
v___x_722_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_722_, 0, v___x_716_);
lean_ctor_set(v___x_722_, 1, v___x_719_);
lean_ctor_set(v___x_722_, 2, v___x_720_);
lean_ctor_set(v___x_722_, 3, v___x_721_);
lean_inc(v_declHint_708_);
v___x_723_ = l_Lean_MessageData_ofConstName(v_declHint_708_, v___x_713_);
v_c_724_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_724_, 0, v___x_722_);
lean_ctor_set(v_c_724_, 1, v___x_723_);
v___x_725_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_712_, v_declHint_708_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
lean_dec_ref(v_env_712_);
lean_dec(v_declHint_708_);
v___x_726_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7);
v___x_727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
lean_ctor_set(v___x_727_, 1, v_c_724_);
v___x_728_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__9);
v___x_729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_727_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = l_Lean_MessageData_note(v___x_729_);
v___x_731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_731_, 0, v_msg_707_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
v___x_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
return v___x_732_;
}
else
{
lean_object* v_val_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_768_; 
v_val_733_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_768_ == 0)
{
v___x_735_ = v___x_725_;
v_isShared_736_ = v_isSharedCheck_768_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_val_733_);
lean_dec(v___x_725_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_768_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v_mod_740_; uint8_t v___x_741_; 
v___x_737_ = lean_box(0);
v___x_738_ = l_Lean_Environment_header(v_env_712_);
lean_dec_ref(v_env_712_);
v___x_739_ = l_Lean_EnvironmentHeader_moduleNames(v___x_738_);
v_mod_740_ = lean_array_get(v___x_737_, v___x_739_, v_val_733_);
lean_dec(v_val_733_);
lean_dec_ref(v___x_739_);
v___x_741_ = l_Lean_isPrivateName(v_declHint_708_);
lean_dec(v_declHint_708_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_753_; 
v___x_742_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__11);
v___x_743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
lean_ctor_set(v___x_743_, 1, v_c_724_);
v___x_744_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__13);
v___x_745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_743_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___x_746_ = l_Lean_MessageData_ofName(v_mod_740_);
v___x_747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_745_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
v___x_748_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__15);
v___x_749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_747_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
v___x_750_ = l_Lean_MessageData_note(v___x_749_);
v___x_751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_751_, 0, v_msg_707_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
if (v_isShared_736_ == 0)
{
lean_ctor_set_tag(v___x_735_, 0);
lean_ctor_set(v___x_735_, 0, v___x_751_);
v___x_753_ = v___x_735_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_751_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
else
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_766_; 
v___x_755_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7);
v___x_756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
lean_ctor_set(v___x_756_, 1, v_c_724_);
v___x_757_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__17);
v___x_758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_756_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
v___x_759_ = l_Lean_MessageData_ofName(v_mod_740_);
v___x_760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_760_, 0, v___x_758_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__19);
v___x_762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_760_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
v___x_763_ = l_Lean_MessageData_note(v___x_762_);
v___x_764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_764_, 0, v_msg_707_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
if (v_isShared_736_ == 0)
{
lean_ctor_set_tag(v___x_735_, 0);
lean_ctor_set(v___x_735_, 0, v___x_764_);
v___x_766_ = v___x_735_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_764_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_769_; 
lean_dec_ref(v_env_712_);
lean_dec(v_declHint_708_);
v___x_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_769_, 0, v_msg_707_);
return v___x_769_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___boxed(lean_object* v_msg_770_, lean_object* v_declHint_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(v_msg_770_, v_declHint_771_, v___y_772_);
lean_dec(v___y_772_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30(lean_object* v_msg_775_, lean_object* v_declHint_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v___x_786_; lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_796_; 
v___x_786_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(v_msg_775_, v_declHint_776_, v___y_784_);
v_a_787_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_796_ == 0)
{
v___x_789_ = v___x_786_;
v_isShared_790_ = v_isSharedCheck_796_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_786_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_796_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_791_ = l_Lean_unknownIdentifierMessageTag;
v___x_792_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
lean_ctor_set(v___x_792_, 1, v_a_787_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v___x_792_);
v___x_794_ = v___x_789_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30___boxed(lean_object* v_msg_797_, lean_object* v_declHint_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30(v_msg_797_, v_declHint_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v___y_800_);
lean_dec(v___y_799_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(lean_object* v_ref_809_, lean_object* v_msg_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
lean_object* v_toCold_820_; lean_object* v_currRecDepth_821_; lean_object* v_ref_822_; uint8_t v_diag_823_; uint8_t v_suppressElabErrors_824_; lean_object* v_ref_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v_toCold_820_ = lean_ctor_get(v___y_817_, 0);
v_currRecDepth_821_ = lean_ctor_get(v___y_817_, 1);
v_ref_822_ = lean_ctor_get(v___y_817_, 2);
v_diag_823_ = lean_ctor_get_uint8(v___y_817_, sizeof(void*)*3);
v_suppressElabErrors_824_ = lean_ctor_get_uint8(v___y_817_, sizeof(void*)*3 + 1);
v_ref_825_ = l_Lean_replaceRef(v_ref_809_, v_ref_822_);
lean_inc(v_currRecDepth_821_);
lean_inc_ref(v_toCold_820_);
v___x_826_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_826_, 0, v_toCold_820_);
lean_ctor_set(v___x_826_, 1, v_currRecDepth_821_);
lean_ctor_set(v___x_826_, 2, v_ref_825_);
lean_ctor_set_uint8(v___x_826_, sizeof(void*)*3, v_diag_823_);
lean_ctor_set_uint8(v___x_826_, sizeof(void*)*3 + 1, v_suppressElabErrors_824_);
v___x_827_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v_msg_810_, v___y_815_, v___y_816_, v___x_826_, v___y_818_);
lean_dec_ref_known(v___x_826_, 3);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg___boxed(lean_object* v_ref_828_, lean_object* v_msg_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(v_ref_828_, v_msg_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
lean_dec(v___y_830_);
lean_dec(v_ref_828_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(lean_object* v_ref_840_, lean_object* v_msg_841_, lean_object* v_declHint_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v___x_852_; lean_object* v_a_853_; lean_object* v___x_854_; 
v___x_852_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30(v_msg_841_, v_declHint_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
v_a_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_a_853_);
lean_dec_ref(v___x_852_);
v___x_854_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(v_ref_840_, v_a_853_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg___boxed(lean_object* v_ref_855_, lean_object* v_msg_856_, lean_object* v_declHint_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(v_ref_855_, v_msg_856_, v_declHint_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec(v___y_859_);
lean_dec(v___y_858_);
lean_dec(v_ref_855_);
return v_res_867_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1(void){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__0));
v___x_870_ = l_Lean_stringToMessageData(v___x_869_);
return v___x_870_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__2));
v___x_873_ = l_Lean_stringToMessageData(v___x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(lean_object* v_ref_874_, lean_object* v_constName_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v___x_885_; uint8_t v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_885_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1);
v___x_886_ = 0;
lean_inc(v_constName_875_);
v___x_887_ = l_Lean_MessageData_ofConstName(v_constName_875_, v___x_886_);
v___x_888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_885_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v___x_889_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3);
v___x_890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_888_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
v___x_891_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(v_ref_874_, v___x_890_, v_constName_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___boxed(lean_object* v_ref_892_, lean_object* v_constName_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(v_ref_892_, v_constName_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec(v___y_894_);
lean_dec(v_ref_892_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(lean_object* v_constName_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v_ref_914_; lean_object* v___x_915_; 
v_ref_914_ = lean_ctor_get(v___y_911_, 2);
v___x_915_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(v_ref_914_, v_constName_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg___boxed(lean_object* v_constName_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(v_constName_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec(v___y_917_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(lean_object* v_constName_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v___x_937_; lean_object* v_env_938_; uint8_t v___x_939_; lean_object* v___x_940_; 
v___x_937_ = lean_st_ref_get(v___y_935_);
v_env_938_ = lean_ctor_get(v___x_937_, 0);
lean_inc_ref(v_env_938_);
lean_dec(v___x_937_);
v___x_939_ = 0;
lean_inc(v_constName_927_);
v___x_940_ = l_Lean_Environment_find_x3f(v_env_938_, v_constName_927_, v___x_939_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v___x_941_; 
v___x_941_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(v_constName_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
return v___x_941_;
}
else
{
lean_object* v_val_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
lean_dec(v_constName_927_);
v_val_942_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_940_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_val_942_);
lean_dec(v___x_940_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
lean_ctor_set_tag(v___x_944_, 0);
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_val_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18___boxed(lean_object* v_constName_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(v_constName_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec(v___y_951_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(lean_object* v_declName_961_, lean_object* v___y_962_){
_start:
{
lean_object* v___x_964_; lean_object* v_env_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_964_ = lean_st_ref_get(v___y_962_);
v_env_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc_ref(v_env_965_);
lean_dec(v___x_964_);
v___x_966_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_965_, v_declName_961_);
v___x_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg___boxed(lean_object* v_declName_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(v_declName_968_, v___y_969_);
lean_dec(v___y_969_);
return v_res_971_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0(void){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l_instMonadEIO(lean_box(0));
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19(lean_object* v_msg_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v_toApplicative_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1084_; 
v___x_989_ = lean_obj_once(&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0, &l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0_once, _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0);
v___x_990_ = l_StateRefT_x27_instMonad___redArg(v___x_989_);
v_toApplicative_991_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1084_ == 0)
{
lean_object* v_unused_1085_; 
v_unused_1085_ = lean_ctor_get(v___x_990_, 1);
lean_dec(v_unused_1085_);
v___x_993_ = v___x_990_;
v_isShared_994_ = v_isSharedCheck_1084_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_toApplicative_991_);
lean_dec(v___x_990_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1084_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v_toFunctor_995_; lean_object* v_toSeq_996_; lean_object* v_toSeqLeft_997_; lean_object* v_toSeqRight_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1082_; 
v_toFunctor_995_ = lean_ctor_get(v_toApplicative_991_, 0);
v_toSeq_996_ = lean_ctor_get(v_toApplicative_991_, 2);
v_toSeqLeft_997_ = lean_ctor_get(v_toApplicative_991_, 3);
v_toSeqRight_998_ = lean_ctor_get(v_toApplicative_991_, 4);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_toApplicative_991_);
if (v_isSharedCheck_1082_ == 0)
{
lean_object* v_unused_1083_; 
v_unused_1083_ = lean_ctor_get(v_toApplicative_991_, 1);
lean_dec(v_unused_1083_);
v___x_1000_ = v_toApplicative_991_;
v_isShared_1001_ = v_isSharedCheck_1082_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_toSeqRight_998_);
lean_inc(v_toSeqLeft_997_);
lean_inc(v_toSeq_996_);
lean_inc(v_toFunctor_995_);
lean_dec(v_toApplicative_991_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1082_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___f_1002_; lean_object* v___f_1003_; lean_object* v___f_1004_; lean_object* v___f_1005_; lean_object* v___x_1006_; lean_object* v___f_1007_; lean_object* v___f_1008_; lean_object* v___f_1009_; lean_object* v___x_1011_; 
v___f_1002_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__1));
v___f_1003_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__2));
lean_inc_ref(v_toFunctor_995_);
v___f_1004_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1004_, 0, v_toFunctor_995_);
v___f_1005_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1005_, 0, v_toFunctor_995_);
v___x_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___f_1004_);
lean_ctor_set(v___x_1006_, 1, v___f_1005_);
v___f_1007_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1007_, 0, v_toSeqRight_998_);
v___f_1008_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1008_, 0, v_toSeqLeft_997_);
v___f_1009_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1009_, 0, v_toSeq_996_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 4, v___f_1007_);
lean_ctor_set(v___x_1000_, 3, v___f_1008_);
lean_ctor_set(v___x_1000_, 2, v___f_1009_);
lean_ctor_set(v___x_1000_, 1, v___f_1002_);
lean_ctor_set(v___x_1000_, 0, v___x_1006_);
v___x_1011_ = v___x_1000_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1006_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v___f_1002_);
lean_ctor_set(v_reuseFailAlloc_1081_, 2, v___f_1009_);
lean_ctor_set(v_reuseFailAlloc_1081_, 3, v___f_1008_);
lean_ctor_set(v_reuseFailAlloc_1081_, 4, v___f_1007_);
v___x_1011_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
lean_object* v___x_1013_; 
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 1, v___f_1003_);
lean_ctor_set(v___x_993_, 0, v___x_1011_);
v___x_1013_ = v___x_993_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1011_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v___f_1003_);
v___x_1013_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
lean_object* v___x_1014_; lean_object* v_toApplicative_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1078_; 
v___x_1014_ = l_StateRefT_x27_instMonad___redArg(v___x_1013_);
v_toApplicative_1015_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1078_ == 0)
{
lean_object* v_unused_1079_; 
v_unused_1079_ = lean_ctor_get(v___x_1014_, 1);
lean_dec(v_unused_1079_);
v___x_1017_ = v___x_1014_;
v_isShared_1018_ = v_isSharedCheck_1078_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_toApplicative_1015_);
lean_dec(v___x_1014_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1078_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v_toFunctor_1019_; lean_object* v_toSeq_1020_; lean_object* v_toSeqLeft_1021_; lean_object* v_toSeqRight_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1076_; 
v_toFunctor_1019_ = lean_ctor_get(v_toApplicative_1015_, 0);
v_toSeq_1020_ = lean_ctor_get(v_toApplicative_1015_, 2);
v_toSeqLeft_1021_ = lean_ctor_get(v_toApplicative_1015_, 3);
v_toSeqRight_1022_ = lean_ctor_get(v_toApplicative_1015_, 4);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_toApplicative_1015_);
if (v_isSharedCheck_1076_ == 0)
{
lean_object* v_unused_1077_; 
v_unused_1077_ = lean_ctor_get(v_toApplicative_1015_, 1);
lean_dec(v_unused_1077_);
v___x_1024_ = v_toApplicative_1015_;
v_isShared_1025_ = v_isSharedCheck_1076_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_toSeqRight_1022_);
lean_inc(v_toSeqLeft_1021_);
lean_inc(v_toSeq_1020_);
lean_inc(v_toFunctor_1019_);
lean_dec(v_toApplicative_1015_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1076_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___f_1026_; lean_object* v___f_1027_; lean_object* v___f_1028_; lean_object* v___f_1029_; lean_object* v___x_1030_; lean_object* v___f_1031_; lean_object* v___f_1032_; lean_object* v___f_1033_; lean_object* v___x_1035_; 
v___f_1026_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__3));
v___f_1027_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__4));
lean_inc_ref(v_toFunctor_1019_);
v___f_1028_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1028_, 0, v_toFunctor_1019_);
v___f_1029_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1029_, 0, v_toFunctor_1019_);
v___x_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___f_1028_);
lean_ctor_set(v___x_1030_, 1, v___f_1029_);
v___f_1031_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1031_, 0, v_toSeqRight_1022_);
v___f_1032_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1032_, 0, v_toSeqLeft_1021_);
v___f_1033_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1033_, 0, v_toSeq_1020_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 4, v___f_1031_);
lean_ctor_set(v___x_1024_, 3, v___f_1032_);
lean_ctor_set(v___x_1024_, 2, v___f_1033_);
lean_ctor_set(v___x_1024_, 1, v___f_1026_);
lean_ctor_set(v___x_1024_, 0, v___x_1030_);
v___x_1035_ = v___x_1024_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1030_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v___f_1026_);
lean_ctor_set(v_reuseFailAlloc_1075_, 2, v___f_1033_);
lean_ctor_set(v_reuseFailAlloc_1075_, 3, v___f_1032_);
lean_ctor_set(v_reuseFailAlloc_1075_, 4, v___f_1031_);
v___x_1035_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1037_; 
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 1, v___f_1027_);
lean_ctor_set(v___x_1017_, 0, v___x_1035_);
v___x_1037_ = v___x_1017_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1035_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v___f_1027_);
v___x_1037_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
lean_object* v___x_1038_; lean_object* v_toApplicative_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1072_; 
v___x_1038_ = l_StateRefT_x27_instMonad___redArg(v___x_1037_);
v_toApplicative_1039_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1072_ == 0)
{
lean_object* v_unused_1073_; 
v_unused_1073_ = lean_ctor_get(v___x_1038_, 1);
lean_dec(v_unused_1073_);
v___x_1041_ = v___x_1038_;
v_isShared_1042_ = v_isSharedCheck_1072_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_toApplicative_1039_);
lean_dec(v___x_1038_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1072_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v_toFunctor_1043_; lean_object* v_toSeq_1044_; lean_object* v_toSeqLeft_1045_; lean_object* v_toSeqRight_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1070_; 
v_toFunctor_1043_ = lean_ctor_get(v_toApplicative_1039_, 0);
v_toSeq_1044_ = lean_ctor_get(v_toApplicative_1039_, 2);
v_toSeqLeft_1045_ = lean_ctor_get(v_toApplicative_1039_, 3);
v_toSeqRight_1046_ = lean_ctor_get(v_toApplicative_1039_, 4);
v_isSharedCheck_1070_ = !lean_is_exclusive(v_toApplicative_1039_);
if (v_isSharedCheck_1070_ == 0)
{
lean_object* v_unused_1071_; 
v_unused_1071_ = lean_ctor_get(v_toApplicative_1039_, 1);
lean_dec(v_unused_1071_);
v___x_1048_ = v_toApplicative_1039_;
v_isShared_1049_ = v_isSharedCheck_1070_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_toSeqRight_1046_);
lean_inc(v_toSeqLeft_1045_);
lean_inc(v_toSeq_1044_);
lean_inc(v_toFunctor_1043_);
lean_dec(v_toApplicative_1039_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1070_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___f_1050_; lean_object* v___f_1051_; lean_object* v___f_1052_; lean_object* v___f_1053_; lean_object* v___x_1054_; lean_object* v___f_1055_; lean_object* v___f_1056_; lean_object* v___f_1057_; lean_object* v___x_1059_; 
v___f_1050_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__5));
v___f_1051_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__6));
lean_inc_ref(v_toFunctor_1043_);
v___f_1052_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1052_, 0, v_toFunctor_1043_);
v___f_1053_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1053_, 0, v_toFunctor_1043_);
v___x_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___f_1052_);
lean_ctor_set(v___x_1054_, 1, v___f_1053_);
v___f_1055_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1055_, 0, v_toSeqRight_1046_);
v___f_1056_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1056_, 0, v_toSeqLeft_1045_);
v___f_1057_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1057_, 0, v_toSeq_1044_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 4, v___f_1055_);
lean_ctor_set(v___x_1048_, 3, v___f_1056_);
lean_ctor_set(v___x_1048_, 2, v___f_1057_);
lean_ctor_set(v___x_1048_, 1, v___f_1050_);
lean_ctor_set(v___x_1048_, 0, v___x_1054_);
v___x_1059_ = v___x_1048_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1054_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v___f_1050_);
lean_ctor_set(v_reuseFailAlloc_1069_, 2, v___f_1057_);
lean_ctor_set(v_reuseFailAlloc_1069_, 3, v___f_1056_);
lean_ctor_set(v_reuseFailAlloc_1069_, 4, v___f_1055_);
v___x_1059_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
lean_object* v___x_1061_; 
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 1, v___f_1051_);
lean_ctor_set(v___x_1041_, 0, v___x_1059_);
v___x_1061_ = v___x_1041_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v___f_1051_);
v___x_1061_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_49650__overap_1066_; lean_object* v___x_1067_; 
v___x_1062_ = l_StateRefT_x27_instMonad___redArg(v___x_1061_);
v___x_1063_ = l_StateRefT_x27_instMonad___redArg(v___x_1062_);
v___x_1064_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_1065_ = l_instInhabitedOfMonad___redArg(v___x_1063_, v___x_1064_);
v___x_49650__overap_1066_ = lean_panic_fn_borrowed(v___x_1065_, v_msg_979_);
lean_dec(v___x_1065_);
lean_inc(v___y_987_);
lean_inc_ref(v___y_986_);
lean_inc(v___y_985_);
lean_inc_ref(v___y_984_);
lean_inc(v___y_983_);
lean_inc_ref(v___y_982_);
lean_inc(v___y_981_);
lean_inc(v___y_980_);
v___x_1067_ = lean_apply_9(v___x_49650__overap_1066_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, lean_box(0));
return v___x_1067_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___boxed(lean_object* v_msg_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19(v_msg_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec(v___y_1087_);
return v_res_1096_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1100_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__2));
v___x_1101_ = lean_unsigned_to_nat(53u);
v___x_1102_ = lean_unsigned_to_nat(62u);
v___x_1103_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__1));
v___x_1104_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__0));
v___x_1105_ = l_mkPanicMessageWithDecl(v___x_1104_, v___x_1103_, v___x_1102_, v___x_1101_, v___x_1100_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21(size_t v_sz_1106_, size_t v_i_1107_, lean_object* v_bs_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
uint8_t v___x_1118_; 
v___x_1118_ = lean_usize_dec_lt(v_i_1107_, v_sz_1106_);
if (v___x_1118_ == 0)
{
lean_object* v___x_1119_; 
v___x_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1119_, 0, v_bs_1108_);
return v___x_1119_;
}
else
{
lean_object* v_v_1120_; lean_object* v___x_1121_; 
v_v_1120_ = lean_array_uget_borrowed(v_bs_1108_, v_i_1107_);
lean_inc(v_v_1120_);
v___x_1121_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(v_v_1120_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1122_; lean_object* v___x_1123_; lean_object* v_bs_x27_1124_; lean_object* v_a_1126_; 
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_a_1122_);
lean_dec_ref_known(v___x_1121_, 1);
v___x_1123_ = lean_unsigned_to_nat(0u);
v_bs_x27_1124_ = lean_array_uset(v_bs_1108_, v_i_1107_, v___x_1123_);
if (lean_obj_tag(v_a_1122_) == 6)
{
lean_object* v_val_1131_; lean_object* v_numFields_1132_; uint8_t v___x_1133_; lean_object* v___x_1134_; 
v_val_1131_ = lean_ctor_get(v_a_1122_, 0);
lean_inc_ref(v_val_1131_);
lean_dec_ref_known(v_a_1122_, 1);
v_numFields_1132_ = lean_ctor_get(v_val_1131_, 4);
lean_inc(v_numFields_1132_);
lean_dec_ref(v_val_1131_);
v___x_1133_ = 0;
v___x_1134_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1134_, 0, v_numFields_1132_);
lean_ctor_set(v___x_1134_, 1, v___x_1123_);
lean_ctor_set_uint8(v___x_1134_, sizeof(void*)*2, v___x_1133_);
v_a_1126_ = v___x_1134_;
goto v___jp_1125_;
}
else
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
lean_dec(v_a_1122_);
v___x_1135_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3);
v___x_1136_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19(v___x_1135_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_a_1137_; 
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_a_1137_);
lean_dec_ref_known(v___x_1136_, 1);
v_a_1126_ = v_a_1137_;
goto v___jp_1125_;
}
else
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1145_; 
lean_dec_ref(v_bs_x27_1124_);
v_a_1138_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1140_ = v___x_1136_;
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1136_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1143_; 
if (v_isShared_1141_ == 0)
{
v___x_1143_ = v___x_1140_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_a_1138_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
}
v___jp_1125_:
{
size_t v___x_1127_; size_t v___x_1128_; lean_object* v___x_1129_; 
v___x_1127_ = ((size_t)1ULL);
v___x_1128_ = lean_usize_add(v_i_1107_, v___x_1127_);
v___x_1129_ = lean_array_uset(v_bs_x27_1124_, v_i_1107_, v_a_1126_);
v_i_1107_ = v___x_1128_;
v_bs_1108_ = v___x_1129_;
goto _start;
}
}
else
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
lean_dec_ref(v_bs_1108_);
v_a_1146_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1148_ = v___x_1121_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1121_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1146_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___boxed(lean_object* v_sz_1154_, lean_object* v_i_1155_, lean_object* v_bs_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
size_t v_sz_boxed_1166_; size_t v_i_boxed_1167_; lean_object* v_res_1168_; 
v_sz_boxed_1166_ = lean_unbox_usize(v_sz_1154_);
lean_dec(v_sz_1154_);
v_i_boxed_1167_ = lean_unbox_usize(v_i_1155_);
lean_dec(v_i_1155_);
v_res_1168_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21(v_sz_boxed_1166_, v_i_boxed_1167_, v_bs_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec(v___y_1157_);
return v_res_1168_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0(void){
_start:
{
lean_object* v___x_1169_; lean_object* v_dummy_1170_; 
v___x_1169_ = lean_box(0);
v_dummy_1170_ = l_Lean_Expr_sort___override(v___x_1169_);
return v_dummy_1170_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1(void){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1171_ = lean_box(0);
v___x_1172_ = lean_unsigned_to_nat(16u);
v___x_1173_ = lean_mk_array(v___x_1172_, v___x_1171_);
return v___x_1173_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2(void){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1174_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1);
v___x_1175_ = lean_unsigned_to_nat(0u);
v___x_1176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
lean_ctor_set(v___x_1176_, 1, v___x_1174_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(lean_object* v_e_1179_, uint8_t v_alsoCasesOn_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
uint8_t v___x_1193_; 
v___x_1193_ = l_Lean_Expr_isApp(v_e_1179_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
lean_dec_ref(v_e_1179_);
v___x_1194_ = lean_box(0);
v___x_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
return v___x_1195_;
}
else
{
lean_object* v___x_1196_; 
v___x_1196_ = l_Lean_Expr_getAppFn(v_e_1179_);
if (lean_obj_tag(v___x_1196_) == 4)
{
lean_object* v_declName_1197_; lean_object* v_us_1198_; lean_object* v___x_1199_; lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1353_; 
v_declName_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc_n(v_declName_1197_, 2);
v_us_1198_ = lean_ctor_get(v___x_1196_, 1);
lean_inc(v_us_1198_);
lean_dec_ref_known(v___x_1196_, 2);
v___x_1199_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(v_declName_1197_, v___y_1188_);
v_a_1200_ = lean_ctor_get(v___x_1199_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1202_ = v___x_1199_;
v_isShared_1203_ = v_isSharedCheck_1353_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1199_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1353_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1204_; 
v___x_1204_ = l_Lean_instInhabitedExpr;
if (lean_obj_tag(v_a_1200_) == 1)
{
lean_object* v_val_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1246_; 
v_val_1205_ = lean_ctor_get(v_a_1200_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v_a_1200_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1207_ = v_a_1200_;
v_isShared_1208_ = v_isSharedCheck_1246_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_val_1205_);
lean_dec(v_a_1200_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1246_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v_dummy_1209_; lean_object* v_nargs_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v_args_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; uint8_t v___x_1217_; 
v_dummy_1209_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
v_nargs_1210_ = l_Lean_Expr_getAppNumArgs(v_e_1179_);
lean_inc(v_nargs_1210_);
v___x_1211_ = lean_mk_array(v_nargs_1210_, v_dummy_1209_);
v___x_1212_ = lean_unsigned_to_nat(1u);
v___x_1213_ = lean_nat_sub(v_nargs_1210_, v___x_1212_);
lean_dec(v_nargs_1210_);
v_args_1214_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1179_, v___x_1211_, v___x_1213_);
v___x_1215_ = lean_array_get_size(v_args_1214_);
v___x_1216_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_1205_);
v___x_1217_ = lean_nat_dec_lt(v___x_1215_, v___x_1216_);
lean_dec(v___x_1216_);
if (v___x_1217_ == 0)
{
lean_object* v_numParams_1218_; lean_object* v_numDiscrs_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1237_; 
v_numParams_1218_ = lean_ctor_get(v_val_1205_, 0);
v_numDiscrs_1219_ = lean_ctor_get(v_val_1205_, 1);
v___x_1220_ = lean_array_mk(v_us_1198_);
v___x_1221_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1218_);
v___x_1222_ = l_Array_extract___redArg(v_args_1214_, v___x_1221_, v_numParams_1218_);
v___x_1223_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_1205_);
v___x_1224_ = lean_array_get(v___x_1204_, v_args_1214_, v___x_1223_);
lean_dec(v___x_1223_);
v___x_1225_ = lean_nat_add(v_numParams_1218_, v___x_1212_);
v___x_1226_ = lean_nat_add(v___x_1225_, v_numDiscrs_1219_);
lean_inc(v___x_1226_);
lean_inc_ref_n(v_args_1214_, 2);
v___x_1227_ = l_Array_toSubarray___redArg(v_args_1214_, v___x_1225_, v___x_1226_);
v___x_1228_ = l_Subarray_copy___redArg(v___x_1227_);
v___x_1229_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1205_);
v___x_1230_ = lean_nat_add(v___x_1226_, v___x_1229_);
lean_dec(v___x_1229_);
lean_inc(v___x_1230_);
v___x_1231_ = l_Array_toSubarray___redArg(v_args_1214_, v___x_1226_, v___x_1230_);
v___x_1232_ = l_Subarray_copy___redArg(v___x_1231_);
v___x_1233_ = l_Array_toSubarray___redArg(v_args_1214_, v___x_1230_, v___x_1215_);
v___x_1234_ = l_Subarray_copy___redArg(v___x_1233_);
v___x_1235_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1235_, 0, v_val_1205_);
lean_ctor_set(v___x_1235_, 1, v_declName_1197_);
lean_ctor_set(v___x_1235_, 2, v___x_1220_);
lean_ctor_set(v___x_1235_, 3, v___x_1222_);
lean_ctor_set(v___x_1235_, 4, v___x_1224_);
lean_ctor_set(v___x_1235_, 5, v___x_1228_);
lean_ctor_set(v___x_1235_, 6, v___x_1232_);
lean_ctor_set(v___x_1235_, 7, v___x_1234_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 0, v___x_1235_);
v___x_1237_ = v___x_1207_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1235_);
v___x_1237_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1239_; 
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 0, v___x_1237_);
v___x_1239_ = v___x_1202_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1237_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
else
{
lean_object* v___x_1242_; lean_object* v___x_1244_; 
lean_dec_ref(v_args_1214_);
lean_del_object(v___x_1207_);
lean_dec(v_val_1205_);
lean_dec(v_us_1198_);
lean_dec(v_declName_1197_);
v___x_1242_ = lean_box(0);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 0, v___x_1242_);
v___x_1244_ = v___x_1202_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v___x_1242_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
else
{
lean_object* v___x_1247_; 
lean_del_object(v___x_1202_);
lean_dec(v_a_1200_);
v___x_1247_ = lean_st_ref_get(v___y_1188_);
if (v_alsoCasesOn_1180_ == 0)
{
lean_dec(v___x_1247_);
lean_dec(v_us_1198_);
lean_dec(v_declName_1197_);
lean_dec_ref(v_e_1179_);
goto v___jp_1190_;
}
else
{
lean_object* v_env_1248_; uint8_t v___x_1249_; 
v_env_1248_ = lean_ctor_get(v___x_1247_, 0);
lean_inc_ref(v_env_1248_);
lean_dec(v___x_1247_);
lean_inc(v_declName_1197_);
v___x_1249_ = l_Lean_isCasesOnRecursor(v_env_1248_, v_declName_1197_);
if (v___x_1249_ == 0)
{
lean_dec(v_us_1198_);
lean_dec(v_declName_1197_);
lean_dec_ref(v_e_1179_);
goto v___jp_1190_;
}
else
{
lean_object* v_indName_1250_; lean_object* v___x_1251_; 
v_indName_1250_ = l_Lean_Name_getPrefix(v_declName_1197_);
v___x_1251_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(v_indName_1250_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1344_; 
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1254_ = v___x_1251_;
v_isShared_1255_ = v_isSharedCheck_1344_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1251_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1344_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
if (lean_obj_tag(v_a_1252_) == 5)
{
lean_object* v_val_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1339_; 
v_val_1256_ = lean_ctor_get(v_a_1252_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v_a_1252_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1258_ = v_a_1252_;
v_isShared_1259_ = v_isSharedCheck_1339_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_val_1256_);
lean_dec(v_a_1252_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1339_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v_toConstantVal_1260_; lean_object* v_numParams_1261_; lean_object* v_numIndices_1262_; lean_object* v_ctors_1263_; lean_object* v_nargs_1264_; lean_object* v_dummy_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v_args_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; uint8_t v___x_1276_; 
v_toConstantVal_1260_ = lean_ctor_get(v_val_1256_, 0);
lean_inc_ref(v_toConstantVal_1260_);
v_numParams_1261_ = lean_ctor_get(v_val_1256_, 1);
lean_inc(v_numParams_1261_);
v_numIndices_1262_ = lean_ctor_get(v_val_1256_, 2);
lean_inc(v_numIndices_1262_);
v_ctors_1263_ = lean_ctor_get(v_val_1256_, 4);
lean_inc(v_ctors_1263_);
v_nargs_1264_ = l_Lean_Expr_getAppNumArgs(v_e_1179_);
v_dummy_1265_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v_nargs_1264_);
v___x_1266_ = lean_mk_array(v_nargs_1264_, v_dummy_1265_);
v___x_1267_ = lean_unsigned_to_nat(1u);
v___x_1268_ = lean_nat_sub(v_nargs_1264_, v___x_1267_);
lean_dec(v_nargs_1264_);
v_args_1269_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1179_, v___x_1266_, v___x_1268_);
v___x_1270_ = lean_nat_add(v_numParams_1261_, v___x_1267_);
v___x_1271_ = lean_nat_add(v___x_1270_, v_numIndices_1262_);
v___x_1272_ = lean_nat_add(v___x_1271_, v___x_1267_);
lean_dec(v___x_1271_);
v___x_1273_ = l_Lean_InductiveVal_numCtors(v_val_1256_);
lean_dec_ref(v_val_1256_);
v___x_1274_ = lean_nat_add(v___x_1272_, v___x_1273_);
lean_dec(v___x_1273_);
v___x_1275_ = lean_array_get_size(v_args_1269_);
v___x_1276_ = lean_nat_dec_le(v___x_1274_, v___x_1275_);
if (v___x_1276_ == 0)
{
lean_object* v___x_1277_; lean_object* v___x_1279_; 
lean_dec(v___x_1274_);
lean_dec(v___x_1272_);
lean_dec(v___x_1270_);
lean_dec_ref(v_args_1269_);
lean_dec(v_ctors_1263_);
lean_dec(v_numIndices_1262_);
lean_dec(v_numParams_1261_);
lean_dec_ref(v_toConstantVal_1260_);
lean_del_object(v___x_1258_);
lean_dec(v_us_1198_);
lean_dec(v_declName_1197_);
v___x_1277_ = lean_box(0);
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 0, v___x_1277_);
v___x_1279_ = v___x_1254_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1277_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
else
{
lean_object* v___x_1281_; lean_object* v_params_1282_; lean_object* v_motive_1283_; lean_object* v_discrs_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v_discrInfos_1287_; lean_object* v_alts_1288_; lean_object* v___y_1290_; lean_object* v___y_1291_; lean_object* v_lower_1330_; lean_object* v_upper_1331_; uint8_t v___x_1338_; 
lean_del_object(v___x_1254_);
v___x_1281_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1261_);
lean_inc_ref_n(v_args_1269_, 3);
v_params_1282_ = l_Array_toSubarray___redArg(v_args_1269_, v___x_1281_, v_numParams_1261_);
v_motive_1283_ = lean_array_get(v___x_1204_, v_args_1269_, v_numParams_1261_);
lean_dec(v_numParams_1261_);
lean_inc(v___x_1272_);
v_discrs_1284_ = l_Array_toSubarray___redArg(v_args_1269_, v___x_1270_, v___x_1272_);
v___x_1285_ = lean_nat_add(v_numIndices_1262_, v___x_1267_);
lean_dec(v_numIndices_1262_);
v___x_1286_ = lean_box(0);
v_discrInfos_1287_ = lean_mk_array(v___x_1285_, v___x_1286_);
lean_inc(v___x_1274_);
v_alts_1288_ = l_Array_toSubarray___redArg(v_args_1269_, v___x_1272_, v___x_1274_);
v___x_1338_ = lean_nat_dec_le(v___x_1274_, v___x_1281_);
if (v___x_1338_ == 0)
{
v_lower_1330_ = v___x_1274_;
v_upper_1331_ = v___x_1275_;
goto v___jp_1329_;
}
else
{
lean_dec(v___x_1274_);
v_lower_1330_ = v___x_1281_;
v_upper_1331_ = v___x_1275_;
goto v___jp_1329_;
}
v___jp_1289_:
{
lean_object* v___x_1292_; size_t v_sz_1293_; size_t v___x_1294_; lean_object* v___x_1295_; 
v___x_1292_ = lean_array_mk(v_ctors_1263_);
v_sz_1293_ = lean_array_size(v___x_1292_);
v___x_1294_ = ((size_t)0ULL);
v___x_1295_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21(v_sz_1293_, v___x_1294_, v___x_1292_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1320_; 
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1298_ = v___x_1295_;
v_isShared_1299_ = v_isSharedCheck_1320_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1295_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1320_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v_start_1300_; lean_object* v_stop_1301_; lean_object* v_start_1302_; lean_object* v_stop_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1315_; 
v_start_1300_ = lean_ctor_get(v_params_1282_, 1);
lean_inc(v_start_1300_);
v_stop_1301_ = lean_ctor_get(v_params_1282_, 2);
lean_inc(v_stop_1301_);
v_start_1302_ = lean_ctor_get(v_discrs_1284_, 1);
lean_inc(v_start_1302_);
v_stop_1303_ = lean_ctor_get(v_discrs_1284_, 2);
lean_inc(v_stop_1303_);
v___x_1304_ = lean_nat_sub(v_stop_1301_, v_start_1300_);
lean_dec(v_start_1300_);
lean_dec(v_stop_1301_);
v___x_1305_ = lean_nat_sub(v_stop_1303_, v_start_1302_);
lean_dec(v_start_1302_);
lean_dec(v_stop_1303_);
v___x_1306_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2);
v___x_1307_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1304_);
lean_ctor_set(v___x_1307_, 1, v___x_1305_);
lean_ctor_set(v___x_1307_, 2, v_a_1296_);
lean_ctor_set(v___x_1307_, 3, v___y_1291_);
lean_ctor_set(v___x_1307_, 4, v_discrInfos_1287_);
lean_ctor_set(v___x_1307_, 5, v___x_1306_);
v___x_1308_ = lean_array_mk(v_us_1198_);
v___x_1309_ = l_Subarray_copy___redArg(v_params_1282_);
v___x_1310_ = l_Subarray_copy___redArg(v_discrs_1284_);
v___x_1311_ = l_Subarray_copy___redArg(v_alts_1288_);
v___x_1312_ = l_Subarray_copy___redArg(v___y_1290_);
v___x_1313_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1307_);
lean_ctor_set(v___x_1313_, 1, v_declName_1197_);
lean_ctor_set(v___x_1313_, 2, v___x_1308_);
lean_ctor_set(v___x_1313_, 3, v___x_1309_);
lean_ctor_set(v___x_1313_, 4, v_motive_1283_);
lean_ctor_set(v___x_1313_, 5, v___x_1310_);
lean_ctor_set(v___x_1313_, 6, v___x_1311_);
lean_ctor_set(v___x_1313_, 7, v___x_1312_);
if (v_isShared_1259_ == 0)
{
lean_ctor_set_tag(v___x_1258_, 1);
lean_ctor_set(v___x_1258_, 0, v___x_1313_);
v___x_1315_ = v___x_1258_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1313_);
v___x_1315_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
lean_object* v___x_1317_; 
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 0, v___x_1315_);
v___x_1317_ = v___x_1298_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1315_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
}
else
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec_ref(v_alts_1288_);
lean_dec_ref(v_discrInfos_1287_);
lean_dec_ref(v_discrs_1284_);
lean_dec(v_motive_1283_);
lean_dec_ref(v_params_1282_);
lean_del_object(v___x_1258_);
lean_dec(v_us_1198_);
lean_dec(v_declName_1197_);
v_a_1321_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___x_1295_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1295_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
v___jp_1329_:
{
lean_object* v_levelParams_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; uint8_t v___x_1336_; 
v_levelParams_1332_ = lean_ctor_get(v_toConstantVal_1260_, 1);
lean_inc(v_levelParams_1332_);
lean_dec_ref(v_toConstantVal_1260_);
v___x_1333_ = l_Array_toSubarray___redArg(v_args_1269_, v_lower_1330_, v_upper_1331_);
v___x_1334_ = l_List_lengthTR___redArg(v_levelParams_1332_);
lean_dec(v_levelParams_1332_);
v___x_1335_ = l_List_lengthTR___redArg(v_us_1198_);
v___x_1336_ = lean_nat_dec_eq(v___x_1334_, v___x_1335_);
lean_dec(v___x_1335_);
lean_dec(v___x_1334_);
if (v___x_1336_ == 0)
{
lean_object* v___x_1337_; 
v___x_1337_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__3));
v___y_1290_ = v___x_1333_;
v___y_1291_ = v___x_1337_;
goto v___jp_1289_;
}
else
{
v___y_1290_ = v___x_1333_;
v___y_1291_ = v___x_1286_;
goto v___jp_1289_;
}
}
}
}
}
else
{
lean_object* v___x_1340_; lean_object* v___x_1342_; 
lean_dec(v_a_1252_);
lean_dec(v_us_1198_);
lean_dec(v_declName_1197_);
lean_dec_ref(v_e_1179_);
v___x_1340_ = lean_box(0);
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 0, v___x_1340_);
v___x_1342_ = v___x_1254_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1340_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
else
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1352_; 
lean_dec(v_us_1198_);
lean_dec(v_declName_1197_);
lean_dec_ref(v_e_1179_);
v_a_1345_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1347_ = v___x_1251_;
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1251_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1350_; 
if (v_isShared_1348_ == 0)
{
v___x_1350_ = v___x_1347_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_a_1345_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
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
lean_dec_ref(v___x_1196_);
lean_dec_ref(v_e_1179_);
goto v___jp_1190_;
}
}
v___jp_1190_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = lean_box(0);
v___x_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
return v___x_1192_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___boxed(lean_object* v_e_1354_, lean_object* v_alsoCasesOn_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
uint8_t v_alsoCasesOn_boxed_1365_; lean_object* v_res_1366_; 
v_alsoCasesOn_boxed_1365_ = lean_unbox(v_alsoCasesOn_1355_);
v_res_1366_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(v_e_1354_, v_alsoCasesOn_boxed_1365_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec(v___y_1356_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0(lean_object* v_k_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v_b_1372_, lean_object* v_c_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v___x_1379_; 
lean_inc(v___y_1377_);
lean_inc_ref(v___y_1376_);
lean_inc(v___y_1375_);
lean_inc_ref(v___y_1374_);
lean_inc(v___y_1371_);
lean_inc_ref(v___y_1370_);
lean_inc(v___y_1369_);
lean_inc(v___y_1368_);
v___x_1379_ = lean_apply_11(v_k_1367_, v_b_1372_, v_c_1373_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, lean_box(0));
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0___boxed(lean_object* v_k_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v_b_1385_, lean_object* v_c_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0(v_k_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v_b_1385_, v_c_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec(v___y_1382_);
lean_dec(v___y_1381_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(lean_object* v_e_1393_, lean_object* v_maxFVars_1394_, lean_object* v_k_1395_, uint8_t v_cleanupAnnotations_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v___f_1406_; uint8_t v___x_1407_; uint8_t v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
lean_inc(v___y_1400_);
lean_inc_ref(v___y_1399_);
lean_inc(v___y_1398_);
lean_inc(v___y_1397_);
v___f_1406_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1406_, 0, v_k_1395_);
lean_closure_set(v___f_1406_, 1, v___y_1397_);
lean_closure_set(v___f_1406_, 2, v___y_1398_);
lean_closure_set(v___f_1406_, 3, v___y_1399_);
lean_closure_set(v___f_1406_, 4, v___y_1400_);
v___x_1407_ = 1;
v___x_1408_ = 0;
v___x_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1409_, 0, v_maxFVars_1394_);
v___x_1410_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1393_, v___x_1407_, v___x_1408_, v___x_1407_, v___x_1408_, v___x_1409_, v___f_1406_, v_cleanupAnnotations_1396_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
lean_dec_ref_known(v___x_1409_, 1);
if (lean_obj_tag(v___x_1410_) == 0)
{
return v___x_1410_;
}
else
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1418_; 
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1413_ = v___x_1410_;
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1410_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1411_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___boxed(lean_object* v_e_1419_, lean_object* v_maxFVars_1420_, lean_object* v_k_1421_, lean_object* v_cleanupAnnotations_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1432_; lean_object* v_res_1433_; 
v_cleanupAnnotations_boxed_1432_ = lean_unbox(v_cleanupAnnotations_1422_);
v_res_1433_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(v_e_1419_, v_maxFVars_1420_, v_k_1421_, v_cleanupAnnotations_boxed_1432_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec(v___y_1423_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0(lean_object* v_k_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v_b_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v___x_1445_; 
lean_inc(v___y_1443_);
lean_inc_ref(v___y_1442_);
lean_inc(v___y_1441_);
lean_inc_ref(v___y_1440_);
lean_inc(v___y_1438_);
lean_inc_ref(v___y_1437_);
lean_inc(v___y_1436_);
lean_inc(v___y_1435_);
v___x_1445_ = lean_apply_10(v_k_1434_, v_b_1439_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, lean_box(0));
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0___boxed(lean_object* v_k_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v_b_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0(v_k_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v_b_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
lean_dec(v___y_1448_);
lean_dec(v___y_1447_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(lean_object* v_name_1458_, lean_object* v_type_1459_, lean_object* v_val_1460_, lean_object* v_k_1461_, uint8_t v_nondep_1462_, uint8_t v_kind_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v___f_1473_; lean_object* v___x_1474_; 
lean_inc(v___y_1467_);
lean_inc_ref(v___y_1466_);
lean_inc(v___y_1465_);
lean_inc(v___y_1464_);
v___f_1473_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1473_, 0, v_k_1461_);
lean_closure_set(v___f_1473_, 1, v___y_1464_);
lean_closure_set(v___f_1473_, 2, v___y_1465_);
lean_closure_set(v___f_1473_, 3, v___y_1466_);
lean_closure_set(v___f_1473_, 4, v___y_1467_);
v___x_1474_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1458_, v_type_1459_, v_val_1460_, v___f_1473_, v_nondep_1462_, v_kind_1463_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
if (lean_obj_tag(v___x_1474_) == 0)
{
return v___x_1474_;
}
else
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1482_; 
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1477_ = v___x_1474_;
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1474_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg___boxed(lean_object* v_name_1483_, lean_object* v_type_1484_, lean_object* v_val_1485_, lean_object* v_k_1486_, lean_object* v_nondep_1487_, lean_object* v_kind_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
uint8_t v_nondep_boxed_1498_; uint8_t v_kind_boxed_1499_; lean_object* v_res_1500_; 
v_nondep_boxed_1498_ = lean_unbox(v_nondep_1487_);
v_kind_boxed_1499_ = lean_unbox(v_kind_1488_);
v_res_1500_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(v_name_1483_, v_type_1484_, v_val_1485_, v_k_1486_, v_nondep_boxed_1498_, v_kind_boxed_1499_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec(v___y_1489_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0(lean_object* v_k_1501_, uint8_t v_usedLetOnly_1502_, lean_object* v_x_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v___x_1513_; 
lean_inc(v___y_1511_);
lean_inc_ref(v___y_1510_);
lean_inc(v___y_1509_);
lean_inc_ref(v___y_1508_);
lean_inc(v___y_1507_);
lean_inc_ref(v___y_1506_);
lean_inc(v___y_1505_);
lean_inc(v___y_1504_);
lean_inc_ref(v_x_1503_);
v___x_1513_ = lean_apply_10(v_k_1501_, v_x_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, lean_box(0));
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; uint8_t v___x_1518_; uint8_t v___x_1519_; lean_object* v___x_1520_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
lean_inc(v_a_1514_);
lean_dec_ref_known(v___x_1513_, 1);
v___x_1515_ = lean_unsigned_to_nat(1u);
v___x_1516_ = lean_mk_empty_array_with_capacity(v___x_1515_);
v___x_1517_ = lean_array_push(v___x_1516_, v_x_1503_);
v___x_1518_ = 0;
v___x_1519_ = 1;
v___x_1520_ = l_Lean_Meta_mkLetFVars(v___x_1517_, v_a_1514_, v_usedLetOnly_1502_, v___x_1518_, v___x_1519_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
lean_dec_ref(v___x_1517_);
return v___x_1520_;
}
else
{
lean_dec_ref(v_x_1503_);
return v___x_1513_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0___boxed(lean_object* v_k_1521_, lean_object* v_usedLetOnly_1522_, lean_object* v_x_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
uint8_t v_usedLetOnly_boxed_1533_; lean_object* v_res_1534_; 
v_usedLetOnly_boxed_1533_ = lean_unbox(v_usedLetOnly_1522_);
v_res_1534_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0(v_k_1521_, v_usedLetOnly_boxed_1533_, v_x_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v___y_1525_);
lean_dec(v___y_1524_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(lean_object* v_name_1535_, lean_object* v_type_1536_, lean_object* v_val_1537_, lean_object* v_k_1538_, uint8_t v_nondep_1539_, uint8_t v_kind_1540_, uint8_t v_usedLetOnly_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
lean_object* v___x_1551_; lean_object* v___f_1552_; lean_object* v___x_1553_; 
v___x_1551_ = lean_box(v_usedLetOnly_1541_);
v___f_1552_ = lean_alloc_closure((void*)(l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0___boxed), 12, 2);
lean_closure_set(v___f_1552_, 0, v_k_1538_);
lean_closure_set(v___f_1552_, 1, v___x_1551_);
v___x_1553_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(v_name_1535_, v_type_1536_, v_val_1537_, v___f_1552_, v_nondep_1539_, v_kind_1540_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___boxed(lean_object* v_name_1554_, lean_object* v_type_1555_, lean_object* v_val_1556_, lean_object* v_k_1557_, lean_object* v_nondep_1558_, lean_object* v_kind_1559_, lean_object* v_usedLetOnly_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
uint8_t v_nondep_boxed_1570_; uint8_t v_kind_boxed_1571_; uint8_t v_usedLetOnly_boxed_1572_; lean_object* v_res_1573_; 
v_nondep_boxed_1570_ = lean_unbox(v_nondep_1558_);
v_kind_boxed_1571_ = lean_unbox(v_kind_1559_);
v_usedLetOnly_boxed_1572_ = lean_unbox(v_usedLetOnly_1560_);
v_res_1573_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(v_name_1554_, v_type_1555_, v_val_1556_, v_k_1557_, v_nondep_boxed_1570_, v_kind_boxed_1571_, v_usedLetOnly_boxed_1572_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec(v___y_1561_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(lean_object* v_name_1574_, uint8_t v_bi_1575_, lean_object* v_type_1576_, lean_object* v_k_1577_, uint8_t v_kind_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
lean_object* v___f_1588_; lean_object* v___x_1589_; 
lean_inc(v___y_1582_);
lean_inc_ref(v___y_1581_);
lean_inc(v___y_1580_);
lean_inc(v___y_1579_);
v___f_1588_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1588_, 0, v_k_1577_);
lean_closure_set(v___f_1588_, 1, v___y_1579_);
lean_closure_set(v___f_1588_, 2, v___y_1580_);
lean_closure_set(v___f_1588_, 3, v___y_1581_);
lean_closure_set(v___f_1588_, 4, v___y_1582_);
v___x_1589_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1574_, v_bi_1575_, v_type_1576_, v___f_1588_, v_kind_1578_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
if (lean_obj_tag(v___x_1589_) == 0)
{
return v___x_1589_;
}
else
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___x_1589_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1589_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1590_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___boxed(lean_object* v_name_1598_, lean_object* v_bi_1599_, lean_object* v_type_1600_, lean_object* v_k_1601_, lean_object* v_kind_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
uint8_t v_bi_boxed_1612_; uint8_t v_kind_boxed_1613_; lean_object* v_res_1614_; 
v_bi_boxed_1612_ = lean_unbox(v_bi_1599_);
v_kind_boxed_1613_ = lean_unbox(v_kind_1602_);
v_res_1614_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_name_1598_, v_bi_boxed_1612_, v_type_1600_, v_k_1601_, v_kind_boxed_1613_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1604_);
lean_dec(v___y_1603_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0(lean_object* v_k_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
lean_object* v___x_1625_; 
lean_inc(v___y_1619_);
lean_inc_ref(v___y_1618_);
lean_inc(v___y_1617_);
lean_inc(v___y_1616_);
v___x_1625_ = lean_apply_9(v_k_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, lean_box(0));
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0___boxed(lean_object* v_k_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0(v_k_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec(v___y_1628_);
lean_dec(v___y_1627_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(lean_object* v_k_1637_, uint8_t v_allowLevelAssignments_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v___f_1648_; lean_object* v___x_1649_; 
lean_inc(v___y_1642_);
lean_inc_ref(v___y_1641_);
lean_inc(v___y_1640_);
lean_inc(v___y_1639_);
v___f_1648_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1648_, 0, v_k_1637_);
lean_closure_set(v___f_1648_, 1, v___y_1639_);
lean_closure_set(v___f_1648_, 2, v___y_1640_);
lean_closure_set(v___f_1648_, 3, v___y_1641_);
lean_closure_set(v___f_1648_, 4, v___y_1642_);
v___x_1649_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1638_, v___f_1648_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
if (lean_obj_tag(v___x_1649_) == 0)
{
return v___x_1649_;
}
else
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1652_ = v___x_1649_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1649_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1650_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___boxed(lean_object* v_k_1658_, lean_object* v_allowLevelAssignments_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1669_; lean_object* v_res_1670_; 
v_allowLevelAssignments_boxed_1669_ = lean_unbox(v_allowLevelAssignments_1659_);
v_res_1670_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v_k_1658_, v_allowLevelAssignments_boxed_1669_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec(v___y_1661_);
lean_dec(v___y_1660_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(lean_object* v_a_1671_, lean_object* v_x_1672_){
_start:
{
if (lean_obj_tag(v_x_1672_) == 0)
{
lean_object* v___x_1673_; 
v___x_1673_ = lean_box(0);
return v___x_1673_;
}
else
{
lean_object* v_key_1674_; lean_object* v_value_1675_; lean_object* v_tail_1676_; uint8_t v___x_1677_; 
v_key_1674_ = lean_ctor_get(v_x_1672_, 0);
v_value_1675_ = lean_ctor_get(v_x_1672_, 1);
v_tail_1676_ = lean_ctor_get(v_x_1672_, 2);
v___x_1677_ = lean_expr_eqv(v_key_1674_, v_a_1671_);
if (v___x_1677_ == 0)
{
v_x_1672_ = v_tail_1676_;
goto _start;
}
else
{
lean_object* v___x_1679_; 
lean_inc(v_value_1675_);
v___x_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1679_, 0, v_value_1675_);
return v___x_1679_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg___boxed(lean_object* v_a_1680_, lean_object* v_x_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(v_a_1680_, v_x_1681_);
lean_dec(v_x_1681_);
lean_dec_ref(v_a_1680_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(lean_object* v_m_1683_, lean_object* v_a_1684_){
_start:
{
lean_object* v_buckets_1685_; lean_object* v___x_1686_; uint64_t v___x_1687_; uint64_t v___x_1688_; uint64_t v___x_1689_; uint64_t v_fold_1690_; uint64_t v___x_1691_; uint64_t v___x_1692_; uint64_t v___x_1693_; size_t v___x_1694_; size_t v___x_1695_; size_t v___x_1696_; size_t v___x_1697_; size_t v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v_buckets_1685_ = lean_ctor_get(v_m_1683_, 1);
v___x_1686_ = lean_array_get_size(v_buckets_1685_);
v___x_1687_ = l_Lean_Expr_hash(v_a_1684_);
v___x_1688_ = 32ULL;
v___x_1689_ = lean_uint64_shift_right(v___x_1687_, v___x_1688_);
v_fold_1690_ = lean_uint64_xor(v___x_1687_, v___x_1689_);
v___x_1691_ = 16ULL;
v___x_1692_ = lean_uint64_shift_right(v_fold_1690_, v___x_1691_);
v___x_1693_ = lean_uint64_xor(v_fold_1690_, v___x_1692_);
v___x_1694_ = lean_uint64_to_usize(v___x_1693_);
v___x_1695_ = lean_usize_of_nat(v___x_1686_);
v___x_1696_ = ((size_t)1ULL);
v___x_1697_ = lean_usize_sub(v___x_1695_, v___x_1696_);
v___x_1698_ = lean_usize_land(v___x_1694_, v___x_1697_);
v___x_1699_ = lean_array_uget_borrowed(v_buckets_1685_, v___x_1698_);
v___x_1700_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(v_a_1684_, v___x_1699_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg___boxed(lean_object* v_m_1701_, lean_object* v_a_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v_m_1701_, v_a_1702_);
lean_dec_ref(v_a_1702_);
lean_dec_ref(v_m_1701_);
return v_res_1703_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(lean_object* v_opts_1704_, lean_object* v_opt_1705_){
_start:
{
lean_object* v_name_1706_; lean_object* v_defValue_1707_; lean_object* v_map_1708_; lean_object* v___x_1709_; 
v_name_1706_ = lean_ctor_get(v_opt_1705_, 0);
v_defValue_1707_ = lean_ctor_get(v_opt_1705_, 1);
v_map_1708_ = lean_ctor_get(v_opts_1704_, 0);
v___x_1709_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1708_, v_name_1706_);
if (lean_obj_tag(v___x_1709_) == 0)
{
uint8_t v___x_1710_; 
v___x_1710_ = lean_unbox(v_defValue_1707_);
return v___x_1710_;
}
else
{
lean_object* v_val_1711_; 
v_val_1711_ = lean_ctor_get(v___x_1709_, 0);
lean_inc(v_val_1711_);
lean_dec_ref_known(v___x_1709_, 1);
if (lean_obj_tag(v_val_1711_) == 1)
{
uint8_t v_v_1712_; 
v_v_1712_ = lean_ctor_get_uint8(v_val_1711_, 0);
lean_dec_ref_known(v_val_1711_, 0);
return v_v_1712_;
}
else
{
uint8_t v___x_1713_; 
lean_dec(v_val_1711_);
v___x_1713_ = lean_unbox(v_defValue_1707_);
return v___x_1713_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5___boxed(lean_object* v_opts_1714_, lean_object* v_opt_1715_){
_start:
{
uint8_t v_res_1716_; lean_object* v_r_1717_; 
v_res_1716_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v_opts_1714_, v_opt_1715_);
lean_dec_ref(v_opt_1715_);
lean_dec_ref(v_opts_1714_);
v_r_1717_ = lean_box(v_res_1716_);
return v_r_1717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(lean_object* v_a_1718_, lean_object* v_b_1719_){
_start:
{
lean_object* v_array_1720_; lean_object* v_start_1721_; lean_object* v_stop_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1735_; 
v_array_1720_ = lean_ctor_get(v_a_1718_, 0);
v_start_1721_ = lean_ctor_get(v_a_1718_, 1);
v_stop_1722_ = lean_ctor_get(v_a_1718_, 2);
v_isSharedCheck_1735_ = !lean_is_exclusive(v_a_1718_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1724_ = v_a_1718_;
v_isShared_1725_ = v_isSharedCheck_1735_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_stop_1722_);
lean_inc(v_start_1721_);
lean_inc(v_array_1720_);
lean_dec(v_a_1718_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1735_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
uint8_t v___x_1726_; 
v___x_1726_ = lean_nat_dec_lt(v_start_1721_, v_stop_1722_);
if (v___x_1726_ == 0)
{
lean_del_object(v___x_1724_);
lean_dec(v_stop_1722_);
lean_dec(v_start_1721_);
lean_dec_ref(v_array_1720_);
return v_b_1719_;
}
else
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1730_; 
v___x_1727_ = lean_unsigned_to_nat(1u);
v___x_1728_ = lean_nat_add(v_start_1721_, v___x_1727_);
lean_inc_ref(v_array_1720_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 1, v___x_1728_);
v___x_1730_ = v___x_1724_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_array_1720_);
lean_ctor_set(v_reuseFailAlloc_1734_, 1, v___x_1728_);
lean_ctor_set(v_reuseFailAlloc_1734_, 2, v_stop_1722_);
v___x_1730_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1731_ = lean_array_fget(v_array_1720_, v_start_1721_);
lean_dec(v_start_1721_);
lean_dec_ref(v_array_1720_);
v___x_1732_ = lean_array_push(v_b_1719_, v___x_1731_);
v_a_1718_ = v___x_1730_;
v_b_1719_ = v___x_1732_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0(lean_object* v_body_1736_, lean_object* v_recFnName_1737_, lean_object* v_fixedPrefixSize_1738_, lean_object* v_F_1739_, lean_object* v_x_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1750_ = lean_expr_instantiate1(v_body_1736_, v_x_1740_);
v___x_1751_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1737_, v_fixedPrefixSize_1738_, v_F_1739_, v___x_1750_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v_a_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; uint8_t v___x_1756_; uint8_t v___x_1757_; uint8_t v___x_1758_; lean_object* v___x_1759_; 
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_a_1752_);
lean_dec_ref_known(v___x_1751_, 1);
v___x_1753_ = lean_unsigned_to_nat(1u);
v___x_1754_ = lean_mk_empty_array_with_capacity(v___x_1753_);
v___x_1755_ = lean_array_push(v___x_1754_, v_x_1740_);
v___x_1756_ = 0;
v___x_1757_ = 1;
v___x_1758_ = 1;
v___x_1759_ = l_Lean_Meta_mkLambdaFVars(v___x_1755_, v_a_1752_, v___x_1756_, v___x_1757_, v___x_1756_, v___x_1757_, v___x_1758_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
lean_dec_ref(v___x_1755_);
return v___x_1759_;
}
else
{
lean_dec_ref(v_x_1740_);
return v___x_1751_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0___boxed(lean_object* v_body_1760_, lean_object* v_recFnName_1761_, lean_object* v_fixedPrefixSize_1762_, lean_object* v_F_1763_, lean_object* v_x_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0(v_body_1760_, v_recFnName_1761_, v_fixedPrefixSize_1762_, v_F_1763_, v_x_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec(v___y_1765_);
lean_dec_ref(v_body_1760_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1(lean_object* v_body_1775_, lean_object* v_recFnName_1776_, lean_object* v_fixedPrefixSize_1777_, lean_object* v_F_1778_, lean_object* v_x_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1789_ = lean_expr_instantiate1(v_body_1775_, v_x_1779_);
v___x_1790_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1776_, v_fixedPrefixSize_1777_, v_F_1778_, v___x_1789_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; uint8_t v___x_1795_; uint8_t v___x_1796_; uint8_t v___x_1797_; lean_object* v___x_1798_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
lean_inc(v_a_1791_);
lean_dec_ref_known(v___x_1790_, 1);
v___x_1792_ = lean_unsigned_to_nat(1u);
v___x_1793_ = lean_mk_empty_array_with_capacity(v___x_1792_);
v___x_1794_ = lean_array_push(v___x_1793_, v_x_1779_);
v___x_1795_ = 0;
v___x_1796_ = 1;
v___x_1797_ = 1;
v___x_1798_ = l_Lean_Meta_mkForallFVars(v___x_1794_, v_a_1791_, v___x_1795_, v___x_1796_, v___x_1796_, v___x_1797_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
lean_dec_ref(v___x_1794_);
return v___x_1798_;
}
else
{
lean_dec_ref(v_x_1779_);
return v___x_1790_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1___boxed(lean_object* v_body_1799_, lean_object* v_recFnName_1800_, lean_object* v_fixedPrefixSize_1801_, lean_object* v_F_1802_, lean_object* v_x_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1(v_body_1799_, v_recFnName_1800_, v_fixedPrefixSize_1801_, v_F_1802_, v_x_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec(v___y_1804_);
lean_dec_ref(v_body_1799_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2___boxed(lean_object* v_body_1814_, lean_object* v_recFnName_1815_, lean_object* v_fixedPrefixSize_1816_, lean_object* v_F_1817_, lean_object* v_x_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2(v_body_1814_, v_recFnName_1815_, v_fixedPrefixSize_1816_, v_F_1817_, v_x_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v_x_1818_);
lean_dec_ref(v_body_1814_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(lean_object* v_recFnName_1831_, lean_object* v_fixedPrefixSize_1832_, lean_object* v_F_1833_, size_t v_sz_1834_, size_t v_i_1835_, lean_object* v_bs_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_){
_start:
{
uint8_t v___x_1846_; 
v___x_1846_ = lean_usize_dec_lt(v_i_1835_, v_sz_1834_);
if (v___x_1846_ == 0)
{
lean_object* v___x_1847_; 
lean_dec_ref(v_F_1833_);
lean_dec(v_fixedPrefixSize_1832_);
lean_dec(v_recFnName_1831_);
v___x_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1847_, 0, v_bs_1836_);
return v___x_1847_;
}
else
{
lean_object* v_v_1848_; lean_object* v___x_1849_; 
v_v_1848_ = lean_array_uget_borrowed(v_bs_1836_, v_i_1835_);
lean_inc(v_v_1848_);
lean_inc_ref(v_F_1833_);
lean_inc(v_fixedPrefixSize_1832_);
lean_inc(v_recFnName_1831_);
v___x_1849_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1831_, v_fixedPrefixSize_1832_, v_F_1833_, v_v_1848_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_a_1850_; lean_object* v___x_1851_; lean_object* v_bs_x27_1852_; size_t v___x_1853_; size_t v___x_1854_; lean_object* v___x_1855_; 
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
lean_inc(v_a_1850_);
lean_dec_ref_known(v___x_1849_, 1);
v___x_1851_ = lean_unsigned_to_nat(0u);
v_bs_x27_1852_ = lean_array_uset(v_bs_1836_, v_i_1835_, v___x_1851_);
v___x_1853_ = ((size_t)1ULL);
v___x_1854_ = lean_usize_add(v_i_1835_, v___x_1853_);
v___x_1855_ = lean_array_uset(v_bs_x27_1852_, v_i_1835_, v_a_1850_);
v_i_1835_ = v___x_1854_;
v_bs_1836_ = v___x_1855_;
goto _start;
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
lean_dec_ref(v_bs_1836_);
lean_dec_ref(v_F_1833_);
lean_dec(v_fixedPrefixSize_1832_);
lean_dec(v_recFnName_1831_);
v_a_1857_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1849_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1849_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4(void){
_start:
{
lean_object* v_cls_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v_cls_1872_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_1873_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__3));
v___x_1874_ = l_Lean_Name_append(v___x_1873_, v_cls_1872_);
return v___x_1874_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6(void){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5));
v___x_1877_ = l_Lean_stringToMessageData(v___x_1876_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(lean_object* v_recFnName_1878_, lean_object* v_fixedPrefixSize_1879_, lean_object* v_F_1880_, lean_object* v_e_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_){
_start:
{
lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v___y_1899_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; uint8_t v___x_1906_; 
v___x_1903_ = l_Lean_Expr_getAppNumArgs(v_e_1881_);
v___x_1904_ = lean_unsigned_to_nat(1u);
v___x_1905_ = lean_nat_add(v_fixedPrefixSize_1879_, v___x_1904_);
v___x_1906_ = lean_nat_dec_lt(v___x_1903_, v___x_1905_);
if (v___x_1906_ == 0)
{
lean_object* v___x_1907_; lean_object* v_dummy_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v_args_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1907_ = l_Lean_instInhabitedExpr;
v_dummy_1908_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_1903_);
v___x_1909_ = lean_mk_array(v___x_1903_, v_dummy_1908_);
v___x_1910_ = lean_nat_sub(v___x_1903_, v___x_1904_);
lean_dec(v___x_1903_);
v_args_1911_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1881_, v___x_1909_, v___x_1910_);
v___x_1912_ = lean_array_get(v___x_1907_, v_args_1911_, v_fixedPrefixSize_1879_);
lean_inc_ref(v_F_1880_);
lean_inc(v_fixedPrefixSize_1879_);
lean_inc(v_recFnName_1878_);
v___x_1913_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1878_, v_fixedPrefixSize_1879_, v_F_1880_, v___x_1912_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_a_1914_);
lean_dec_ref_known(v___x_1913_, 1);
lean_inc_ref(v_F_1880_);
v___x_1915_ = l_Lean_Expr_app___override(v_F_1880_, v_a_1914_);
lean_inc(v_a_1889_);
lean_inc_ref(v_a_1888_);
lean_inc(v_a_1887_);
lean_inc_ref(v_a_1886_);
lean_inc_ref(v___x_1915_);
v___x_1916_ = lean_infer_type(v___x_1915_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; lean_object* v___x_1918_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_a_1917_);
lean_dec_ref_known(v___x_1916_, 1);
lean_inc(v_a_1889_);
lean_inc_ref(v_a_1888_);
lean_inc(v_a_1887_);
lean_inc_ref(v_a_1886_);
v___x_1918_ = lean_whnf(v_a_1917_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_a_1919_);
lean_dec_ref_known(v___x_1918_, 1);
v___x_1920_ = l_Lean_Expr_bindingDomain_x21(v_a_1919_);
lean_dec(v_a_1919_);
v___x_1921_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg(v___x_1920_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v_a_1922_; lean_object* v___x_1923_; lean_object* v_lower_1925_; lean_object* v_upper_1926_; lean_object* v___x_1950_; lean_object* v___x_1951_; uint8_t v___x_1952_; 
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_a_1922_);
lean_dec_ref_known(v___x_1921_, 1);
v___x_1923_ = l_Lean_Expr_app___override(v___x_1915_, v_a_1922_);
v___x_1950_ = lean_unsigned_to_nat(0u);
v___x_1951_ = lean_array_get_size(v_args_1911_);
v___x_1952_ = lean_nat_dec_le(v___x_1905_, v___x_1950_);
if (v___x_1952_ == 0)
{
v_lower_1925_ = v___x_1905_;
v_upper_1926_ = v___x_1951_;
goto v___jp_1924_;
}
else
{
lean_dec(v___x_1905_);
v_lower_1925_ = v___x_1950_;
v_upper_1926_ = v___x_1951_;
goto v___jp_1924_;
}
v___jp_1924_:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; size_t v_sz_1930_; size_t v___x_1931_; lean_object* v___x_1932_; 
v___x_1927_ = l_Array_toSubarray___redArg(v_args_1911_, v_lower_1925_, v_upper_1926_);
v___x_1928_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
v___x_1929_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(v___x_1927_, v___x_1928_);
v_sz_1930_ = lean_array_size(v___x_1929_);
v___x_1931_ = ((size_t)0ULL);
v___x_1932_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_1878_, v_fixedPrefixSize_1879_, v_F_1880_, v_sz_1930_, v___x_1931_, v___x_1929_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1941_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1935_ = v___x_1932_;
v_isShared_1936_ = v_isSharedCheck_1941_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1932_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1941_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1937_; lean_object* v___x_1939_; 
v___x_1937_ = l_Lean_mkAppN(v___x_1923_, v_a_1933_);
lean_dec(v_a_1933_);
if (v_isShared_1936_ == 0)
{
lean_ctor_set(v___x_1935_, 0, v___x_1937_);
v___x_1939_ = v___x_1935_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v___x_1937_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
lean_dec_ref(v___x_1923_);
v_a_1942_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1932_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1932_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1915_);
lean_dec_ref(v_args_1911_);
lean_dec(v___x_1905_);
lean_dec_ref(v_F_1880_);
lean_dec(v_fixedPrefixSize_1879_);
lean_dec(v_recFnName_1878_);
return v___x_1921_;
}
}
else
{
lean_dec_ref(v___x_1915_);
lean_dec_ref(v_args_1911_);
lean_dec(v___x_1905_);
lean_dec_ref(v_F_1880_);
lean_dec(v_fixedPrefixSize_1879_);
lean_dec(v_recFnName_1878_);
return v___x_1918_;
}
}
else
{
lean_dec_ref(v___x_1915_);
lean_dec_ref(v_args_1911_);
lean_dec(v___x_1905_);
lean_dec_ref(v_F_1880_);
lean_dec(v_fixedPrefixSize_1879_);
lean_dec(v_recFnName_1878_);
return v___x_1916_;
}
}
else
{
lean_dec_ref(v_args_1911_);
lean_dec(v___x_1905_);
lean_dec_ref(v_F_1880_);
lean_dec(v_fixedPrefixSize_1879_);
lean_dec(v_recFnName_1878_);
return v___x_1913_;
}
}
else
{
lean_object* v_toCold_1953_; lean_object* v_options_1954_; uint8_t v_hasTrace_1955_; 
lean_dec(v___x_1905_);
lean_dec(v___x_1903_);
v_toCold_1953_ = lean_ctor_get(v_a_1888_, 0);
v_options_1954_ = lean_ctor_get(v_toCold_1953_, 2);
v_hasTrace_1955_ = lean_ctor_get_uint8(v_options_1954_, sizeof(void*)*1);
if (v_hasTrace_1955_ == 0)
{
v___y_1892_ = v_a_1882_;
v___y_1893_ = v_a_1883_;
v___y_1894_ = v_a_1884_;
v___y_1895_ = v_a_1885_;
v___y_1896_ = v_a_1886_;
v___y_1897_ = v_a_1887_;
v___y_1898_ = v_a_1888_;
v___y_1899_ = v_a_1889_;
goto v___jp_1891_;
}
else
{
lean_object* v_inheritedTraceOptions_1956_; lean_object* v_cls_1957_; lean_object* v___x_1958_; uint8_t v___x_1959_; 
v_inheritedTraceOptions_1956_ = lean_ctor_get(v_toCold_1953_, 11);
v_cls_1957_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_1958_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_1959_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1956_, v_options_1954_, v___x_1958_);
if (v___x_1959_ == 0)
{
v___y_1892_ = v_a_1882_;
v___y_1893_ = v_a_1883_;
v___y_1894_ = v_a_1884_;
v___y_1895_ = v_a_1885_;
v___y_1896_ = v_a_1886_;
v___y_1897_ = v_a_1887_;
v___y_1898_ = v_a_1888_;
v___y_1899_ = v_a_1889_;
goto v___jp_1891_;
}
else
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1960_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6);
lean_inc_ref(v_e_1881_);
v___x_1961_ = l_Lean_indentExpr(v_e_1881_);
v___x_1962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1960_);
lean_ctor_set(v___x_1962_, 1, v___x_1961_);
v___x_1963_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(v_cls_1957_, v___x_1962_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_dec_ref_known(v___x_1963_, 1);
v___y_1892_ = v_a_1882_;
v___y_1893_ = v_a_1883_;
v___y_1894_ = v_a_1884_;
v___y_1895_ = v_a_1885_;
v___y_1896_ = v_a_1886_;
v___y_1897_ = v_a_1887_;
v___y_1898_ = v_a_1888_;
v___y_1899_ = v_a_1889_;
goto v___jp_1891_;
}
else
{
lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1971_; 
lean_dec_ref(v_e_1881_);
lean_dec_ref(v_F_1880_);
lean_dec(v_fixedPrefixSize_1879_);
lean_dec(v_recFnName_1878_);
v_a_1964_ = lean_ctor_get(v___x_1963_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1966_ = v___x_1963_;
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1963_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_a_1964_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
}
}
v___jp_1891_:
{
lean_object* v___x_1900_; 
v___x_1900_ = l_Lean_Meta_etaExpand(v_e_1881_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v_a_1901_; lean_object* v___x_1902_; 
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
lean_inc(v_a_1901_);
lean_dec_ref_known(v___x_1900_, 1);
v___x_1902_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1878_, v_fixedPrefixSize_1879_, v_F_1880_, v_a_1901_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
return v___x_1902_;
}
else
{
lean_dec_ref(v_F_1880_);
lean_dec(v_fixedPrefixSize_1879_);
lean_dec(v_recFnName_1878_);
return v___x_1900_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(lean_object* v_recFnName_1972_, lean_object* v_fixedPrefixSize_1973_, lean_object* v_F_1974_, lean_object* v_x_1975_, lean_object* v_x_1976_, lean_object* v_x_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
if (lean_obj_tag(v_x_1975_) == 5)
{
lean_object* v_fn_1987_; lean_object* v_arg_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v_fn_1987_ = lean_ctor_get(v_x_1975_, 0);
lean_inc_ref(v_fn_1987_);
v_arg_1988_ = lean_ctor_get(v_x_1975_, 1);
lean_inc_ref(v_arg_1988_);
lean_dec_ref_known(v_x_1975_, 2);
v___x_1989_ = lean_array_set(v_x_1976_, v_x_1977_, v_arg_1988_);
v___x_1990_ = lean_unsigned_to_nat(1u);
v___x_1991_ = lean_nat_sub(v_x_1977_, v___x_1990_);
lean_dec(v_x_1977_);
v_x_1975_ = v_fn_1987_;
v_x_1976_ = v___x_1989_;
v_x_1977_ = v___x_1991_;
goto _start;
}
else
{
lean_object* v___x_1993_; 
lean_dec(v_x_1977_);
lean_inc_ref(v_F_1974_);
lean_inc(v_fixedPrefixSize_1973_);
lean_inc(v_recFnName_1972_);
v___x_1993_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1972_, v_fixedPrefixSize_1973_, v_F_1974_, v_x_1975_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_a_1994_; size_t v_sz_1995_; size_t v___x_1996_; lean_object* v___x_1997_; 
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
lean_inc(v_a_1994_);
lean_dec_ref_known(v___x_1993_, 1);
v_sz_1995_ = lean_array_size(v_x_1976_);
v___x_1996_ = ((size_t)0ULL);
v___x_1997_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_1972_, v_fixedPrefixSize_1973_, v_F_1974_, v_sz_1995_, v___x_1996_, v_x_1976_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_a_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2006_; 
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2000_ = v___x_1997_;
v_isShared_2001_ = v_isSharedCheck_2006_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_a_1998_);
lean_dec(v___x_1997_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2006_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2002_; lean_object* v___x_2004_; 
v___x_2002_ = l_Lean_mkAppN(v_a_1994_, v_a_1998_);
lean_dec(v_a_1998_);
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 0, v___x_2002_);
v___x_2004_ = v___x_2000_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v___x_2002_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
else
{
lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2014_; 
lean_dec(v_a_1994_);
v_a_2007_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2009_ = v___x_1997_;
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v___x_1997_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2012_; 
if (v_isShared_2010_ == 0)
{
v___x_2012_ = v___x_2009_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_a_2007_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
else
{
lean_dec_ref(v_x_1976_);
lean_dec_ref(v_F_1974_);
lean_dec(v_fixedPrefixSize_1973_);
lean_dec(v_recFnName_1972_);
return v___x_1993_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(lean_object* v_recFnName_2015_, lean_object* v_fixedPrefixSize_2016_, lean_object* v_F_2017_, lean_object* v_e_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_){
_start:
{
uint8_t v___x_2028_; 
v___x_2028_ = l_Lean_Expr_isAppOf(v_e_2018_, v_recFnName_2015_);
if (v___x_2028_ == 0)
{
lean_object* v_dummy_2029_; lean_object* v_nargs_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v_dummy_2029_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
v_nargs_2030_ = l_Lean_Expr_getAppNumArgs(v_e_2018_);
lean_inc(v_nargs_2030_);
v___x_2031_ = lean_mk_array(v_nargs_2030_, v_dummy_2029_);
v___x_2032_ = lean_unsigned_to_nat(1u);
v___x_2033_ = lean_nat_sub(v_nargs_2030_, v___x_2032_);
lean_dec(v_nargs_2030_);
v___x_2034_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(v_recFnName_2015_, v_fixedPrefixSize_2016_, v_F_2017_, v_e_2018_, v___x_2031_, v___x_2033_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_);
return v___x_2034_;
}
else
{
lean_object* v___x_2035_; 
v___x_2035_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2015_, v_fixedPrefixSize_2016_, v_F_2017_, v_e_2018_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_);
return v___x_2035_;
}
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2037_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__0));
v___x_2038_ = l_Lean_stringToMessageData(v___x_2037_);
return v___x_2038_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2040_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__2));
v___x_2041_ = l_Lean_stringToMessageData(v___x_2040_);
return v___x_2041_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0(lean_object* v___x_2042_, lean_object* v_b_2043_, lean_object* v_recFnName_2044_, lean_object* v_fixedPrefixSize_2045_, uint8_t v___x_2046_, lean_object* v___x_2047_, lean_object* v_a_2048_, lean_object* v_e_2049_, lean_object* v_xs_2050_, lean_object* v_altBody_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_){
_start:
{
lean_object* v___x_2068_; uint8_t v___x_2069_; 
v___x_2068_ = lean_array_get_size(v_xs_2050_);
v___x_2069_ = lean_nat_dec_eq(v___x_2068_, v___x_2047_);
if (v___x_2069_ == 0)
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
lean_dec_ref(v_altBody_2051_);
lean_dec(v_fixedPrefixSize_2045_);
lean_dec(v_recFnName_2044_);
v___x_2070_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1);
v___x_2071_ = l_Lean_indentExpr(v_a_2048_);
v___x_2072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2070_);
lean_ctor_set(v___x_2072_, 1, v___x_2071_);
v___x_2073_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3);
v___x_2074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2072_);
lean_ctor_set(v___x_2074_, 1, v___x_2073_);
v___x_2075_ = l_Lean_indentExpr(v_e_2049_);
v___x_2076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2074_);
lean_ctor_set(v___x_2076_, 1, v___x_2075_);
v___x_2077_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v___x_2076_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2080_ = v___x_2077_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2077_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2078_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
else
{
lean_dec_ref(v_e_2049_);
lean_dec_ref(v_a_2048_);
goto v___jp_2061_;
}
v___jp_2061_:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2062_ = lean_array_get_borrowed(v___x_2042_, v_xs_2050_, v_b_2043_);
lean_inc(v___x_2062_);
v___x_2063_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2044_, v_fixedPrefixSize_2045_, v___x_2062_, v_altBody_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_a_2064_; uint8_t v___x_2065_; uint8_t v___x_2066_; lean_object* v___x_2067_; 
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2064_);
lean_dec_ref_known(v___x_2063_, 1);
v___x_2065_ = 0;
v___x_2066_ = 1;
v___x_2067_ = l_Lean_Meta_mkLambdaFVars(v_xs_2050_, v_a_2064_, v___x_2065_, v___x_2046_, v___x_2065_, v___x_2046_, v___x_2066_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
return v___x_2067_;
}
else
{
return v___x_2063_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___boxed(lean_object** _args){
lean_object* v___x_2086_ = _args[0];
lean_object* v_b_2087_ = _args[1];
lean_object* v_recFnName_2088_ = _args[2];
lean_object* v_fixedPrefixSize_2089_ = _args[3];
lean_object* v___x_2090_ = _args[4];
lean_object* v___x_2091_ = _args[5];
lean_object* v_a_2092_ = _args[6];
lean_object* v_e_2093_ = _args[7];
lean_object* v_xs_2094_ = _args[8];
lean_object* v_altBody_2095_ = _args[9];
lean_object* v___y_2096_ = _args[10];
lean_object* v___y_2097_ = _args[11];
lean_object* v___y_2098_ = _args[12];
lean_object* v___y_2099_ = _args[13];
lean_object* v___y_2100_ = _args[14];
lean_object* v___y_2101_ = _args[15];
lean_object* v___y_2102_ = _args[16];
lean_object* v___y_2103_ = _args[17];
lean_object* v___y_2104_ = _args[18];
_start:
{
uint8_t v___x_57591__boxed_2105_; lean_object* v_res_2106_; 
v___x_57591__boxed_2105_ = lean_unbox(v___x_2090_);
v_res_2106_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0(v___x_2086_, v_b_2087_, v_recFnName_2088_, v_fixedPrefixSize_2089_, v___x_57591__boxed_2105_, v___x_2091_, v_a_2092_, v_e_2093_, v_xs_2094_, v_altBody_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v_xs_2094_);
lean_dec(v___x_2091_);
lean_dec(v_b_2087_);
lean_dec_ref(v___x_2086_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(lean_object* v_recFnName_2107_, lean_object* v_fixedPrefixSize_2108_, lean_object* v_e_2109_, lean_object* v_as_2110_, lean_object* v_bs_2111_, lean_object* v_i_2112_, lean_object* v_cs_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
lean_object* v___x_2123_; uint8_t v___x_2124_; 
v___x_2123_ = lean_array_get_size(v_as_2110_);
v___x_2124_ = lean_nat_dec_lt(v_i_2112_, v___x_2123_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2125_; 
lean_dec(v_i_2112_);
lean_dec_ref(v_e_2109_);
lean_dec(v_fixedPrefixSize_2108_);
lean_dec(v_recFnName_2107_);
v___x_2125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2125_, 0, v_cs_2113_);
return v___x_2125_;
}
else
{
lean_object* v___x_2126_; uint8_t v___x_2127_; 
v___x_2126_ = lean_array_get_size(v_bs_2111_);
v___x_2127_ = lean_nat_dec_lt(v_i_2112_, v___x_2126_);
if (v___x_2127_ == 0)
{
lean_object* v___x_2128_; 
lean_dec(v_i_2112_);
lean_dec_ref(v_e_2109_);
lean_dec(v_fixedPrefixSize_2108_);
lean_dec(v_recFnName_2107_);
v___x_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2128_, 0, v_cs_2113_);
return v___x_2128_;
}
else
{
lean_object* v___x_2129_; lean_object* v_a_2130_; lean_object* v_b_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___f_2135_; uint8_t v___x_2136_; lean_object* v___x_2137_; 
v___x_2129_ = l_Lean_instInhabitedExpr;
v_a_2130_ = lean_array_fget_borrowed(v_as_2110_, v_i_2112_);
v_b_2131_ = lean_array_fget_borrowed(v_bs_2111_, v_i_2112_);
v___x_2132_ = lean_unsigned_to_nat(1u);
v___x_2133_ = lean_nat_add(v_b_2131_, v___x_2132_);
v___x_2134_ = lean_box(v___x_2127_);
lean_inc_ref(v_e_2109_);
lean_inc_n(v_a_2130_, 2);
lean_inc(v___x_2133_);
lean_inc(v_fixedPrefixSize_2108_);
lean_inc(v_recFnName_2107_);
lean_inc(v_b_2131_);
v___f_2135_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___boxed), 19, 8);
lean_closure_set(v___f_2135_, 0, v___x_2129_);
lean_closure_set(v___f_2135_, 1, v_b_2131_);
lean_closure_set(v___f_2135_, 2, v_recFnName_2107_);
lean_closure_set(v___f_2135_, 3, v_fixedPrefixSize_2108_);
lean_closure_set(v___f_2135_, 4, v___x_2134_);
lean_closure_set(v___f_2135_, 5, v___x_2133_);
lean_closure_set(v___f_2135_, 6, v_a_2130_);
lean_closure_set(v___f_2135_, 7, v_e_2109_);
v___x_2136_ = 0;
v___x_2137_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(v_a_2130_, v___x_2133_, v___f_2135_, v___x_2136_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2138_);
lean_dec_ref_known(v___x_2137_, 1);
v___x_2139_ = lean_nat_add(v_i_2112_, v___x_2132_);
lean_dec(v_i_2112_);
v___x_2140_ = lean_array_push(v_cs_2113_, v_a_2138_);
v_i_2112_ = v___x_2139_;
v_cs_2113_ = v___x_2140_;
goto _start;
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2149_; 
lean_dec_ref(v_cs_2113_);
lean_dec(v_i_2112_);
lean_dec_ref(v_e_2109_);
lean_dec(v_fixedPrefixSize_2108_);
lean_dec(v_recFnName_2107_);
v_a_2142_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2144_ = v___x_2137_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2137_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(lean_object* v_recFnName_2150_, lean_object* v_fixedPrefixSize_2151_, lean_object* v_F_2152_, lean_object* v_e_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_){
_start:
{
switch(lean_obj_tag(v_e_2153_))
{
case 6:
{
lean_object* v_binderName_2163_; lean_object* v_binderType_2164_; lean_object* v_body_2165_; uint8_t v_binderInfo_2166_; lean_object* v___x_2167_; 
v_binderName_2163_ = lean_ctor_get(v_e_2153_, 0);
lean_inc(v_binderName_2163_);
v_binderType_2164_ = lean_ctor_get(v_e_2153_, 1);
lean_inc_ref(v_binderType_2164_);
v_body_2165_ = lean_ctor_get(v_e_2153_, 2);
lean_inc_ref(v_body_2165_);
v_binderInfo_2166_ = lean_ctor_get_uint8(v_e_2153_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2153_, 3);
lean_inc_ref(v_F_2152_);
lean_inc(v_fixedPrefixSize_2151_);
lean_inc(v_recFnName_2150_);
v___x_2167_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2150_, v_fixedPrefixSize_2151_, v_F_2152_, v_binderType_2164_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; lean_object* v___f_2169_; uint8_t v___x_2170_; lean_object* v___x_2171_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_a_2168_);
lean_dec_ref_known(v___x_2167_, 1);
v___f_2169_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0___boxed), 14, 4);
lean_closure_set(v___f_2169_, 0, v_body_2165_);
lean_closure_set(v___f_2169_, 1, v_recFnName_2150_);
lean_closure_set(v___f_2169_, 2, v_fixedPrefixSize_2151_);
lean_closure_set(v___f_2169_, 3, v_F_2152_);
v___x_2170_ = 0;
v___x_2171_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_binderName_2163_, v_binderInfo_2166_, v_a_2168_, v___f_2169_, v___x_2170_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
return v___x_2171_;
}
else
{
lean_dec_ref(v_body_2165_);
lean_dec(v_binderName_2163_);
lean_dec_ref(v_F_2152_);
lean_dec(v_fixedPrefixSize_2151_);
lean_dec(v_recFnName_2150_);
return v___x_2167_;
}
}
case 7:
{
lean_object* v_binderName_2172_; lean_object* v_binderType_2173_; lean_object* v_body_2174_; uint8_t v_binderInfo_2175_; lean_object* v___x_2176_; 
v_binderName_2172_ = lean_ctor_get(v_e_2153_, 0);
lean_inc(v_binderName_2172_);
v_binderType_2173_ = lean_ctor_get(v_e_2153_, 1);
lean_inc_ref(v_binderType_2173_);
v_body_2174_ = lean_ctor_get(v_e_2153_, 2);
lean_inc_ref(v_body_2174_);
v_binderInfo_2175_ = lean_ctor_get_uint8(v_e_2153_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2153_, 3);
lean_inc_ref(v_F_2152_);
lean_inc(v_fixedPrefixSize_2151_);
lean_inc(v_recFnName_2150_);
v___x_2176_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2150_, v_fixedPrefixSize_2151_, v_F_2152_, v_binderType_2173_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; lean_object* v___f_2178_; uint8_t v___x_2179_; lean_object* v___x_2180_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_a_2177_);
lean_dec_ref_known(v___x_2176_, 1);
v___f_2178_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1___boxed), 14, 4);
lean_closure_set(v___f_2178_, 0, v_body_2174_);
lean_closure_set(v___f_2178_, 1, v_recFnName_2150_);
lean_closure_set(v___f_2178_, 2, v_fixedPrefixSize_2151_);
lean_closure_set(v___f_2178_, 3, v_F_2152_);
v___x_2179_ = 0;
v___x_2180_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_binderName_2172_, v_binderInfo_2175_, v_a_2177_, v___f_2178_, v___x_2179_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
return v___x_2180_;
}
else
{
lean_dec_ref(v_body_2174_);
lean_dec(v_binderName_2172_);
lean_dec_ref(v_F_2152_);
lean_dec(v_fixedPrefixSize_2151_);
lean_dec(v_recFnName_2150_);
return v___x_2176_;
}
}
case 8:
{
lean_object* v_declName_2181_; lean_object* v_type_2182_; lean_object* v_value_2183_; lean_object* v_body_2184_; uint8_t v_nondep_2185_; lean_object* v___x_2186_; 
v_declName_2181_ = lean_ctor_get(v_e_2153_, 0);
lean_inc(v_declName_2181_);
v_type_2182_ = lean_ctor_get(v_e_2153_, 1);
lean_inc_ref(v_type_2182_);
v_value_2183_ = lean_ctor_get(v_e_2153_, 2);
lean_inc_ref(v_value_2183_);
v_body_2184_ = lean_ctor_get(v_e_2153_, 3);
lean_inc_ref(v_body_2184_);
v_nondep_2185_ = lean_ctor_get_uint8(v_e_2153_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2153_, 4);
lean_inc_ref(v_F_2152_);
lean_inc(v_fixedPrefixSize_2151_);
lean_inc(v_recFnName_2150_);
v___x_2186_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2150_, v_fixedPrefixSize_2151_, v_F_2152_, v_type_2182_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v_a_2187_; lean_object* v___x_2188_; 
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
lean_inc(v_a_2187_);
lean_dec_ref_known(v___x_2186_, 1);
lean_inc_ref(v_F_2152_);
lean_inc(v_fixedPrefixSize_2151_);
lean_inc(v_recFnName_2150_);
v___x_2188_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2150_, v_fixedPrefixSize_2151_, v_F_2152_, v_value_2183_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v_a_2189_; lean_object* v___f_2190_; uint8_t v___x_2191_; uint8_t v___x_2192_; lean_object* v___x_2193_; 
v_a_2189_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_a_2189_);
lean_dec_ref_known(v___x_2188_, 1);
v___f_2190_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2___boxed), 14, 4);
lean_closure_set(v___f_2190_, 0, v_body_2184_);
lean_closure_set(v___f_2190_, 1, v_recFnName_2150_);
lean_closure_set(v___f_2190_, 2, v_fixedPrefixSize_2151_);
lean_closure_set(v___f_2190_, 3, v_F_2152_);
v___x_2191_ = 0;
v___x_2192_ = 0;
v___x_2193_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(v_declName_2181_, v_a_2187_, v_a_2189_, v___f_2190_, v_nondep_2185_, v___x_2191_, v___x_2192_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
return v___x_2193_;
}
else
{
lean_dec(v_a_2187_);
lean_dec_ref(v_body_2184_);
lean_dec(v_declName_2181_);
lean_dec_ref(v_F_2152_);
lean_dec(v_fixedPrefixSize_2151_);
lean_dec(v_recFnName_2150_);
return v___x_2188_;
}
}
else
{
lean_dec_ref(v_body_2184_);
lean_dec_ref(v_value_2183_);
lean_dec(v_declName_2181_);
lean_dec_ref(v_F_2152_);
lean_dec(v_fixedPrefixSize_2151_);
lean_dec(v_recFnName_2150_);
return v___x_2186_;
}
}
case 10:
{
lean_object* v_data_2194_; lean_object* v_expr_2195_; lean_object* v___x_2196_; 
v_data_2194_ = lean_ctor_get(v_e_2153_, 0);
lean_inc(v_data_2194_);
v_expr_2195_ = lean_ctor_get(v_e_2153_, 1);
lean_inc_ref(v_expr_2195_);
v___x_2196_ = l_Lean_getRecAppSyntax_x3f(v_e_2153_);
lean_dec_ref_known(v_e_2153_, 2);
if (lean_obj_tag(v___x_2196_) == 1)
{
lean_object* v_val_2197_; lean_object* v_toCold_2198_; lean_object* v_currRecDepth_2199_; lean_object* v_ref_2200_; uint8_t v_diag_2201_; uint8_t v_suppressElabErrors_2202_; lean_object* v_ref_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
lean_dec(v_data_2194_);
v_val_2197_ = lean_ctor_get(v___x_2196_, 0);
lean_inc(v_val_2197_);
lean_dec_ref_known(v___x_2196_, 1);
v_toCold_2198_ = lean_ctor_get(v_a_2160_, 0);
v_currRecDepth_2199_ = lean_ctor_get(v_a_2160_, 1);
v_ref_2200_ = lean_ctor_get(v_a_2160_, 2);
v_diag_2201_ = lean_ctor_get_uint8(v_a_2160_, sizeof(void*)*3);
v_suppressElabErrors_2202_ = lean_ctor_get_uint8(v_a_2160_, sizeof(void*)*3 + 1);
v_ref_2203_ = l_Lean_replaceRef(v_val_2197_, v_ref_2200_);
lean_dec(v_val_2197_);
lean_inc(v_currRecDepth_2199_);
lean_inc_ref(v_toCold_2198_);
v___x_2204_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2204_, 0, v_toCold_2198_);
lean_ctor_set(v___x_2204_, 1, v_currRecDepth_2199_);
lean_ctor_set(v___x_2204_, 2, v_ref_2203_);
lean_ctor_set_uint8(v___x_2204_, sizeof(void*)*3, v_diag_2201_);
lean_ctor_set_uint8(v___x_2204_, sizeof(void*)*3 + 1, v_suppressElabErrors_2202_);
v___x_2205_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2150_, v_fixedPrefixSize_2151_, v_F_2152_, v_expr_2195_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v___x_2204_, v_a_2161_);
lean_dec_ref_known(v___x_2204_, 3);
return v___x_2205_;
}
else
{
lean_object* v___x_2206_; 
lean_dec(v___x_2196_);
v___x_2206_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2150_, v_fixedPrefixSize_2151_, v_F_2152_, v_expr_2195_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2215_; 
v_a_2207_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2209_ = v___x_2206_;
v_isShared_2210_ = v_isSharedCheck_2215_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2206_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2215_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2211_; lean_object* v___x_2213_; 
v___x_2211_ = l_Lean_mkMData(v_data_2194_, v_a_2207_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 0, v___x_2211_);
v___x_2213_ = v___x_2209_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2211_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
else
{
lean_dec(v_data_2194_);
return v___x_2206_;
}
}
}
case 11:
{
lean_object* v_typeName_2216_; lean_object* v_idx_2217_; lean_object* v_struct_2218_; lean_object* v___x_2219_; 
v_typeName_2216_ = lean_ctor_get(v_e_2153_, 0);
lean_inc(v_typeName_2216_);
v_idx_2217_ = lean_ctor_get(v_e_2153_, 1);
lean_inc(v_idx_2217_);
v_struct_2218_ = lean_ctor_get(v_e_2153_, 2);
lean_inc_ref(v_struct_2218_);
lean_dec_ref_known(v_e_2153_, 3);
v___x_2219_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2150_, v_fixedPrefixSize_2151_, v_F_2152_, v_struct_2218_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
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
v___x_2224_ = l_Lean_mkProj(v_typeName_2216_, v_idx_2217_, v_a_2220_);
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
lean_dec(v_idx_2217_);
lean_dec(v_typeName_2216_);
return v___x_2219_;
}
}
case 4:
{
uint8_t v___x_2229_; 
v___x_2229_ = l_Lean_Expr_isConstOf(v_e_2153_, v_recFnName_2150_);
if (v___x_2229_ == 0)
{
lean_object* v___x_2230_; 
lean_dec_ref(v_F_2152_);
lean_dec(v_fixedPrefixSize_2151_);
lean_dec(v_recFnName_2150_);
v___x_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2230_, 0, v_e_2153_);
return v___x_2230_;
}
else
{
lean_object* v___x_2231_; 
v___x_2231_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2150_, v_fixedPrefixSize_2151_, v_F_2152_, v_e_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
return v___x_2231_;
}
}
case 5:
{
uint8_t v___x_2232_; lean_object* v___x_2233_; 
v___x_2232_ = 1;
lean_inc_ref(v_e_2153_);
v___x_2233_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(v_e_2153_, v___x_2232_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v_a_2234_; 
v_a_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc(v_a_2234_);
lean_dec_ref_known(v___x_2233_, 1);
if (lean_obj_tag(v_a_2234_) == 0)
{
lean_object* v___x_2235_; 
v___x_2235_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2150_, v_fixedPrefixSize_2151_, v_F_2152_, v_e_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
return v___x_2235_;
}
else
{
lean_object* v_val_2236_; lean_object* v___x_2237_; 
v_val_2236_ = lean_ctor_get(v_a_2234_, 0);
lean_inc(v_val_2236_);
lean_dec_ref_known(v_a_2234_, 1);
lean_inc_ref(v_F_2152_);
v___x_2237_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_val_2236_, v_F_2152_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v_a_2238_; 
v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
lean_inc(v_a_2238_);
lean_dec_ref_known(v___x_2237_, 1);
if (lean_obj_tag(v_a_2238_) == 1)
{
lean_object* v_val_2239_; lean_object* v_toMatcherInfo_2240_; lean_object* v_matcherName_2241_; lean_object* v_matcherLevels_2242_; lean_object* v_params_2243_; lean_object* v_motive_2244_; lean_object* v_discrs_2245_; lean_object* v_alts_2246_; lean_object* v_remaining_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v_val_2239_ = lean_ctor_get(v_a_2238_, 0);
lean_inc(v_val_2239_);
lean_dec_ref_known(v_a_2238_, 1);
v_toMatcherInfo_2240_ = lean_ctor_get(v_val_2239_, 0);
lean_inc_ref(v_toMatcherInfo_2240_);
v_matcherName_2241_ = lean_ctor_get(v_val_2239_, 1);
lean_inc(v_matcherName_2241_);
v_matcherLevels_2242_ = lean_ctor_get(v_val_2239_, 2);
lean_inc_ref(v_matcherLevels_2242_);
v_params_2243_ = lean_ctor_get(v_val_2239_, 3);
lean_inc_ref(v_params_2243_);
v_motive_2244_ = lean_ctor_get(v_val_2239_, 4);
lean_inc_ref(v_motive_2244_);
v_discrs_2245_ = lean_ctor_get(v_val_2239_, 5);
lean_inc_ref(v_discrs_2245_);
v_alts_2246_ = lean_ctor_get(v_val_2239_, 6);
lean_inc_ref(v_alts_2246_);
v_remaining_2247_ = lean_ctor_get(v_val_2239_, 7);
lean_inc_ref(v_remaining_2247_);
v___x_2248_ = l_Lean_Meta_MatcherApp_altNumParams(v_val_2239_);
v___x_2249_ = lean_unsigned_to_nat(0u);
v___x_2250_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
lean_inc(v_fixedPrefixSize_2151_);
lean_inc(v_recFnName_2150_);
v___x_2251_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(v_recFnName_2150_, v_fixedPrefixSize_2151_, v_e_2153_, v_alts_2246_, v___x_2248_, v___x_2249_, v___x_2250_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
lean_dec_ref(v___x_2248_);
lean_dec_ref(v_alts_2246_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v_a_2252_; size_t v_sz_2253_; size_t v___x_2254_; lean_object* v___x_2255_; 
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_a_2252_);
lean_dec_ref_known(v___x_2251_, 1);
v_sz_2253_ = lean_array_size(v_discrs_2245_);
v___x_2254_ = ((size_t)0ULL);
v___x_2255_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_2150_, v_fixedPrefixSize_2151_, v_F_2152_, v_sz_2253_, v___x_2254_, v_discrs_2245_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2265_; 
v_a_2256_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2258_ = v___x_2255_;
v_isShared_2259_ = v_isSharedCheck_2265_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v___x_2255_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2265_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2263_; 
v___x_2260_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2260_, 0, v_toMatcherInfo_2240_);
lean_ctor_set(v___x_2260_, 1, v_matcherName_2241_);
lean_ctor_set(v___x_2260_, 2, v_matcherLevels_2242_);
lean_ctor_set(v___x_2260_, 3, v_params_2243_);
lean_ctor_set(v___x_2260_, 4, v_motive_2244_);
lean_ctor_set(v___x_2260_, 5, v_a_2256_);
lean_ctor_set(v___x_2260_, 6, v_a_2252_);
lean_ctor_set(v___x_2260_, 7, v_remaining_2247_);
v___x_2261_ = l_Lean_Meta_MatcherApp_toExpr(v___x_2260_);
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 0, v___x_2261_);
v___x_2263_ = v___x_2258_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v___x_2261_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
else
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2273_; 
lean_dec(v_a_2252_);
lean_dec_ref(v_remaining_2247_);
lean_dec_ref(v_motive_2244_);
lean_dec_ref(v_params_2243_);
lean_dec_ref(v_matcherLevels_2242_);
lean_dec(v_matcherName_2241_);
lean_dec_ref(v_toMatcherInfo_2240_);
v_a_2266_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2268_ = v___x_2255_;
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2255_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2271_; 
if (v_isShared_2269_ == 0)
{
v___x_2271_ = v___x_2268_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2266_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
else
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2281_; 
lean_dec_ref(v_remaining_2247_);
lean_dec_ref(v_discrs_2245_);
lean_dec_ref(v_motive_2244_);
lean_dec_ref(v_params_2243_);
lean_dec_ref(v_matcherLevels_2242_);
lean_dec(v_matcherName_2241_);
lean_dec_ref(v_toMatcherInfo_2240_);
lean_dec_ref(v_F_2152_);
lean_dec(v_fixedPrefixSize_2151_);
lean_dec(v_recFnName_2150_);
v_a_2274_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2276_ = v___x_2251_;
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2251_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2279_; 
if (v_isShared_2277_ == 0)
{
v___x_2279_ = v___x_2276_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_a_2274_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
}
else
{
lean_object* v___x_2282_; 
lean_dec(v_a_2238_);
v___x_2282_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2150_, v_fixedPrefixSize_2151_, v_F_2152_, v_e_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
return v___x_2282_;
}
}
else
{
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2290_; 
lean_dec_ref_known(v_e_2153_, 2);
lean_dec_ref(v_F_2152_);
lean_dec(v_fixedPrefixSize_2151_);
lean_dec(v_recFnName_2150_);
v_a_2283_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2285_ = v___x_2237_;
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2237_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2288_; 
if (v_isShared_2286_ == 0)
{
v___x_2288_ = v___x_2285_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_a_2283_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
}
else
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
lean_dec_ref_known(v_e_2153_, 2);
lean_dec_ref(v_F_2152_);
lean_dec(v_fixedPrefixSize_2151_);
lean_dec(v_recFnName_2150_);
v_a_2291_ = lean_ctor_get(v___x_2233_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2293_ = v___x_2233_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___x_2233_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2291_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
default: 
{
lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
lean_dec_ref(v_F_2152_);
lean_dec(v_fixedPrefixSize_2151_);
v___x_2299_ = lean_unsigned_to_nat(1u);
v___x_2300_ = lean_mk_empty_array_with_capacity(v___x_2299_);
v___x_2301_ = lean_array_push(v___x_2300_, v_recFnName_2150_);
lean_inc_ref(v_e_2153_);
v___x_2302_ = l_Lean_Elab_ensureNoRecFn(v___x_2301_, v_e_2153_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2309_; 
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2309_ == 0)
{
lean_object* v_unused_2310_; 
v_unused_2310_ = lean_ctor_get(v___x_2302_, 0);
lean_dec(v_unused_2310_);
v___x_2304_ = v___x_2302_;
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
else
{
lean_dec(v___x_2302_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2307_; 
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 0, v_e_2153_);
v___x_2307_ = v___x_2304_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_e_2153_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
else
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2318_; 
lean_dec_ref(v_e_2153_);
v_a_2311_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2313_ = v___x_2302_;
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2302_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2316_; 
if (v_isShared_2314_ == 0)
{
v___x_2316_ = v___x_2313_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_a_2311_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(lean_object* v_recFnName_2319_, lean_object* v_fixedPrefixSize_2320_, lean_object* v_F_2321_, lean_object* v_e_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_){
_start:
{
lean_object* v___y_2333_; lean_object* v___y_2334_; lean_object* v___x_2351_; 
lean_inc_ref(v_e_2322_);
lean_inc(v_recFnName_2319_);
v___x_2351_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___redArg(v_recFnName_2319_, v_e_2322_, v_a_2323_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2440_; 
v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2354_ = v___x_2351_;
v_isShared_2355_ = v_isSharedCheck_2440_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2351_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2440_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
uint8_t v___x_2356_; 
v___x_2356_ = lean_unbox(v_a_2352_);
lean_dec(v_a_2352_);
if (v___x_2356_ == 0)
{
lean_object* v___x_2358_; 
lean_dec_ref(v_F_2321_);
lean_dec(v_fixedPrefixSize_2320_);
lean_dec(v_recFnName_2319_);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 0, v_e_2322_);
v___x_2358_ = v___x_2354_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_e_2322_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
else
{
lean_object* v___x_2360_; uint8_t v___x_2361_; lean_object* v___y_2363_; lean_object* v___y_2364_; lean_object* v___y_2365_; lean_object* v___y_2366_; lean_object* v___y_2367_; lean_object* v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___x_2418_; 
lean_del_object(v___x_2354_);
v___x_2360_ = lean_st_ref_get(v_a_2324_);
v___x_2361_ = 0;
v___x_2418_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v___x_2360_, v_e_2322_);
lean_dec(v___x_2360_);
if (lean_obj_tag(v___x_2418_) == 1)
{
lean_object* v_val_2419_; lean_object* v_fst_2420_; lean_object* v_snd_2421_; lean_object* v___x_2422_; 
v_val_2419_ = lean_ctor_get(v___x_2418_, 0);
lean_inc(v_val_2419_);
lean_dec_ref_known(v___x_2418_, 1);
v_fst_2420_ = lean_ctor_get(v_val_2419_, 0);
lean_inc(v_fst_2420_);
v_snd_2421_ = lean_ctor_get(v_val_2419_, 1);
lean_inc(v_snd_2421_);
lean_dec(v_val_2419_);
v___x_2422_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___redArg(v_snd_2421_, v_a_2327_);
lean_dec(v_snd_2421_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v_a_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2431_; 
v_a_2423_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2425_ = v___x_2422_;
v_isShared_2426_ = v_isSharedCheck_2431_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_a_2423_);
lean_dec(v___x_2422_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2431_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
uint8_t v___x_2427_; 
v___x_2427_ = lean_unbox(v_a_2423_);
lean_dec(v_a_2423_);
if (v___x_2427_ == 0)
{
lean_del_object(v___x_2425_);
lean_dec(v_fst_2420_);
v___y_2363_ = v_a_2323_;
v___y_2364_ = v_a_2324_;
v___y_2365_ = v_a_2325_;
v___y_2366_ = v_a_2326_;
v___y_2367_ = v_a_2327_;
v___y_2368_ = v_a_2328_;
v___y_2369_ = v_a_2329_;
v___y_2370_ = v_a_2330_;
goto v___jp_2362_;
}
else
{
lean_object* v___x_2429_; 
lean_dec_ref(v_e_2322_);
lean_dec_ref(v_F_2321_);
lean_dec(v_fixedPrefixSize_2320_);
lean_dec(v_recFnName_2319_);
if (v_isShared_2426_ == 0)
{
lean_ctor_set(v___x_2425_, 0, v_fst_2420_);
v___x_2429_ = v___x_2425_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_fst_2420_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
else
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2439_; 
lean_dec(v_fst_2420_);
lean_dec_ref(v_e_2322_);
lean_dec_ref(v_F_2321_);
lean_dec(v_fixedPrefixSize_2320_);
lean_dec(v_recFnName_2319_);
v_a_2432_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2434_ = v___x_2422_;
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2422_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2437_; 
if (v_isShared_2435_ == 0)
{
v___x_2437_ = v___x_2434_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_a_2432_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
}
}
else
{
lean_dec(v___x_2418_);
v___y_2363_ = v_a_2323_;
v___y_2364_ = v_a_2324_;
v___y_2365_ = v_a_2325_;
v___y_2366_ = v_a_2326_;
v___y_2367_ = v_a_2327_;
v___y_2368_ = v_a_2328_;
v___y_2369_ = v_a_2329_;
v___y_2370_ = v_a_2330_;
goto v___jp_2362_;
}
v___jp_2362_:
{
lean_object* v___x_2371_; 
lean_inc_ref(v_e_2322_);
v___x_2371_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(v_recFnName_2319_, v_fixedPrefixSize_2320_, v_F_2321_, v_e_2322_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_object* v_a_2372_; lean_object* v___x_2373_; 
v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
lean_inc(v_a_2372_);
lean_dec_ref_known(v___x_2371_, 1);
v___x_2373_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId(v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_object* v_a_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2409_; 
v_a_2374_ = lean_ctor_get(v___x_2373_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2376_ = v___x_2373_;
v_isShared_2377_ = v_isSharedCheck_2409_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_a_2374_);
lean_dec(v___x_2373_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2409_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v_toCold_2382_; lean_object* v_options_2383_; lean_object* v___x_2384_; uint8_t v___x_2385_; 
v___x_2378_ = lean_st_ref_take(v___y_2364_);
lean_inc(v_a_2372_);
v___x_2379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2379_, 0, v_a_2372_);
lean_ctor_set(v___x_2379_, 1, v_a_2374_);
lean_inc_ref(v_e_2322_);
v___x_2380_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4___redArg(v___x_2378_, v_e_2322_, v___x_2379_);
v___x_2381_ = lean_st_ref_put(v___y_2364_, v___x_2380_);
v_toCold_2382_ = lean_ctor_get(v___y_2369_, 0);
v_options_2383_ = lean_ctor_get(v_toCold_2382_, 2);
v___x_2384_ = l_Lean_Elab_WF_debug_definition_wf_replaceRecApps;
v___x_2385_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v_options_2383_, v___x_2384_);
if (v___x_2385_ == 0)
{
lean_object* v___x_2387_; 
lean_dec_ref(v_e_2322_);
if (v_isShared_2377_ == 0)
{
lean_ctor_set(v___x_2376_, 0, v_a_2372_);
v___x_2387_ = v___x_2376_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2372_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
else
{
lean_object* v___x_2389_; uint8_t v_transparency_2390_; lean_object* v___f_2391_; uint8_t v___x_2392_; uint8_t v___x_2393_; 
lean_del_object(v___x_2376_);
v___x_2389_ = l_Lean_Meta_Context_config(v___y_2367_);
v_transparency_2390_ = lean_ctor_get_uint8(v___x_2389_, 9);
lean_dec_ref(v___x_2389_);
lean_inc(v_a_2372_);
v___f_2391_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___boxed), 11, 2);
lean_closure_set(v___f_2391_, 0, v_a_2372_);
lean_closure_set(v___f_2391_, 1, v_e_2322_);
v___x_2392_ = 0;
v___x_2393_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2390_, v___x_2392_);
if (v___x_2393_ == 0)
{
lean_object* v_keyedConfig_2394_; uint8_t v_trackZetaDelta_2395_; lean_object* v_zetaDeltaSet_2396_; lean_object* v_lctx_2397_; lean_object* v_localInstances_2398_; lean_object* v_defEqCtx_x3f_2399_; lean_object* v_synthPendingDepth_2400_; lean_object* v_customCanUnfoldPredicate_x3f_2401_; uint8_t v_univApprox_2402_; uint8_t v_inTypeClassResolution_2403_; uint8_t v_cacheInferType_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v_keyedConfig_2394_ = lean_ctor_get(v___y_2367_, 0);
v_trackZetaDelta_2395_ = lean_ctor_get_uint8(v___y_2367_, sizeof(void*)*7);
v_zetaDeltaSet_2396_ = lean_ctor_get(v___y_2367_, 1);
v_lctx_2397_ = lean_ctor_get(v___y_2367_, 2);
v_localInstances_2398_ = lean_ctor_get(v___y_2367_, 3);
v_defEqCtx_x3f_2399_ = lean_ctor_get(v___y_2367_, 4);
v_synthPendingDepth_2400_ = lean_ctor_get(v___y_2367_, 5);
v_customCanUnfoldPredicate_x3f_2401_ = lean_ctor_get(v___y_2367_, 6);
v_univApprox_2402_ = lean_ctor_get_uint8(v___y_2367_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2403_ = lean_ctor_get_uint8(v___y_2367_, sizeof(void*)*7 + 2);
v_cacheInferType_2404_ = lean_ctor_get_uint8(v___y_2367_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2394_);
v___x_2405_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2392_, v_keyedConfig_2394_);
lean_inc(v_customCanUnfoldPredicate_x3f_2401_);
lean_inc(v_synthPendingDepth_2400_);
lean_inc(v_defEqCtx_x3f_2399_);
lean_inc_ref(v_localInstances_2398_);
lean_inc_ref(v_lctx_2397_);
lean_inc(v_zetaDeltaSet_2396_);
v___x_2406_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2406_, 0, v___x_2405_);
lean_ctor_set(v___x_2406_, 1, v_zetaDeltaSet_2396_);
lean_ctor_set(v___x_2406_, 2, v_lctx_2397_);
lean_ctor_set(v___x_2406_, 3, v_localInstances_2398_);
lean_ctor_set(v___x_2406_, 4, v_defEqCtx_x3f_2399_);
lean_ctor_set(v___x_2406_, 5, v_synthPendingDepth_2400_);
lean_ctor_set(v___x_2406_, 6, v_customCanUnfoldPredicate_x3f_2401_);
lean_ctor_set_uint8(v___x_2406_, sizeof(void*)*7, v_trackZetaDelta_2395_);
lean_ctor_set_uint8(v___x_2406_, sizeof(void*)*7 + 1, v_univApprox_2402_);
lean_ctor_set_uint8(v___x_2406_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2403_);
lean_ctor_set_uint8(v___x_2406_, sizeof(void*)*7 + 3, v_cacheInferType_2404_);
v___x_2407_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v___f_2391_, v___x_2361_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___x_2406_, v___y_2368_, v___y_2369_, v___y_2370_);
lean_dec_ref_known(v___x_2406_, 7);
v___y_2333_ = v_a_2372_;
v___y_2334_ = v___x_2407_;
goto v___jp_2332_;
}
else
{
lean_object* v___x_2408_; 
v___x_2408_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v___f_2391_, v___x_2361_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
v___y_2333_ = v_a_2372_;
v___y_2334_ = v___x_2408_;
goto v___jp_2332_;
}
}
}
}
else
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2417_; 
lean_dec(v_a_2372_);
lean_dec_ref(v_e_2322_);
v_a_2410_ = lean_ctor_get(v___x_2373_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2412_ = v___x_2373_;
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2373_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2415_; 
if (v_isShared_2413_ == 0)
{
v___x_2415_ = v___x_2412_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_a_2410_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
}
else
{
lean_dec_ref(v_e_2322_);
return v___x_2371_;
}
}
}
}
}
else
{
lean_object* v_a_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2448_; 
lean_dec_ref(v_e_2322_);
lean_dec_ref(v_F_2321_);
lean_dec(v_fixedPrefixSize_2320_);
lean_dec(v_recFnName_2319_);
v_a_2441_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2443_ = v___x_2351_;
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_a_2441_);
lean_dec(v___x_2351_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2446_; 
if (v_isShared_2444_ == 0)
{
v___x_2446_ = v___x_2443_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_a_2441_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
}
v___jp_2332_:
{
if (lean_obj_tag(v___y_2334_) == 0)
{
lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
v_isSharedCheck_2341_ = !lean_is_exclusive(v___y_2334_);
if (v_isSharedCheck_2341_ == 0)
{
lean_object* v_unused_2342_; 
v_unused_2342_ = lean_ctor_get(v___y_2334_, 0);
lean_dec(v_unused_2342_);
v___x_2336_ = v___y_2334_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_dec(v___y_2334_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 0, v___y_2333_);
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v___y_2333_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
else
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2350_; 
lean_dec_ref(v___y_2333_);
v_a_2343_ = lean_ctor_get(v___y_2334_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___y_2334_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2345_ = v___y_2334_;
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___y_2334_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2(lean_object* v_body_2449_, lean_object* v_recFnName_2450_, lean_object* v_fixedPrefixSize_2451_, lean_object* v_F_2452_, lean_object* v_x_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2463_ = lean_expr_instantiate1(v_body_2449_, v_x_2453_);
v___x_2464_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2450_, v_fixedPrefixSize_2451_, v_F_2452_, v___x_2463_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
return v___x_2464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp___boxed(lean_object* v_recFnName_2465_, lean_object* v_fixedPrefixSize_2466_, lean_object* v_F_2467_, lean_object* v_e_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_){
_start:
{
lean_object* v_res_2478_; 
v_res_2478_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2465_, v_fixedPrefixSize_2466_, v_F_2467_, v_e_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_);
lean_dec(v_a_2476_);
lean_dec_ref(v_a_2475_);
lean_dec(v_a_2474_);
lean_dec_ref(v_a_2473_);
lean_dec(v_a_2472_);
lean_dec_ref(v_a_2471_);
lean_dec(v_a_2470_);
lean_dec(v_a_2469_);
return v_res_2478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1___boxed(lean_object* v_recFnName_2479_, lean_object* v_fixedPrefixSize_2480_, lean_object* v_F_2481_, lean_object* v_sz_2482_, lean_object* v_i_2483_, lean_object* v_bs_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
size_t v_sz_boxed_2494_; size_t v_i_boxed_2495_; lean_object* v_res_2496_; 
v_sz_boxed_2494_ = lean_unbox_usize(v_sz_2482_);
lean_dec(v_sz_2482_);
v_i_boxed_2495_ = lean_unbox_usize(v_i_2483_);
lean_dec(v_i_2483_);
v_res_2496_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_2479_, v_fixedPrefixSize_2480_, v_F_2481_, v_sz_boxed_2494_, v_i_boxed_2495_, v_bs_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
lean_dec(v___y_2486_);
lean_dec(v___y_2485_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16___boxed(lean_object* v_recFnName_2497_, lean_object* v_fixedPrefixSize_2498_, lean_object* v_F_2499_, lean_object* v_x_2500_, lean_object* v_x_2501_, lean_object* v_x_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
lean_object* v_res_2512_; 
v_res_2512_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(v_recFnName_2497_, v_fixedPrefixSize_2498_, v_F_2499_, v_x_2500_, v_x_2501_, v_x_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec(v___y_2503_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___boxed(lean_object* v_recFnName_2513_, lean_object* v_fixedPrefixSize_2514_, lean_object* v_e_2515_, lean_object* v_as_2516_, lean_object* v_bs_2517_, lean_object* v_i_2518_, lean_object* v_cs_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
lean_object* v_res_2529_; 
v_res_2529_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(v_recFnName_2513_, v_fixedPrefixSize_2514_, v_e_2515_, v_as_2516_, v_bs_2517_, v_i_2518_, v_cs_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec(v___y_2521_);
lean_dec(v___y_2520_);
lean_dec_ref(v_bs_2517_);
lean_dec_ref(v_as_2516_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___boxed(lean_object* v_recFnName_2530_, lean_object* v_fixedPrefixSize_2531_, lean_object* v_F_2532_, lean_object* v_e_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_){
_start:
{
lean_object* v_res_2543_; 
v_res_2543_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2530_, v_fixedPrefixSize_2531_, v_F_2532_, v_e_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_);
lean_dec(v_a_2541_);
lean_dec_ref(v_a_2540_);
lean_dec(v_a_2539_);
lean_dec_ref(v_a_2538_);
lean_dec(v_a_2537_);
lean_dec_ref(v_a_2536_);
lean_dec(v_a_2535_);
lean_dec(v_a_2534_);
return v_res_2543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___boxed(lean_object* v_recFnName_2544_, lean_object* v_fixedPrefixSize_2545_, lean_object* v_F_2546_, lean_object* v_e_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_){
_start:
{
lean_object* v_res_2557_; 
v_res_2557_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2544_, v_fixedPrefixSize_2545_, v_F_2546_, v_e_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_);
lean_dec(v_a_2555_);
lean_dec_ref(v_a_2554_);
lean_dec(v_a_2553_);
lean_dec_ref(v_a_2552_);
lean_dec(v_a_2551_);
lean_dec_ref(v_a_2550_);
lean_dec(v_a_2549_);
lean_dec(v_a_2548_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___boxed(lean_object* v_recFnName_2558_, lean_object* v_fixedPrefixSize_2559_, lean_object* v_F_2560_, lean_object* v_e_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(v_recFnName_2558_, v_fixedPrefixSize_2559_, v_F_2560_, v_e_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_);
lean_dec(v_a_2569_);
lean_dec_ref(v_a_2568_);
lean_dec(v_a_2567_);
lean_dec_ref(v_a_2566_);
lean_dec(v_a_2565_);
lean_dec_ref(v_a_2564_);
lean_dec(v_a_2563_);
lean_dec(v_a_2562_);
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7(lean_object* v_00_u03b1_2572_, lean_object* v_k_2573_, uint8_t v_allowLevelAssignments_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
lean_object* v___x_2584_; 
v___x_2584_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v_k_2573_, v_allowLevelAssignments_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
return v___x_2584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___boxed(lean_object* v_00_u03b1_2585_, lean_object* v_k_2586_, lean_object* v_allowLevelAssignments_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2597_; lean_object* v_res_2598_; 
v_allowLevelAssignments_boxed_2597_ = lean_unbox(v_allowLevelAssignments_2587_);
v_res_2598_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7(v_00_u03b1_2585_, v_k_2586_, v_allowLevelAssignments_boxed_2597_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec(v___y_2589_);
lean_dec(v___y_2588_);
return v_res_2598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10(lean_object* v_00_u03b1_2599_, lean_object* v_name_2600_, uint8_t v_bi_2601_, lean_object* v_type_2602_, lean_object* v_k_2603_, uint8_t v_kind_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
lean_object* v___x_2614_; 
v___x_2614_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_name_2600_, v_bi_2601_, v_type_2602_, v_k_2603_, v_kind_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___boxed(lean_object* v_00_u03b1_2615_, lean_object* v_name_2616_, lean_object* v_bi_2617_, lean_object* v_type_2618_, lean_object* v_k_2619_, lean_object* v_kind_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
uint8_t v_bi_boxed_2630_; uint8_t v_kind_boxed_2631_; lean_object* v_res_2632_; 
v_bi_boxed_2630_ = lean_unbox(v_bi_2617_);
v_kind_boxed_2631_ = lean_unbox(v_kind_2620_);
v_res_2632_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10(v_00_u03b1_2615_, v_name_2616_, v_bi_boxed_2630_, v_type_2618_, v_k_2619_, v_kind_boxed_2631_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec(v___y_2622_);
lean_dec(v___y_2621_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(lean_object* v_00_u03b1_2633_, lean_object* v_e_2634_, lean_object* v_maxFVars_2635_, lean_object* v_k_2636_, uint8_t v_cleanupAnnotations_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_){
_start:
{
lean_object* v___x_2647_; 
v___x_2647_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(v_e_2634_, v_maxFVars_2635_, v_k_2636_, v_cleanupAnnotations_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___boxed(lean_object* v_00_u03b1_2648_, lean_object* v_e_2649_, lean_object* v_maxFVars_2650_, lean_object* v_k_2651_, lean_object* v_cleanupAnnotations_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2662_; lean_object* v_res_2663_; 
v_cleanupAnnotations_boxed_2662_ = lean_unbox(v_cleanupAnnotations_2652_);
v_res_2663_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(v_00_u03b1_2648_, v_e_2649_, v_maxFVars_2650_, v_k_2651_, v_cleanupAnnotations_boxed_2662_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec(v___y_2654_);
lean_dec(v___y_2653_);
return v_res_2663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0(lean_object* v_inst_2664_, lean_object* v_R_2665_, lean_object* v_a_2666_, lean_object* v_b_2667_){
_start:
{
lean_object* v___x_2668_; 
v___x_2668_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(v_a_2666_, v_b_2667_);
return v___x_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2(lean_object* v_cls_2669_, lean_object* v_msg_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_){
_start:
{
lean_object* v___x_2680_; 
v___x_2680_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(v_cls_2669_, v_msg_2670_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
return v___x_2680_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___boxed(lean_object* v_cls_2681_, lean_object* v_msg_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_){
_start:
{
lean_object* v_res_2692_; 
v_res_2692_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2(v_cls_2681_, v_msg_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
lean_dec(v___y_2684_);
lean_dec(v___y_2683_);
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4(lean_object* v_00_u03b2_2693_, lean_object* v_m_2694_, lean_object* v_a_2695_, lean_object* v_b_2696_){
_start:
{
lean_object* v___x_2697_; 
v___x_2697_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4___redArg(v_m_2694_, v_a_2695_, v_b_2696_);
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(lean_object* v_00_u03b1_2698_, lean_object* v_msg_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v___x_2709_; 
v___x_2709_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v_msg_2699_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___boxed(lean_object* v_00_u03b1_2710_, lean_object* v_msg_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(v_00_u03b1_2710_, v_msg_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec(v___y_2713_);
lean_dec(v___y_2712_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8(lean_object* v_00_u03b2_2722_, lean_object* v_m_2723_, lean_object* v_a_2724_){
_start:
{
lean_object* v___x_2725_; 
v___x_2725_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v_m_2723_, v_a_2724_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___boxed(lean_object* v_00_u03b2_2726_, lean_object* v_m_2727_, lean_object* v_a_2728_){
_start:
{
lean_object* v_res_2729_; 
v_res_2729_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8(v_00_u03b2_2726_, v_m_2727_, v_a_2728_);
lean_dec_ref(v_a_2728_);
lean_dec_ref(v_m_2727_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15(lean_object* v_00_u03b1_2730_, lean_object* v_name_2731_, lean_object* v_type_2732_, lean_object* v_val_2733_, lean_object* v_k_2734_, uint8_t v_nondep_2735_, uint8_t v_kind_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_){
_start:
{
lean_object* v___x_2746_; 
v___x_2746_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(v_name_2731_, v_type_2732_, v_val_2733_, v_k_2734_, v_nondep_2735_, v_kind_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
return v___x_2746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___boxed(lean_object* v_00_u03b1_2747_, lean_object* v_name_2748_, lean_object* v_type_2749_, lean_object* v_val_2750_, lean_object* v_k_2751_, lean_object* v_nondep_2752_, lean_object* v_kind_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_){
_start:
{
uint8_t v_nondep_boxed_2763_; uint8_t v_kind_boxed_2764_; lean_object* v_res_2765_; 
v_nondep_boxed_2763_ = lean_unbox(v_nondep_2752_);
v_kind_boxed_2764_ = lean_unbox(v_kind_2753_);
v_res_2765_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15(v_00_u03b1_2747_, v_name_2748_, v_type_2749_, v_val_2750_, v_k_2751_, v_nondep_boxed_2763_, v_kind_boxed_2764_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
lean_dec(v___y_2757_);
lean_dec_ref(v___y_2756_);
lean_dec(v___y_2755_);
lean_dec(v___y_2754_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20(lean_object* v_declName_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v___x_2776_; 
v___x_2776_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(v_declName_2766_, v___y_2774_);
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___boxed(lean_object* v_declName_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
lean_object* v_res_2787_; 
v_res_2787_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20(v_declName_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_);
lean_dec(v___y_2785_);
lean_dec_ref(v___y_2784_);
lean_dec(v___y_2783_);
lean_dec_ref(v___y_2782_);
lean_dec(v___y_2781_);
lean_dec_ref(v___y_2780_);
lean_dec(v___y_2779_);
lean_dec(v___y_2778_);
return v_res_2787_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4(lean_object* v_00_u03b2_2788_, lean_object* v_a_2789_, lean_object* v_x_2790_){
_start:
{
uint8_t v___x_2791_; 
v___x_2791_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg(v_a_2789_, v_x_2790_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___boxed(lean_object* v_00_u03b2_2792_, lean_object* v_a_2793_, lean_object* v_x_2794_){
_start:
{
uint8_t v_res_2795_; lean_object* v_r_2796_; 
v_res_2795_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4(v_00_u03b2_2792_, v_a_2793_, v_x_2794_);
lean_dec(v_x_2794_);
lean_dec_ref(v_a_2793_);
v_r_2796_ = lean_box(v_res_2795_);
return v_r_2796_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5(lean_object* v_00_u03b2_2797_, lean_object* v_data_2798_){
_start:
{
lean_object* v___x_2799_; 
v___x_2799_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5___redArg(v_data_2798_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6(lean_object* v_00_u03b2_2800_, lean_object* v_a_2801_, lean_object* v_b_2802_, lean_object* v_x_2803_){
_start:
{
lean_object* v___x_2804_; 
v___x_2804_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6___redArg(v_a_2801_, v_b_2802_, v_x_2803_);
return v___x_2804_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11(lean_object* v_00_u03b2_2805_, lean_object* v_a_2806_, lean_object* v_x_2807_){
_start:
{
lean_object* v___x_2808_; 
v___x_2808_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(v_a_2806_, v_x_2807_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___boxed(lean_object* v_00_u03b2_2809_, lean_object* v_a_2810_, lean_object* v_x_2811_){
_start:
{
lean_object* v_res_2812_; 
v_res_2812_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11(v_00_u03b2_2809_, v_a_2810_, v_x_2811_);
lean_dec(v_x_2811_);
lean_dec_ref(v_a_2810_);
return v_res_2812_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12(lean_object* v_00_u03b2_2813_, lean_object* v_i_2814_, lean_object* v_source_2815_, lean_object* v_target_2816_){
_start:
{
lean_object* v___x_2817_; 
v___x_2817_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12___redArg(v_i_2814_, v_source_2815_, v_target_2816_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21(lean_object* v_00_u03b1_2818_, lean_object* v_constName_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
lean_object* v___x_2829_; 
v___x_2829_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(v_constName_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___boxed(lean_object* v_00_u03b1_2830_, lean_object* v_constName_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21(v_00_u03b1_2830_, v_constName_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec(v___y_2832_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12_spec__22(lean_object* v_00_u03b2_2842_, lean_object* v_x_2843_, lean_object* v_x_2844_){
_start:
{
lean_object* v___x_2845_; 
v___x_2845_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12_spec__22___redArg(v_x_2843_, v_x_2844_);
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27(lean_object* v_00_u03b1_2846_, lean_object* v_ref_2847_, lean_object* v_constName_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
lean_object* v___x_2858_; 
v___x_2858_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(v_ref_2847_, v_constName_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___boxed(lean_object* v_00_u03b1_2859_, lean_object* v_ref_2860_, lean_object* v_constName_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_){
_start:
{
lean_object* v_res_2871_; 
v_res_2871_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27(v_00_u03b1_2859_, v_ref_2860_, v_constName_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec(v___y_2862_);
lean_dec(v_ref_2860_);
return v_res_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29(lean_object* v_00_u03b1_2872_, lean_object* v_ref_2873_, lean_object* v_msg_2874_, lean_object* v_declHint_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
lean_object* v___x_2885_; 
v___x_2885_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(v_ref_2873_, v_msg_2874_, v_declHint_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___boxed(lean_object* v_00_u03b1_2886_, lean_object* v_ref_2887_, lean_object* v_msg_2888_, lean_object* v_declHint_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_){
_start:
{
lean_object* v_res_2899_; 
v_res_2899_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29(v_00_u03b1_2886_, v_ref_2887_, v_msg_2888_, v_declHint_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_);
lean_dec(v___y_2897_);
lean_dec_ref(v___y_2896_);
lean_dec(v___y_2895_);
lean_dec_ref(v___y_2894_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
lean_dec(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec(v_ref_2887_);
return v_res_2899_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31(lean_object* v_msg_2900_, lean_object* v_declHint_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_){
_start:
{
lean_object* v___x_2911_; 
v___x_2911_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(v_msg_2900_, v_declHint_2901_, v___y_2909_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___boxed(lean_object* v_msg_2912_, lean_object* v_declHint_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31(v_msg_2912_, v_declHint_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec(v___y_2914_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31(lean_object* v_00_u03b1_2924_, lean_object* v_ref_2925_, lean_object* v_msg_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_){
_start:
{
lean_object* v___x_2936_; 
v___x_2936_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(v_ref_2925_, v_msg_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___boxed(lean_object* v_00_u03b1_2937_, lean_object* v_ref_2938_, lean_object* v_msg_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_){
_start:
{
lean_object* v_res_2949_; 
v_res_2949_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31(v_00_u03b1_2937_, v_ref_2938_, v_msg_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec(v___y_2940_);
lean_dec(v_ref_2938_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(lean_object* v_cls_2950_, lean_object* v_msg_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_){
_start:
{
lean_object* v_ref_2957_; lean_object* v___x_2958_; lean_object* v_a_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_3003_; 
v_ref_2957_ = lean_ctor_get(v___y_2954_, 2);
v___x_2958_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_);
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_3003_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2961_ = v___x_2958_;
v_isShared_2962_ = v_isSharedCheck_3003_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_a_2959_);
lean_dec(v___x_2958_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_3003_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2963_; lean_object* v_traceState_2964_; lean_object* v_env_2965_; lean_object* v_nextMacroScope_2966_; lean_object* v_ngen_2967_; lean_object* v_auxDeclNGen_2968_; lean_object* v_cache_2969_; lean_object* v_messages_2970_; lean_object* v_infoState_2971_; lean_object* v_snapshotTasks_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_3002_; 
v___x_2963_ = lean_st_ref_take(v___y_2955_);
v_traceState_2964_ = lean_ctor_get(v___x_2963_, 4);
v_env_2965_ = lean_ctor_get(v___x_2963_, 0);
v_nextMacroScope_2966_ = lean_ctor_get(v___x_2963_, 1);
v_ngen_2967_ = lean_ctor_get(v___x_2963_, 2);
v_auxDeclNGen_2968_ = lean_ctor_get(v___x_2963_, 3);
v_cache_2969_ = lean_ctor_get(v___x_2963_, 5);
v_messages_2970_ = lean_ctor_get(v___x_2963_, 6);
v_infoState_2971_ = lean_ctor_get(v___x_2963_, 7);
v_snapshotTasks_2972_ = lean_ctor_get(v___x_2963_, 8);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2974_ = v___x_2963_;
v_isShared_2975_ = v_isSharedCheck_3002_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_snapshotTasks_2972_);
lean_inc(v_infoState_2971_);
lean_inc(v_messages_2970_);
lean_inc(v_cache_2969_);
lean_inc(v_traceState_2964_);
lean_inc(v_auxDeclNGen_2968_);
lean_inc(v_ngen_2967_);
lean_inc(v_nextMacroScope_2966_);
lean_inc(v_env_2965_);
lean_dec(v___x_2963_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_3002_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
uint64_t v_tid_2976_; lean_object* v_traces_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_3001_; 
v_tid_2976_ = lean_ctor_get_uint64(v_traceState_2964_, sizeof(void*)*1);
v_traces_2977_ = lean_ctor_get(v_traceState_2964_, 0);
v_isSharedCheck_3001_ = !lean_is_exclusive(v_traceState_2964_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2979_ = v_traceState_2964_;
v_isShared_2980_ = v_isSharedCheck_3001_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_traces_2977_);
lean_dec(v_traceState_2964_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_3001_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___x_2981_; double v___x_2982_; uint8_t v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2991_; 
v___x_2981_ = lean_box(0);
v___x_2982_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0);
v___x_2983_ = 0;
v___x_2984_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__1));
v___x_2985_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2985_, 0, v_cls_2950_);
lean_ctor_set(v___x_2985_, 1, v___x_2981_);
lean_ctor_set(v___x_2985_, 2, v___x_2984_);
lean_ctor_set_float(v___x_2985_, sizeof(void*)*3, v___x_2982_);
lean_ctor_set_float(v___x_2985_, sizeof(void*)*3 + 8, v___x_2982_);
lean_ctor_set_uint8(v___x_2985_, sizeof(void*)*3 + 16, v___x_2983_);
v___x_2986_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__2));
v___x_2987_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2985_);
lean_ctor_set(v___x_2987_, 1, v_a_2959_);
lean_ctor_set(v___x_2987_, 2, v___x_2986_);
lean_inc(v_ref_2957_);
v___x_2988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2988_, 0, v_ref_2957_);
lean_ctor_set(v___x_2988_, 1, v___x_2987_);
v___x_2989_ = l_Lean_PersistentArray_push___redArg(v_traces_2977_, v___x_2988_);
if (v_isShared_2980_ == 0)
{
lean_ctor_set(v___x_2979_, 0, v___x_2989_);
v___x_2991_ = v___x_2979_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v___x_2989_);
lean_ctor_set_uint64(v_reuseFailAlloc_3000_, sizeof(void*)*1, v_tid_2976_);
v___x_2991_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
lean_object* v___x_2993_; 
if (v_isShared_2975_ == 0)
{
lean_ctor_set(v___x_2974_, 4, v___x_2991_);
v___x_2993_ = v___x_2974_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_env_2965_);
lean_ctor_set(v_reuseFailAlloc_2999_, 1, v_nextMacroScope_2966_);
lean_ctor_set(v_reuseFailAlloc_2999_, 2, v_ngen_2967_);
lean_ctor_set(v_reuseFailAlloc_2999_, 3, v_auxDeclNGen_2968_);
lean_ctor_set(v_reuseFailAlloc_2999_, 4, v___x_2991_);
lean_ctor_set(v_reuseFailAlloc_2999_, 5, v_cache_2969_);
lean_ctor_set(v_reuseFailAlloc_2999_, 6, v_messages_2970_);
lean_ctor_set(v_reuseFailAlloc_2999_, 7, v_infoState_2971_);
lean_ctor_set(v_reuseFailAlloc_2999_, 8, v_snapshotTasks_2972_);
v___x_2993_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2997_; 
v___x_2994_ = lean_st_ref_put(v___y_2955_, v___x_2993_);
v___x_2995_ = lean_box(0);
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 0, v___x_2995_);
v___x_2997_ = v___x_2961_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v___x_2995_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg___boxed(lean_object* v_cls_3004_, lean_object* v_msg_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_){
_start:
{
lean_object* v_res_3011_; 
v_res_3011_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3004_, v_msg_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_);
lean_dec(v___y_3009_);
lean_dec_ref(v___y_3008_);
lean_dec(v___y_3007_);
lean_dec_ref(v___y_3006_);
return v_res_3011_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0(void){
_start:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3012_ = lean_box(0);
v___x_3013_ = lean_unsigned_to_nat(16u);
v___x_3014_ = lean_mk_array(v___x_3013_, v___x_3012_);
return v___x_3014_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1(void){
_start:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3015_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0);
v___x_3016_ = lean_unsigned_to_nat(0u);
v___x_3017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3017_, 0, v___x_3016_);
lean_ctor_set(v___x_3017_, 1, v___x_3015_);
return v___x_3017_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3(void){
_start:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3019_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__2));
v___x_3020_ = l_Lean_stringToMessageData(v___x_3019_);
return v___x_3020_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5(void){
_start:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3022_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__4));
v___x_3023_ = l_Lean_stringToMessageData(v___x_3022_);
return v___x_3023_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7(void){
_start:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3025_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__6));
v___x_3026_ = l_Lean_stringToMessageData(v___x_3025_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(lean_object* v_recFnName_3027_, lean_object* v_fixedPrefixSize_3028_, lean_object* v_F_3029_, lean_object* v_e_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_){
_start:
{
lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v_toCold_3059_; lean_object* v_options_3060_; uint8_t v_hasTrace_3061_; 
v_toCold_3059_ = lean_ctor_get(v_a_3035_, 0);
v_options_3060_ = lean_ctor_get(v_toCold_3059_, 2);
v_hasTrace_3061_ = lean_ctor_get_uint8(v_options_3060_, sizeof(void*)*1);
if (v_hasTrace_3061_ == 0)
{
v___y_3039_ = v_a_3031_;
v___y_3040_ = v_a_3032_;
v___y_3041_ = v_a_3033_;
v___y_3042_ = v_a_3034_;
v___y_3043_ = v_a_3035_;
v___y_3044_ = v_a_3036_;
goto v___jp_3038_;
}
else
{
lean_object* v_inheritedTraceOptions_3062_; lean_object* v_cls_3063_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v_options_3070_; lean_object* v_inheritedTraceOptions_3071_; lean_object* v___y_3072_; lean_object* v___x_3093_; uint8_t v___x_3094_; 
v_inheritedTraceOptions_3062_ = lean_ctor_get(v_toCold_3059_, 11);
v_cls_3063_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_3093_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_3094_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3062_, v_options_3060_, v___x_3093_);
if (v___x_3094_ == 0)
{
v___y_3065_ = v_a_3031_;
v___y_3066_ = v_a_3032_;
v___y_3067_ = v_a_3033_;
v___y_3068_ = v_a_3034_;
v___y_3069_ = v_a_3035_;
v_options_3070_ = v_options_3060_;
v_inheritedTraceOptions_3071_ = v_inheritedTraceOptions_3062_;
v___y_3072_ = v_a_3036_;
goto v___jp_3064_;
}
else
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; 
v___x_3095_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7);
lean_inc_ref(v_e_3030_);
v___x_3096_ = l_Lean_indentExpr(v_e_3030_);
v___x_3097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3097_, 0, v___x_3095_);
lean_ctor_set(v___x_3097_, 1, v___x_3096_);
v___x_3098_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3063_, v___x_3097_, v_a_3033_, v_a_3034_, v_a_3035_, v_a_3036_);
if (lean_obj_tag(v___x_3098_) == 0)
{
lean_dec_ref_known(v___x_3098_, 1);
v___y_3065_ = v_a_3031_;
v___y_3066_ = v_a_3032_;
v___y_3067_ = v_a_3033_;
v___y_3068_ = v_a_3034_;
v___y_3069_ = v_a_3035_;
v_options_3070_ = v_options_3060_;
v_inheritedTraceOptions_3071_ = v_inheritedTraceOptions_3062_;
v___y_3072_ = v_a_3036_;
goto v___jp_3064_;
}
else
{
lean_object* v_a_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3106_; 
lean_dec_ref(v_e_3030_);
lean_dec_ref(v_F_3029_);
lean_dec(v_fixedPrefixSize_3028_);
lean_dec(v_recFnName_3027_);
v_a_3099_ = lean_ctor_get(v___x_3098_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3098_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3101_ = v___x_3098_;
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_a_3099_);
lean_dec(v___x_3098_);
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
v___jp_3064_:
{
lean_object* v___x_3073_; uint8_t v___x_3074_; 
v___x_3073_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_3074_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3071_, v_options_3070_, v___x_3073_);
if (v___x_3074_ == 0)
{
v___y_3039_ = v___y_3065_;
v___y_3040_ = v___y_3066_;
v___y_3041_ = v___y_3067_;
v___y_3042_ = v___y_3068_;
v___y_3043_ = v___y_3069_;
v___y_3044_ = v___y_3072_;
goto v___jp_3038_;
}
else
{
lean_object* v___x_3075_; 
lean_inc(v___y_3072_);
lean_inc_ref(v___y_3069_);
lean_inc(v___y_3068_);
lean_inc_ref(v___y_3067_);
lean_inc_ref(v_F_3029_);
v___x_3075_ = lean_infer_type(v_F_3029_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3072_);
if (lean_obj_tag(v___x_3075_) == 0)
{
lean_object* v_a_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v_a_3076_ = lean_ctor_get(v___x_3075_, 0);
lean_inc(v_a_3076_);
lean_dec_ref_known(v___x_3075_, 1);
v___x_3077_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3);
lean_inc_ref(v_F_3029_);
v___x_3078_ = l_Lean_MessageData_ofExpr(v_F_3029_);
v___x_3079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3079_, 0, v___x_3077_);
lean_ctor_set(v___x_3079_, 1, v___x_3078_);
v___x_3080_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5);
v___x_3081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3081_, 0, v___x_3079_);
lean_ctor_set(v___x_3081_, 1, v___x_3080_);
v___x_3082_ = l_Lean_indentExpr(v_a_3076_);
v___x_3083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3083_, 0, v___x_3081_);
lean_ctor_set(v___x_3083_, 1, v___x_3082_);
v___x_3084_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3063_, v___x_3083_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3072_);
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_dec_ref_known(v___x_3084_, 1);
v___y_3039_ = v___y_3065_;
v___y_3040_ = v___y_3066_;
v___y_3041_ = v___y_3067_;
v___y_3042_ = v___y_3068_;
v___y_3043_ = v___y_3069_;
v___y_3044_ = v___y_3072_;
goto v___jp_3038_;
}
else
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3092_; 
lean_dec_ref(v_e_3030_);
lean_dec_ref(v_F_3029_);
lean_dec(v_fixedPrefixSize_3028_);
lean_dec(v_recFnName_3027_);
v_a_3085_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3087_ = v___x_3084_;
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3084_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3090_; 
if (v_isShared_3088_ == 0)
{
v___x_3090_ = v___x_3087_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_a_3085_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
}
}
else
{
lean_dec_ref(v_e_3030_);
lean_dec_ref(v_F_3029_);
lean_dec(v_fixedPrefixSize_3028_);
lean_dec(v_recFnName_3027_);
return v___x_3075_;
}
}
}
}
v___jp_3038_:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3045_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1);
v___x_3046_ = lean_st_mk_ref(v___x_3045_);
v___x_3047_ = lean_st_mk_ref(v___x_3045_);
v___x_3048_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_3027_, v_fixedPrefixSize_3028_, v_F_3029_, v_e_3030_, v___x_3047_, v___x_3046_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v_a_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3058_; 
v_a_3049_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3051_ = v___x_3048_;
v_isShared_3052_ = v_isSharedCheck_3058_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_a_3049_);
lean_dec(v___x_3048_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3058_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3056_; 
v___x_3053_ = lean_st_ref_get(v___x_3047_);
lean_dec(v___x_3047_);
lean_dec(v___x_3053_);
v___x_3054_ = lean_st_ref_get(v___x_3046_);
lean_dec(v___x_3046_);
lean_dec(v___x_3054_);
if (v_isShared_3052_ == 0)
{
v___x_3056_ = v___x_3051_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_a_3049_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
else
{
lean_dec(v___x_3047_);
lean_dec(v___x_3046_);
return v___x_3048_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___boxed(lean_object* v_recFnName_3107_, lean_object* v_fixedPrefixSize_3108_, lean_object* v_F_3109_, lean_object* v_e_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_){
_start:
{
lean_object* v_res_3118_; 
v_res_3118_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(v_recFnName_3107_, v_fixedPrefixSize_3108_, v_F_3109_, v_e_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_, v_a_3115_, v_a_3116_);
lean_dec(v_a_3116_);
lean_dec_ref(v_a_3115_);
lean_dec(v_a_3114_);
lean_dec_ref(v_a_3113_);
lean_dec(v_a_3112_);
lean_dec_ref(v_a_3111_);
return v_res_3118_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0(lean_object* v_cls_3119_, lean_object* v_msg_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_){
_start:
{
lean_object* v___x_3128_; 
v___x_3128_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3119_, v_msg_3120_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_);
return v___x_3128_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___boxed(lean_object* v_cls_3129_, lean_object* v_msg_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_){
_start:
{
lean_object* v_res_3138_; 
v_res_3138_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0(v_cls_3129_, v_msg_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
return v_res_3138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0(lean_object* v_k_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v_b_3142_, lean_object* v_c_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_){
_start:
{
lean_object* v___x_3149_; 
lean_inc(v___y_3147_);
lean_inc_ref(v___y_3146_);
lean_inc(v___y_3145_);
lean_inc_ref(v___y_3144_);
lean_inc(v___y_3141_);
lean_inc_ref(v___y_3140_);
v___x_3149_ = lean_apply_9(v_k_3139_, v_b_3142_, v_c_3143_, v___y_3140_, v___y_3141_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, lean_box(0));
return v___x_3149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed(lean_object* v_k_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v_b_3153_, lean_object* v_c_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_){
_start:
{
lean_object* v_res_3160_; 
v_res_3160_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0(v_k_3150_, v___y_3151_, v___y_3152_, v_b_3153_, v_c_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
return v_res_3160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(lean_object* v_e_3161_, lean_object* v_k_3162_, uint8_t v_cleanupAnnotations_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_){
_start:
{
lean_object* v___f_3171_; uint8_t v___x_3172_; uint8_t v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
lean_inc(v___y_3165_);
lean_inc_ref(v___y_3164_);
v___f_3171_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3171_, 0, v_k_3162_);
lean_closure_set(v___f_3171_, 1, v___y_3164_);
lean_closure_set(v___f_3171_, 2, v___y_3165_);
v___x_3172_ = 1;
v___x_3173_ = 0;
v___x_3174_ = lean_box(0);
v___x_3175_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3161_, v___x_3172_, v___x_3173_, v___x_3172_, v___x_3173_, v___x_3174_, v___f_3171_, v_cleanupAnnotations_3163_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
if (lean_obj_tag(v___x_3175_) == 0)
{
return v___x_3175_;
}
else
{
lean_object* v_a_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3183_; 
v_a_3176_ = lean_ctor_get(v___x_3175_, 0);
v_isSharedCheck_3183_ = !lean_is_exclusive(v___x_3175_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3178_ = v___x_3175_;
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_a_3176_);
lean_dec(v___x_3175_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v___x_3181_; 
if (v_isShared_3179_ == 0)
{
v___x_3181_ = v___x_3178_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_a_3176_);
v___x_3181_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
return v___x_3181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___boxed(lean_object* v_e_3184_, lean_object* v_k_3185_, lean_object* v_cleanupAnnotations_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3194_; lean_object* v_res_3195_; 
v_cleanupAnnotations_boxed_3194_ = lean_unbox(v_cleanupAnnotations_3186_);
v_res_3195_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v_e_3184_, v_k_3185_, v_cleanupAnnotations_boxed_3194_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3191_);
lean_dec(v___y_3190_);
lean_dec_ref(v___y_3189_);
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
return v_res_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0(lean_object* v_00_u03b1_3196_, lean_object* v_e_3197_, lean_object* v_k_3198_, uint8_t v_cleanupAnnotations_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_){
_start:
{
lean_object* v___x_3207_; 
v___x_3207_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v_e_3197_, v_k_3198_, v_cleanupAnnotations_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
return v___x_3207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___boxed(lean_object* v_00_u03b1_3208_, lean_object* v_e_3209_, lean_object* v_k_3210_, lean_object* v_cleanupAnnotations_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3219_; lean_object* v_res_3220_; 
v_cleanupAnnotations_boxed_3219_ = lean_unbox(v_cleanupAnnotations_3211_);
v_res_3220_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0(v_00_u03b1_3208_, v_e_3209_, v_k_3210_, v_cleanupAnnotations_boxed_3219_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_);
lean_dec(v___y_3217_);
lean_dec_ref(v___y_3216_);
lean_dec(v___y_3215_);
lean_dec_ref(v___y_3214_);
lean_dec(v___y_3213_);
lean_dec_ref(v___y_3212_);
return v_res_3220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(lean_object* v_e_3221_, lean_object* v_maxFVars_3222_, lean_object* v_k_3223_, uint8_t v_cleanupAnnotations_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_){
_start:
{
lean_object* v___f_3232_; uint8_t v___x_3233_; uint8_t v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; 
lean_inc(v___y_3226_);
lean_inc_ref(v___y_3225_);
v___f_3232_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3232_, 0, v_k_3223_);
lean_closure_set(v___f_3232_, 1, v___y_3225_);
lean_closure_set(v___f_3232_, 2, v___y_3226_);
v___x_3233_ = 1;
v___x_3234_ = 0;
v___x_3235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3235_, 0, v_maxFVars_3222_);
v___x_3236_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3221_, v___x_3233_, v___x_3234_, v___x_3233_, v___x_3234_, v___x_3235_, v___f_3232_, v_cleanupAnnotations_3224_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_);
lean_dec_ref_known(v___x_3235_, 1);
if (lean_obj_tag(v___x_3236_) == 0)
{
return v___x_3236_;
}
else
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
v_reuseFailAlloc_3243_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg___boxed(lean_object* v_e_3245_, lean_object* v_maxFVars_3246_, lean_object* v_k_3247_, lean_object* v_cleanupAnnotations_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3256_; lean_object* v_res_3257_; 
v_cleanupAnnotations_boxed_3256_ = lean_unbox(v_cleanupAnnotations_3248_);
v_res_3257_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_e_3245_, v_maxFVars_3246_, v_k_3247_, v_cleanupAnnotations_boxed_3256_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
return v_res_3257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2(lean_object* v_00_u03b1_3258_, lean_object* v_e_3259_, lean_object* v_maxFVars_3260_, lean_object* v_k_3261_, uint8_t v_cleanupAnnotations_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_){
_start:
{
lean_object* v___x_3270_; 
v___x_3270_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_e_3259_, v_maxFVars_3260_, v_k_3261_, v_cleanupAnnotations_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___boxed(lean_object* v_00_u03b1_3271_, lean_object* v_e_3272_, lean_object* v_maxFVars_3273_, lean_object* v_k_3274_, lean_object* v_cleanupAnnotations_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3283_; lean_object* v_res_3284_; 
v_cleanupAnnotations_boxed_3283_ = lean_unbox(v_cleanupAnnotations_3275_);
v_res_3284_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2(v_00_u03b1_3271_, v_e_3272_, v_maxFVars_3273_, v_k_3274_, v_cleanupAnnotations_boxed_3283_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
lean_dec(v___y_3277_);
lean_dec_ref(v___y_3276_);
return v_res_3284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0(lean_object* v_a_3285_, lean_object* v___x_3286_, lean_object* v___x_3287_, lean_object* v_x_3288_, uint8_t v___x_3289_, lean_object* v_xs_3290_, lean_object* v_type_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_){
_start:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3299_ = l_Lean_LocalDecl_type(v_a_3285_);
v___x_3300_ = lean_array_get_borrowed(v___x_3286_, v_xs_3290_, v___x_3287_);
v___x_3301_ = l_Lean_Expr_replaceFVar(v___x_3299_, v_x_3288_, v___x_3300_);
lean_dec_ref(v___x_3299_);
v___x_3302_ = l_Lean_mkArrow(v___x_3301_, v_type_3291_, v___y_3296_, v___y_3297_);
if (lean_obj_tag(v___x_3302_) == 0)
{
lean_object* v_a_3303_; uint8_t v___x_3304_; uint8_t v___x_3305_; lean_object* v___x_3306_; 
v_a_3303_ = lean_ctor_get(v___x_3302_, 0);
lean_inc_n(v_a_3303_, 2);
lean_dec_ref_known(v___x_3302_, 1);
v___x_3304_ = 0;
v___x_3305_ = 1;
v___x_3306_ = l_Lean_Meta_mkLambdaFVars(v_xs_3290_, v_a_3303_, v___x_3304_, v___x_3289_, v___x_3304_, v___x_3289_, v___x_3305_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_object* v_a_3307_; lean_object* v___x_3308_; 
v_a_3307_ = lean_ctor_get(v___x_3306_, 0);
lean_inc(v_a_3307_);
lean_dec_ref_known(v___x_3306_, 1);
v___x_3308_ = l_Lean_Meta_getLevel(v_a_3303_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
if (lean_obj_tag(v___x_3308_) == 0)
{
lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3317_; 
v_a_3309_ = lean_ctor_get(v___x_3308_, 0);
v_isSharedCheck_3317_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3317_ == 0)
{
v___x_3311_ = v___x_3308_;
v_isShared_3312_ = v_isSharedCheck_3317_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v___x_3308_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3317_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3313_; lean_object* v___x_3315_; 
v___x_3313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3313_, 0, v_a_3307_);
lean_ctor_set(v___x_3313_, 1, v_a_3309_);
if (v_isShared_3312_ == 0)
{
lean_ctor_set(v___x_3311_, 0, v___x_3313_);
v___x_3315_ = v___x_3311_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v___x_3313_);
v___x_3315_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
return v___x_3315_;
}
}
}
else
{
lean_object* v_a_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3325_; 
lean_dec(v_a_3307_);
v_a_3318_ = lean_ctor_get(v___x_3308_, 0);
v_isSharedCheck_3325_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3320_ = v___x_3308_;
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_a_3318_);
lean_dec(v___x_3308_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v___x_3323_; 
if (v_isShared_3321_ == 0)
{
v___x_3323_ = v___x_3320_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_a_3318_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
return v___x_3323_;
}
}
}
}
else
{
lean_object* v_a_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3333_; 
lean_dec(v_a_3303_);
v_a_3326_ = lean_ctor_get(v___x_3306_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v___x_3306_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3328_ = v___x_3306_;
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_a_3326_);
lean_dec(v___x_3306_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___x_3331_; 
if (v_isShared_3329_ == 0)
{
v___x_3331_ = v___x_3328_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v_a_3326_);
v___x_3331_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
return v___x_3331_;
}
}
}
}
else
{
lean_object* v_a_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3341_; 
v_a_3334_ = lean_ctor_get(v___x_3302_, 0);
v_isSharedCheck_3341_ = !lean_is_exclusive(v___x_3302_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3336_ = v___x_3302_;
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_a_3334_);
lean_dec(v___x_3302_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3339_; 
if (v_isShared_3337_ == 0)
{
v___x_3339_ = v___x_3336_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_a_3334_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed(lean_object* v_a_3342_, lean_object* v___x_3343_, lean_object* v___x_3344_, lean_object* v_x_3345_, lean_object* v___x_3346_, lean_object* v_xs_3347_, lean_object* v_type_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_){
_start:
{
uint8_t v___x_6244__boxed_3356_; lean_object* v_res_3357_; 
v___x_6244__boxed_3356_ = lean_unbox(v___x_3346_);
v_res_3357_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0(v_a_3342_, v___x_3343_, v___x_3344_, v_x_3345_, v___x_6244__boxed_3356_, v_xs_3347_, v_type_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_);
lean_dec(v___y_3354_);
lean_dec_ref(v___y_3353_);
lean_dec(v___y_3352_);
lean_dec_ref(v___y_3351_);
lean_dec(v___y_3350_);
lean_dec_ref(v___y_3349_);
lean_dec_ref(v_xs_3347_);
lean_dec(v___x_3344_);
lean_dec_ref(v___x_3343_);
lean_dec_ref(v_a_3342_);
return v_res_3357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0(lean_object* v_k_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v_b_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_){
_start:
{
lean_object* v___x_3367_; 
lean_inc(v___y_3365_);
lean_inc_ref(v___y_3364_);
lean_inc(v___y_3363_);
lean_inc_ref(v___y_3362_);
lean_inc(v___y_3360_);
lean_inc_ref(v___y_3359_);
v___x_3367_ = lean_apply_8(v_k_3358_, v_b_3361_, v___y_3359_, v___y_3360_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, lean_box(0));
return v___x_3367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_k_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v_b_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_){
_start:
{
lean_object* v_res_3377_; 
v_res_3377_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0(v_k_3368_, v___y_3369_, v___y_3370_, v_b_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
lean_dec(v___y_3375_);
lean_dec_ref(v___y_3374_);
lean_dec(v___y_3373_);
lean_dec_ref(v___y_3372_);
lean_dec(v___y_3370_);
lean_dec_ref(v___y_3369_);
return v_res_3377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(lean_object* v_name_3378_, uint8_t v_bi_3379_, lean_object* v_type_3380_, lean_object* v_k_3381_, uint8_t v_kind_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_){
_start:
{
lean_object* v___f_3390_; lean_object* v___x_3391_; 
lean_inc(v___y_3384_);
lean_inc_ref(v___y_3383_);
v___f_3390_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3390_, 0, v_k_3381_);
lean_closure_set(v___f_3390_, 1, v___y_3383_);
lean_closure_set(v___f_3390_, 2, v___y_3384_);
v___x_3391_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3378_, v_bi_3379_, v_type_3380_, v___f_3390_, v_kind_3382_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_);
if (lean_obj_tag(v___x_3391_) == 0)
{
return v___x_3391_;
}
else
{
lean_object* v_a_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3399_; 
v_a_3392_ = lean_ctor_get(v___x_3391_, 0);
v_isSharedCheck_3399_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3399_ == 0)
{
v___x_3394_ = v___x_3391_;
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_a_3392_);
lean_dec(v___x_3391_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
lean_object* v___x_3397_; 
if (v_isShared_3395_ == 0)
{
v___x_3397_ = v___x_3394_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v_a_3392_);
v___x_3397_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
return v___x_3397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___boxed(lean_object* v_name_3400_, lean_object* v_bi_3401_, lean_object* v_type_3402_, lean_object* v_k_3403_, lean_object* v_kind_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_){
_start:
{
uint8_t v_bi_boxed_3412_; uint8_t v_kind_boxed_3413_; lean_object* v_res_3414_; 
v_bi_boxed_3412_ = lean_unbox(v_bi_3401_);
v_kind_boxed_3413_ = lean_unbox(v_kind_3404_);
v_res_3414_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(v_name_3400_, v_bi_boxed_3412_, v_type_3402_, v_k_3403_, v_kind_boxed_3413_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
return v_res_3414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(lean_object* v_name_3415_, lean_object* v_type_3416_, lean_object* v_k_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_){
_start:
{
uint8_t v___x_3425_; uint8_t v___x_3426_; lean_object* v___x_3427_; 
v___x_3425_ = 0;
v___x_3426_ = 0;
v___x_3427_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(v_name_3415_, v___x_3425_, v_type_3416_, v_k_3417_, v___x_3426_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_);
return v___x_3427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___boxed(lean_object* v_name_3428_, lean_object* v_type_3429_, lean_object* v_k_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_){
_start:
{
lean_object* v_res_3438_; 
v_res_3438_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_name_3428_, v_type_3429_, v_k_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_);
lean_dec(v___y_3436_);
lean_dec_ref(v___y_3435_);
lean_dec(v___y_3434_);
lean_dec_ref(v___y_3433_);
lean_dec(v___y_3432_);
lean_dec_ref(v___y_3431_);
return v_res_3438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(lean_object* v_x_3452_, lean_object* v_F_3453_, lean_object* v_val_3454_, lean_object* v_k_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_){
_start:
{
lean_object* v___x_3463_; uint8_t v___y_3465_; uint8_t v___x_3579_; 
v___x_3463_ = l_Lean_instInhabitedExpr;
v___x_3579_ = l_Lean_Expr_isFVar(v_x_3452_);
if (v___x_3579_ == 0)
{
v___y_3465_ = v___x_3579_;
goto v___jp_3464_;
}
else
{
lean_object* v___x_3580_; lean_object* v___x_3581_; uint8_t v___x_3582_; 
v___x_3580_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6));
v___x_3581_ = lean_unsigned_to_nat(6u);
v___x_3582_ = l_Lean_Expr_isAppOfArity(v_val_3454_, v___x_3580_, v___x_3581_);
v___y_3465_ = v___x_3582_;
goto v___jp_3464_;
}
v___jp_3464_:
{
if (v___y_3465_ == 0)
{
lean_object* v___x_3466_; 
lean_inc(v_a_3461_);
lean_inc_ref(v_a_3460_);
lean_inc(v_a_3459_);
lean_inc_ref(v_a_3458_);
lean_inc(v_a_3457_);
lean_inc_ref(v_a_3456_);
v___x_3466_ = lean_apply_10(v_k_3455_, v_x_3452_, v_F_3453_, v_val_3454_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_, lean_box(0));
return v___x_3466_;
}
else
{
lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; uint8_t v___x_3473_; 
v___x_3467_ = lean_unsigned_to_nat(3u);
v___x_3468_ = l_Lean_Expr_getAppNumArgs(v_val_3454_);
v___x_3469_ = lean_nat_sub(v___x_3468_, v___x_3467_);
v___x_3470_ = lean_unsigned_to_nat(1u);
v___x_3471_ = lean_nat_sub(v___x_3469_, v___x_3470_);
lean_dec(v___x_3469_);
v___x_3472_ = l_Lean_Expr_getRevArg_x21(v_val_3454_, v___x_3471_);
v___x_3473_ = lean_expr_eqv(v___x_3472_, v_x_3452_);
lean_dec_ref(v___x_3472_);
if (v___x_3473_ == 0)
{
lean_object* v___x_3474_; 
lean_dec(v___x_3468_);
lean_inc(v_a_3461_);
lean_inc_ref(v_a_3460_);
lean_inc(v_a_3459_);
lean_inc_ref(v_a_3458_);
lean_inc(v_a_3457_);
lean_inc_ref(v_a_3456_);
v___x_3474_ = lean_apply_10(v_k_3455_, v_x_3452_, v_F_3453_, v_val_3454_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_, lean_box(0));
return v___x_3474_;
}
else
{
lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; uint8_t v___x_3479_; 
v___x_3475_ = lean_unsigned_to_nat(4u);
v___x_3476_ = lean_nat_sub(v___x_3468_, v___x_3475_);
v___x_3477_ = lean_nat_sub(v___x_3476_, v___x_3470_);
lean_dec(v___x_3476_);
v___x_3478_ = l_Lean_Expr_getRevArg_x21(v_val_3454_, v___x_3477_);
v___x_3479_ = l_Lean_Expr_isLambda(v___x_3478_);
lean_dec_ref(v___x_3478_);
if (v___x_3479_ == 0)
{
lean_object* v___x_3480_; 
lean_dec(v___x_3468_);
lean_inc(v_a_3461_);
lean_inc_ref(v_a_3460_);
lean_inc(v_a_3459_);
lean_inc_ref(v_a_3458_);
lean_inc(v_a_3457_);
lean_inc_ref(v_a_3456_);
v___x_3480_ = lean_apply_10(v_k_3455_, v_x_3452_, v_F_3453_, v_val_3454_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_, lean_box(0));
return v___x_3480_;
}
else
{
lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; uint8_t v___x_3485_; 
v___x_3481_ = lean_unsigned_to_nat(5u);
v___x_3482_ = lean_nat_sub(v___x_3468_, v___x_3481_);
v___x_3483_ = lean_nat_sub(v___x_3482_, v___x_3470_);
lean_dec(v___x_3482_);
v___x_3484_ = l_Lean_Expr_getRevArg_x21(v_val_3454_, v___x_3483_);
v___x_3485_ = l_Lean_Expr_isLambda(v___x_3484_);
lean_dec_ref(v___x_3484_);
if (v___x_3485_ == 0)
{
lean_object* v___x_3486_; 
lean_dec(v___x_3468_);
lean_inc(v_a_3461_);
lean_inc_ref(v_a_3460_);
lean_inc(v_a_3459_);
lean_inc_ref(v_a_3458_);
lean_inc(v_a_3457_);
lean_inc_ref(v_a_3456_);
v___x_3486_ = lean_apply_10(v_k_3455_, v_x_3452_, v_F_3453_, v_val_3454_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_, lean_box(0));
return v___x_3486_;
}
else
{
lean_object* v___x_3487_; lean_object* v___x_3488_; 
v___x_3487_ = l_Lean_Expr_fvarId_x21(v_F_3453_);
v___x_3488_ = l_Lean_FVarId_getDecl___redArg(v___x_3487_, v_a_3458_, v_a_3460_, v_a_3461_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v_a_3489_; lean_object* v_dummy_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v_args_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___f_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; uint8_t v___x_3499_; lean_object* v___x_3500_; 
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
lean_inc_n(v_a_3489_, 2);
lean_dec_ref_known(v___x_3488_, 1);
v_dummy_3490_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_3468_);
v___x_3491_ = lean_mk_array(v___x_3468_, v_dummy_3490_);
v___x_3492_ = lean_nat_sub(v___x_3468_, v___x_3470_);
lean_dec(v___x_3468_);
v_args_3493_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_3454_, v___x_3491_, v___x_3492_);
v___x_3494_ = lean_unsigned_to_nat(0u);
v___x_3495_ = lean_box(v___x_3479_);
lean_inc_ref(v_x_3452_);
v___f_3496_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed), 14, 5);
lean_closure_set(v___f_3496_, 0, v_a_3489_);
lean_closure_set(v___f_3496_, 1, v___x_3463_);
lean_closure_set(v___f_3496_, 2, v___x_3494_);
lean_closure_set(v___f_3496_, 3, v_x_3452_);
lean_closure_set(v___f_3496_, 4, v___x_3495_);
v___x_3497_ = lean_unsigned_to_nat(2u);
v___x_3498_ = lean_array_get(v___x_3463_, v_args_3493_, v___x_3497_);
v___x_3499_ = 0;
v___x_3500_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_3498_, v___f_3496_, v___x_3499_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
if (lean_obj_tag(v___x_3500_) == 0)
{
lean_object* v_a_3501_; lean_object* v_fst_3502_; lean_object* v_snd_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3562_; 
v_a_3501_ = lean_ctor_get(v___x_3500_, 0);
lean_inc(v_a_3501_);
lean_dec_ref_known(v___x_3500_, 1);
v_fst_3502_ = lean_ctor_get(v_a_3501_, 0);
v_snd_3503_ = lean_ctor_get(v_a_3501_, 1);
v_isSharedCheck_3562_ = !lean_is_exclusive(v_a_3501_);
if (v_isSharedCheck_3562_ == 0)
{
v___x_3505_ = v_a_3501_;
v_isShared_3506_ = v_isSharedCheck_3562_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_snd_3503_);
lean_inc(v_fst_3502_);
lean_dec(v_a_3501_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3562_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v_00_u03b1_3507_; lean_object* v_00_u03b2_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; 
v_00_u03b1_3507_ = lean_array_get(v___x_3463_, v_args_3493_, v___x_3494_);
v_00_u03b2_3508_ = lean_array_get(v___x_3463_, v_args_3493_, v___x_3470_);
v___x_3509_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__2));
v___x_3510_ = lean_array_get(v___x_3463_, v_args_3493_, v___x_3475_);
lean_inc_ref(v_x_3452_);
lean_inc(v_a_3489_);
lean_inc_ref(v_k_3455_);
lean_inc(v_00_u03b2_3508_);
lean_inc(v_00_u03b1_3507_);
v___x_3511_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3463_, v___x_3494_, v_00_u03b1_3507_, v_00_u03b2_3508_, v___x_3467_, v_k_3455_, v___x_3497_, v___x_3499_, v___x_3479_, v_a_3489_, v_x_3452_, v___x_3470_, v___x_3509_, v___x_3510_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_object* v_a_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; 
v_a_3512_ = lean_ctor_get(v___x_3511_, 0);
lean_inc(v_a_3512_);
lean_dec_ref_known(v___x_3511_, 1);
v___x_3513_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__4));
v___x_3514_ = lean_array_get(v___x_3463_, v_args_3493_, v___x_3481_);
lean_dec_ref(v_args_3493_);
lean_inc_ref(v_x_3452_);
lean_inc(v_00_u03b2_3508_);
lean_inc(v_00_u03b1_3507_);
v___x_3515_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3463_, v___x_3494_, v_00_u03b1_3507_, v_00_u03b2_3508_, v___x_3467_, v_k_3455_, v___x_3497_, v___x_3499_, v___x_3479_, v_a_3489_, v_x_3452_, v___x_3470_, v___x_3513_, v___x_3514_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_a_3516_; lean_object* v___x_3517_; 
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
lean_inc(v_a_3516_);
lean_dec_ref_known(v___x_3515_, 1);
lean_inc(v_00_u03b1_3507_);
v___x_3517_ = l_Lean_Meta_getLevel(v_00_u03b1_3507_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
if (lean_obj_tag(v___x_3517_) == 0)
{
lean_object* v_a_3518_; lean_object* v___x_3519_; 
v_a_3518_ = lean_ctor_get(v___x_3517_, 0);
lean_inc(v_a_3518_);
lean_dec_ref_known(v___x_3517_, 1);
lean_inc(v_00_u03b2_3508_);
v___x_3519_ = l_Lean_Meta_getLevel(v_00_u03b2_3508_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3545_; 
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3522_ = v___x_3519_;
v_isShared_3523_ = v_isSharedCheck_3545_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3519_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3545_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3527_; 
v___x_3524_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6));
v___x_3525_ = lean_box(0);
if (v_isShared_3506_ == 0)
{
lean_ctor_set_tag(v___x_3505_, 1);
lean_ctor_set(v___x_3505_, 1, v___x_3525_);
lean_ctor_set(v___x_3505_, 0, v_a_3520_);
v___x_3527_ = v___x_3505_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_a_3520_);
lean_ctor_set(v_reuseFailAlloc_3544_, 1, v___x_3525_);
v___x_3527_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3542_; 
v___x_3528_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3528_, 0, v_a_3518_);
lean_ctor_set(v___x_3528_, 1, v___x_3527_);
v___x_3529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3529_, 0, v_snd_3503_);
lean_ctor_set(v___x_3529_, 1, v___x_3528_);
v___x_3530_ = l_Lean_mkConst(v___x_3524_, v___x_3529_);
v___x_3531_ = lean_unsigned_to_nat(7u);
v___x_3532_ = lean_mk_empty_array_with_capacity(v___x_3531_);
v___x_3533_ = lean_array_push(v___x_3532_, v_00_u03b1_3507_);
v___x_3534_ = lean_array_push(v___x_3533_, v_00_u03b2_3508_);
v___x_3535_ = lean_array_push(v___x_3534_, v_fst_3502_);
v___x_3536_ = lean_array_push(v___x_3535_, v_x_3452_);
v___x_3537_ = lean_array_push(v___x_3536_, v_a_3512_);
v___x_3538_ = lean_array_push(v___x_3537_, v_a_3516_);
v___x_3539_ = lean_array_push(v___x_3538_, v_F_3453_);
v___x_3540_ = l_Lean_mkAppN(v___x_3530_, v___x_3539_);
lean_dec_ref(v___x_3539_);
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 0, v___x_3540_);
v___x_3542_ = v___x_3522_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v___x_3540_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
return v___x_3542_;
}
}
}
}
else
{
lean_object* v_a_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3553_; 
lean_dec(v_a_3518_);
lean_dec(v_a_3516_);
lean_dec(v_a_3512_);
lean_dec(v_00_u03b2_3508_);
lean_dec(v_00_u03b1_3507_);
lean_del_object(v___x_3505_);
lean_dec(v_snd_3503_);
lean_dec(v_fst_3502_);
lean_dec_ref(v_F_3453_);
lean_dec_ref(v_x_3452_);
v_a_3546_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3548_ = v___x_3519_;
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_a_3546_);
lean_dec(v___x_3519_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
lean_object* v___x_3551_; 
if (v_isShared_3549_ == 0)
{
v___x_3551_ = v___x_3548_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_a_3546_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
}
}
else
{
lean_object* v_a_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3561_; 
lean_dec(v_a_3516_);
lean_dec(v_a_3512_);
lean_dec(v_00_u03b2_3508_);
lean_dec(v_00_u03b1_3507_);
lean_del_object(v___x_3505_);
lean_dec(v_snd_3503_);
lean_dec(v_fst_3502_);
lean_dec_ref(v_F_3453_);
lean_dec_ref(v_x_3452_);
v_a_3554_ = lean_ctor_get(v___x_3517_, 0);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___x_3517_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3556_ = v___x_3517_;
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_a_3554_);
lean_dec(v___x_3517_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
lean_object* v___x_3559_; 
if (v_isShared_3557_ == 0)
{
v___x_3559_ = v___x_3556_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v_a_3554_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
}
}
else
{
lean_dec(v_a_3512_);
lean_dec(v_00_u03b2_3508_);
lean_dec(v_00_u03b1_3507_);
lean_del_object(v___x_3505_);
lean_dec(v_snd_3503_);
lean_dec(v_fst_3502_);
lean_dec_ref(v_F_3453_);
lean_dec_ref(v_x_3452_);
return v___x_3515_;
}
}
else
{
lean_dec(v_00_u03b2_3508_);
lean_dec(v_00_u03b1_3507_);
lean_del_object(v___x_3505_);
lean_dec(v_snd_3503_);
lean_dec(v_fst_3502_);
lean_dec_ref(v_args_3493_);
lean_dec(v_a_3489_);
lean_dec_ref(v_k_3455_);
lean_dec_ref(v_F_3453_);
lean_dec_ref(v_x_3452_);
return v___x_3511_;
}
}
}
else
{
lean_object* v_a_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3570_; 
lean_dec_ref(v_args_3493_);
lean_dec(v_a_3489_);
lean_dec_ref(v_k_3455_);
lean_dec_ref(v_F_3453_);
lean_dec_ref(v_x_3452_);
v_a_3563_ = lean_ctor_get(v___x_3500_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v___x_3500_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3565_ = v___x_3500_;
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_a_3563_);
lean_dec(v___x_3500_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3568_; 
if (v_isShared_3566_ == 0)
{
v___x_3568_ = v___x_3565_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_a_3563_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
}
else
{
lean_object* v_a_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3578_; 
lean_dec(v___x_3468_);
lean_dec_ref(v_k_3455_);
lean_dec_ref(v_val_3454_);
lean_dec_ref(v_F_3453_);
lean_dec_ref(v_x_3452_);
v_a_3571_ = lean_ctor_get(v___x_3488_, 0);
v_isSharedCheck_3578_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3573_ = v___x_3488_;
v_isShared_3574_ = v_isSharedCheck_3578_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_a_3571_);
lean_dec(v___x_3488_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3578_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v___x_3576_; 
if (v_isShared_3574_ == 0)
{
v___x_3576_ = v___x_3573_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_a_3571_);
v___x_3576_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
return v___x_3576_;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1(lean_object* v___x_3583_, lean_object* v_body_3584_, lean_object* v_k_3585_, lean_object* v___x_3586_, uint8_t v___x_3587_, uint8_t v___x_3588_, lean_object* v_FNew_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_){
_start:
{
lean_object* v___x_3597_; 
lean_inc_ref(v_FNew_3589_);
lean_inc_ref(v___x_3583_);
v___x_3597_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v___x_3583_, v_FNew_3589_, v_body_3584_, v_k_3585_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_);
if (lean_obj_tag(v___x_3597_) == 0)
{
lean_object* v_a_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; uint8_t v___x_3602_; lean_object* v___x_3603_; 
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
lean_inc(v_a_3598_);
lean_dec_ref_known(v___x_3597_, 1);
v___x_3599_ = lean_mk_empty_array_with_capacity(v___x_3586_);
v___x_3600_ = lean_array_push(v___x_3599_, v___x_3583_);
v___x_3601_ = lean_array_push(v___x_3600_, v_FNew_3589_);
v___x_3602_ = 1;
v___x_3603_ = l_Lean_Meta_mkLambdaFVars(v___x_3601_, v_a_3598_, v___x_3587_, v___x_3588_, v___x_3587_, v___x_3588_, v___x_3602_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_);
lean_dec_ref(v___x_3601_);
return v___x_3603_;
}
else
{
lean_dec_ref(v_FNew_3589_);
lean_dec_ref(v___x_3583_);
return v___x_3597_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1___boxed(lean_object* v___x_3604_, lean_object* v_body_3605_, lean_object* v_k_3606_, lean_object* v___x_3607_, lean_object* v___x_3608_, lean_object* v___x_3609_, lean_object* v_FNew_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_){
_start:
{
uint8_t v___x_6490__boxed_3618_; uint8_t v___x_6491__boxed_3619_; lean_object* v_res_3620_; 
v___x_6490__boxed_3618_ = lean_unbox(v___x_3608_);
v___x_6491__boxed_3619_ = lean_unbox(v___x_3609_);
v_res_3620_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1(v___x_3604_, v_body_3605_, v_k_3606_, v___x_3607_, v___x_6490__boxed_3618_, v___x_6491__boxed_3619_, v_FNew_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_);
lean_dec(v___y_3616_);
lean_dec_ref(v___y_3615_);
lean_dec(v___y_3614_);
lean_dec_ref(v___y_3613_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec(v___x_3607_);
return v_res_3620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2(lean_object* v___x_3621_, lean_object* v___x_3622_, lean_object* v_00_u03b1_3623_, lean_object* v_00_u03b2_3624_, lean_object* v___x_3625_, lean_object* v_ctorName_3626_, lean_object* v_k_3627_, lean_object* v___x_3628_, uint8_t v___x_3629_, uint8_t v___x_3630_, lean_object* v_a_3631_, lean_object* v_x_3632_, lean_object* v_xs_3633_, lean_object* v_body_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_){
_start:
{
lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3642_ = lean_array_get_borrowed(v___x_3621_, v_xs_3633_, v___x_3622_);
v___x_3643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3643_, 0, v_00_u03b1_3623_);
v___x_3644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3644_, 0, v_00_u03b2_3624_);
lean_inc(v___x_3642_);
v___x_3645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3645_, 0, v___x_3642_);
v___x_3646_ = lean_mk_empty_array_with_capacity(v___x_3625_);
v___x_3647_ = lean_array_push(v___x_3646_, v___x_3643_);
v___x_3648_ = lean_array_push(v___x_3647_, v___x_3644_);
v___x_3649_ = lean_array_push(v___x_3648_, v___x_3645_);
v___x_3650_ = l_Lean_Meta_mkAppOptM(v_ctorName_3626_, v___x_3649_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_);
if (lean_obj_tag(v___x_3650_) == 0)
{
lean_object* v_a_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___f_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; 
v_a_3651_ = lean_ctor_get(v___x_3650_, 0);
lean_inc(v_a_3651_);
lean_dec_ref_known(v___x_3650_, 1);
v___x_3652_ = lean_box(v___x_3629_);
v___x_3653_ = lean_box(v___x_3630_);
lean_inc(v___x_3642_);
v___f_3654_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1___boxed), 14, 6);
lean_closure_set(v___f_3654_, 0, v___x_3642_);
lean_closure_set(v___f_3654_, 1, v_body_3634_);
lean_closure_set(v___f_3654_, 2, v_k_3627_);
lean_closure_set(v___f_3654_, 3, v___x_3628_);
lean_closure_set(v___f_3654_, 4, v___x_3652_);
lean_closure_set(v___f_3654_, 5, v___x_3653_);
v___x_3655_ = l_Lean_LocalDecl_type(v_a_3631_);
v___x_3656_ = l_Lean_Expr_replaceFVar(v___x_3655_, v_x_3632_, v_a_3651_);
lean_dec(v_a_3651_);
lean_dec_ref(v___x_3655_);
v___x_3657_ = l_Lean_LocalDecl_userName(v_a_3631_);
v___x_3658_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v___x_3657_, v___x_3656_, v___f_3654_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_);
return v___x_3658_;
}
else
{
lean_dec_ref(v_body_3634_);
lean_dec_ref(v_x_3632_);
lean_dec(v___x_3628_);
lean_dec_ref(v_k_3627_);
return v___x_3650_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2___boxed(lean_object** _args){
lean_object* v___x_3659_ = _args[0];
lean_object* v___x_3660_ = _args[1];
lean_object* v_00_u03b1_3661_ = _args[2];
lean_object* v_00_u03b2_3662_ = _args[3];
lean_object* v___x_3663_ = _args[4];
lean_object* v_ctorName_3664_ = _args[5];
lean_object* v_k_3665_ = _args[6];
lean_object* v___x_3666_ = _args[7];
lean_object* v___x_3667_ = _args[8];
lean_object* v___x_3668_ = _args[9];
lean_object* v_a_3669_ = _args[10];
lean_object* v_x_3670_ = _args[11];
lean_object* v_xs_3671_ = _args[12];
lean_object* v_body_3672_ = _args[13];
lean_object* v___y_3673_ = _args[14];
lean_object* v___y_3674_ = _args[15];
lean_object* v___y_3675_ = _args[16];
lean_object* v___y_3676_ = _args[17];
lean_object* v___y_3677_ = _args[18];
lean_object* v___y_3678_ = _args[19];
lean_object* v___y_3679_ = _args[20];
_start:
{
uint8_t v___x_6511__boxed_3680_; uint8_t v___x_6512__boxed_3681_; lean_object* v_res_3682_; 
v___x_6511__boxed_3680_ = lean_unbox(v___x_3667_);
v___x_6512__boxed_3681_ = lean_unbox(v___x_3668_);
v_res_3682_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2(v___x_3659_, v___x_3660_, v_00_u03b1_3661_, v_00_u03b2_3662_, v___x_3663_, v_ctorName_3664_, v_k_3665_, v___x_3666_, v___x_6511__boxed_3680_, v___x_6512__boxed_3681_, v_a_3669_, v_x_3670_, v_xs_3671_, v_body_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_);
lean_dec(v___y_3678_);
lean_dec_ref(v___y_3677_);
lean_dec(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
lean_dec_ref(v_xs_3671_);
lean_dec_ref(v_a_3669_);
lean_dec(v___x_3663_);
lean_dec(v___x_3660_);
lean_dec_ref(v___x_3659_);
return v_res_3682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(lean_object* v___x_3683_, lean_object* v___x_3684_, lean_object* v_00_u03b1_3685_, lean_object* v_00_u03b2_3686_, lean_object* v___x_3687_, lean_object* v_k_3688_, lean_object* v___x_3689_, uint8_t v___x_3690_, uint8_t v___x_3691_, lean_object* v_a_3692_, lean_object* v_x_3693_, lean_object* v___x_3694_, lean_object* v_ctorName_3695_, lean_object* v_minor_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_){
_start:
{
lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___f_3706_; lean_object* v___x_3707_; 
v___x_3704_ = lean_box(v___x_3690_);
v___x_3705_ = lean_box(v___x_3691_);
v___f_3706_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2___boxed), 21, 12);
lean_closure_set(v___f_3706_, 0, v___x_3683_);
lean_closure_set(v___f_3706_, 1, v___x_3684_);
lean_closure_set(v___f_3706_, 2, v_00_u03b1_3685_);
lean_closure_set(v___f_3706_, 3, v_00_u03b2_3686_);
lean_closure_set(v___f_3706_, 4, v___x_3687_);
lean_closure_set(v___f_3706_, 5, v_ctorName_3695_);
lean_closure_set(v___f_3706_, 6, v_k_3688_);
lean_closure_set(v___f_3706_, 7, v___x_3689_);
lean_closure_set(v___f_3706_, 8, v___x_3704_);
lean_closure_set(v___f_3706_, 9, v___x_3705_);
lean_closure_set(v___f_3706_, 10, v_a_3692_);
lean_closure_set(v___f_3706_, 11, v_x_3693_);
v___x_3707_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_minor_3696_, v___x_3694_, v___f_3706_, v___x_3690_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_);
return v___x_3707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3___boxed(lean_object** _args){
lean_object* v___x_3708_ = _args[0];
lean_object* v___x_3709_ = _args[1];
lean_object* v_00_u03b1_3710_ = _args[2];
lean_object* v_00_u03b2_3711_ = _args[3];
lean_object* v___x_3712_ = _args[4];
lean_object* v_k_3713_ = _args[5];
lean_object* v___x_3714_ = _args[6];
lean_object* v___x_3715_ = _args[7];
lean_object* v___x_3716_ = _args[8];
lean_object* v_a_3717_ = _args[9];
lean_object* v_x_3718_ = _args[10];
lean_object* v___x_3719_ = _args[11];
lean_object* v_ctorName_3720_ = _args[12];
lean_object* v_minor_3721_ = _args[13];
lean_object* v___y_3722_ = _args[14];
lean_object* v___y_3723_ = _args[15];
lean_object* v___y_3724_ = _args[16];
lean_object* v___y_3725_ = _args[17];
lean_object* v___y_3726_ = _args[18];
lean_object* v___y_3727_ = _args[19];
lean_object* v___y_3728_ = _args[20];
_start:
{
uint8_t v___x_6475__boxed_3729_; uint8_t v___x_6476__boxed_3730_; lean_object* v_res_3731_; 
v___x_6475__boxed_3729_ = lean_unbox(v___x_3715_);
v___x_6476__boxed_3730_ = lean_unbox(v___x_3716_);
v_res_3731_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3708_, v___x_3709_, v_00_u03b1_3710_, v_00_u03b2_3711_, v___x_3712_, v_k_3713_, v___x_3714_, v___x_6475__boxed_3729_, v___x_6476__boxed_3730_, v_a_3717_, v_x_3718_, v___x_3719_, v_ctorName_3720_, v_minor_3721_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_);
lean_dec(v___y_3727_);
lean_dec_ref(v___y_3726_);
lean_dec(v___y_3725_);
lean_dec_ref(v___y_3724_);
lean_dec(v___y_3723_);
lean_dec_ref(v___y_3722_);
return v_res_3731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___boxed(lean_object* v_x_3732_, lean_object* v_F_3733_, lean_object* v_val_3734_, lean_object* v_k_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_){
_start:
{
lean_object* v_res_3743_; 
v_res_3743_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v_x_3732_, v_F_3733_, v_val_3734_, v_k_3735_, v_a_3736_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_, v_a_3741_);
lean_dec(v_a_3741_);
lean_dec_ref(v_a_3740_);
lean_dec(v_a_3739_);
lean_dec_ref(v_a_3738_);
lean_dec(v_a_3737_);
lean_dec_ref(v_a_3736_);
return v_res_3743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1(lean_object* v_00_u03b1_3744_, lean_object* v_name_3745_, uint8_t v_bi_3746_, lean_object* v_type_3747_, lean_object* v_k_3748_, uint8_t v_kind_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_){
_start:
{
lean_object* v___x_3757_; 
v___x_3757_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(v_name_3745_, v_bi_3746_, v_type_3747_, v_k_3748_, v_kind_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_);
return v___x_3757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___boxed(lean_object* v_00_u03b1_3758_, lean_object* v_name_3759_, lean_object* v_bi_3760_, lean_object* v_type_3761_, lean_object* v_k_3762_, lean_object* v_kind_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_){
_start:
{
uint8_t v_bi_boxed_3771_; uint8_t v_kind_boxed_3772_; lean_object* v_res_3773_; 
v_bi_boxed_3771_ = lean_unbox(v_bi_3760_);
v_kind_boxed_3772_ = lean_unbox(v_kind_3763_);
v_res_3773_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1(v_00_u03b1_3758_, v_name_3759_, v_bi_boxed_3771_, v_type_3761_, v_k_3762_, v_kind_boxed_3772_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_);
lean_dec(v___y_3769_);
lean_dec_ref(v___y_3768_);
lean_dec(v___y_3767_);
lean_dec_ref(v___y_3766_);
lean_dec(v___y_3765_);
lean_dec_ref(v___y_3764_);
return v_res_3773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1(lean_object* v_00_u03b1_3774_, lean_object* v_name_3775_, lean_object* v_type_3776_, lean_object* v_k_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_){
_start:
{
lean_object* v___x_3785_; 
v___x_3785_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_name_3775_, v_type_3776_, v_k_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_);
return v___x_3785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___boxed(lean_object* v_00_u03b1_3786_, lean_object* v_name_3787_, lean_object* v_type_3788_, lean_object* v_k_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_){
_start:
{
lean_object* v_res_3797_; 
v_res_3797_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1(v_00_u03b1_3786_, v_name_3787_, v_type_3788_, v_k_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_);
lean_dec(v___y_3795_);
lean_dec_ref(v___y_3794_);
lean_dec(v___y_3793_);
lean_dec_ref(v___y_3792_);
lean_dec(v___y_3791_);
lean_dec_ref(v___y_3790_);
return v_res_3797_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3798_; 
v___x_3798_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return v___x_3798_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(lean_object* v_msg_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_){
_start:
{
lean_object* v___x_3807_; lean_object* v___x_3331__overap_3808_; lean_object* v___x_3809_; 
v___x_3807_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0, &l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0);
v___x_3331__overap_3808_ = lean_panic_fn_borrowed(v___x_3807_, v_msg_3799_);
lean_inc(v___y_3805_);
lean_inc_ref(v___y_3804_);
lean_inc(v___y_3803_);
lean_inc_ref(v___y_3802_);
lean_inc(v___y_3801_);
lean_inc_ref(v___y_3800_);
v___x_3809_ = lean_apply_7(v___x_3331__overap_3808_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, lean_box(0));
return v___x_3809_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___boxed(lean_object* v_msg_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_){
_start:
{
lean_object* v_res_3818_; 
v_res_3818_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(v_msg_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_);
lean_dec(v___y_3816_);
lean_dec_ref(v___y_3815_);
lean_dec(v___y_3814_);
lean_dec_ref(v___y_3813_);
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3811_);
return v_res_3818_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3(void){
_start:
{
lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; 
v___x_3822_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__2));
v___x_3823_ = lean_unsigned_to_nat(49u);
v___x_3824_ = lean_unsigned_to_nat(186u);
v___x_3825_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__1));
v___x_3826_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__0));
v___x_3827_ = l_mkPanicMessageWithDecl(v___x_3826_, v___x_3825_, v___x_3824_, v___x_3823_, v___x_3822_);
return v___x_3827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1___boxed(lean_object* v___x_3833_, lean_object* v_a_3834_, lean_object* v_k_3835_, lean_object* v___x_3836_, lean_object* v___x_3837_, lean_object* v___x_3838_, lean_object* v___x_3839_, lean_object* v___x_3840_, lean_object* v_FNew_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_){
_start:
{
uint8_t v___x_3499__boxed_3849_; uint8_t v___x_3500__boxed_3850_; uint8_t v___x_3501__boxed_3851_; lean_object* v_res_3852_; 
v___x_3499__boxed_3849_ = lean_unbox(v___x_3838_);
v___x_3500__boxed_3850_ = lean_unbox(v___x_3839_);
v___x_3501__boxed_3851_ = lean_unbox(v___x_3840_);
v_res_3852_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1(v___x_3833_, v_a_3834_, v_k_3835_, v___x_3836_, v___x_3837_, v___x_3499__boxed_3849_, v___x_3500__boxed_3850_, v___x_3501__boxed_3851_, v_FNew_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_);
lean_dec(v___y_3847_);
lean_dec_ref(v___y_3846_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec(v___y_3843_);
lean_dec_ref(v___y_3842_);
lean_dec(v___x_3836_);
return v_res_3852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0(lean_object* v___x_3853_, lean_object* v___x_3854_, lean_object* v___x_3855_, lean_object* v___x_3856_, uint8_t v___x_3857_, uint8_t v___x_3858_, lean_object* v_00_u03b1_3859_, lean_object* v_00_u03b2_3860_, lean_object* v___x_3861_, lean_object* v_k_3862_, lean_object* v___x_3863_, lean_object* v_a_3864_, lean_object* v_x_3865_, lean_object* v_xs_3866_, lean_object* v_body_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_){
_start:
{
lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; uint8_t v___x_3880_; lean_object* v___x_3881_; 
v___x_3875_ = lean_array_get(v___x_3853_, v_xs_3866_, v___x_3854_);
v___x_3876_ = lean_array_get(v___x_3853_, v_xs_3866_, v___x_3855_);
v___x_3877_ = lean_array_get_size(v_xs_3866_);
v___x_3878_ = l_Array_toSubarray___redArg(v_xs_3866_, v___x_3856_, v___x_3877_);
v___x_3879_ = l_Subarray_copy___redArg(v___x_3878_);
v___x_3880_ = 1;
v___x_3881_ = l_Lean_Meta_mkLambdaFVars(v___x_3879_, v_body_3867_, v___x_3857_, v___x_3858_, v___x_3857_, v___x_3858_, v___x_3880_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
lean_dec_ref(v___x_3879_);
if (lean_obj_tag(v___x_3881_) == 0)
{
lean_object* v_a_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3908_; 
v_a_3882_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3908_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3908_ == 0)
{
v___x_3884_ = v___x_3881_;
v_isShared_3885_ = v_isSharedCheck_3908_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_a_3882_);
lean_dec(v___x_3881_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3908_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v___x_3886_; lean_object* v___x_3888_; 
v___x_3886_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__2));
if (v_isShared_3885_ == 0)
{
lean_ctor_set_tag(v___x_3884_, 1);
lean_ctor_set(v___x_3884_, 0, v_00_u03b1_3859_);
v___x_3888_ = v___x_3884_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_00_u03b1_3859_);
v___x_3888_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3889_, 0, v_00_u03b2_3860_);
lean_inc(v___x_3875_);
v___x_3890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3890_, 0, v___x_3875_);
lean_inc(v___x_3876_);
v___x_3891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3876_);
v___x_3892_ = lean_mk_empty_array_with_capacity(v___x_3861_);
v___x_3893_ = lean_array_push(v___x_3892_, v___x_3888_);
v___x_3894_ = lean_array_push(v___x_3893_, v___x_3889_);
v___x_3895_ = lean_array_push(v___x_3894_, v___x_3890_);
v___x_3896_ = lean_array_push(v___x_3895_, v___x_3891_);
v___x_3897_ = l_Lean_Meta_mkAppOptM(v___x_3886_, v___x_3896_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
if (lean_obj_tag(v___x_3897_) == 0)
{
lean_object* v_a_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___f_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; 
v_a_3898_ = lean_ctor_get(v___x_3897_, 0);
lean_inc(v_a_3898_);
lean_dec_ref_known(v___x_3897_, 1);
v___x_3899_ = lean_box(v___x_3857_);
v___x_3900_ = lean_box(v___x_3858_);
v___x_3901_ = lean_box(v___x_3880_);
v___f_3902_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1___boxed), 16, 8);
lean_closure_set(v___f_3902_, 0, v___x_3876_);
lean_closure_set(v___f_3902_, 1, v_a_3882_);
lean_closure_set(v___f_3902_, 2, v_k_3862_);
lean_closure_set(v___f_3902_, 3, v___x_3863_);
lean_closure_set(v___f_3902_, 4, v___x_3875_);
lean_closure_set(v___f_3902_, 5, v___x_3899_);
lean_closure_set(v___f_3902_, 6, v___x_3900_);
lean_closure_set(v___f_3902_, 7, v___x_3901_);
v___x_3903_ = l_Lean_LocalDecl_type(v_a_3864_);
v___x_3904_ = l_Lean_Expr_replaceFVar(v___x_3903_, v_x_3865_, v_a_3898_);
lean_dec(v_a_3898_);
lean_dec_ref(v___x_3903_);
v___x_3905_ = l_Lean_LocalDecl_userName(v_a_3864_);
v___x_3906_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v___x_3905_, v___x_3904_, v___f_3902_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
return v___x_3906_;
}
else
{
lean_dec(v_a_3882_);
lean_dec(v___x_3876_);
lean_dec(v___x_3875_);
lean_dec_ref(v_x_3865_);
lean_dec(v___x_3863_);
lean_dec_ref(v_k_3862_);
return v___x_3897_;
}
}
}
}
else
{
lean_dec(v___x_3876_);
lean_dec(v___x_3875_);
lean_dec_ref(v_x_3865_);
lean_dec(v___x_3863_);
lean_dec_ref(v_k_3862_);
lean_dec_ref(v_00_u03b2_3860_);
lean_dec_ref(v_00_u03b1_3859_);
return v___x_3881_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___boxed(lean_object** _args){
lean_object* v___x_3909_ = _args[0];
lean_object* v___x_3910_ = _args[1];
lean_object* v___x_3911_ = _args[2];
lean_object* v___x_3912_ = _args[3];
lean_object* v___x_3913_ = _args[4];
lean_object* v___x_3914_ = _args[5];
lean_object* v_00_u03b1_3915_ = _args[6];
lean_object* v_00_u03b2_3916_ = _args[7];
lean_object* v___x_3917_ = _args[8];
lean_object* v_k_3918_ = _args[9];
lean_object* v___x_3919_ = _args[10];
lean_object* v_a_3920_ = _args[11];
lean_object* v_x_3921_ = _args[12];
lean_object* v_xs_3922_ = _args[13];
lean_object* v_body_3923_ = _args[14];
lean_object* v___y_3924_ = _args[15];
lean_object* v___y_3925_ = _args[16];
lean_object* v___y_3926_ = _args[17];
lean_object* v___y_3927_ = _args[18];
lean_object* v___y_3928_ = _args[19];
lean_object* v___y_3929_ = _args[20];
lean_object* v___y_3930_ = _args[21];
_start:
{
uint8_t v___x_3526__boxed_3931_; uint8_t v___x_3527__boxed_3932_; lean_object* v_res_3933_; 
v___x_3526__boxed_3931_ = lean_unbox(v___x_3913_);
v___x_3527__boxed_3932_ = lean_unbox(v___x_3914_);
v_res_3933_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0(v___x_3909_, v___x_3910_, v___x_3911_, v___x_3912_, v___x_3526__boxed_3931_, v___x_3527__boxed_3932_, v_00_u03b1_3915_, v_00_u03b2_3916_, v___x_3917_, v_k_3918_, v___x_3919_, v_a_3920_, v_x_3921_, v_xs_3922_, v_body_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_);
lean_dec(v___y_3929_);
lean_dec_ref(v___y_3928_);
lean_dec(v___y_3927_);
lean_dec_ref(v___y_3926_);
lean_dec(v___y_3925_);
lean_dec_ref(v___y_3924_);
lean_dec_ref(v_a_3920_);
lean_dec(v___x_3917_);
lean_dec(v___x_3911_);
lean_dec(v___x_3910_);
lean_dec_ref(v___x_3909_);
return v_res_3933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(lean_object* v_x_3937_, lean_object* v_F_3938_, lean_object* v_val_3939_, lean_object* v_k_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_){
_start:
{
lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; lean_object* v___y_3952_; lean_object* v___y_3953_; lean_object* v___y_3954_; lean_object* v___x_3957_; uint8_t v___y_3959_; uint8_t v___x_4050_; 
v___x_3957_ = l_Lean_instInhabitedExpr;
v___x_4050_ = l_Lean_Expr_isFVar(v_x_3937_);
if (v___x_4050_ == 0)
{
v___y_3959_ = v___x_4050_;
goto v___jp_3958_;
}
else
{
lean_object* v___x_4051_; lean_object* v___x_4052_; uint8_t v___x_4053_; 
v___x_4051_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4));
v___x_4052_ = lean_unsigned_to_nat(5u);
v___x_4053_ = l_Lean_Expr_isAppOfArity(v_val_3939_, v___x_4051_, v___x_4052_);
v___y_3959_ = v___x_4053_;
goto v___jp_3958_;
}
v___jp_3948_:
{
lean_object* v___x_3955_; lean_object* v___x_3956_; 
v___x_3955_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3);
v___x_3956_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(v___x_3955_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
return v___x_3956_;
}
v___jp_3958_:
{
if (v___y_3959_ == 0)
{
lean_object* v___x_3960_; 
lean_dec_ref(v_x_3937_);
lean_inc(v_a_3946_);
lean_inc_ref(v_a_3945_);
lean_inc(v_a_3944_);
lean_inc_ref(v_a_3943_);
lean_inc(v_a_3942_);
lean_inc_ref(v_a_3941_);
v___x_3960_ = lean_apply_9(v_k_3940_, v_F_3938_, v_val_3939_, v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, lean_box(0));
return v___x_3960_;
}
else
{
lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; uint8_t v___x_3967_; 
v___x_3961_ = lean_unsigned_to_nat(3u);
v___x_3962_ = l_Lean_Expr_getAppNumArgs(v_val_3939_);
v___x_3963_ = lean_nat_sub(v___x_3962_, v___x_3961_);
v___x_3964_ = lean_unsigned_to_nat(1u);
v___x_3965_ = lean_nat_sub(v___x_3963_, v___x_3964_);
lean_dec(v___x_3963_);
v___x_3966_ = l_Lean_Expr_getRevArg_x21(v_val_3939_, v___x_3965_);
v___x_3967_ = lean_expr_eqv(v___x_3966_, v_x_3937_);
lean_dec_ref(v___x_3966_);
if (v___x_3967_ == 0)
{
lean_object* v___x_3968_; 
lean_dec(v___x_3962_);
lean_dec_ref(v_x_3937_);
lean_inc(v_a_3946_);
lean_inc_ref(v_a_3945_);
lean_inc(v_a_3944_);
lean_inc_ref(v_a_3943_);
lean_inc(v_a_3942_);
lean_inc_ref(v_a_3941_);
v___x_3968_ = lean_apply_9(v_k_3940_, v_F_3938_, v_val_3939_, v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, lean_box(0));
return v___x_3968_;
}
else
{
lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; uint8_t v___x_3973_; 
v___x_3969_ = lean_unsigned_to_nat(4u);
v___x_3970_ = lean_nat_sub(v___x_3962_, v___x_3969_);
v___x_3971_ = lean_nat_sub(v___x_3970_, v___x_3964_);
lean_dec(v___x_3970_);
v___x_3972_ = l_Lean_Expr_getRevArg_x21(v_val_3939_, v___x_3971_);
v___x_3973_ = l_Lean_Expr_isLambda(v___x_3972_);
if (v___x_3973_ == 0)
{
lean_object* v___x_3974_; 
lean_dec_ref(v___x_3972_);
lean_dec(v___x_3962_);
lean_dec_ref(v_x_3937_);
lean_inc(v_a_3946_);
lean_inc_ref(v_a_3945_);
lean_inc(v_a_3944_);
lean_inc_ref(v_a_3943_);
lean_inc(v_a_3942_);
lean_inc_ref(v_a_3941_);
v___x_3974_ = lean_apply_9(v_k_3940_, v_F_3938_, v_val_3939_, v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, lean_box(0));
return v___x_3974_;
}
else
{
lean_object* v___x_3975_; uint8_t v___x_3976_; 
v___x_3975_ = l_Lean_Expr_bindingBody_x21(v___x_3972_);
lean_dec_ref(v___x_3972_);
v___x_3976_ = l_Lean_Expr_isLambda(v___x_3975_);
lean_dec_ref(v___x_3975_);
if (v___x_3976_ == 0)
{
lean_object* v___x_3977_; 
lean_dec(v___x_3962_);
lean_dec_ref(v_x_3937_);
lean_inc(v_a_3946_);
lean_inc_ref(v_a_3945_);
lean_inc(v_a_3944_);
lean_inc_ref(v_a_3943_);
lean_inc(v_a_3942_);
lean_inc_ref(v_a_3941_);
v___x_3977_ = lean_apply_9(v_k_3940_, v_F_3938_, v_val_3939_, v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, lean_box(0));
return v___x_3977_;
}
else
{
lean_object* v___x_3978_; lean_object* v___x_3979_; 
v___x_3978_ = l_Lean_Expr_getAppFn(v_val_3939_);
v___x_3979_ = l_Lean_Expr_constLevels_x21(v___x_3978_);
lean_dec_ref(v___x_3978_);
if (lean_obj_tag(v___x_3979_) == 1)
{
lean_object* v_tail_3980_; 
v_tail_3980_ = lean_ctor_get(v___x_3979_, 1);
lean_inc(v_tail_3980_);
lean_dec_ref_known(v___x_3979_, 2);
if (lean_obj_tag(v_tail_3980_) == 1)
{
lean_object* v_tail_3981_; 
v_tail_3981_ = lean_ctor_get(v_tail_3980_, 1);
lean_inc(v_tail_3981_);
if (lean_obj_tag(v_tail_3981_) == 1)
{
lean_object* v_tail_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_4048_; 
v_tail_3982_ = lean_ctor_get(v_tail_3981_, 1);
v_isSharedCheck_4048_ = !lean_is_exclusive(v_tail_3981_);
if (v_isSharedCheck_4048_ == 0)
{
lean_object* v_unused_4049_; 
v_unused_4049_ = lean_ctor_get(v_tail_3981_, 0);
lean_dec(v_unused_4049_);
v___x_3984_ = v_tail_3981_;
v_isShared_3985_ = v_isSharedCheck_4048_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_tail_3982_);
lean_dec(v_tail_3981_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_4048_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
if (lean_obj_tag(v_tail_3982_) == 0)
{
lean_object* v___x_3986_; lean_object* v___x_3987_; 
v___x_3986_ = l_Lean_Expr_fvarId_x21(v_F_3938_);
v___x_3987_ = l_Lean_FVarId_getDecl___redArg(v___x_3986_, v_a_3943_, v_a_3945_, v_a_3946_);
if (lean_obj_tag(v___x_3987_) == 0)
{
lean_object* v_a_3988_; lean_object* v_dummy_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v_args_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___f_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; uint8_t v___x_3998_; lean_object* v___x_3999_; 
v_a_3988_ = lean_ctor_get(v___x_3987_, 0);
lean_inc_n(v_a_3988_, 2);
lean_dec_ref_known(v___x_3987_, 1);
v_dummy_3989_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_3962_);
v___x_3990_ = lean_mk_array(v___x_3962_, v_dummy_3989_);
v___x_3991_ = lean_nat_sub(v___x_3962_, v___x_3964_);
lean_dec(v___x_3962_);
v_args_3992_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_3939_, v___x_3990_, v___x_3991_);
v___x_3993_ = lean_unsigned_to_nat(0u);
v___x_3994_ = lean_box(v___x_3973_);
lean_inc_ref(v_x_3937_);
v___f_3995_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed), 14, 5);
lean_closure_set(v___f_3995_, 0, v_a_3988_);
lean_closure_set(v___f_3995_, 1, v___x_3957_);
lean_closure_set(v___f_3995_, 2, v___x_3993_);
lean_closure_set(v___f_3995_, 3, v_x_3937_);
lean_closure_set(v___f_3995_, 4, v___x_3994_);
v___x_3996_ = lean_unsigned_to_nat(2u);
v___x_3997_ = lean_array_get(v___x_3957_, v_args_3992_, v___x_3996_);
v___x_3998_ = 0;
v___x_3999_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_3997_, v___f_3995_, v___x_3998_, v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_);
if (lean_obj_tag(v___x_3999_) == 0)
{
lean_object* v_a_4000_; lean_object* v_fst_4001_; lean_object* v_snd_4002_; lean_object* v_00_u03b1_4003_; lean_object* v_00_u03b2_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___f_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; 
v_a_4000_ = lean_ctor_get(v___x_3999_, 0);
lean_inc(v_a_4000_);
lean_dec_ref_known(v___x_3999_, 1);
v_fst_4001_ = lean_ctor_get(v_a_4000_, 0);
lean_inc(v_fst_4001_);
v_snd_4002_ = lean_ctor_get(v_a_4000_, 1);
lean_inc(v_snd_4002_);
lean_dec(v_a_4000_);
v_00_u03b1_4003_ = lean_array_get(v___x_3957_, v_args_3992_, v___x_3993_);
v_00_u03b2_4004_ = lean_array_get(v___x_3957_, v_args_3992_, v___x_3964_);
v___x_4005_ = lean_box(v___x_3998_);
v___x_4006_ = lean_box(v___x_3973_);
lean_inc_ref(v_x_3937_);
lean_inc(v_00_u03b2_4004_);
lean_inc(v_00_u03b1_4003_);
v___f_4007_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___boxed), 22, 13);
lean_closure_set(v___f_4007_, 0, v___x_3957_);
lean_closure_set(v___f_4007_, 1, v___x_3993_);
lean_closure_set(v___f_4007_, 2, v___x_3964_);
lean_closure_set(v___f_4007_, 3, v___x_3996_);
lean_closure_set(v___f_4007_, 4, v___x_4005_);
lean_closure_set(v___f_4007_, 5, v___x_4006_);
lean_closure_set(v___f_4007_, 6, v_00_u03b1_4003_);
lean_closure_set(v___f_4007_, 7, v_00_u03b2_4004_);
lean_closure_set(v___f_4007_, 8, v___x_3969_);
lean_closure_set(v___f_4007_, 9, v_k_3940_);
lean_closure_set(v___f_4007_, 10, v___x_3961_);
lean_closure_set(v___f_4007_, 11, v_a_3988_);
lean_closure_set(v___f_4007_, 12, v_x_3937_);
v___x_4008_ = lean_array_get(v___x_3957_, v_args_3992_, v___x_3969_);
lean_dec_ref(v_args_3992_);
v___x_4009_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_4008_, v___f_4007_, v___x_3998_, v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_);
if (lean_obj_tag(v___x_4009_) == 0)
{
lean_object* v_a_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4031_; 
v_a_4010_ = lean_ctor_get(v___x_4009_, 0);
v_isSharedCheck_4031_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4031_ == 0)
{
v___x_4012_ = v___x_4009_;
v_isShared_4013_ = v_isSharedCheck_4031_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_a_4010_);
lean_dec(v___x_4009_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4031_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v___x_4014_; lean_object* v___x_4016_; 
v___x_4014_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4));
if (v_isShared_3985_ == 0)
{
lean_ctor_set(v___x_3984_, 1, v_tail_3980_);
lean_ctor_set(v___x_3984_, 0, v_snd_4002_);
v___x_4016_ = v___x_3984_;
goto v_reusejp_4015_;
}
else
{
lean_object* v_reuseFailAlloc_4030_; 
v_reuseFailAlloc_4030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4030_, 0, v_snd_4002_);
lean_ctor_set(v_reuseFailAlloc_4030_, 1, v_tail_3980_);
v___x_4016_ = v_reuseFailAlloc_4030_;
goto v_reusejp_4015_;
}
v_reusejp_4015_:
{
lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4028_; 
v___x_4017_ = l_Lean_mkConst(v___x_4014_, v___x_4016_);
v___x_4018_ = lean_unsigned_to_nat(6u);
v___x_4019_ = lean_mk_empty_array_with_capacity(v___x_4018_);
v___x_4020_ = lean_array_push(v___x_4019_, v_00_u03b1_4003_);
v___x_4021_ = lean_array_push(v___x_4020_, v_00_u03b2_4004_);
v___x_4022_ = lean_array_push(v___x_4021_, v_fst_4001_);
v___x_4023_ = lean_array_push(v___x_4022_, v_x_3937_);
v___x_4024_ = lean_array_push(v___x_4023_, v_a_4010_);
v___x_4025_ = lean_array_push(v___x_4024_, v_F_3938_);
v___x_4026_ = l_Lean_mkAppN(v___x_4017_, v___x_4025_);
lean_dec_ref(v___x_4025_);
if (v_isShared_4013_ == 0)
{
lean_ctor_set(v___x_4012_, 0, v___x_4026_);
v___x_4028_ = v___x_4012_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v___x_4026_);
v___x_4028_ = v_reuseFailAlloc_4029_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
return v___x_4028_;
}
}
}
}
else
{
lean_dec(v_00_u03b2_4004_);
lean_dec(v_00_u03b1_4003_);
lean_dec(v_snd_4002_);
lean_dec(v_fst_4001_);
lean_del_object(v___x_3984_);
lean_dec_ref_known(v_tail_3980_, 2);
lean_dec_ref(v_F_3938_);
lean_dec_ref(v_x_3937_);
return v___x_4009_;
}
}
else
{
lean_object* v_a_4032_; lean_object* v___x_4034_; uint8_t v_isShared_4035_; uint8_t v_isSharedCheck_4039_; 
lean_dec_ref(v_args_3992_);
lean_dec(v_a_3988_);
lean_del_object(v___x_3984_);
lean_dec_ref_known(v_tail_3980_, 2);
lean_dec_ref(v_k_3940_);
lean_dec_ref(v_F_3938_);
lean_dec_ref(v_x_3937_);
v_a_4032_ = lean_ctor_get(v___x_3999_, 0);
v_isSharedCheck_4039_ = !lean_is_exclusive(v___x_3999_);
if (v_isSharedCheck_4039_ == 0)
{
v___x_4034_ = v___x_3999_;
v_isShared_4035_ = v_isSharedCheck_4039_;
goto v_resetjp_4033_;
}
else
{
lean_inc(v_a_4032_);
lean_dec(v___x_3999_);
v___x_4034_ = lean_box(0);
v_isShared_4035_ = v_isSharedCheck_4039_;
goto v_resetjp_4033_;
}
v_resetjp_4033_:
{
lean_object* v___x_4037_; 
if (v_isShared_4035_ == 0)
{
v___x_4037_ = v___x_4034_;
goto v_reusejp_4036_;
}
else
{
lean_object* v_reuseFailAlloc_4038_; 
v_reuseFailAlloc_4038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4038_, 0, v_a_4032_);
v___x_4037_ = v_reuseFailAlloc_4038_;
goto v_reusejp_4036_;
}
v_reusejp_4036_:
{
return v___x_4037_;
}
}
}
}
else
{
lean_object* v_a_4040_; lean_object* v___x_4042_; uint8_t v_isShared_4043_; uint8_t v_isSharedCheck_4047_; 
lean_del_object(v___x_3984_);
lean_dec_ref_known(v_tail_3980_, 2);
lean_dec(v___x_3962_);
lean_dec_ref(v_k_3940_);
lean_dec_ref(v_val_3939_);
lean_dec_ref(v_F_3938_);
lean_dec_ref(v_x_3937_);
v_a_4040_ = lean_ctor_get(v___x_3987_, 0);
v_isSharedCheck_4047_ = !lean_is_exclusive(v___x_3987_);
if (v_isSharedCheck_4047_ == 0)
{
v___x_4042_ = v___x_3987_;
v_isShared_4043_ = v_isSharedCheck_4047_;
goto v_resetjp_4041_;
}
else
{
lean_inc(v_a_4040_);
lean_dec(v___x_3987_);
v___x_4042_ = lean_box(0);
v_isShared_4043_ = v_isSharedCheck_4047_;
goto v_resetjp_4041_;
}
v_resetjp_4041_:
{
lean_object* v___x_4045_; 
if (v_isShared_4043_ == 0)
{
v___x_4045_ = v___x_4042_;
goto v_reusejp_4044_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v_a_4040_);
v___x_4045_ = v_reuseFailAlloc_4046_;
goto v_reusejp_4044_;
}
v_reusejp_4044_:
{
return v___x_4045_;
}
}
}
}
else
{
lean_del_object(v___x_3984_);
lean_dec(v_tail_3982_);
lean_dec_ref_known(v_tail_3980_, 2);
lean_dec(v___x_3962_);
lean_dec_ref(v_k_3940_);
lean_dec_ref(v_val_3939_);
lean_dec_ref(v_F_3938_);
lean_dec_ref(v_x_3937_);
v___y_3949_ = v_a_3941_;
v___y_3950_ = v_a_3942_;
v___y_3951_ = v_a_3943_;
v___y_3952_ = v_a_3944_;
v___y_3953_ = v_a_3945_;
v___y_3954_ = v_a_3946_;
goto v___jp_3948_;
}
}
}
else
{
lean_dec(v_tail_3981_);
lean_dec_ref_known(v_tail_3980_, 2);
lean_dec(v___x_3962_);
lean_dec_ref(v_k_3940_);
lean_dec_ref(v_val_3939_);
lean_dec_ref(v_F_3938_);
lean_dec_ref(v_x_3937_);
v___y_3949_ = v_a_3941_;
v___y_3950_ = v_a_3942_;
v___y_3951_ = v_a_3943_;
v___y_3952_ = v_a_3944_;
v___y_3953_ = v_a_3945_;
v___y_3954_ = v_a_3946_;
goto v___jp_3948_;
}
}
else
{
lean_dec(v_tail_3980_);
lean_dec(v___x_3962_);
lean_dec_ref(v_k_3940_);
lean_dec_ref(v_val_3939_);
lean_dec_ref(v_F_3938_);
lean_dec_ref(v_x_3937_);
v___y_3949_ = v_a_3941_;
v___y_3950_ = v_a_3942_;
v___y_3951_ = v_a_3943_;
v___y_3952_ = v_a_3944_;
v___y_3953_ = v_a_3945_;
v___y_3954_ = v_a_3946_;
goto v___jp_3948_;
}
}
else
{
lean_dec(v___x_3979_);
lean_dec(v___x_3962_);
lean_dec_ref(v_k_3940_);
lean_dec_ref(v_val_3939_);
lean_dec_ref(v_F_3938_);
lean_dec_ref(v_x_3937_);
v___y_3949_ = v_a_3941_;
v___y_3950_ = v_a_3942_;
v___y_3951_ = v_a_3943_;
v___y_3952_ = v_a_3944_;
v___y_3953_ = v_a_3945_;
v___y_3954_ = v_a_3946_;
goto v___jp_3948_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1(lean_object* v___x_4054_, lean_object* v_a_4055_, lean_object* v_k_4056_, lean_object* v___x_4057_, lean_object* v___x_4058_, uint8_t v___x_4059_, uint8_t v___x_4060_, uint8_t v___x_4061_, lean_object* v_FNew_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_){
_start:
{
lean_object* v___x_4070_; 
lean_inc_ref(v_FNew_4062_);
lean_inc_ref(v___x_4054_);
v___x_4070_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v___x_4054_, v_FNew_4062_, v_a_4055_, v_k_4056_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_);
if (lean_obj_tag(v___x_4070_) == 0)
{
lean_object* v_a_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; 
v_a_4071_ = lean_ctor_get(v___x_4070_, 0);
lean_inc(v_a_4071_);
lean_dec_ref_known(v___x_4070_, 1);
v___x_4072_ = lean_mk_empty_array_with_capacity(v___x_4057_);
v___x_4073_ = lean_array_push(v___x_4072_, v___x_4058_);
v___x_4074_ = lean_array_push(v___x_4073_, v___x_4054_);
v___x_4075_ = lean_array_push(v___x_4074_, v_FNew_4062_);
v___x_4076_ = l_Lean_Meta_mkLambdaFVars(v___x_4075_, v_a_4071_, v___x_4059_, v___x_4060_, v___x_4059_, v___x_4060_, v___x_4061_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_);
lean_dec_ref(v___x_4075_);
return v___x_4076_;
}
else
{
lean_dec_ref(v_FNew_4062_);
lean_dec_ref(v___x_4058_);
lean_dec_ref(v___x_4054_);
return v___x_4070_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___boxed(lean_object* v_x_4077_, lean_object* v_F_4078_, lean_object* v_val_4079_, lean_object* v_k_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_, lean_object* v_a_4084_, lean_object* v_a_4085_, lean_object* v_a_4086_, lean_object* v_a_4087_){
_start:
{
lean_object* v_res_4088_; 
v_res_4088_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v_x_4077_, v_F_4078_, v_val_4079_, v_k_4080_, v_a_4081_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_, v_a_4086_);
lean_dec(v_a_4086_);
lean_dec_ref(v_a_4085_);
lean_dec(v_a_4084_);
lean_dec_ref(v_a_4083_);
lean_dec(v_a_4082_);
lean_dec_ref(v_a_4081_);
return v_res_4088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0(lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_){
_start:
{
lean_object* v___x_4102_; 
v___x_4102_ = l_Lean_Elab_WF_applyCleanWfTactic(v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
if (lean_obj_tag(v___x_4102_) == 0)
{
lean_object* v_ref_4103_; uint8_t v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; 
lean_dec_ref_known(v___x_4102_, 1);
v_ref_4103_ = lean_ctor_get(v___y_4099_, 2);
v___x_4104_ = 0;
v___x_4105_ = l_Lean_SourceInfo_fromRef(v_ref_4103_, v___x_4104_);
v___x_4106_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__1));
v___x_4107_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__2));
lean_inc(v___x_4105_);
v___x_4108_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4108_, 0, v___x_4105_);
lean_ctor_set(v___x_4108_, 1, v___x_4107_);
v___x_4109_ = l_Lean_Syntax_node1(v___x_4105_, v___x_4106_, v___x_4108_);
v___x_4110_ = l_Lean_Elab_Tactic_evalTactic(v___x_4109_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
return v___x_4110_;
}
else
{
return v___x_4102_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___boxed(lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_){
_start:
{
lean_object* v_res_4120_; 
v_res_4120_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0(v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_);
lean_dec(v___y_4118_);
lean_dec_ref(v___y_4117_);
lean_dec(v___y_4116_);
lean_dec_ref(v___y_4115_);
lean_dec(v___y_4114_);
lean_dec_ref(v___y_4113_);
lean_dec(v___y_4112_);
lean_dec_ref(v___y_4111_);
return v_res_4120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(lean_object* v_mvarId_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_){
_start:
{
lean_object* v___f_4130_; lean_object* v___x_4131_; 
v___f_4130_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___closed__0));
v___x_4131_ = l_Lean_Elab_Tactic_run(v_mvarId_4122_, v___f_4130_, v_a_4123_, v_a_4124_, v_a_4125_, v_a_4126_, v_a_4127_, v_a_4128_);
if (lean_obj_tag(v___x_4131_) == 0)
{
lean_object* v_a_4132_; lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4142_; 
v_a_4132_ = lean_ctor_get(v___x_4131_, 0);
v_isSharedCheck_4142_ = !lean_is_exclusive(v___x_4131_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4134_ = v___x_4131_;
v_isShared_4135_ = v_isSharedCheck_4142_;
goto v_resetjp_4133_;
}
else
{
lean_inc(v_a_4132_);
lean_dec(v___x_4131_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4142_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
uint8_t v___x_4136_; 
v___x_4136_ = l_List_isEmpty___redArg(v_a_4132_);
if (v___x_4136_ == 0)
{
lean_object* v___x_4137_; 
lean_del_object(v___x_4134_);
v___x_4137_ = l_Lean_Elab_Term_reportUnsolvedGoals(v_a_4132_, v_a_4125_, v_a_4126_, v_a_4127_, v_a_4128_);
return v___x_4137_;
}
else
{
lean_object* v___x_4138_; lean_object* v___x_4140_; 
lean_dec(v_a_4132_);
v___x_4138_ = lean_box(0);
if (v_isShared_4135_ == 0)
{
lean_ctor_set(v___x_4134_, 0, v___x_4138_);
v___x_4140_ = v___x_4134_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v___x_4138_);
v___x_4140_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
return v___x_4140_;
}
}
}
}
else
{
lean_object* v_a_4143_; lean_object* v___x_4145_; uint8_t v_isShared_4146_; uint8_t v_isSharedCheck_4150_; 
v_a_4143_ = lean_ctor_get(v___x_4131_, 0);
v_isSharedCheck_4150_ = !lean_is_exclusive(v___x_4131_);
if (v_isSharedCheck_4150_ == 0)
{
v___x_4145_ = v___x_4131_;
v_isShared_4146_ = v_isSharedCheck_4150_;
goto v_resetjp_4144_;
}
else
{
lean_inc(v_a_4143_);
lean_dec(v___x_4131_);
v___x_4145_ = lean_box(0);
v_isShared_4146_ = v_isSharedCheck_4150_;
goto v_resetjp_4144_;
}
v_resetjp_4144_:
{
lean_object* v___x_4148_; 
if (v_isShared_4146_ == 0)
{
v___x_4148_ = v___x_4145_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v_a_4143_);
v___x_4148_ = v_reuseFailAlloc_4149_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
return v___x_4148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___boxed(lean_object* v_mvarId_4151_, lean_object* v_a_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_){
_start:
{
lean_object* v_res_4159_; 
v_res_4159_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(v_mvarId_4151_, v_a_4152_, v_a_4153_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_);
lean_dec(v_a_4157_);
lean_dec_ref(v_a_4156_);
lean_dec(v_a_4155_);
lean_dec_ref(v_a_4154_);
lean_dec(v_a_4153_);
lean_dec_ref(v_a_4152_);
return v_res_4159_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(lean_object* v_x_4160_, lean_object* v_x_4161_, lean_object* v_x_4162_, lean_object* v_x_4163_){
_start:
{
lean_object* v_ks_4164_; lean_object* v_vs_4165_; lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4189_; 
v_ks_4164_ = lean_ctor_get(v_x_4160_, 0);
v_vs_4165_ = lean_ctor_get(v_x_4160_, 1);
v_isSharedCheck_4189_ = !lean_is_exclusive(v_x_4160_);
if (v_isSharedCheck_4189_ == 0)
{
v___x_4167_ = v_x_4160_;
v_isShared_4168_ = v_isSharedCheck_4189_;
goto v_resetjp_4166_;
}
else
{
lean_inc(v_vs_4165_);
lean_inc(v_ks_4164_);
lean_dec(v_x_4160_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4189_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
lean_object* v___x_4169_; uint8_t v___x_4170_; 
v___x_4169_ = lean_array_get_size(v_ks_4164_);
v___x_4170_ = lean_nat_dec_lt(v_x_4161_, v___x_4169_);
if (v___x_4170_ == 0)
{
lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4174_; 
lean_dec(v_x_4161_);
v___x_4171_ = lean_array_push(v_ks_4164_, v_x_4162_);
v___x_4172_ = lean_array_push(v_vs_4165_, v_x_4163_);
if (v_isShared_4168_ == 0)
{
lean_ctor_set(v___x_4167_, 1, v___x_4172_);
lean_ctor_set(v___x_4167_, 0, v___x_4171_);
v___x_4174_ = v___x_4167_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v___x_4171_);
lean_ctor_set(v_reuseFailAlloc_4175_, 1, v___x_4172_);
v___x_4174_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
return v___x_4174_;
}
}
else
{
lean_object* v_k_x27_4176_; uint8_t v___x_4177_; 
v_k_x27_4176_ = lean_array_fget_borrowed(v_ks_4164_, v_x_4161_);
v___x_4177_ = l_Lean_instBEqMVarId_beq(v_x_4162_, v_k_x27_4176_);
if (v___x_4177_ == 0)
{
lean_object* v___x_4179_; 
if (v_isShared_4168_ == 0)
{
v___x_4179_ = v___x_4167_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4183_; 
v_reuseFailAlloc_4183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4183_, 0, v_ks_4164_);
lean_ctor_set(v_reuseFailAlloc_4183_, 1, v_vs_4165_);
v___x_4179_ = v_reuseFailAlloc_4183_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
lean_object* v___x_4180_; lean_object* v___x_4181_; 
v___x_4180_ = lean_unsigned_to_nat(1u);
v___x_4181_ = lean_nat_add(v_x_4161_, v___x_4180_);
lean_dec(v_x_4161_);
v_x_4160_ = v___x_4179_;
v_x_4161_ = v___x_4181_;
goto _start;
}
}
else
{
lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4187_; 
v___x_4184_ = lean_array_fset(v_ks_4164_, v_x_4161_, v_x_4162_);
v___x_4185_ = lean_array_fset(v_vs_4165_, v_x_4161_, v_x_4163_);
lean_dec(v_x_4161_);
if (v_isShared_4168_ == 0)
{
lean_ctor_set(v___x_4167_, 1, v___x_4185_);
lean_ctor_set(v___x_4167_, 0, v___x_4184_);
v___x_4187_ = v___x_4167_;
goto v_reusejp_4186_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v___x_4184_);
lean_ctor_set(v_reuseFailAlloc_4188_, 1, v___x_4185_);
v___x_4187_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4186_;
}
v_reusejp_4186_:
{
return v___x_4187_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_4190_, lean_object* v_k_4191_, lean_object* v_v_4192_){
_start:
{
lean_object* v___x_4193_; lean_object* v___x_4194_; 
v___x_4193_ = lean_unsigned_to_nat(0u);
v___x_4194_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_n_4190_, v___x_4193_, v_k_4191_, v_v_4192_);
return v___x_4194_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4195_; 
v___x_4195_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(lean_object* v_x_4196_, size_t v_x_4197_, size_t v_x_4198_, lean_object* v_x_4199_, lean_object* v_x_4200_){
_start:
{
if (lean_obj_tag(v_x_4196_) == 0)
{
lean_object* v_es_4201_; size_t v___x_4202_; size_t v___x_4203_; lean_object* v_j_4204_; lean_object* v___x_4205_; uint8_t v___x_4206_; 
v_es_4201_ = lean_ctor_get(v_x_4196_, 0);
v___x_4202_ = ((size_t)31ULL);
v___x_4203_ = lean_usize_land(v_x_4197_, v___x_4202_);
v_j_4204_ = lean_usize_to_nat(v___x_4203_);
v___x_4205_ = lean_array_get_size(v_es_4201_);
v___x_4206_ = lean_nat_dec_lt(v_j_4204_, v___x_4205_);
if (v___x_4206_ == 0)
{
lean_dec(v_j_4204_);
lean_dec(v_x_4200_);
lean_dec(v_x_4199_);
return v_x_4196_;
}
else
{
lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4245_; 
lean_inc_ref(v_es_4201_);
v_isSharedCheck_4245_ = !lean_is_exclusive(v_x_4196_);
if (v_isSharedCheck_4245_ == 0)
{
lean_object* v_unused_4246_; 
v_unused_4246_ = lean_ctor_get(v_x_4196_, 0);
lean_dec(v_unused_4246_);
v___x_4208_ = v_x_4196_;
v_isShared_4209_ = v_isSharedCheck_4245_;
goto v_resetjp_4207_;
}
else
{
lean_dec(v_x_4196_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4245_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
lean_object* v_v_4210_; lean_object* v___x_4211_; lean_object* v_xs_x27_4212_; lean_object* v___y_4214_; 
v_v_4210_ = lean_array_fget(v_es_4201_, v_j_4204_);
v___x_4211_ = lean_box(0);
v_xs_x27_4212_ = lean_array_fset(v_es_4201_, v_j_4204_, v___x_4211_);
switch(lean_obj_tag(v_v_4210_))
{
case 0:
{
lean_object* v_key_4219_; lean_object* v_val_4220_; lean_object* v___x_4222_; uint8_t v_isShared_4223_; uint8_t v_isSharedCheck_4230_; 
v_key_4219_ = lean_ctor_get(v_v_4210_, 0);
v_val_4220_ = lean_ctor_get(v_v_4210_, 1);
v_isSharedCheck_4230_ = !lean_is_exclusive(v_v_4210_);
if (v_isSharedCheck_4230_ == 0)
{
v___x_4222_ = v_v_4210_;
v_isShared_4223_ = v_isSharedCheck_4230_;
goto v_resetjp_4221_;
}
else
{
lean_inc(v_val_4220_);
lean_inc(v_key_4219_);
lean_dec(v_v_4210_);
v___x_4222_ = lean_box(0);
v_isShared_4223_ = v_isSharedCheck_4230_;
goto v_resetjp_4221_;
}
v_resetjp_4221_:
{
uint8_t v___x_4224_; 
v___x_4224_ = l_Lean_instBEqMVarId_beq(v_x_4199_, v_key_4219_);
if (v___x_4224_ == 0)
{
lean_object* v___x_4225_; lean_object* v___x_4226_; 
lean_del_object(v___x_4222_);
v___x_4225_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4219_, v_val_4220_, v_x_4199_, v_x_4200_);
v___x_4226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4226_, 0, v___x_4225_);
v___y_4214_ = v___x_4226_;
goto v___jp_4213_;
}
else
{
lean_object* v___x_4228_; 
lean_dec(v_val_4220_);
lean_dec(v_key_4219_);
if (v_isShared_4223_ == 0)
{
lean_ctor_set(v___x_4222_, 1, v_x_4200_);
lean_ctor_set(v___x_4222_, 0, v_x_4199_);
v___x_4228_ = v___x_4222_;
goto v_reusejp_4227_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v_x_4199_);
lean_ctor_set(v_reuseFailAlloc_4229_, 1, v_x_4200_);
v___x_4228_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4227_;
}
v_reusejp_4227_:
{
v___y_4214_ = v___x_4228_;
goto v___jp_4213_;
}
}
}
}
case 1:
{
lean_object* v_node_4231_; lean_object* v___x_4233_; uint8_t v_isShared_4234_; uint8_t v_isSharedCheck_4243_; 
v_node_4231_ = lean_ctor_get(v_v_4210_, 0);
v_isSharedCheck_4243_ = !lean_is_exclusive(v_v_4210_);
if (v_isSharedCheck_4243_ == 0)
{
v___x_4233_ = v_v_4210_;
v_isShared_4234_ = v_isSharedCheck_4243_;
goto v_resetjp_4232_;
}
else
{
lean_inc(v_node_4231_);
lean_dec(v_v_4210_);
v___x_4233_ = lean_box(0);
v_isShared_4234_ = v_isSharedCheck_4243_;
goto v_resetjp_4232_;
}
v_resetjp_4232_:
{
size_t v___x_4235_; size_t v___x_4236_; size_t v___x_4237_; size_t v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4241_; 
v___x_4235_ = ((size_t)5ULL);
v___x_4236_ = lean_usize_shift_right(v_x_4197_, v___x_4235_);
v___x_4237_ = ((size_t)1ULL);
v___x_4238_ = lean_usize_add(v_x_4198_, v___x_4237_);
v___x_4239_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_node_4231_, v___x_4236_, v___x_4238_, v_x_4199_, v_x_4200_);
if (v_isShared_4234_ == 0)
{
lean_ctor_set(v___x_4233_, 0, v___x_4239_);
v___x_4241_ = v___x_4233_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4242_; 
v_reuseFailAlloc_4242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4242_, 0, v___x_4239_);
v___x_4241_ = v_reuseFailAlloc_4242_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
v___y_4214_ = v___x_4241_;
goto v___jp_4213_;
}
}
}
default: 
{
lean_object* v___x_4244_; 
v___x_4244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4244_, 0, v_x_4199_);
lean_ctor_set(v___x_4244_, 1, v_x_4200_);
v___y_4214_ = v___x_4244_;
goto v___jp_4213_;
}
}
v___jp_4213_:
{
lean_object* v___x_4215_; lean_object* v___x_4217_; 
v___x_4215_ = lean_array_fset(v_xs_x27_4212_, v_j_4204_, v___y_4214_);
lean_dec(v_j_4204_);
if (v_isShared_4209_ == 0)
{
lean_ctor_set(v___x_4208_, 0, v___x_4215_);
v___x_4217_ = v___x_4208_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v___x_4215_);
v___x_4217_ = v_reuseFailAlloc_4218_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
return v___x_4217_;
}
}
}
}
}
else
{
lean_object* v_ks_4247_; lean_object* v_vs_4248_; lean_object* v___x_4250_; uint8_t v_isShared_4251_; uint8_t v_isSharedCheck_4266_; 
v_ks_4247_ = lean_ctor_get(v_x_4196_, 0);
v_vs_4248_ = lean_ctor_get(v_x_4196_, 1);
v_isSharedCheck_4266_ = !lean_is_exclusive(v_x_4196_);
if (v_isSharedCheck_4266_ == 0)
{
v___x_4250_ = v_x_4196_;
v_isShared_4251_ = v_isSharedCheck_4266_;
goto v_resetjp_4249_;
}
else
{
lean_inc(v_vs_4248_);
lean_inc(v_ks_4247_);
lean_dec(v_x_4196_);
v___x_4250_ = lean_box(0);
v_isShared_4251_ = v_isSharedCheck_4266_;
goto v_resetjp_4249_;
}
v_resetjp_4249_:
{
lean_object* v___x_4253_; 
if (v_isShared_4251_ == 0)
{
v___x_4253_ = v___x_4250_;
goto v_reusejp_4252_;
}
else
{
lean_object* v_reuseFailAlloc_4265_; 
v_reuseFailAlloc_4265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4265_, 0, v_ks_4247_);
lean_ctor_set(v_reuseFailAlloc_4265_, 1, v_vs_4248_);
v___x_4253_ = v_reuseFailAlloc_4265_;
goto v_reusejp_4252_;
}
v_reusejp_4252_:
{
lean_object* v_newNode_4254_; size_t v___x_4255_; uint8_t v___x_4256_; 
v_newNode_4254_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(v___x_4253_, v_x_4199_, v_x_4200_);
v___x_4255_ = ((size_t)7ULL);
v___x_4256_ = lean_usize_dec_le(v___x_4255_, v_x_4198_);
if (v___x_4256_ == 0)
{
lean_object* v___x_4257_; lean_object* v___x_4258_; uint8_t v___x_4259_; 
v___x_4257_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4254_);
v___x_4258_ = lean_unsigned_to_nat(4u);
v___x_4259_ = lean_nat_dec_lt(v___x_4257_, v___x_4258_);
lean_dec(v___x_4257_);
if (v___x_4259_ == 0)
{
lean_object* v_ks_4260_; lean_object* v_vs_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; 
v_ks_4260_ = lean_ctor_get(v_newNode_4254_, 0);
lean_inc_ref(v_ks_4260_);
v_vs_4261_ = lean_ctor_get(v_newNode_4254_, 1);
lean_inc_ref(v_vs_4261_);
lean_dec_ref(v_newNode_4254_);
v___x_4262_ = lean_unsigned_to_nat(0u);
v___x_4263_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_4264_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_x_4198_, v_ks_4260_, v_vs_4261_, v___x_4262_, v___x_4263_);
lean_dec_ref(v_vs_4261_);
lean_dec_ref(v_ks_4260_);
return v___x_4264_;
}
else
{
return v_newNode_4254_;
}
}
else
{
return v_newNode_4254_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_4267_, lean_object* v_keys_4268_, lean_object* v_vals_4269_, lean_object* v_i_4270_, lean_object* v_entries_4271_){
_start:
{
lean_object* v___x_4272_; uint8_t v___x_4273_; 
v___x_4272_ = lean_array_get_size(v_keys_4268_);
v___x_4273_ = lean_nat_dec_lt(v_i_4270_, v___x_4272_);
if (v___x_4273_ == 0)
{
lean_dec(v_i_4270_);
return v_entries_4271_;
}
else
{
lean_object* v_k_4274_; lean_object* v_v_4275_; uint64_t v___x_4276_; size_t v_h_4277_; size_t v___x_4278_; lean_object* v___x_4279_; size_t v___x_4280_; size_t v___x_4281_; size_t v___x_4282_; size_t v_h_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; 
v_k_4274_ = lean_array_fget_borrowed(v_keys_4268_, v_i_4270_);
v_v_4275_ = lean_array_fget_borrowed(v_vals_4269_, v_i_4270_);
v___x_4276_ = l_Lean_instHashableMVarId_hash(v_k_4274_);
v_h_4277_ = lean_uint64_to_usize(v___x_4276_);
v___x_4278_ = ((size_t)5ULL);
v___x_4279_ = lean_unsigned_to_nat(1u);
v___x_4280_ = ((size_t)1ULL);
v___x_4281_ = lean_usize_sub(v_depth_4267_, v___x_4280_);
v___x_4282_ = lean_usize_mul(v___x_4278_, v___x_4281_);
v_h_4283_ = lean_usize_shift_right(v_h_4277_, v___x_4282_);
v___x_4284_ = lean_nat_add(v_i_4270_, v___x_4279_);
lean_dec(v_i_4270_);
lean_inc(v_v_4275_);
lean_inc(v_k_4274_);
v___x_4285_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_entries_4271_, v_h_4283_, v_depth_4267_, v_k_4274_, v_v_4275_);
v_i_4270_ = v___x_4284_;
v_entries_4271_ = v___x_4285_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_4287_, lean_object* v_keys_4288_, lean_object* v_vals_4289_, lean_object* v_i_4290_, lean_object* v_entries_4291_){
_start:
{
size_t v_depth_boxed_4292_; lean_object* v_res_4293_; 
v_depth_boxed_4292_ = lean_unbox_usize(v_depth_4287_);
lean_dec(v_depth_4287_);
v_res_4293_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_4292_, v_keys_4288_, v_vals_4289_, v_i_4290_, v_entries_4291_);
lean_dec_ref(v_vals_4289_);
lean_dec_ref(v_keys_4288_);
return v_res_4293_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_4294_, lean_object* v_x_4295_, lean_object* v_x_4296_, lean_object* v_x_4297_, lean_object* v_x_4298_){
_start:
{
size_t v_x_3982__boxed_4299_; size_t v_x_3983__boxed_4300_; lean_object* v_res_4301_; 
v_x_3982__boxed_4299_ = lean_unbox_usize(v_x_4295_);
lean_dec(v_x_4295_);
v_x_3983__boxed_4300_ = lean_unbox_usize(v_x_4296_);
lean_dec(v_x_4296_);
v_res_4301_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4294_, v_x_3982__boxed_4299_, v_x_3983__boxed_4300_, v_x_4297_, v_x_4298_);
return v_res_4301_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(lean_object* v_x_4302_, lean_object* v_x_4303_, lean_object* v_x_4304_){
_start:
{
uint64_t v___x_4305_; size_t v___x_4306_; size_t v___x_4307_; lean_object* v___x_4308_; 
v___x_4305_ = l_Lean_instHashableMVarId_hash(v_x_4303_);
v___x_4306_ = lean_uint64_to_usize(v___x_4305_);
v___x_4307_ = ((size_t)1ULL);
v___x_4308_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4302_, v___x_4306_, v___x_4307_, v_x_4303_, v_x_4304_);
return v___x_4308_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(lean_object* v_mvarId_4309_, lean_object* v_val_4310_, lean_object* v___y_4311_){
_start:
{
lean_object* v___x_4313_; lean_object* v_mctx_4314_; lean_object* v_cache_4315_; lean_object* v_zetaDeltaFVarIds_4316_; lean_object* v_postponed_4317_; lean_object* v_diag_4318_; lean_object* v___x_4320_; uint8_t v_isShared_4321_; uint8_t v_isSharedCheck_4347_; 
v___x_4313_ = lean_st_ref_take(v___y_4311_);
v_mctx_4314_ = lean_ctor_get(v___x_4313_, 0);
v_cache_4315_ = lean_ctor_get(v___x_4313_, 1);
v_zetaDeltaFVarIds_4316_ = lean_ctor_get(v___x_4313_, 2);
v_postponed_4317_ = lean_ctor_get(v___x_4313_, 3);
v_diag_4318_ = lean_ctor_get(v___x_4313_, 4);
v_isSharedCheck_4347_ = !lean_is_exclusive(v___x_4313_);
if (v_isSharedCheck_4347_ == 0)
{
v___x_4320_ = v___x_4313_;
v_isShared_4321_ = v_isSharedCheck_4347_;
goto v_resetjp_4319_;
}
else
{
lean_inc(v_diag_4318_);
lean_inc(v_postponed_4317_);
lean_inc(v_zetaDeltaFVarIds_4316_);
lean_inc(v_cache_4315_);
lean_inc(v_mctx_4314_);
lean_dec(v___x_4313_);
v___x_4320_ = lean_box(0);
v_isShared_4321_ = v_isSharedCheck_4347_;
goto v_resetjp_4319_;
}
v_resetjp_4319_:
{
lean_object* v_depth_4322_; lean_object* v_levelAssignDepth_4323_; lean_object* v_lmvarCounter_4324_; lean_object* v_mvarCounter_4325_; lean_object* v_lDecls_4326_; lean_object* v_decls_4327_; lean_object* v_userNames_4328_; lean_object* v_lAssignment_4329_; lean_object* v_eAssignment_4330_; lean_object* v_dAssignment_4331_; lean_object* v_instanceTypedMVars_4332_; lean_object* v___x_4334_; uint8_t v_isShared_4335_; uint8_t v_isSharedCheck_4346_; 
v_depth_4322_ = lean_ctor_get(v_mctx_4314_, 0);
v_levelAssignDepth_4323_ = lean_ctor_get(v_mctx_4314_, 1);
v_lmvarCounter_4324_ = lean_ctor_get(v_mctx_4314_, 2);
v_mvarCounter_4325_ = lean_ctor_get(v_mctx_4314_, 3);
v_lDecls_4326_ = lean_ctor_get(v_mctx_4314_, 4);
v_decls_4327_ = lean_ctor_get(v_mctx_4314_, 5);
v_userNames_4328_ = lean_ctor_get(v_mctx_4314_, 6);
v_lAssignment_4329_ = lean_ctor_get(v_mctx_4314_, 7);
v_eAssignment_4330_ = lean_ctor_get(v_mctx_4314_, 8);
v_dAssignment_4331_ = lean_ctor_get(v_mctx_4314_, 9);
v_instanceTypedMVars_4332_ = lean_ctor_get(v_mctx_4314_, 10);
v_isSharedCheck_4346_ = !lean_is_exclusive(v_mctx_4314_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4334_ = v_mctx_4314_;
v_isShared_4335_ = v_isSharedCheck_4346_;
goto v_resetjp_4333_;
}
else
{
lean_inc(v_instanceTypedMVars_4332_);
lean_inc(v_dAssignment_4331_);
lean_inc(v_eAssignment_4330_);
lean_inc(v_lAssignment_4329_);
lean_inc(v_userNames_4328_);
lean_inc(v_decls_4327_);
lean_inc(v_lDecls_4326_);
lean_inc(v_mvarCounter_4325_);
lean_inc(v_lmvarCounter_4324_);
lean_inc(v_levelAssignDepth_4323_);
lean_inc(v_depth_4322_);
lean_dec(v_mctx_4314_);
v___x_4334_ = lean_box(0);
v_isShared_4335_ = v_isSharedCheck_4346_;
goto v_resetjp_4333_;
}
v_resetjp_4333_:
{
lean_object* v___x_4336_; lean_object* v___x_4338_; 
v___x_4336_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(v_eAssignment_4330_, v_mvarId_4309_, v_val_4310_);
if (v_isShared_4335_ == 0)
{
lean_ctor_set(v___x_4334_, 8, v___x_4336_);
v___x_4338_ = v___x_4334_;
goto v_reusejp_4337_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_depth_4322_);
lean_ctor_set(v_reuseFailAlloc_4345_, 1, v_levelAssignDepth_4323_);
lean_ctor_set(v_reuseFailAlloc_4345_, 2, v_lmvarCounter_4324_);
lean_ctor_set(v_reuseFailAlloc_4345_, 3, v_mvarCounter_4325_);
lean_ctor_set(v_reuseFailAlloc_4345_, 4, v_lDecls_4326_);
lean_ctor_set(v_reuseFailAlloc_4345_, 5, v_decls_4327_);
lean_ctor_set(v_reuseFailAlloc_4345_, 6, v_userNames_4328_);
lean_ctor_set(v_reuseFailAlloc_4345_, 7, v_lAssignment_4329_);
lean_ctor_set(v_reuseFailAlloc_4345_, 8, v___x_4336_);
lean_ctor_set(v_reuseFailAlloc_4345_, 9, v_dAssignment_4331_);
lean_ctor_set(v_reuseFailAlloc_4345_, 10, v_instanceTypedMVars_4332_);
v___x_4338_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4337_;
}
v_reusejp_4337_:
{
lean_object* v___x_4340_; 
if (v_isShared_4321_ == 0)
{
lean_ctor_set(v___x_4320_, 0, v___x_4338_);
v___x_4340_ = v___x_4320_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4344_; 
v_reuseFailAlloc_4344_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4344_, 0, v___x_4338_);
lean_ctor_set(v_reuseFailAlloc_4344_, 1, v_cache_4315_);
lean_ctor_set(v_reuseFailAlloc_4344_, 2, v_zetaDeltaFVarIds_4316_);
lean_ctor_set(v_reuseFailAlloc_4344_, 3, v_postponed_4317_);
lean_ctor_set(v_reuseFailAlloc_4344_, 4, v_diag_4318_);
v___x_4340_ = v_reuseFailAlloc_4344_;
goto v_reusejp_4339_;
}
v_reusejp_4339_:
{
lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; 
v___x_4341_ = lean_st_ref_put(v___y_4311_, v___x_4340_);
v___x_4342_ = lean_box(0);
v___x_4343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4343_, 0, v___x_4342_);
return v___x_4343_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg___boxed(lean_object* v_mvarId_4348_, lean_object* v_val_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_){
_start:
{
lean_object* v_res_4352_; 
v_res_4352_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mvarId_4348_, v_val_4349_, v___y_4350_);
lean_dec(v___y_4350_);
return v_res_4352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___lam__0(lean_object* v_mv_u2081_4357_, lean_object* v_mv_u2082_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_){
_start:
{
lean_object* v___x_4367_; 
lean_inc(v_mv_u2081_4357_);
v___x_4367_ = l_Lean_MVarId_getDecl(v_mv_u2081_4357_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_);
if (lean_obj_tag(v___x_4367_) == 0)
{
lean_object* v_a_4368_; lean_object* v___x_4369_; 
v_a_4368_ = lean_ctor_get(v___x_4367_, 0);
lean_inc(v_a_4368_);
lean_dec_ref_known(v___x_4367_, 1);
lean_inc(v_mv_u2082_4358_);
v___x_4369_ = l_Lean_MVarId_getDecl(v_mv_u2082_4358_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_);
if (lean_obj_tag(v___x_4369_) == 0)
{
lean_object* v_a_4370_; lean_object* v_lctx_4371_; lean_object* v_type_4372_; lean_object* v_lctx_4373_; lean_object* v_type_4374_; uint8_t v___x_4375_; 
v_a_4370_ = lean_ctor_get(v___x_4369_, 0);
lean_inc(v_a_4370_);
lean_dec_ref_known(v___x_4369_, 1);
v_lctx_4371_ = lean_ctor_get(v_a_4368_, 1);
lean_inc_ref(v_lctx_4371_);
v_type_4372_ = lean_ctor_get(v_a_4368_, 2);
lean_inc_ref(v_type_4372_);
lean_dec(v_a_4368_);
v_lctx_4373_ = lean_ctor_get(v_a_4370_, 1);
lean_inc_ref(v_lctx_4373_);
v_type_4374_ = lean_ctor_get(v_a_4370_, 2);
lean_inc_ref(v_type_4374_);
lean_dec(v_a_4370_);
v___x_4375_ = lean_expr_eqv(v_type_4372_, v_type_4374_);
lean_dec_ref(v_type_4374_);
lean_dec_ref(v_type_4372_);
if (v___x_4375_ == 0)
{
lean_dec_ref(v_lctx_4373_);
lean_dec_ref(v_lctx_4371_);
lean_dec(v_mv_u2082_4358_);
lean_dec(v_mv_u2081_4357_);
goto v___jp_4364_;
}
else
{
lean_object* v___x_4376_; uint8_t v___x_4377_; 
v___x_4376_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
v___x_4377_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_4371_, v_lctx_4373_, v___x_4376_);
if (v___x_4377_ == 0)
{
uint8_t v___x_4378_; 
v___x_4378_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_4373_, v_lctx_4371_, v___x_4376_);
lean_dec_ref(v_lctx_4371_);
lean_dec_ref(v_lctx_4373_);
if (v___x_4378_ == 0)
{
lean_dec(v_mv_u2082_4358_);
lean_dec(v_mv_u2081_4357_);
goto v___jp_4364_;
}
else
{
lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4390_; 
v___x_4379_ = l_Lean_Expr_mvar___override(v_mv_u2082_4358_);
v___x_4380_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mv_u2081_4357_, v___x_4379_, v___y_4360_);
v_isSharedCheck_4390_ = !lean_is_exclusive(v___x_4380_);
if (v_isSharedCheck_4390_ == 0)
{
lean_object* v_unused_4391_; 
v_unused_4391_ = lean_ctor_get(v___x_4380_, 0);
lean_dec(v_unused_4391_);
v___x_4382_ = v___x_4380_;
v_isShared_4383_ = v_isSharedCheck_4390_;
goto v_resetjp_4381_;
}
else
{
lean_dec(v___x_4380_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4390_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4388_; 
v___x_4384_ = lean_box(v___x_4377_);
v___x_4385_ = lean_box(v___x_4375_);
v___x_4386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4386_, 0, v___x_4384_);
lean_ctor_set(v___x_4386_, 1, v___x_4385_);
if (v_isShared_4383_ == 0)
{
lean_ctor_set(v___x_4382_, 0, v___x_4386_);
v___x_4388_ = v___x_4382_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4389_; 
v_reuseFailAlloc_4389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4389_, 0, v___x_4386_);
v___x_4388_ = v_reuseFailAlloc_4389_;
goto v_reusejp_4387_;
}
v_reusejp_4387_:
{
return v___x_4388_;
}
}
}
}
else
{
lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4395_; uint8_t v_isShared_4396_; uint8_t v_isSharedCheck_4404_; 
lean_dec_ref(v_lctx_4373_);
lean_dec_ref(v_lctx_4371_);
v___x_4392_ = l_Lean_Expr_mvar___override(v_mv_u2081_4357_);
v___x_4393_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mv_u2082_4358_, v___x_4392_, v___y_4360_);
v_isSharedCheck_4404_ = !lean_is_exclusive(v___x_4393_);
if (v_isSharedCheck_4404_ == 0)
{
lean_object* v_unused_4405_; 
v_unused_4405_ = lean_ctor_get(v___x_4393_, 0);
lean_dec(v_unused_4405_);
v___x_4395_ = v___x_4393_;
v_isShared_4396_ = v_isSharedCheck_4404_;
goto v_resetjp_4394_;
}
else
{
lean_dec(v___x_4393_);
v___x_4395_ = lean_box(0);
v_isShared_4396_ = v_isSharedCheck_4404_;
goto v_resetjp_4394_;
}
v_resetjp_4394_:
{
uint8_t v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4402_; 
v___x_4397_ = 0;
v___x_4398_ = lean_box(v___x_4375_);
v___x_4399_ = lean_box(v___x_4397_);
v___x_4400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4400_, 0, v___x_4398_);
lean_ctor_set(v___x_4400_, 1, v___x_4399_);
if (v_isShared_4396_ == 0)
{
lean_ctor_set(v___x_4395_, 0, v___x_4400_);
v___x_4402_ = v___x_4395_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v___x_4400_);
v___x_4402_ = v_reuseFailAlloc_4403_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
return v___x_4402_;
}
}
}
}
}
else
{
lean_object* v_a_4406_; lean_object* v___x_4408_; uint8_t v_isShared_4409_; uint8_t v_isSharedCheck_4413_; 
lean_dec(v_a_4368_);
lean_dec(v_mv_u2082_4358_);
lean_dec(v_mv_u2081_4357_);
v_a_4406_ = lean_ctor_get(v___x_4369_, 0);
v_isSharedCheck_4413_ = !lean_is_exclusive(v___x_4369_);
if (v_isSharedCheck_4413_ == 0)
{
v___x_4408_ = v___x_4369_;
v_isShared_4409_ = v_isSharedCheck_4413_;
goto v_resetjp_4407_;
}
else
{
lean_inc(v_a_4406_);
lean_dec(v___x_4369_);
v___x_4408_ = lean_box(0);
v_isShared_4409_ = v_isSharedCheck_4413_;
goto v_resetjp_4407_;
}
v_resetjp_4407_:
{
lean_object* v___x_4411_; 
if (v_isShared_4409_ == 0)
{
v___x_4411_ = v___x_4408_;
goto v_reusejp_4410_;
}
else
{
lean_object* v_reuseFailAlloc_4412_; 
v_reuseFailAlloc_4412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4412_, 0, v_a_4406_);
v___x_4411_ = v_reuseFailAlloc_4412_;
goto v_reusejp_4410_;
}
v_reusejp_4410_:
{
return v___x_4411_;
}
}
}
}
else
{
lean_object* v_a_4414_; lean_object* v___x_4416_; uint8_t v_isShared_4417_; uint8_t v_isSharedCheck_4421_; 
lean_dec(v_mv_u2082_4358_);
lean_dec(v_mv_u2081_4357_);
v_a_4414_ = lean_ctor_get(v___x_4367_, 0);
v_isSharedCheck_4421_ = !lean_is_exclusive(v___x_4367_);
if (v_isSharedCheck_4421_ == 0)
{
v___x_4416_ = v___x_4367_;
v_isShared_4417_ = v_isSharedCheck_4421_;
goto v_resetjp_4415_;
}
else
{
lean_inc(v_a_4414_);
lean_dec(v___x_4367_);
v___x_4416_ = lean_box(0);
v_isShared_4417_ = v_isSharedCheck_4421_;
goto v_resetjp_4415_;
}
v_resetjp_4415_:
{
lean_object* v___x_4419_; 
if (v_isShared_4417_ == 0)
{
v___x_4419_ = v___x_4416_;
goto v_reusejp_4418_;
}
else
{
lean_object* v_reuseFailAlloc_4420_; 
v_reuseFailAlloc_4420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4420_, 0, v_a_4414_);
v___x_4419_ = v_reuseFailAlloc_4420_;
goto v_reusejp_4418_;
}
v_reusejp_4418_:
{
return v___x_4419_;
}
}
}
v___jp_4364_:
{
lean_object* v___x_4365_; lean_object* v___x_4366_; 
v___x_4365_ = ((lean_object*)(l_Lean_Elab_WF_assignSubsumed___lam__0___closed__0));
v___x_4366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4366_, 0, v___x_4365_);
return v___x_4366_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___lam__0___boxed(lean_object* v_mv_u2081_4422_, lean_object* v_mv_u2082_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_){
_start:
{
lean_object* v_res_4429_; 
v_res_4429_ = l_Lean_Elab_WF_assignSubsumed___lam__0(v_mv_u2081_4422_, v_mv_u2082_4423_, v___y_4424_, v___y_4425_, v___y_4426_, v___y_4427_);
lean_dec(v___y_4427_);
lean_dec_ref(v___y_4426_);
lean_dec(v___y_4425_);
lean_dec_ref(v___y_4424_);
return v_res_4429_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1(lean_object* v___x_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_){
_start:
{
lean_object* v___x_4436_; 
v___x_4436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4436_, 0, v___x_4430_);
return v___x_4436_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1___boxed(lean_object* v___x_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_){
_start:
{
lean_object* v_res_4443_; 
v_res_4443_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1(v___x_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_);
lean_dec(v___y_4441_);
lean_dec_ref(v___y_4440_);
lean_dec(v___y_4439_);
lean_dec_ref(v___y_4438_);
return v_res_4443_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0(lean_object* v_f_4444_, lean_object* v___x_4445_, lean_object* v___x_4446_, lean_object* v___x_4447_, lean_object* v_a_4448_, uint8_t v___x_4449_, lean_object* v_snd_4450_, lean_object* v_fst_4451_, lean_object* v_next_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_){
_start:
{
lean_object* v___x_4458_; 
v___x_4458_ = lean_apply_7(v_f_4444_, v___x_4445_, v___x_4446_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_, lean_box(0));
if (lean_obj_tag(v___x_4458_) == 0)
{
lean_object* v_a_4459_; lean_object* v___x_4461_; uint8_t v_isShared_4462_; uint8_t v_isSharedCheck_4494_; 
v_a_4459_ = lean_ctor_get(v___x_4458_, 0);
v_isSharedCheck_4494_ = !lean_is_exclusive(v___x_4458_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_4461_ = v___x_4458_;
v_isShared_4462_ = v_isSharedCheck_4494_;
goto v_resetjp_4460_;
}
else
{
lean_inc(v_a_4459_);
lean_dec(v___x_4458_);
v___x_4461_ = lean_box(0);
v_isShared_4462_ = v_isSharedCheck_4494_;
goto v_resetjp_4460_;
}
v_resetjp_4460_:
{
lean_object* v_fst_4463_; lean_object* v_snd_4464_; lean_object* v___x_4466_; uint8_t v_isShared_4467_; uint8_t v_isSharedCheck_4493_; 
v_fst_4463_ = lean_ctor_get(v_a_4459_, 0);
v_snd_4464_ = lean_ctor_get(v_a_4459_, 1);
v_isSharedCheck_4493_ = !lean_is_exclusive(v_a_4459_);
if (v_isSharedCheck_4493_ == 0)
{
v___x_4466_ = v_a_4459_;
v_isShared_4467_ = v_isSharedCheck_4493_;
goto v_resetjp_4465_;
}
else
{
lean_inc(v_snd_4464_);
lean_inc(v_fst_4463_);
lean_dec(v_a_4459_);
v___x_4466_ = lean_box(0);
v_isShared_4467_ = v_isSharedCheck_4493_;
goto v_resetjp_4465_;
}
v_resetjp_4465_:
{
lean_object* v_removed_4469_; lean_object* v_numRemoved_4470_; uint8_t v___x_4489_; 
v___x_4489_ = lean_unbox(v_fst_4463_);
lean_dec(v_fst_4463_);
if (v___x_4489_ == 0)
{
lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; 
v___x_4490_ = lean_nat_add(v_snd_4450_, v___x_4447_);
lean_dec(v_snd_4450_);
v___x_4491_ = lean_box(v___x_4449_);
v___x_4492_ = lean_array_set(v_fst_4451_, v_next_4452_, v___x_4491_);
v_removed_4469_ = v___x_4492_;
v_numRemoved_4470_ = v___x_4490_;
goto v___jp_4468_;
}
else
{
v_removed_4469_ = v_fst_4451_;
v_numRemoved_4470_ = v_snd_4450_;
goto v___jp_4468_;
}
v___jp_4468_:
{
uint8_t v___x_4471_; 
v___x_4471_ = lean_unbox(v_snd_4464_);
lean_dec(v_snd_4464_);
if (v___x_4471_ == 0)
{
lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4476_; 
v___x_4472_ = lean_nat_add(v_numRemoved_4470_, v___x_4447_);
lean_dec(v_numRemoved_4470_);
v___x_4473_ = lean_box(v___x_4449_);
v___x_4474_ = lean_array_set(v_removed_4469_, v_a_4448_, v___x_4473_);
if (v_isShared_4467_ == 0)
{
lean_ctor_set(v___x_4466_, 1, v___x_4472_);
lean_ctor_set(v___x_4466_, 0, v___x_4474_);
v___x_4476_ = v___x_4466_;
goto v_reusejp_4475_;
}
else
{
lean_object* v_reuseFailAlloc_4481_; 
v_reuseFailAlloc_4481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4481_, 0, v___x_4474_);
lean_ctor_set(v_reuseFailAlloc_4481_, 1, v___x_4472_);
v___x_4476_ = v_reuseFailAlloc_4481_;
goto v_reusejp_4475_;
}
v_reusejp_4475_:
{
lean_object* v___x_4477_; lean_object* v___x_4479_; 
v___x_4477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4477_, 0, v___x_4476_);
if (v_isShared_4462_ == 0)
{
lean_ctor_set(v___x_4461_, 0, v___x_4477_);
v___x_4479_ = v___x_4461_;
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
else
{
lean_object* v___x_4483_; 
if (v_isShared_4467_ == 0)
{
lean_ctor_set(v___x_4466_, 1, v_numRemoved_4470_);
lean_ctor_set(v___x_4466_, 0, v_removed_4469_);
v___x_4483_ = v___x_4466_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4488_; 
v_reuseFailAlloc_4488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4488_, 0, v_removed_4469_);
lean_ctor_set(v_reuseFailAlloc_4488_, 1, v_numRemoved_4470_);
v___x_4483_ = v_reuseFailAlloc_4488_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
lean_object* v___x_4484_; lean_object* v___x_4486_; 
v___x_4484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4484_, 0, v___x_4483_);
if (v_isShared_4462_ == 0)
{
lean_ctor_set(v___x_4461_, 0, v___x_4484_);
v___x_4486_ = v___x_4461_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v___x_4484_);
v___x_4486_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
return v___x_4486_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4502_; 
lean_dec(v_fst_4451_);
lean_dec(v_snd_4450_);
v_a_4495_ = lean_ctor_get(v___x_4458_, 0);
v_isSharedCheck_4502_ = !lean_is_exclusive(v___x_4458_);
if (v_isSharedCheck_4502_ == 0)
{
v___x_4497_ = v___x_4458_;
v_isShared_4498_ = v_isSharedCheck_4502_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_a_4495_);
lean_dec(v___x_4458_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4502_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v___x_4500_; 
if (v_isShared_4498_ == 0)
{
v___x_4500_ = v___x_4497_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4501_; 
v_reuseFailAlloc_4501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4501_, 0, v_a_4495_);
v___x_4500_ = v_reuseFailAlloc_4501_;
goto v_reusejp_4499_;
}
v_reusejp_4499_:
{
return v___x_4500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_f_4503_, lean_object* v___x_4504_, lean_object* v___x_4505_, lean_object* v___x_4506_, lean_object* v_a_4507_, lean_object* v___x_4508_, lean_object* v_snd_4509_, lean_object* v_fst_4510_, lean_object* v_next_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_){
_start:
{
uint8_t v___x_4355__boxed_4517_; lean_object* v_res_4518_; 
v___x_4355__boxed_4517_ = lean_unbox(v___x_4508_);
v_res_4518_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0(v_f_4503_, v___x_4504_, v___x_4505_, v___x_4506_, v_a_4507_, v___x_4355__boxed_4517_, v_snd_4509_, v_fst_4510_, v_next_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_);
lean_dec(v_next_4511_);
lean_dec(v_a_4507_);
lean_dec(v___x_4506_);
return v_res_4518_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(lean_object* v_upperBound_4519_, lean_object* v_a_4520_, lean_object* v_next_4521_, lean_object* v_f_4522_, lean_object* v_a_4523_, lean_object* v_b_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_){
_start:
{
uint8_t v___x_4530_; 
v___x_4530_ = lean_nat_dec_lt(v_a_4523_, v_upperBound_4519_);
if (v___x_4530_ == 0)
{
lean_object* v___x_4531_; 
lean_dec(v_a_4523_);
lean_dec_ref(v_f_4522_);
lean_dec(v_next_4521_);
v___x_4531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4531_, 0, v_b_4524_);
return v___x_4531_;
}
else
{
lean_object* v_fst_4532_; lean_object* v_snd_4533_; lean_object* v___x_4535_; uint8_t v_isShared_4536_; uint8_t v_isSharedCheck_4580_; 
v_fst_4532_ = lean_ctor_get(v_b_4524_, 0);
v_snd_4533_ = lean_ctor_get(v_b_4524_, 1);
v_isSharedCheck_4580_ = !lean_is_exclusive(v_b_4524_);
if (v_isSharedCheck_4580_ == 0)
{
v___x_4535_ = v_b_4524_;
v_isShared_4536_ = v_isSharedCheck_4580_;
goto v_resetjp_4534_;
}
else
{
lean_inc(v_snd_4533_);
lean_inc(v_fst_4532_);
lean_dec(v_b_4524_);
v___x_4535_ = lean_box(0);
v_isShared_4536_ = v_isSharedCheck_4580_;
goto v_resetjp_4534_;
}
v_resetjp_4534_:
{
lean_object* v___x_4537_; lean_object* v___y_4539_; uint8_t v___y_4562_; uint8_t v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; uint8_t v___x_4575_; 
v___x_4537_ = lean_unsigned_to_nat(1u);
v___x_4572_ = 0;
v___x_4573_ = lean_box(v___x_4572_);
v___x_4574_ = lean_array_get(v___x_4573_, v_fst_4532_, v_next_4521_);
lean_dec(v___x_4573_);
v___x_4575_ = lean_unbox(v___x_4574_);
if (v___x_4575_ == 0)
{
lean_object* v___x_4576_; lean_object* v___x_4577_; uint8_t v___x_4578_; 
lean_dec(v___x_4574_);
v___x_4576_ = lean_box(v___x_4572_);
v___x_4577_ = lean_array_get(v___x_4576_, v_fst_4532_, v_a_4523_);
lean_dec(v___x_4576_);
v___x_4578_ = lean_unbox(v___x_4577_);
lean_dec(v___x_4577_);
v___y_4562_ = v___x_4578_;
goto v___jp_4561_;
}
else
{
uint8_t v___x_4579_; 
v___x_4579_ = lean_unbox(v___x_4574_);
lean_dec(v___x_4574_);
v___y_4562_ = v___x_4579_;
goto v___jp_4561_;
}
v___jp_4538_:
{
lean_object* v___x_4540_; 
lean_inc(v___y_4528_);
lean_inc_ref(v___y_4527_);
lean_inc(v___y_4526_);
lean_inc_ref(v___y_4525_);
v___x_4540_ = lean_apply_5(v___y_4539_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_, lean_box(0));
if (lean_obj_tag(v___x_4540_) == 0)
{
lean_object* v_a_4541_; lean_object* v___x_4543_; uint8_t v_isShared_4544_; uint8_t v_isSharedCheck_4552_; 
v_a_4541_ = lean_ctor_get(v___x_4540_, 0);
v_isSharedCheck_4552_ = !lean_is_exclusive(v___x_4540_);
if (v_isSharedCheck_4552_ == 0)
{
v___x_4543_ = v___x_4540_;
v_isShared_4544_ = v_isSharedCheck_4552_;
goto v_resetjp_4542_;
}
else
{
lean_inc(v_a_4541_);
lean_dec(v___x_4540_);
v___x_4543_ = lean_box(0);
v_isShared_4544_ = v_isSharedCheck_4552_;
goto v_resetjp_4542_;
}
v_resetjp_4542_:
{
if (lean_obj_tag(v_a_4541_) == 0)
{
lean_object* v_a_4545_; lean_object* v___x_4547_; 
lean_dec(v_a_4523_);
lean_dec_ref(v_f_4522_);
lean_dec(v_next_4521_);
v_a_4545_ = lean_ctor_get(v_a_4541_, 0);
lean_inc(v_a_4545_);
lean_dec_ref_known(v_a_4541_, 1);
if (v_isShared_4544_ == 0)
{
lean_ctor_set(v___x_4543_, 0, v_a_4545_);
v___x_4547_ = v___x_4543_;
goto v_reusejp_4546_;
}
else
{
lean_object* v_reuseFailAlloc_4548_; 
v_reuseFailAlloc_4548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4548_, 0, v_a_4545_);
v___x_4547_ = v_reuseFailAlloc_4548_;
goto v_reusejp_4546_;
}
v_reusejp_4546_:
{
return v___x_4547_;
}
}
else
{
lean_object* v_a_4549_; lean_object* v___x_4550_; 
lean_del_object(v___x_4543_);
v_a_4549_ = lean_ctor_get(v_a_4541_, 0);
lean_inc(v_a_4549_);
lean_dec_ref_known(v_a_4541_, 1);
v___x_4550_ = lean_nat_add(v_a_4523_, v___x_4537_);
lean_dec(v_a_4523_);
v_a_4523_ = v___x_4550_;
v_b_4524_ = v_a_4549_;
goto _start;
}
}
}
else
{
lean_object* v_a_4553_; lean_object* v___x_4555_; uint8_t v_isShared_4556_; uint8_t v_isSharedCheck_4560_; 
lean_dec(v_a_4523_);
lean_dec_ref(v_f_4522_);
lean_dec(v_next_4521_);
v_a_4553_ = lean_ctor_get(v___x_4540_, 0);
v_isSharedCheck_4560_ = !lean_is_exclusive(v___x_4540_);
if (v_isSharedCheck_4560_ == 0)
{
v___x_4555_ = v___x_4540_;
v_isShared_4556_ = v_isSharedCheck_4560_;
goto v_resetjp_4554_;
}
else
{
lean_inc(v_a_4553_);
lean_dec(v___x_4540_);
v___x_4555_ = lean_box(0);
v_isShared_4556_ = v_isSharedCheck_4560_;
goto v_resetjp_4554_;
}
v_resetjp_4554_:
{
lean_object* v___x_4558_; 
if (v_isShared_4556_ == 0)
{
v___x_4558_ = v___x_4555_;
goto v_reusejp_4557_;
}
else
{
lean_object* v_reuseFailAlloc_4559_; 
v_reuseFailAlloc_4559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4559_, 0, v_a_4553_);
v___x_4558_ = v_reuseFailAlloc_4559_;
goto v_reusejp_4557_;
}
v_reusejp_4557_:
{
return v___x_4558_;
}
}
}
}
v___jp_4561_:
{
if (v___y_4562_ == 0)
{
lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___f_4566_; 
lean_del_object(v___x_4535_);
v___x_4563_ = lean_array_fget_borrowed(v_a_4520_, v_next_4521_);
v___x_4564_ = lean_array_fget_borrowed(v_a_4520_, v_a_4523_);
v___x_4565_ = lean_box(v___x_4530_);
lean_inc(v_next_4521_);
lean_inc(v_a_4523_);
lean_inc(v___x_4564_);
lean_inc(v___x_4563_);
lean_inc_ref(v_f_4522_);
v___f_4566_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4566_, 0, v_f_4522_);
lean_closure_set(v___f_4566_, 1, v___x_4563_);
lean_closure_set(v___f_4566_, 2, v___x_4564_);
lean_closure_set(v___f_4566_, 3, v___x_4537_);
lean_closure_set(v___f_4566_, 4, v_a_4523_);
lean_closure_set(v___f_4566_, 5, v___x_4565_);
lean_closure_set(v___f_4566_, 6, v_snd_4533_);
lean_closure_set(v___f_4566_, 7, v_fst_4532_);
lean_closure_set(v___f_4566_, 8, v_next_4521_);
v___y_4539_ = v___f_4566_;
goto v___jp_4538_;
}
else
{
lean_object* v___x_4568_; 
if (v_isShared_4536_ == 0)
{
v___x_4568_ = v___x_4535_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4571_; 
v_reuseFailAlloc_4571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4571_, 0, v_fst_4532_);
lean_ctor_set(v_reuseFailAlloc_4571_, 1, v_snd_4533_);
v___x_4568_ = v_reuseFailAlloc_4571_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
lean_object* v___x_4569_; lean_object* v___f_4570_; 
v___x_4569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4569_, 0, v___x_4568_);
v___f_4570_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1___boxed), 6, 1);
lean_closure_set(v___f_4570_, 0, v___x_4569_);
v___y_4539_ = v___f_4570_;
goto v___jp_4538_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___boxed(lean_object* v_upperBound_4581_, lean_object* v_a_4582_, lean_object* v_next_4583_, lean_object* v_f_4584_, lean_object* v_a_4585_, lean_object* v_b_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_){
_start:
{
lean_object* v_res_4592_; 
v_res_4592_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v_upperBound_4581_, v_a_4582_, v_next_4583_, v_f_4584_, v_a_4585_, v_b_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_);
lean_dec(v___y_4590_);
lean_dec_ref(v___y_4589_);
lean_dec(v___y_4588_);
lean_dec_ref(v___y_4587_);
lean_dec_ref(v_a_4582_);
lean_dec(v_upperBound_4581_);
return v_res_4592_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(lean_object* v_upperBound_4593_, lean_object* v___x_4594_, lean_object* v_a_4595_, lean_object* v_f_4596_, lean_object* v_a_4597_, lean_object* v_b_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_){
_start:
{
uint8_t v___x_4604_; 
v___x_4604_ = lean_nat_dec_lt(v_a_4597_, v_upperBound_4593_);
if (v___x_4604_ == 0)
{
lean_object* v___x_4605_; 
lean_dec(v_a_4597_);
lean_dec_ref(v_f_4596_);
v___x_4605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4605_, 0, v_b_4598_);
return v___x_4605_;
}
else
{
lean_object* v_fst_4606_; lean_object* v_snd_4607_; lean_object* v___x_4609_; uint8_t v_isShared_4610_; uint8_t v_isSharedCheck_4628_; 
v_fst_4606_ = lean_ctor_get(v_b_4598_, 0);
v_snd_4607_ = lean_ctor_get(v_b_4598_, 1);
v_isSharedCheck_4628_ = !lean_is_exclusive(v_b_4598_);
if (v_isSharedCheck_4628_ == 0)
{
v___x_4609_ = v_b_4598_;
v_isShared_4610_ = v_isSharedCheck_4628_;
goto v_resetjp_4608_;
}
else
{
lean_inc(v_snd_4607_);
lean_inc(v_fst_4606_);
lean_dec(v_b_4598_);
v___x_4609_ = lean_box(0);
v_isShared_4610_ = v_isSharedCheck_4628_;
goto v_resetjp_4608_;
}
v_resetjp_4608_:
{
lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4614_; 
v___x_4611_ = lean_unsigned_to_nat(1u);
v___x_4612_ = lean_nat_add(v_a_4597_, v___x_4611_);
if (v_isShared_4610_ == 0)
{
v___x_4614_ = v___x_4609_;
goto v_reusejp_4613_;
}
else
{
lean_object* v_reuseFailAlloc_4627_; 
v_reuseFailAlloc_4627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4627_, 0, v_fst_4606_);
lean_ctor_set(v_reuseFailAlloc_4627_, 1, v_snd_4607_);
v___x_4614_ = v_reuseFailAlloc_4627_;
goto v_reusejp_4613_;
}
v_reusejp_4613_:
{
lean_object* v___x_4615_; 
lean_inc(v___x_4612_);
lean_inc_ref(v_f_4596_);
v___x_4615_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v___x_4594_, v_a_4595_, v_a_4597_, v_f_4596_, v___x_4612_, v___x_4614_, v___y_4599_, v___y_4600_, v___y_4601_, v___y_4602_);
if (lean_obj_tag(v___x_4615_) == 0)
{
lean_object* v_a_4616_; lean_object* v_fst_4617_; lean_object* v_snd_4618_; lean_object* v___x_4620_; uint8_t v_isShared_4621_; uint8_t v_isSharedCheck_4626_; 
v_a_4616_ = lean_ctor_get(v___x_4615_, 0);
lean_inc(v_a_4616_);
lean_dec_ref_known(v___x_4615_, 1);
v_fst_4617_ = lean_ctor_get(v_a_4616_, 0);
v_snd_4618_ = lean_ctor_get(v_a_4616_, 1);
v_isSharedCheck_4626_ = !lean_is_exclusive(v_a_4616_);
if (v_isSharedCheck_4626_ == 0)
{
v___x_4620_ = v_a_4616_;
v_isShared_4621_ = v_isSharedCheck_4626_;
goto v_resetjp_4619_;
}
else
{
lean_inc(v_snd_4618_);
lean_inc(v_fst_4617_);
lean_dec(v_a_4616_);
v___x_4620_ = lean_box(0);
v_isShared_4621_ = v_isSharedCheck_4626_;
goto v_resetjp_4619_;
}
v_resetjp_4619_:
{
lean_object* v___x_4623_; 
if (v_isShared_4621_ == 0)
{
v___x_4623_ = v___x_4620_;
goto v_reusejp_4622_;
}
else
{
lean_object* v_reuseFailAlloc_4625_; 
v_reuseFailAlloc_4625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4625_, 0, v_fst_4617_);
lean_ctor_set(v_reuseFailAlloc_4625_, 1, v_snd_4618_);
v___x_4623_ = v_reuseFailAlloc_4625_;
goto v_reusejp_4622_;
}
v_reusejp_4622_:
{
v_a_4597_ = v___x_4612_;
v_b_4598_ = v___x_4623_;
goto _start;
}
}
}
else
{
lean_dec(v___x_4612_);
lean_dec_ref(v_f_4596_);
return v___x_4615_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_4629_, lean_object* v___x_4630_, lean_object* v_a_4631_, lean_object* v_f_4632_, lean_object* v_a_4633_, lean_object* v_b_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_){
_start:
{
lean_object* v_res_4640_; 
v_res_4640_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v_upperBound_4629_, v___x_4630_, v_a_4631_, v_f_4632_, v_a_4633_, v_b_4634_, v___y_4635_, v___y_4636_, v___y_4637_, v___y_4638_);
lean_dec(v___y_4638_);
lean_dec_ref(v___y_4637_);
lean_dec(v___y_4636_);
lean_dec_ref(v___y_4635_);
lean_dec_ref(v_a_4631_);
lean_dec(v___x_4630_);
lean_dec(v_upperBound_4629_);
return v_res_4640_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0(lean_object* v___x_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_){
_start:
{
lean_object* v___x_4647_; 
v___x_4647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4647_, 0, v___x_4641_);
return v___x_4647_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed(lean_object* v___x_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_){
_start:
{
lean_object* v_res_4654_; 
v_res_4654_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0(v___x_4648_, v___y_4649_, v___y_4650_, v___y_4651_, v___y_4652_);
lean_dec(v___y_4652_);
lean_dec_ref(v___y_4651_);
lean_dec(v___y_4650_);
lean_dec_ref(v___y_4649_);
return v_res_4654_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(lean_object* v_upperBound_4655_, lean_object* v_removed_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_, lean_object* v_b_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_){
_start:
{
lean_object* v___y_4666_; uint8_t v___x_4689_; 
v___x_4689_ = lean_nat_dec_lt(v_a_4658_, v_upperBound_4655_);
if (v___x_4689_ == 0)
{
lean_object* v___x_4690_; 
lean_dec(v_a_4658_);
v___x_4690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4690_, 0, v_b_4659_);
return v___x_4690_;
}
else
{
uint8_t v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; uint8_t v___x_4694_; 
v___x_4691_ = 0;
v___x_4692_ = lean_box(v___x_4691_);
v___x_4693_ = lean_array_get(v___x_4692_, v_removed_4656_, v_a_4658_);
lean_dec(v___x_4692_);
v___x_4694_ = lean_unbox(v___x_4693_);
lean_dec(v___x_4693_);
if (v___x_4694_ == 0)
{
lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___f_4698_; 
v___x_4695_ = lean_array_fget_borrowed(v_a_4657_, v_a_4658_);
lean_inc(v___x_4695_);
v___x_4696_ = lean_array_push(v_b_4659_, v___x_4695_);
v___x_4697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4697_, 0, v___x_4696_);
v___f_4698_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4698_, 0, v___x_4697_);
v___y_4666_ = v___f_4698_;
goto v___jp_4665_;
}
else
{
lean_object* v___x_4699_; lean_object* v___f_4700_; 
v___x_4699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4699_, 0, v_b_4659_);
v___f_4700_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4700_, 0, v___x_4699_);
v___y_4666_ = v___f_4700_;
goto v___jp_4665_;
}
}
v___jp_4665_:
{
lean_object* v___x_4667_; 
lean_inc(v___y_4663_);
lean_inc_ref(v___y_4662_);
lean_inc(v___y_4661_);
lean_inc_ref(v___y_4660_);
v___x_4667_ = lean_apply_5(v___y_4666_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_, lean_box(0));
if (lean_obj_tag(v___x_4667_) == 0)
{
lean_object* v_a_4668_; lean_object* v___x_4670_; uint8_t v_isShared_4671_; uint8_t v_isSharedCheck_4680_; 
v_a_4668_ = lean_ctor_get(v___x_4667_, 0);
v_isSharedCheck_4680_ = !lean_is_exclusive(v___x_4667_);
if (v_isSharedCheck_4680_ == 0)
{
v___x_4670_ = v___x_4667_;
v_isShared_4671_ = v_isSharedCheck_4680_;
goto v_resetjp_4669_;
}
else
{
lean_inc(v_a_4668_);
lean_dec(v___x_4667_);
v___x_4670_ = lean_box(0);
v_isShared_4671_ = v_isSharedCheck_4680_;
goto v_resetjp_4669_;
}
v_resetjp_4669_:
{
if (lean_obj_tag(v_a_4668_) == 0)
{
lean_object* v_a_4672_; lean_object* v___x_4674_; 
lean_dec(v_a_4658_);
v_a_4672_ = lean_ctor_get(v_a_4668_, 0);
lean_inc(v_a_4672_);
lean_dec_ref_known(v_a_4668_, 1);
if (v_isShared_4671_ == 0)
{
lean_ctor_set(v___x_4670_, 0, v_a_4672_);
v___x_4674_ = v___x_4670_;
goto v_reusejp_4673_;
}
else
{
lean_object* v_reuseFailAlloc_4675_; 
v_reuseFailAlloc_4675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4675_, 0, v_a_4672_);
v___x_4674_ = v_reuseFailAlloc_4675_;
goto v_reusejp_4673_;
}
v_reusejp_4673_:
{
return v___x_4674_;
}
}
else
{
lean_object* v_a_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; 
lean_del_object(v___x_4670_);
v_a_4676_ = lean_ctor_get(v_a_4668_, 0);
lean_inc(v_a_4676_);
lean_dec_ref_known(v_a_4668_, 1);
v___x_4677_ = lean_unsigned_to_nat(1u);
v___x_4678_ = lean_nat_add(v_a_4658_, v___x_4677_);
lean_dec(v_a_4658_);
v_a_4658_ = v___x_4678_;
v_b_4659_ = v_a_4676_;
goto _start;
}
}
}
else
{
lean_object* v_a_4681_; lean_object* v___x_4683_; uint8_t v_isShared_4684_; uint8_t v_isSharedCheck_4688_; 
lean_dec(v_a_4658_);
v_a_4681_ = lean_ctor_get(v___x_4667_, 0);
v_isSharedCheck_4688_ = !lean_is_exclusive(v___x_4667_);
if (v_isSharedCheck_4688_ == 0)
{
v___x_4683_ = v___x_4667_;
v_isShared_4684_ = v_isSharedCheck_4688_;
goto v_resetjp_4682_;
}
else
{
lean_inc(v_a_4681_);
lean_dec(v___x_4667_);
v___x_4683_ = lean_box(0);
v_isShared_4684_ = v_isSharedCheck_4688_;
goto v_resetjp_4682_;
}
v_resetjp_4682_:
{
lean_object* v___x_4686_; 
if (v_isShared_4684_ == 0)
{
v___x_4686_ = v___x_4683_;
goto v_reusejp_4685_;
}
else
{
lean_object* v_reuseFailAlloc_4687_; 
v_reuseFailAlloc_4687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4687_, 0, v_a_4681_);
v___x_4686_ = v_reuseFailAlloc_4687_;
goto v_reusejp_4685_;
}
v_reusejp_4685_:
{
return v___x_4686_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___boxed(lean_object* v_upperBound_4701_, lean_object* v_removed_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_, lean_object* v_b_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_){
_start:
{
lean_object* v_res_4711_; 
v_res_4711_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v_upperBound_4701_, v_removed_4702_, v_a_4703_, v_a_4704_, v_b_4705_, v___y_4706_, v___y_4707_, v___y_4708_, v___y_4709_);
lean_dec(v___y_4709_);
lean_dec_ref(v___y_4708_);
lean_dec(v___y_4707_);
lean_dec_ref(v___y_4706_);
lean_dec_ref(v_a_4703_);
lean_dec_ref(v_removed_4702_);
lean_dec(v_upperBound_4701_);
return v_res_4711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(lean_object* v_a_4712_, lean_object* v_f_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_){
_start:
{
lean_object* v___x_4719_; uint8_t v___x_4720_; lean_object* v___x_4721_; lean_object* v_removed_4722_; lean_object* v_numRemoved_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; 
v___x_4719_ = lean_array_get_size(v_a_4712_);
v___x_4720_ = 0;
v___x_4721_ = lean_box(v___x_4720_);
v_removed_4722_ = lean_mk_array(v___x_4719_, v___x_4721_);
v_numRemoved_4723_ = lean_unsigned_to_nat(0u);
v___x_4724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4724_, 0, v_removed_4722_);
lean_ctor_set(v___x_4724_, 1, v_numRemoved_4723_);
v___x_4725_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v___x_4719_, v___x_4719_, v_a_4712_, v_f_4713_, v_numRemoved_4723_, v___x_4724_, v___y_4714_, v___y_4715_, v___y_4716_, v___y_4717_);
if (lean_obj_tag(v___x_4725_) == 0)
{
lean_object* v_a_4726_; lean_object* v_fst_4727_; lean_object* v_snd_4728_; lean_object* v_a_x27_4729_; lean_object* v___x_4730_; 
v_a_4726_ = lean_ctor_get(v___x_4725_, 0);
lean_inc(v_a_4726_);
lean_dec_ref_known(v___x_4725_, 1);
v_fst_4727_ = lean_ctor_get(v_a_4726_, 0);
lean_inc(v_fst_4727_);
v_snd_4728_ = lean_ctor_get(v_a_4726_, 1);
lean_inc(v_snd_4728_);
lean_dec(v_a_4726_);
v_a_x27_4729_ = lean_mk_empty_array_with_capacity(v_snd_4728_);
lean_dec(v_snd_4728_);
v___x_4730_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v___x_4719_, v_fst_4727_, v_a_4712_, v_numRemoved_4723_, v_a_x27_4729_, v___y_4714_, v___y_4715_, v___y_4716_, v___y_4717_);
lean_dec(v_fst_4727_);
return v___x_4730_;
}
else
{
lean_object* v_a_4731_; lean_object* v___x_4733_; uint8_t v_isShared_4734_; uint8_t v_isSharedCheck_4738_; 
v_a_4731_ = lean_ctor_get(v___x_4725_, 0);
v_isSharedCheck_4738_ = !lean_is_exclusive(v___x_4725_);
if (v_isSharedCheck_4738_ == 0)
{
v___x_4733_ = v___x_4725_;
v_isShared_4734_ = v_isSharedCheck_4738_;
goto v_resetjp_4732_;
}
else
{
lean_inc(v_a_4731_);
lean_dec(v___x_4725_);
v___x_4733_ = lean_box(0);
v_isShared_4734_ = v_isSharedCheck_4738_;
goto v_resetjp_4732_;
}
v_resetjp_4732_:
{
lean_object* v___x_4736_; 
if (v_isShared_4734_ == 0)
{
v___x_4736_ = v___x_4733_;
goto v_reusejp_4735_;
}
else
{
lean_object* v_reuseFailAlloc_4737_; 
v_reuseFailAlloc_4737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4737_, 0, v_a_4731_);
v___x_4736_ = v_reuseFailAlloc_4737_;
goto v_reusejp_4735_;
}
v_reusejp_4735_:
{
return v___x_4736_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg___boxed(lean_object* v_a_4739_, lean_object* v_f_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_){
_start:
{
lean_object* v_res_4746_; 
v_res_4746_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_a_4739_, v_f_4740_, v___y_4741_, v___y_4742_, v___y_4743_, v___y_4744_);
lean_dec(v___y_4744_);
lean_dec_ref(v___y_4743_);
lean_dec(v___y_4742_);
lean_dec_ref(v___y_4741_);
lean_dec_ref(v_a_4739_);
return v_res_4746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed(lean_object* v_mvars_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_){
_start:
{
lean_object* v___f_4754_; lean_object* v___x_4755_; 
v___f_4754_ = ((lean_object*)(l_Lean_Elab_WF_assignSubsumed___closed__0));
v___x_4755_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_mvars_4748_, v___f_4754_, v_a_4749_, v_a_4750_, v_a_4751_, v_a_4752_);
return v___x_4755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___boxed(lean_object* v_mvars_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_){
_start:
{
lean_object* v_res_4762_; 
v_res_4762_ = l_Lean_Elab_WF_assignSubsumed(v_mvars_4756_, v_a_4757_, v_a_4758_, v_a_4759_, v_a_4760_);
lean_dec(v_a_4760_);
lean_dec_ref(v_a_4759_);
lean_dec(v_a_4758_);
lean_dec_ref(v_a_4757_);
lean_dec_ref(v_mvars_4756_);
return v_res_4762_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0(lean_object* v_mvarId_4763_, lean_object* v_val_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_, lean_object* v___y_4768_){
_start:
{
lean_object* v___x_4770_; 
v___x_4770_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mvarId_4763_, v_val_4764_, v___y_4766_);
return v___x_4770_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___boxed(lean_object* v_mvarId_4771_, lean_object* v_val_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_){
_start:
{
lean_object* v_res_4778_; 
v_res_4778_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0(v_mvarId_4771_, v_val_4772_, v___y_4773_, v___y_4774_, v___y_4775_, v___y_4776_);
lean_dec(v___y_4776_);
lean_dec_ref(v___y_4775_);
lean_dec(v___y_4774_);
lean_dec_ref(v___y_4773_);
return v_res_4778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1(lean_object* v_00_u03b1_4779_, lean_object* v_a_4780_, lean_object* v_f_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_){
_start:
{
lean_object* v___x_4787_; 
v___x_4787_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_a_4780_, v_f_4781_, v___y_4782_, v___y_4783_, v___y_4784_, v___y_4785_);
return v___x_4787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___boxed(lean_object* v_00_u03b1_4788_, lean_object* v_a_4789_, lean_object* v_f_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_){
_start:
{
lean_object* v_res_4796_; 
v_res_4796_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1(v_00_u03b1_4788_, v_a_4789_, v_f_4790_, v___y_4791_, v___y_4792_, v___y_4793_, v___y_4794_);
lean_dec(v___y_4794_);
lean_dec_ref(v___y_4793_);
lean_dec(v___y_4792_);
lean_dec_ref(v___y_4791_);
lean_dec_ref(v_a_4789_);
return v_res_4796_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0(lean_object* v_00_u03b2_4797_, lean_object* v_x_4798_, lean_object* v_x_4799_, lean_object* v_x_4800_){
_start:
{
lean_object* v___x_4801_; 
v___x_4801_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(v_x_4798_, v_x_4799_, v_x_4800_);
return v___x_4801_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2(lean_object* v_upperBound_4802_, lean_object* v_00_u03b1_4803_, lean_object* v_a_4804_, lean_object* v_next_4805_, lean_object* v_f_4806_, lean_object* v_inst_4807_, lean_object* v_R_4808_, lean_object* v_a_4809_, lean_object* v_b_4810_, lean_object* v_c_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_){
_start:
{
lean_object* v___x_4817_; 
v___x_4817_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v_upperBound_4802_, v_a_4804_, v_next_4805_, v_f_4806_, v_a_4809_, v_b_4810_, v___y_4812_, v___y_4813_, v___y_4814_, v___y_4815_);
return v___x_4817_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___boxed(lean_object* v_upperBound_4818_, lean_object* v_00_u03b1_4819_, lean_object* v_a_4820_, lean_object* v_next_4821_, lean_object* v_f_4822_, lean_object* v_inst_4823_, lean_object* v_R_4824_, lean_object* v_a_4825_, lean_object* v_b_4826_, lean_object* v_c_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_){
_start:
{
lean_object* v_res_4833_; 
v_res_4833_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2(v_upperBound_4818_, v_00_u03b1_4819_, v_a_4820_, v_next_4821_, v_f_4822_, v_inst_4823_, v_R_4824_, v_a_4825_, v_b_4826_, v_c_4827_, v___y_4828_, v___y_4829_, v___y_4830_, v___y_4831_);
lean_dec(v___y_4831_);
lean_dec_ref(v___y_4830_);
lean_dec(v___y_4829_);
lean_dec_ref(v___y_4828_);
lean_dec_ref(v_a_4820_);
lean_dec(v_upperBound_4818_);
return v_res_4833_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3(lean_object* v_00_u03b1_4834_, lean_object* v_upperBound_4835_, lean_object* v_removed_4836_, lean_object* v_a_4837_, lean_object* v_inst_4838_, lean_object* v_R_4839_, lean_object* v_a_4840_, lean_object* v_b_4841_, lean_object* v_c_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_){
_start:
{
lean_object* v___x_4848_; 
v___x_4848_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v_upperBound_4835_, v_removed_4836_, v_a_4837_, v_a_4840_, v_b_4841_, v___y_4843_, v___y_4844_, v___y_4845_, v___y_4846_);
return v___x_4848_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___boxed(lean_object* v_00_u03b1_4849_, lean_object* v_upperBound_4850_, lean_object* v_removed_4851_, lean_object* v_a_4852_, lean_object* v_inst_4853_, lean_object* v_R_4854_, lean_object* v_a_4855_, lean_object* v_b_4856_, lean_object* v_c_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_){
_start:
{
lean_object* v_res_4863_; 
v_res_4863_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3(v_00_u03b1_4849_, v_upperBound_4850_, v_removed_4851_, v_a_4852_, v_inst_4853_, v_R_4854_, v_a_4855_, v_b_4856_, v_c_4857_, v___y_4858_, v___y_4859_, v___y_4860_, v___y_4861_);
lean_dec(v___y_4861_);
lean_dec_ref(v___y_4860_);
lean_dec(v___y_4859_);
lean_dec_ref(v___y_4858_);
lean_dec_ref(v_a_4852_);
lean_dec_ref(v_removed_4851_);
lean_dec(v_upperBound_4850_);
return v_res_4863_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4(lean_object* v_upperBound_4864_, lean_object* v___x_4865_, lean_object* v_00_u03b1_4866_, lean_object* v_a_4867_, lean_object* v_f_4868_, lean_object* v_inst_4869_, lean_object* v_R_4870_, lean_object* v_a_4871_, lean_object* v_b_4872_, lean_object* v_c_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_){
_start:
{
lean_object* v___x_4879_; 
v___x_4879_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v_upperBound_4864_, v___x_4865_, v_a_4867_, v_f_4868_, v_a_4871_, v_b_4872_, v___y_4874_, v___y_4875_, v___y_4876_, v___y_4877_);
return v___x_4879_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___boxed(lean_object* v_upperBound_4880_, lean_object* v___x_4881_, lean_object* v_00_u03b1_4882_, lean_object* v_a_4883_, lean_object* v_f_4884_, lean_object* v_inst_4885_, lean_object* v_R_4886_, lean_object* v_a_4887_, lean_object* v_b_4888_, lean_object* v_c_4889_, lean_object* v___y_4890_, lean_object* v___y_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_){
_start:
{
lean_object* v_res_4895_; 
v_res_4895_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4(v_upperBound_4880_, v___x_4881_, v_00_u03b1_4882_, v_a_4883_, v_f_4884_, v_inst_4885_, v_R_4886_, v_a_4887_, v_b_4888_, v_c_4889_, v___y_4890_, v___y_4891_, v___y_4892_, v___y_4893_);
lean_dec(v___y_4893_);
lean_dec_ref(v___y_4892_);
lean_dec(v___y_4891_);
lean_dec_ref(v___y_4890_);
lean_dec_ref(v_a_4883_);
lean_dec(v___x_4881_);
lean_dec(v_upperBound_4880_);
return v_res_4895_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4896_, lean_object* v_x_4897_, size_t v_x_4898_, size_t v_x_4899_, lean_object* v_x_4900_, lean_object* v_x_4901_){
_start:
{
lean_object* v___x_4902_; 
v___x_4902_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4897_, v_x_4898_, v_x_4899_, v_x_4900_, v_x_4901_);
return v___x_4902_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4903_, lean_object* v_x_4904_, lean_object* v_x_4905_, lean_object* v_x_4906_, lean_object* v_x_4907_, lean_object* v_x_4908_){
_start:
{
size_t v_x_4925__boxed_4909_; size_t v_x_4926__boxed_4910_; lean_object* v_res_4911_; 
v_x_4925__boxed_4909_ = lean_unbox_usize(v_x_4905_);
lean_dec(v_x_4905_);
v_x_4926__boxed_4910_ = lean_unbox_usize(v_x_4906_);
lean_dec(v_x_4906_);
v_res_4911_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1(v_00_u03b2_4903_, v_x_4904_, v_x_4925__boxed_4909_, v_x_4926__boxed_4910_, v_x_4907_, v_x_4908_);
return v_res_4911_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_4912_, lean_object* v_n_4913_, lean_object* v_k_4914_, lean_object* v_v_4915_){
_start:
{
lean_object* v___x_4916_; 
v___x_4916_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(v_n_4913_, v_k_4914_, v_v_4915_);
return v___x_4916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_4917_, size_t v_depth_4918_, lean_object* v_keys_4919_, lean_object* v_vals_4920_, lean_object* v_heq_4921_, lean_object* v_i_4922_, lean_object* v_entries_4923_){
_start:
{
lean_object* v___x_4924_; 
v___x_4924_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_4918_, v_keys_4919_, v_vals_4920_, v_i_4922_, v_entries_4923_);
return v___x_4924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_4925_, lean_object* v_depth_4926_, lean_object* v_keys_4927_, lean_object* v_vals_4928_, lean_object* v_heq_4929_, lean_object* v_i_4930_, lean_object* v_entries_4931_){
_start:
{
size_t v_depth_boxed_4932_; lean_object* v_res_4933_; 
v_depth_boxed_4932_ = lean_unbox_usize(v_depth_4926_);
lean_dec(v_depth_4926_);
v_res_4933_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_4925_, v_depth_boxed_4932_, v_keys_4927_, v_vals_4928_, v_heq_4929_, v_i_4930_, v_entries_4931_);
lean_dec_ref(v_vals_4928_);
lean_dec_ref(v_keys_4927_);
return v_res_4933_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_4934_, lean_object* v_x_4935_, lean_object* v_x_4936_, lean_object* v_x_4937_, lean_object* v_x_4938_){
_start:
{
lean_object* v___x_4939_; 
v___x_4939_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_x_4935_, v_x_4936_, v_x_4937_, v_x_4938_);
return v___x_4939_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4941_; lean_object* v___x_4942_; 
v___x_4941_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__0));
v___x_4942_ = l_Lean_stringToMessageData(v___x_4941_);
return v___x_4942_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4944_; lean_object* v___x_4945_; 
v___x_4944_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__2));
v___x_4945_ = l_Lean_stringToMessageData(v___x_4944_);
return v___x_4945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(lean_object* v_argsPacker_4946_, lean_object* v_as_4947_, size_t v_sz_4948_, size_t v_i_4949_, lean_object* v_b_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_){
_start:
{
lean_object* v_a_4957_; uint8_t v___x_4961_; 
v___x_4961_ = lean_usize_dec_lt(v_i_4949_, v_sz_4948_);
if (v___x_4961_ == 0)
{
lean_object* v___x_4962_; 
v___x_4962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4962_, 0, v_b_4950_);
return v___x_4962_;
}
else
{
lean_object* v_a_4963_; lean_object* v___x_4964_; 
v_a_4963_ = lean_array_uget_borrowed(v_as_4947_, v_i_4949_);
lean_inc(v_a_4963_);
v___x_4964_ = l_Lean_MVarId_getType(v_a_4963_, v___y_4951_, v___y_4952_, v___y_4953_, v___y_4954_);
if (lean_obj_tag(v___x_4964_) == 0)
{
lean_object* v_a_4965_; lean_object* v___y_4967_; lean_object* v___y_4968_; lean_object* v___y_4969_; lean_object* v___y_4970_; 
v_a_4965_ = lean_ctor_get(v___x_4964_, 0);
lean_inc(v_a_4965_);
lean_dec_ref_known(v___x_4964_, 1);
if (lean_obj_tag(v_a_4965_) == 10)
{
lean_object* v_expr_4983_; 
v_expr_4983_ = lean_ctor_get(v_a_4965_, 1);
if (lean_obj_tag(v_expr_4983_) == 5)
{
lean_object* v_arg_4984_; lean_object* v___x_4985_; 
lean_inc_ref(v_expr_4983_);
lean_dec_ref_known(v_a_4965_, 2);
v_arg_4984_ = lean_ctor_get(v_expr_4983_, 1);
lean_inc_ref_n(v_arg_4984_, 2);
lean_dec_ref_known(v_expr_4983_, 2);
v___x_4985_ = l_Lean_Meta_ArgsPacker_unpack(v_argsPacker_4946_, v_arg_4984_);
if (lean_obj_tag(v___x_4985_) == 1)
{
lean_object* v_val_4986_; lean_object* v_fst_4987_; lean_object* v___x_4988_; uint8_t v___x_4989_; 
lean_dec_ref(v_arg_4984_);
v_val_4986_ = lean_ctor_get(v___x_4985_, 0);
lean_inc(v_val_4986_);
lean_dec_ref_known(v___x_4985_, 1);
v_fst_4987_ = lean_ctor_get(v_val_4986_, 0);
lean_inc(v_fst_4987_);
lean_dec(v_val_4986_);
v___x_4988_ = lean_array_get_size(v_b_4950_);
v___x_4989_ = lean_nat_dec_lt(v_fst_4987_, v___x_4988_);
if (v___x_4989_ == 0)
{
lean_dec(v_fst_4987_);
v_a_4957_ = v_b_4950_;
goto v___jp_4956_;
}
else
{
lean_object* v_v_4990_; lean_object* v___x_4991_; lean_object* v_xs_x27_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; 
v_v_4990_ = lean_array_fget(v_b_4950_, v_fst_4987_);
v___x_4991_ = lean_box(0);
v_xs_x27_4992_ = lean_array_fset(v_b_4950_, v_fst_4987_, v___x_4991_);
lean_inc(v_a_4963_);
v___x_4993_ = lean_array_push(v_v_4990_, v_a_4963_);
v___x_4994_ = lean_array_fset(v_xs_x27_4992_, v_fst_4987_, v___x_4993_);
lean_dec(v_fst_4987_);
v_a_4957_ = v___x_4994_;
goto v___jp_4956_;
}
}
else
{
lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; 
lean_dec(v___x_4985_);
v___x_4995_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3);
v___x_4996_ = l_Lean_indentExpr(v_arg_4984_);
v___x_4997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4997_, 0, v___x_4995_);
lean_ctor_set(v___x_4997_, 1, v___x_4996_);
v___x_4998_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v___x_4997_, v___y_4951_, v___y_4952_, v___y_4953_, v___y_4954_);
if (lean_obj_tag(v___x_4998_) == 0)
{
lean_dec_ref_known(v___x_4998_, 1);
v_a_4957_ = v_b_4950_;
goto v___jp_4956_;
}
else
{
lean_object* v_a_4999_; lean_object* v___x_5001_; uint8_t v_isShared_5002_; uint8_t v_isSharedCheck_5006_; 
lean_dec_ref(v_b_4950_);
v_a_4999_ = lean_ctor_get(v___x_4998_, 0);
v_isSharedCheck_5006_ = !lean_is_exclusive(v___x_4998_);
if (v_isSharedCheck_5006_ == 0)
{
v___x_5001_ = v___x_4998_;
v_isShared_5002_ = v_isSharedCheck_5006_;
goto v_resetjp_5000_;
}
else
{
lean_inc(v_a_4999_);
lean_dec(v___x_4998_);
v___x_5001_ = lean_box(0);
v_isShared_5002_ = v_isSharedCheck_5006_;
goto v_resetjp_5000_;
}
v_resetjp_5000_:
{
lean_object* v___x_5004_; 
if (v_isShared_5002_ == 0)
{
v___x_5004_ = v___x_5001_;
goto v_reusejp_5003_;
}
else
{
lean_object* v_reuseFailAlloc_5005_; 
v_reuseFailAlloc_5005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5005_, 0, v_a_4999_);
v___x_5004_ = v_reuseFailAlloc_5005_;
goto v_reusejp_5003_;
}
v_reusejp_5003_:
{
return v___x_5004_;
}
}
}
}
}
else
{
v___y_4967_ = v___y_4951_;
v___y_4968_ = v___y_4952_;
v___y_4969_ = v___y_4953_;
v___y_4970_ = v___y_4954_;
goto v___jp_4966_;
}
}
else
{
v___y_4967_ = v___y_4951_;
v___y_4968_ = v___y_4952_;
v___y_4969_ = v___y_4953_;
v___y_4970_ = v___y_4954_;
goto v___jp_4966_;
}
v___jp_4966_:
{
lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; 
v___x_4971_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1);
v___x_4972_ = l_Lean_indentExpr(v_a_4965_);
v___x_4973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4973_, 0, v___x_4971_);
lean_ctor_set(v___x_4973_, 1, v___x_4972_);
v___x_4974_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v___x_4973_, v___y_4967_, v___y_4968_, v___y_4969_, v___y_4970_);
if (lean_obj_tag(v___x_4974_) == 0)
{
lean_dec_ref_known(v___x_4974_, 1);
v_a_4957_ = v_b_4950_;
goto v___jp_4956_;
}
else
{
lean_object* v_a_4975_; lean_object* v___x_4977_; uint8_t v_isShared_4978_; uint8_t v_isSharedCheck_4982_; 
lean_dec_ref(v_b_4950_);
v_a_4975_ = lean_ctor_get(v___x_4974_, 0);
v_isSharedCheck_4982_ = !lean_is_exclusive(v___x_4974_);
if (v_isSharedCheck_4982_ == 0)
{
v___x_4977_ = v___x_4974_;
v_isShared_4978_ = v_isSharedCheck_4982_;
goto v_resetjp_4976_;
}
else
{
lean_inc(v_a_4975_);
lean_dec(v___x_4974_);
v___x_4977_ = lean_box(0);
v_isShared_4978_ = v_isSharedCheck_4982_;
goto v_resetjp_4976_;
}
v_resetjp_4976_:
{
lean_object* v___x_4980_; 
if (v_isShared_4978_ == 0)
{
v___x_4980_ = v___x_4977_;
goto v_reusejp_4979_;
}
else
{
lean_object* v_reuseFailAlloc_4981_; 
v_reuseFailAlloc_4981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4981_, 0, v_a_4975_);
v___x_4980_ = v_reuseFailAlloc_4981_;
goto v_reusejp_4979_;
}
v_reusejp_4979_:
{
return v___x_4980_;
}
}
}
}
}
else
{
lean_object* v_a_5007_; lean_object* v___x_5009_; uint8_t v_isShared_5010_; uint8_t v_isSharedCheck_5014_; 
lean_dec_ref(v_b_4950_);
v_a_5007_ = lean_ctor_get(v___x_4964_, 0);
v_isSharedCheck_5014_ = !lean_is_exclusive(v___x_4964_);
if (v_isSharedCheck_5014_ == 0)
{
v___x_5009_ = v___x_4964_;
v_isShared_5010_ = v_isSharedCheck_5014_;
goto v_resetjp_5008_;
}
else
{
lean_inc(v_a_5007_);
lean_dec(v___x_4964_);
v___x_5009_ = lean_box(0);
v_isShared_5010_ = v_isSharedCheck_5014_;
goto v_resetjp_5008_;
}
v_resetjp_5008_:
{
lean_object* v___x_5012_; 
if (v_isShared_5010_ == 0)
{
v___x_5012_ = v___x_5009_;
goto v_reusejp_5011_;
}
else
{
lean_object* v_reuseFailAlloc_5013_; 
v_reuseFailAlloc_5013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5013_, 0, v_a_5007_);
v___x_5012_ = v_reuseFailAlloc_5013_;
goto v_reusejp_5011_;
}
v_reusejp_5011_:
{
return v___x_5012_;
}
}
}
}
v___jp_4956_:
{
size_t v___x_4958_; size_t v___x_4959_; 
v___x_4958_ = ((size_t)1ULL);
v___x_4959_ = lean_usize_add(v_i_4949_, v___x_4958_);
v_i_4949_ = v___x_4959_;
v_b_4950_ = v_a_4957_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___boxed(lean_object* v_argsPacker_5015_, lean_object* v_as_5016_, lean_object* v_sz_5017_, lean_object* v_i_5018_, lean_object* v_b_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_){
_start:
{
size_t v_sz_boxed_5025_; size_t v_i_boxed_5026_; lean_object* v_res_5027_; 
v_sz_boxed_5025_ = lean_unbox_usize(v_sz_5017_);
lean_dec(v_sz_5017_);
v_i_boxed_5026_ = lean_unbox_usize(v_i_5018_);
lean_dec(v_i_5018_);
v_res_5027_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(v_argsPacker_5015_, v_as_5016_, v_sz_boxed_5025_, v_i_boxed_5026_, v_b_5019_, v___y_5020_, v___y_5021_, v___y_5022_, v___y_5023_);
lean_dec(v___y_5023_);
lean_dec_ref(v___y_5022_);
lean_dec(v___y_5021_);
lean_dec_ref(v___y_5020_);
lean_dec_ref(v_as_5016_);
lean_dec_ref(v_argsPacker_5015_);
return v_res_5027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_groupGoalsByFunction(lean_object* v_argsPacker_5028_, lean_object* v_numFuncs_5029_, lean_object* v_goals_5030_, lean_object* v_a_5031_, lean_object* v_a_5032_, lean_object* v_a_5033_, lean_object* v_a_5034_){
_start:
{
lean_object* v___x_5036_; lean_object* v_r_5037_; size_t v_sz_5038_; size_t v___x_5039_; lean_object* v___x_5040_; 
v___x_5036_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg___closed__0));
v_r_5037_ = lean_mk_array(v_numFuncs_5029_, v___x_5036_);
v_sz_5038_ = lean_array_size(v_goals_5030_);
v___x_5039_ = ((size_t)0ULL);
v___x_5040_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(v_argsPacker_5028_, v_goals_5030_, v_sz_5038_, v___x_5039_, v_r_5037_, v_a_5031_, v_a_5032_, v_a_5033_, v_a_5034_);
return v___x_5040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_groupGoalsByFunction___boxed(lean_object* v_argsPacker_5041_, lean_object* v_numFuncs_5042_, lean_object* v_goals_5043_, lean_object* v_a_5044_, lean_object* v_a_5045_, lean_object* v_a_5046_, lean_object* v_a_5047_, lean_object* v_a_5048_){
_start:
{
lean_object* v_res_5049_; 
v_res_5049_ = l_Lean_Elab_WF_groupGoalsByFunction(v_argsPacker_5041_, v_numFuncs_5042_, v_goals_5043_, v_a_5044_, v_a_5045_, v_a_5046_, v_a_5047_);
lean_dec(v_a_5047_);
lean_dec_ref(v_a_5046_);
lean_dec(v_a_5045_);
lean_dec_ref(v_a_5044_);
lean_dec_ref(v_goals_5043_);
lean_dec_ref(v_argsPacker_5041_);
return v_res_5049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(lean_object* v_t_5050_, lean_object* v___y_5051_){
_start:
{
lean_object* v___x_5053_; lean_object* v_infoState_5054_; uint8_t v_enabled_5055_; 
v___x_5053_ = lean_st_ref_get(v___y_5051_);
v_infoState_5054_ = lean_ctor_get(v___x_5053_, 7);
lean_inc_ref(v_infoState_5054_);
lean_dec(v___x_5053_);
v_enabled_5055_ = lean_ctor_get_uint8(v_infoState_5054_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5054_);
if (v_enabled_5055_ == 0)
{
lean_object* v___x_5056_; lean_object* v___x_5057_; 
lean_dec_ref(v_t_5050_);
v___x_5056_ = lean_box(0);
v___x_5057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5057_, 0, v___x_5056_);
return v___x_5057_;
}
else
{
lean_object* v___x_5058_; lean_object* v_infoState_5059_; lean_object* v_env_5060_; lean_object* v_nextMacroScope_5061_; lean_object* v_ngen_5062_; lean_object* v_auxDeclNGen_5063_; lean_object* v_traceState_5064_; lean_object* v_cache_5065_; lean_object* v_messages_5066_; lean_object* v_snapshotTasks_5067_; lean_object* v___x_5069_; uint8_t v_isShared_5070_; uint8_t v_isSharedCheck_5089_; 
v___x_5058_ = lean_st_ref_take(v___y_5051_);
v_infoState_5059_ = lean_ctor_get(v___x_5058_, 7);
v_env_5060_ = lean_ctor_get(v___x_5058_, 0);
v_nextMacroScope_5061_ = lean_ctor_get(v___x_5058_, 1);
v_ngen_5062_ = lean_ctor_get(v___x_5058_, 2);
v_auxDeclNGen_5063_ = lean_ctor_get(v___x_5058_, 3);
v_traceState_5064_ = lean_ctor_get(v___x_5058_, 4);
v_cache_5065_ = lean_ctor_get(v___x_5058_, 5);
v_messages_5066_ = lean_ctor_get(v___x_5058_, 6);
v_snapshotTasks_5067_ = lean_ctor_get(v___x_5058_, 8);
v_isSharedCheck_5089_ = !lean_is_exclusive(v___x_5058_);
if (v_isSharedCheck_5089_ == 0)
{
v___x_5069_ = v___x_5058_;
v_isShared_5070_ = v_isSharedCheck_5089_;
goto v_resetjp_5068_;
}
else
{
lean_inc(v_snapshotTasks_5067_);
lean_inc(v_infoState_5059_);
lean_inc(v_messages_5066_);
lean_inc(v_cache_5065_);
lean_inc(v_traceState_5064_);
lean_inc(v_auxDeclNGen_5063_);
lean_inc(v_ngen_5062_);
lean_inc(v_nextMacroScope_5061_);
lean_inc(v_env_5060_);
lean_dec(v___x_5058_);
v___x_5069_ = lean_box(0);
v_isShared_5070_ = v_isSharedCheck_5089_;
goto v_resetjp_5068_;
}
v_resetjp_5068_:
{
uint8_t v_enabled_5071_; lean_object* v_assignment_5072_; lean_object* v_lazyAssignment_5073_; lean_object* v_trees_5074_; lean_object* v___x_5076_; uint8_t v_isShared_5077_; uint8_t v_isSharedCheck_5088_; 
v_enabled_5071_ = lean_ctor_get_uint8(v_infoState_5059_, sizeof(void*)*3);
v_assignment_5072_ = lean_ctor_get(v_infoState_5059_, 0);
v_lazyAssignment_5073_ = lean_ctor_get(v_infoState_5059_, 1);
v_trees_5074_ = lean_ctor_get(v_infoState_5059_, 2);
v_isSharedCheck_5088_ = !lean_is_exclusive(v_infoState_5059_);
if (v_isSharedCheck_5088_ == 0)
{
v___x_5076_ = v_infoState_5059_;
v_isShared_5077_ = v_isSharedCheck_5088_;
goto v_resetjp_5075_;
}
else
{
lean_inc(v_trees_5074_);
lean_inc(v_lazyAssignment_5073_);
lean_inc(v_assignment_5072_);
lean_dec(v_infoState_5059_);
v___x_5076_ = lean_box(0);
v_isShared_5077_ = v_isSharedCheck_5088_;
goto v_resetjp_5075_;
}
v_resetjp_5075_:
{
lean_object* v___x_5078_; lean_object* v___x_5080_; 
v___x_5078_ = l_Lean_PersistentArray_push___redArg(v_trees_5074_, v_t_5050_);
if (v_isShared_5077_ == 0)
{
lean_ctor_set(v___x_5076_, 2, v___x_5078_);
v___x_5080_ = v___x_5076_;
goto v_reusejp_5079_;
}
else
{
lean_object* v_reuseFailAlloc_5087_; 
v_reuseFailAlloc_5087_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5087_, 0, v_assignment_5072_);
lean_ctor_set(v_reuseFailAlloc_5087_, 1, v_lazyAssignment_5073_);
lean_ctor_set(v_reuseFailAlloc_5087_, 2, v___x_5078_);
lean_ctor_set_uint8(v_reuseFailAlloc_5087_, sizeof(void*)*3, v_enabled_5071_);
v___x_5080_ = v_reuseFailAlloc_5087_;
goto v_reusejp_5079_;
}
v_reusejp_5079_:
{
lean_object* v___x_5082_; 
if (v_isShared_5070_ == 0)
{
lean_ctor_set(v___x_5069_, 7, v___x_5080_);
v___x_5082_ = v___x_5069_;
goto v_reusejp_5081_;
}
else
{
lean_object* v_reuseFailAlloc_5086_; 
v_reuseFailAlloc_5086_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5086_, 0, v_env_5060_);
lean_ctor_set(v_reuseFailAlloc_5086_, 1, v_nextMacroScope_5061_);
lean_ctor_set(v_reuseFailAlloc_5086_, 2, v_ngen_5062_);
lean_ctor_set(v_reuseFailAlloc_5086_, 3, v_auxDeclNGen_5063_);
lean_ctor_set(v_reuseFailAlloc_5086_, 4, v_traceState_5064_);
lean_ctor_set(v_reuseFailAlloc_5086_, 5, v_cache_5065_);
lean_ctor_set(v_reuseFailAlloc_5086_, 6, v_messages_5066_);
lean_ctor_set(v_reuseFailAlloc_5086_, 7, v___x_5080_);
lean_ctor_set(v_reuseFailAlloc_5086_, 8, v_snapshotTasks_5067_);
v___x_5082_ = v_reuseFailAlloc_5086_;
goto v_reusejp_5081_;
}
v_reusejp_5081_:
{
lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; 
v___x_5083_ = lean_st_ref_put(v___y_5051_, v___x_5082_);
v___x_5084_ = lean_box(0);
v___x_5085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5085_, 0, v___x_5084_);
return v___x_5085_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg___boxed(lean_object* v_t_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_){
_start:
{
lean_object* v_res_5093_; 
v_res_5093_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v_t_5090_, v___y_5091_);
lean_dec(v___y_5091_);
return v_res_5093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0(lean_object* v_t_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_){
_start:
{
lean_object* v___x_5102_; 
v___x_5102_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v_t_5094_, v___y_5100_);
return v___x_5102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___boxed(lean_object* v_t_5103_, lean_object* v___y_5104_, lean_object* v___y_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_){
_start:
{
lean_object* v_res_5111_; 
v_res_5111_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0(v_t_5103_, v___y_5104_, v___y_5105_, v___y_5106_, v___y_5107_, v___y_5108_, v___y_5109_);
lean_dec(v___y_5109_);
lean_dec_ref(v___y_5108_);
lean_dec(v___y_5107_);
lean_dec_ref(v___y_5106_);
lean_dec(v___y_5105_);
lean_dec_ref(v___y_5104_);
return v_res_5111_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(lean_object* v_e_5112_, lean_object* v___y_5113_){
_start:
{
uint8_t v___x_5115_; 
v___x_5115_ = l_Lean_Expr_hasMVar(v_e_5112_);
if (v___x_5115_ == 0)
{
lean_object* v___x_5116_; 
v___x_5116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5116_, 0, v_e_5112_);
return v___x_5116_;
}
else
{
lean_object* v___x_5117_; lean_object* v_mctx_5118_; lean_object* v___x_5119_; lean_object* v_fst_5120_; lean_object* v_snd_5121_; lean_object* v___x_5122_; lean_object* v_cache_5123_; lean_object* v_zetaDeltaFVarIds_5124_; lean_object* v_postponed_5125_; lean_object* v_diag_5126_; lean_object* v___x_5128_; uint8_t v_isShared_5129_; uint8_t v_isSharedCheck_5135_; 
v___x_5117_ = lean_st_ref_get(v___y_5113_);
v_mctx_5118_ = lean_ctor_get(v___x_5117_, 0);
lean_inc_ref(v_mctx_5118_);
lean_dec(v___x_5117_);
v___x_5119_ = l_Lean_instantiateMVarsCore(v_mctx_5118_, v_e_5112_);
v_fst_5120_ = lean_ctor_get(v___x_5119_, 0);
lean_inc(v_fst_5120_);
v_snd_5121_ = lean_ctor_get(v___x_5119_, 1);
lean_inc(v_snd_5121_);
lean_dec_ref(v___x_5119_);
v___x_5122_ = lean_st_ref_take(v___y_5113_);
v_cache_5123_ = lean_ctor_get(v___x_5122_, 1);
v_zetaDeltaFVarIds_5124_ = lean_ctor_get(v___x_5122_, 2);
v_postponed_5125_ = lean_ctor_get(v___x_5122_, 3);
v_diag_5126_ = lean_ctor_get(v___x_5122_, 4);
v_isSharedCheck_5135_ = !lean_is_exclusive(v___x_5122_);
if (v_isSharedCheck_5135_ == 0)
{
lean_object* v_unused_5136_; 
v_unused_5136_ = lean_ctor_get(v___x_5122_, 0);
lean_dec(v_unused_5136_);
v___x_5128_ = v___x_5122_;
v_isShared_5129_ = v_isSharedCheck_5135_;
goto v_resetjp_5127_;
}
else
{
lean_inc(v_diag_5126_);
lean_inc(v_postponed_5125_);
lean_inc(v_zetaDeltaFVarIds_5124_);
lean_inc(v_cache_5123_);
lean_dec(v___x_5122_);
v___x_5128_ = lean_box(0);
v_isShared_5129_ = v_isSharedCheck_5135_;
goto v_resetjp_5127_;
}
v_resetjp_5127_:
{
lean_object* v___x_5131_; 
if (v_isShared_5129_ == 0)
{
lean_ctor_set(v___x_5128_, 0, v_snd_5121_);
v___x_5131_ = v___x_5128_;
goto v_reusejp_5130_;
}
else
{
lean_object* v_reuseFailAlloc_5134_; 
v_reuseFailAlloc_5134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5134_, 0, v_snd_5121_);
lean_ctor_set(v_reuseFailAlloc_5134_, 1, v_cache_5123_);
lean_ctor_set(v_reuseFailAlloc_5134_, 2, v_zetaDeltaFVarIds_5124_);
lean_ctor_set(v_reuseFailAlloc_5134_, 3, v_postponed_5125_);
lean_ctor_set(v_reuseFailAlloc_5134_, 4, v_diag_5126_);
v___x_5131_ = v_reuseFailAlloc_5134_;
goto v_reusejp_5130_;
}
v_reusejp_5130_:
{
lean_object* v___x_5132_; lean_object* v___x_5133_; 
v___x_5132_ = lean_st_ref_put(v___y_5113_, v___x_5131_);
v___x_5133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5133_, 0, v_fst_5120_);
return v___x_5133_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg___boxed(lean_object* v_e_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_){
_start:
{
lean_object* v_res_5140_; 
v_res_5140_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_e_5137_, v___y_5138_);
lean_dec(v___y_5138_);
return v_res_5140_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7(lean_object* v_e_5141_, lean_object* v___y_5142_, lean_object* v___y_5143_, lean_object* v___y_5144_, lean_object* v___y_5145_){
_start:
{
lean_object* v___x_5147_; 
v___x_5147_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_e_5141_, v___y_5143_);
return v___x_5147_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___boxed(lean_object* v_e_5148_, lean_object* v___y_5149_, lean_object* v___y_5150_, lean_object* v___y_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_){
_start:
{
lean_object* v_res_5154_; 
v_res_5154_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7(v_e_5148_, v___y_5149_, v___y_5150_, v___y_5151_, v___y_5152_);
lean_dec(v___y_5152_);
lean_dec_ref(v___y_5151_);
lean_dec(v___y_5150_);
lean_dec_ref(v___y_5149_);
return v_res_5154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(lean_object* v_as_5155_, size_t v_i_5156_, size_t v_stop_5157_, lean_object* v_b_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_){
_start:
{
uint8_t v___x_5166_; 
v___x_5166_ = lean_usize_dec_eq(v_i_5156_, v_stop_5157_);
if (v___x_5166_ == 0)
{
lean_object* v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; 
v___x_5167_ = lean_array_uget_borrowed(v_as_5155_, v_i_5156_);
lean_inc(v___x_5167_);
v___x_5168_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_5168_, 0, v___x_5167_);
v___x_5169_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v___x_5168_, v___y_5164_);
if (lean_obj_tag(v___x_5169_) == 0)
{
lean_object* v_a_5170_; size_t v___x_5171_; size_t v___x_5172_; 
v_a_5170_ = lean_ctor_get(v___x_5169_, 0);
lean_inc(v_a_5170_);
lean_dec_ref_known(v___x_5169_, 1);
v___x_5171_ = ((size_t)1ULL);
v___x_5172_ = lean_usize_add(v_i_5156_, v___x_5171_);
v_i_5156_ = v___x_5172_;
v_b_5158_ = v_a_5170_;
goto _start;
}
else
{
return v___x_5169_;
}
}
else
{
lean_object* v___x_5174_; 
v___x_5174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5174_, 0, v_b_5158_);
return v___x_5174_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4___boxed(lean_object* v_as_5175_, lean_object* v_i_5176_, lean_object* v_stop_5177_, lean_object* v_b_5178_, lean_object* v___y_5179_, lean_object* v___y_5180_, lean_object* v___y_5181_, lean_object* v___y_5182_, lean_object* v___y_5183_, lean_object* v___y_5184_, lean_object* v___y_5185_){
_start:
{
size_t v_i_boxed_5186_; size_t v_stop_boxed_5187_; lean_object* v_res_5188_; 
v_i_boxed_5186_ = lean_unbox_usize(v_i_5176_);
lean_dec(v_i_5176_);
v_stop_boxed_5187_ = lean_unbox_usize(v_stop_5177_);
lean_dec(v_stop_5177_);
v_res_5188_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v_as_5175_, v_i_boxed_5186_, v_stop_boxed_5187_, v_b_5178_, v___y_5179_, v___y_5180_, v___y_5181_, v___y_5182_, v___y_5183_, v___y_5184_);
lean_dec(v___y_5184_);
lean_dec_ref(v___y_5183_);
lean_dec(v___y_5182_);
lean_dec_ref(v___y_5181_);
lean_dec(v___y_5180_);
lean_dec_ref(v___y_5179_);
lean_dec_ref(v_as_5175_);
return v_res_5188_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; 
v___x_5189_ = lean_unsigned_to_nat(32u);
v___x_5190_ = lean_mk_empty_array_with_capacity(v___x_5189_);
v___x_5191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5191_, 0, v___x_5190_);
return v___x_5191_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; lean_object* v___x_5197_; 
v___x_5192_ = ((size_t)5ULL);
v___x_5193_ = lean_unsigned_to_nat(0u);
v___x_5194_ = lean_unsigned_to_nat(32u);
v___x_5195_ = lean_mk_empty_array_with_capacity(v___x_5194_);
v___x_5196_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0);
v___x_5197_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5197_, 0, v___x_5196_);
lean_ctor_set(v___x_5197_, 1, v___x_5195_);
lean_ctor_set(v___x_5197_, 2, v___x_5193_);
lean_ctor_set(v___x_5197_, 3, v___x_5193_);
lean_ctor_set_usize(v___x_5197_, 4, v___x_5192_);
return v___x_5197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(lean_object* v___y_5198_){
_start:
{
lean_object* v___x_5200_; lean_object* v_infoState_5201_; lean_object* v_trees_5202_; lean_object* v___x_5203_; lean_object* v_infoState_5204_; lean_object* v_env_5205_; lean_object* v_nextMacroScope_5206_; lean_object* v_ngen_5207_; lean_object* v_auxDeclNGen_5208_; lean_object* v_traceState_5209_; lean_object* v_cache_5210_; lean_object* v_messages_5211_; lean_object* v_snapshotTasks_5212_; lean_object* v___x_5214_; uint8_t v_isShared_5215_; uint8_t v_isSharedCheck_5233_; 
v___x_5200_ = lean_st_ref_get(v___y_5198_);
v_infoState_5201_ = lean_ctor_get(v___x_5200_, 7);
lean_inc_ref(v_infoState_5201_);
lean_dec(v___x_5200_);
v_trees_5202_ = lean_ctor_get(v_infoState_5201_, 2);
lean_inc_ref(v_trees_5202_);
lean_dec_ref(v_infoState_5201_);
v___x_5203_ = lean_st_ref_take(v___y_5198_);
v_infoState_5204_ = lean_ctor_get(v___x_5203_, 7);
v_env_5205_ = lean_ctor_get(v___x_5203_, 0);
v_nextMacroScope_5206_ = lean_ctor_get(v___x_5203_, 1);
v_ngen_5207_ = lean_ctor_get(v___x_5203_, 2);
v_auxDeclNGen_5208_ = lean_ctor_get(v___x_5203_, 3);
v_traceState_5209_ = lean_ctor_get(v___x_5203_, 4);
v_cache_5210_ = lean_ctor_get(v___x_5203_, 5);
v_messages_5211_ = lean_ctor_get(v___x_5203_, 6);
v_snapshotTasks_5212_ = lean_ctor_get(v___x_5203_, 8);
v_isSharedCheck_5233_ = !lean_is_exclusive(v___x_5203_);
if (v_isSharedCheck_5233_ == 0)
{
v___x_5214_ = v___x_5203_;
v_isShared_5215_ = v_isSharedCheck_5233_;
goto v_resetjp_5213_;
}
else
{
lean_inc(v_snapshotTasks_5212_);
lean_inc(v_infoState_5204_);
lean_inc(v_messages_5211_);
lean_inc(v_cache_5210_);
lean_inc(v_traceState_5209_);
lean_inc(v_auxDeclNGen_5208_);
lean_inc(v_ngen_5207_);
lean_inc(v_nextMacroScope_5206_);
lean_inc(v_env_5205_);
lean_dec(v___x_5203_);
v___x_5214_ = lean_box(0);
v_isShared_5215_ = v_isSharedCheck_5233_;
goto v_resetjp_5213_;
}
v_resetjp_5213_:
{
uint8_t v_enabled_5216_; lean_object* v_assignment_5217_; lean_object* v_lazyAssignment_5218_; lean_object* v___x_5220_; uint8_t v_isShared_5221_; uint8_t v_isSharedCheck_5231_; 
v_enabled_5216_ = lean_ctor_get_uint8(v_infoState_5204_, sizeof(void*)*3);
v_assignment_5217_ = lean_ctor_get(v_infoState_5204_, 0);
v_lazyAssignment_5218_ = lean_ctor_get(v_infoState_5204_, 1);
v_isSharedCheck_5231_ = !lean_is_exclusive(v_infoState_5204_);
if (v_isSharedCheck_5231_ == 0)
{
lean_object* v_unused_5232_; 
v_unused_5232_ = lean_ctor_get(v_infoState_5204_, 2);
lean_dec(v_unused_5232_);
v___x_5220_ = v_infoState_5204_;
v_isShared_5221_ = v_isSharedCheck_5231_;
goto v_resetjp_5219_;
}
else
{
lean_inc(v_lazyAssignment_5218_);
lean_inc(v_assignment_5217_);
lean_dec(v_infoState_5204_);
v___x_5220_ = lean_box(0);
v_isShared_5221_ = v_isSharedCheck_5231_;
goto v_resetjp_5219_;
}
v_resetjp_5219_:
{
lean_object* v___x_5222_; lean_object* v___x_5224_; 
v___x_5222_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1);
if (v_isShared_5221_ == 0)
{
lean_ctor_set(v___x_5220_, 2, v___x_5222_);
v___x_5224_ = v___x_5220_;
goto v_reusejp_5223_;
}
else
{
lean_object* v_reuseFailAlloc_5230_; 
v_reuseFailAlloc_5230_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5230_, 0, v_assignment_5217_);
lean_ctor_set(v_reuseFailAlloc_5230_, 1, v_lazyAssignment_5218_);
lean_ctor_set(v_reuseFailAlloc_5230_, 2, v___x_5222_);
lean_ctor_set_uint8(v_reuseFailAlloc_5230_, sizeof(void*)*3, v_enabled_5216_);
v___x_5224_ = v_reuseFailAlloc_5230_;
goto v_reusejp_5223_;
}
v_reusejp_5223_:
{
lean_object* v___x_5226_; 
if (v_isShared_5215_ == 0)
{
lean_ctor_set(v___x_5214_, 7, v___x_5224_);
v___x_5226_ = v___x_5214_;
goto v_reusejp_5225_;
}
else
{
lean_object* v_reuseFailAlloc_5229_; 
v_reuseFailAlloc_5229_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5229_, 0, v_env_5205_);
lean_ctor_set(v_reuseFailAlloc_5229_, 1, v_nextMacroScope_5206_);
lean_ctor_set(v_reuseFailAlloc_5229_, 2, v_ngen_5207_);
lean_ctor_set(v_reuseFailAlloc_5229_, 3, v_auxDeclNGen_5208_);
lean_ctor_set(v_reuseFailAlloc_5229_, 4, v_traceState_5209_);
lean_ctor_set(v_reuseFailAlloc_5229_, 5, v_cache_5210_);
lean_ctor_set(v_reuseFailAlloc_5229_, 6, v_messages_5211_);
lean_ctor_set(v_reuseFailAlloc_5229_, 7, v___x_5224_);
lean_ctor_set(v_reuseFailAlloc_5229_, 8, v_snapshotTasks_5212_);
v___x_5226_ = v_reuseFailAlloc_5229_;
goto v_reusejp_5225_;
}
v_reusejp_5225_:
{
lean_object* v___x_5227_; lean_object* v___x_5228_; 
v___x_5227_ = lean_st_ref_put(v___y_5198_, v___x_5226_);
v___x_5228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5228_, 0, v_trees_5202_);
return v___x_5228_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___boxed(lean_object* v___y_5234_, lean_object* v___y_5235_){
_start:
{
lean_object* v_res_5236_; 
v_res_5236_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_5234_);
lean_dec(v___y_5234_);
return v_res_5236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(lean_object* v___y_5237_, lean_object* v_mkInfoTree_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_, lean_object* v_a_5246_, lean_object* v_a_x3f_5247_){
_start:
{
lean_object* v___x_5249_; lean_object* v_infoState_5250_; lean_object* v_trees_5251_; lean_object* v___x_5252_; 
v___x_5249_ = lean_st_ref_get(v___y_5237_);
v_infoState_5250_ = lean_ctor_get(v___x_5249_, 7);
lean_inc_ref(v_infoState_5250_);
lean_dec(v___x_5249_);
v_trees_5251_ = lean_ctor_get(v_infoState_5250_, 2);
lean_inc_ref(v_trees_5251_);
lean_dec_ref(v_infoState_5250_);
lean_inc(v___y_5237_);
lean_inc_ref(v___y_5245_);
lean_inc(v___y_5244_);
lean_inc_ref(v___y_5243_);
lean_inc(v___y_5242_);
lean_inc_ref(v___y_5241_);
lean_inc(v___y_5240_);
lean_inc_ref(v___y_5239_);
v___x_5252_ = lean_apply_10(v_mkInfoTree_5238_, v_trees_5251_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_, v___y_5244_, v___y_5245_, v___y_5237_, lean_box(0));
if (lean_obj_tag(v___x_5252_) == 0)
{
lean_object* v_a_5253_; lean_object* v___x_5255_; uint8_t v_isShared_5256_; uint8_t v_isSharedCheck_5291_; 
v_a_5253_ = lean_ctor_get(v___x_5252_, 0);
v_isSharedCheck_5291_ = !lean_is_exclusive(v___x_5252_);
if (v_isSharedCheck_5291_ == 0)
{
v___x_5255_ = v___x_5252_;
v_isShared_5256_ = v_isSharedCheck_5291_;
goto v_resetjp_5254_;
}
else
{
lean_inc(v_a_5253_);
lean_dec(v___x_5252_);
v___x_5255_ = lean_box(0);
v_isShared_5256_ = v_isSharedCheck_5291_;
goto v_resetjp_5254_;
}
v_resetjp_5254_:
{
lean_object* v___x_5257_; lean_object* v_infoState_5258_; lean_object* v_env_5259_; lean_object* v_nextMacroScope_5260_; lean_object* v_ngen_5261_; lean_object* v_auxDeclNGen_5262_; lean_object* v_traceState_5263_; lean_object* v_cache_5264_; lean_object* v_messages_5265_; lean_object* v_snapshotTasks_5266_; lean_object* v___x_5268_; uint8_t v_isShared_5269_; uint8_t v_isSharedCheck_5290_; 
v___x_5257_ = lean_st_ref_take(v___y_5237_);
v_infoState_5258_ = lean_ctor_get(v___x_5257_, 7);
v_env_5259_ = lean_ctor_get(v___x_5257_, 0);
v_nextMacroScope_5260_ = lean_ctor_get(v___x_5257_, 1);
v_ngen_5261_ = lean_ctor_get(v___x_5257_, 2);
v_auxDeclNGen_5262_ = lean_ctor_get(v___x_5257_, 3);
v_traceState_5263_ = lean_ctor_get(v___x_5257_, 4);
v_cache_5264_ = lean_ctor_get(v___x_5257_, 5);
v_messages_5265_ = lean_ctor_get(v___x_5257_, 6);
v_snapshotTasks_5266_ = lean_ctor_get(v___x_5257_, 8);
v_isSharedCheck_5290_ = !lean_is_exclusive(v___x_5257_);
if (v_isSharedCheck_5290_ == 0)
{
v___x_5268_ = v___x_5257_;
v_isShared_5269_ = v_isSharedCheck_5290_;
goto v_resetjp_5267_;
}
else
{
lean_inc(v_snapshotTasks_5266_);
lean_inc(v_infoState_5258_);
lean_inc(v_messages_5265_);
lean_inc(v_cache_5264_);
lean_inc(v_traceState_5263_);
lean_inc(v_auxDeclNGen_5262_);
lean_inc(v_ngen_5261_);
lean_inc(v_nextMacroScope_5260_);
lean_inc(v_env_5259_);
lean_dec(v___x_5257_);
v___x_5268_ = lean_box(0);
v_isShared_5269_ = v_isSharedCheck_5290_;
goto v_resetjp_5267_;
}
v_resetjp_5267_:
{
uint8_t v_enabled_5270_; lean_object* v_assignment_5271_; lean_object* v_lazyAssignment_5272_; lean_object* v___x_5274_; uint8_t v_isShared_5275_; uint8_t v_isSharedCheck_5288_; 
v_enabled_5270_ = lean_ctor_get_uint8(v_infoState_5258_, sizeof(void*)*3);
v_assignment_5271_ = lean_ctor_get(v_infoState_5258_, 0);
v_lazyAssignment_5272_ = lean_ctor_get(v_infoState_5258_, 1);
v_isSharedCheck_5288_ = !lean_is_exclusive(v_infoState_5258_);
if (v_isSharedCheck_5288_ == 0)
{
lean_object* v_unused_5289_; 
v_unused_5289_ = lean_ctor_get(v_infoState_5258_, 2);
lean_dec(v_unused_5289_);
v___x_5274_ = v_infoState_5258_;
v_isShared_5275_ = v_isSharedCheck_5288_;
goto v_resetjp_5273_;
}
else
{
lean_inc(v_lazyAssignment_5272_);
lean_inc(v_assignment_5271_);
lean_dec(v_infoState_5258_);
v___x_5274_ = lean_box(0);
v_isShared_5275_ = v_isSharedCheck_5288_;
goto v_resetjp_5273_;
}
v_resetjp_5273_:
{
lean_object* v___x_5276_; lean_object* v___x_5278_; 
v___x_5276_ = l_Lean_PersistentArray_push___redArg(v_a_5246_, v_a_5253_);
if (v_isShared_5275_ == 0)
{
lean_ctor_set(v___x_5274_, 2, v___x_5276_);
v___x_5278_ = v___x_5274_;
goto v_reusejp_5277_;
}
else
{
lean_object* v_reuseFailAlloc_5287_; 
v_reuseFailAlloc_5287_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5287_, 0, v_assignment_5271_);
lean_ctor_set(v_reuseFailAlloc_5287_, 1, v_lazyAssignment_5272_);
lean_ctor_set(v_reuseFailAlloc_5287_, 2, v___x_5276_);
lean_ctor_set_uint8(v_reuseFailAlloc_5287_, sizeof(void*)*3, v_enabled_5270_);
v___x_5278_ = v_reuseFailAlloc_5287_;
goto v_reusejp_5277_;
}
v_reusejp_5277_:
{
lean_object* v___x_5280_; 
if (v_isShared_5269_ == 0)
{
lean_ctor_set(v___x_5268_, 7, v___x_5278_);
v___x_5280_ = v___x_5268_;
goto v_reusejp_5279_;
}
else
{
lean_object* v_reuseFailAlloc_5286_; 
v_reuseFailAlloc_5286_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5286_, 0, v_env_5259_);
lean_ctor_set(v_reuseFailAlloc_5286_, 1, v_nextMacroScope_5260_);
lean_ctor_set(v_reuseFailAlloc_5286_, 2, v_ngen_5261_);
lean_ctor_set(v_reuseFailAlloc_5286_, 3, v_auxDeclNGen_5262_);
lean_ctor_set(v_reuseFailAlloc_5286_, 4, v_traceState_5263_);
lean_ctor_set(v_reuseFailAlloc_5286_, 5, v_cache_5264_);
lean_ctor_set(v_reuseFailAlloc_5286_, 6, v_messages_5265_);
lean_ctor_set(v_reuseFailAlloc_5286_, 7, v___x_5278_);
lean_ctor_set(v_reuseFailAlloc_5286_, 8, v_snapshotTasks_5266_);
v___x_5280_ = v_reuseFailAlloc_5286_;
goto v_reusejp_5279_;
}
v_reusejp_5279_:
{
lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5284_; 
v___x_5281_ = lean_st_ref_put(v___y_5237_, v___x_5280_);
v___x_5282_ = lean_box(0);
if (v_isShared_5256_ == 0)
{
lean_ctor_set(v___x_5255_, 0, v___x_5282_);
v___x_5284_ = v___x_5255_;
goto v_reusejp_5283_;
}
else
{
lean_object* v_reuseFailAlloc_5285_; 
v_reuseFailAlloc_5285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5285_, 0, v___x_5282_);
v___x_5284_ = v_reuseFailAlloc_5285_;
goto v_reusejp_5283_;
}
v_reusejp_5283_:
{
return v___x_5284_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5292_; lean_object* v___x_5294_; uint8_t v_isShared_5295_; uint8_t v_isSharedCheck_5299_; 
lean_dec_ref(v_a_5246_);
v_a_5292_ = lean_ctor_get(v___x_5252_, 0);
v_isSharedCheck_5299_ = !lean_is_exclusive(v___x_5252_);
if (v_isSharedCheck_5299_ == 0)
{
v___x_5294_ = v___x_5252_;
v_isShared_5295_ = v_isSharedCheck_5299_;
goto v_resetjp_5293_;
}
else
{
lean_inc(v_a_5292_);
lean_dec(v___x_5252_);
v___x_5294_ = lean_box(0);
v_isShared_5295_ = v_isSharedCheck_5299_;
goto v_resetjp_5293_;
}
v_resetjp_5293_:
{
lean_object* v___x_5297_; 
if (v_isShared_5295_ == 0)
{
v___x_5297_ = v___x_5294_;
goto v_reusejp_5296_;
}
else
{
lean_object* v_reuseFailAlloc_5298_; 
v_reuseFailAlloc_5298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5298_, 0, v_a_5292_);
v___x_5297_ = v_reuseFailAlloc_5298_;
goto v_reusejp_5296_;
}
v_reusejp_5296_:
{
return v___x_5297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0___boxed(lean_object* v___y_5300_, lean_object* v_mkInfoTree_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_, lean_object* v_a_5309_, lean_object* v_a_x3f_5310_, lean_object* v___y_5311_){
_start:
{
lean_object* v_res_5312_; 
v_res_5312_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5300_, v_mkInfoTree_5301_, v___y_5302_, v___y_5303_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_, v___y_5308_, v_a_5309_, v_a_x3f_5310_);
lean_dec(v_a_x3f_5310_);
lean_dec_ref(v___y_5308_);
lean_dec(v___y_5307_);
lean_dec_ref(v___y_5306_);
lean_dec(v___y_5305_);
lean_dec_ref(v___y_5304_);
lean_dec(v___y_5303_);
lean_dec_ref(v___y_5302_);
lean_dec(v___y_5300_);
return v_res_5312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(lean_object* v_x_5313_, lean_object* v_mkInfoTree_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_){
_start:
{
lean_object* v___x_5324_; lean_object* v_infoState_5325_; uint8_t v_enabled_5326_; 
v___x_5324_ = lean_st_ref_get(v___y_5322_);
v_infoState_5325_ = lean_ctor_get(v___x_5324_, 7);
lean_inc_ref(v_infoState_5325_);
lean_dec(v___x_5324_);
v_enabled_5326_ = lean_ctor_get_uint8(v_infoState_5325_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5325_);
if (v_enabled_5326_ == 0)
{
lean_object* v___x_5327_; 
lean_dec_ref(v_mkInfoTree_5314_);
lean_inc(v___y_5322_);
lean_inc_ref(v___y_5321_);
lean_inc(v___y_5320_);
lean_inc_ref(v___y_5319_);
lean_inc(v___y_5318_);
lean_inc_ref(v___y_5317_);
lean_inc(v___y_5316_);
lean_inc_ref(v___y_5315_);
v___x_5327_ = lean_apply_9(v_x_5313_, v___y_5315_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_, lean_box(0));
return v___x_5327_;
}
else
{
lean_object* v___x_5328_; lean_object* v_a_5329_; lean_object* v_r_5330_; 
v___x_5328_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_5322_);
v_a_5329_ = lean_ctor_get(v___x_5328_, 0);
lean_inc(v_a_5329_);
lean_dec_ref(v___x_5328_);
lean_inc(v___y_5322_);
lean_inc_ref(v___y_5321_);
lean_inc(v___y_5320_);
lean_inc_ref(v___y_5319_);
lean_inc(v___y_5318_);
lean_inc_ref(v___y_5317_);
lean_inc(v___y_5316_);
lean_inc_ref(v___y_5315_);
v_r_5330_ = lean_apply_9(v_x_5313_, v___y_5315_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_, lean_box(0));
if (lean_obj_tag(v_r_5330_) == 0)
{
lean_object* v_a_5331_; lean_object* v___x_5333_; uint8_t v_isShared_5334_; uint8_t v_isSharedCheck_5355_; 
v_a_5331_ = lean_ctor_get(v_r_5330_, 0);
v_isSharedCheck_5355_ = !lean_is_exclusive(v_r_5330_);
if (v_isSharedCheck_5355_ == 0)
{
v___x_5333_ = v_r_5330_;
v_isShared_5334_ = v_isSharedCheck_5355_;
goto v_resetjp_5332_;
}
else
{
lean_inc(v_a_5331_);
lean_dec(v_r_5330_);
v___x_5333_ = lean_box(0);
v_isShared_5334_ = v_isSharedCheck_5355_;
goto v_resetjp_5332_;
}
v_resetjp_5332_:
{
lean_object* v___x_5336_; 
lean_inc(v_a_5331_);
if (v_isShared_5334_ == 0)
{
lean_ctor_set_tag(v___x_5333_, 1);
v___x_5336_ = v___x_5333_;
goto v_reusejp_5335_;
}
else
{
lean_object* v_reuseFailAlloc_5354_; 
v_reuseFailAlloc_5354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5354_, 0, v_a_5331_);
v___x_5336_ = v_reuseFailAlloc_5354_;
goto v_reusejp_5335_;
}
v_reusejp_5335_:
{
lean_object* v___x_5337_; 
v___x_5337_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5322_, v_mkInfoTree_5314_, v___y_5315_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v_a_5329_, v___x_5336_);
lean_dec_ref(v___x_5336_);
if (lean_obj_tag(v___x_5337_) == 0)
{
lean_object* v___x_5339_; uint8_t v_isShared_5340_; uint8_t v_isSharedCheck_5344_; 
v_isSharedCheck_5344_ = !lean_is_exclusive(v___x_5337_);
if (v_isSharedCheck_5344_ == 0)
{
lean_object* v_unused_5345_; 
v_unused_5345_ = lean_ctor_get(v___x_5337_, 0);
lean_dec(v_unused_5345_);
v___x_5339_ = v___x_5337_;
v_isShared_5340_ = v_isSharedCheck_5344_;
goto v_resetjp_5338_;
}
else
{
lean_dec(v___x_5337_);
v___x_5339_ = lean_box(0);
v_isShared_5340_ = v_isSharedCheck_5344_;
goto v_resetjp_5338_;
}
v_resetjp_5338_:
{
lean_object* v___x_5342_; 
if (v_isShared_5340_ == 0)
{
lean_ctor_set(v___x_5339_, 0, v_a_5331_);
v___x_5342_ = v___x_5339_;
goto v_reusejp_5341_;
}
else
{
lean_object* v_reuseFailAlloc_5343_; 
v_reuseFailAlloc_5343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5343_, 0, v_a_5331_);
v___x_5342_ = v_reuseFailAlloc_5343_;
goto v_reusejp_5341_;
}
v_reusejp_5341_:
{
return v___x_5342_;
}
}
}
else
{
lean_object* v_a_5346_; lean_object* v___x_5348_; uint8_t v_isShared_5349_; uint8_t v_isSharedCheck_5353_; 
lean_dec(v_a_5331_);
v_a_5346_ = lean_ctor_get(v___x_5337_, 0);
v_isSharedCheck_5353_ = !lean_is_exclusive(v___x_5337_);
if (v_isSharedCheck_5353_ == 0)
{
v___x_5348_ = v___x_5337_;
v_isShared_5349_ = v_isSharedCheck_5353_;
goto v_resetjp_5347_;
}
else
{
lean_inc(v_a_5346_);
lean_dec(v___x_5337_);
v___x_5348_ = lean_box(0);
v_isShared_5349_ = v_isSharedCheck_5353_;
goto v_resetjp_5347_;
}
v_resetjp_5347_:
{
lean_object* v___x_5351_; 
if (v_isShared_5349_ == 0)
{
v___x_5351_ = v___x_5348_;
goto v_reusejp_5350_;
}
else
{
lean_object* v_reuseFailAlloc_5352_; 
v_reuseFailAlloc_5352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5352_, 0, v_a_5346_);
v___x_5351_ = v_reuseFailAlloc_5352_;
goto v_reusejp_5350_;
}
v_reusejp_5350_:
{
return v___x_5351_;
}
}
}
}
}
}
else
{
lean_object* v_a_5356_; lean_object* v___x_5357_; lean_object* v___x_5358_; 
v_a_5356_ = lean_ctor_get(v_r_5330_, 0);
lean_inc(v_a_5356_);
lean_dec_ref_known(v_r_5330_, 1);
v___x_5357_ = lean_box(0);
v___x_5358_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5322_, v_mkInfoTree_5314_, v___y_5315_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v_a_5329_, v___x_5357_);
if (lean_obj_tag(v___x_5358_) == 0)
{
lean_object* v___x_5360_; uint8_t v_isShared_5361_; uint8_t v_isSharedCheck_5365_; 
v_isSharedCheck_5365_ = !lean_is_exclusive(v___x_5358_);
if (v_isSharedCheck_5365_ == 0)
{
lean_object* v_unused_5366_; 
v_unused_5366_ = lean_ctor_get(v___x_5358_, 0);
lean_dec(v_unused_5366_);
v___x_5360_ = v___x_5358_;
v_isShared_5361_ = v_isSharedCheck_5365_;
goto v_resetjp_5359_;
}
else
{
lean_dec(v___x_5358_);
v___x_5360_ = lean_box(0);
v_isShared_5361_ = v_isSharedCheck_5365_;
goto v_resetjp_5359_;
}
v_resetjp_5359_:
{
lean_object* v___x_5363_; 
if (v_isShared_5361_ == 0)
{
lean_ctor_set_tag(v___x_5360_, 1);
lean_ctor_set(v___x_5360_, 0, v_a_5356_);
v___x_5363_ = v___x_5360_;
goto v_reusejp_5362_;
}
else
{
lean_object* v_reuseFailAlloc_5364_; 
v_reuseFailAlloc_5364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5364_, 0, v_a_5356_);
v___x_5363_ = v_reuseFailAlloc_5364_;
goto v_reusejp_5362_;
}
v_reusejp_5362_:
{
return v___x_5363_;
}
}
}
else
{
lean_object* v_a_5367_; lean_object* v___x_5369_; uint8_t v_isShared_5370_; uint8_t v_isSharedCheck_5374_; 
lean_dec(v_a_5356_);
v_a_5367_ = lean_ctor_get(v___x_5358_, 0);
v_isSharedCheck_5374_ = !lean_is_exclusive(v___x_5358_);
if (v_isSharedCheck_5374_ == 0)
{
v___x_5369_ = v___x_5358_;
v_isShared_5370_ = v_isSharedCheck_5374_;
goto v_resetjp_5368_;
}
else
{
lean_inc(v_a_5367_);
lean_dec(v___x_5358_);
v___x_5369_ = lean_box(0);
v_isShared_5370_ = v_isSharedCheck_5374_;
goto v_resetjp_5368_;
}
v_resetjp_5368_:
{
lean_object* v___x_5372_; 
if (v_isShared_5370_ == 0)
{
v___x_5372_ = v___x_5369_;
goto v_reusejp_5371_;
}
else
{
lean_object* v_reuseFailAlloc_5373_; 
v_reuseFailAlloc_5373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5373_, 0, v_a_5367_);
v___x_5372_ = v_reuseFailAlloc_5373_;
goto v_reusejp_5371_;
}
v_reusejp_5371_:
{
return v___x_5372_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___boxed(lean_object* v_x_5375_, lean_object* v_mkInfoTree_5376_, lean_object* v___y_5377_, lean_object* v___y_5378_, lean_object* v___y_5379_, lean_object* v___y_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_){
_start:
{
lean_object* v_res_5386_; 
v_res_5386_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v_x_5375_, v_mkInfoTree_5376_, v___y_5377_, v___y_5378_, v___y_5379_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_);
lean_dec(v___y_5384_);
lean_dec_ref(v___y_5383_);
lean_dec(v___y_5382_);
lean_dec_ref(v___y_5381_);
lean_dec(v___y_5380_);
lean_dec_ref(v___y_5379_);
lean_dec(v___y_5378_);
lean_dec_ref(v___y_5377_);
return v_res_5386_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1(lean_object* v_a_5387_, lean_object* v_trees_5388_, lean_object* v___y_5389_, lean_object* v___y_5390_, lean_object* v___y_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_, lean_object* v___y_5394_, lean_object* v___y_5395_, lean_object* v___y_5396_){
_start:
{
lean_object* v___x_5398_; 
lean_inc(v___y_5396_);
lean_inc_ref(v___y_5395_);
lean_inc(v___y_5394_);
lean_inc_ref(v___y_5393_);
lean_inc(v___y_5392_);
lean_inc_ref(v___y_5391_);
lean_inc(v___y_5390_);
lean_inc_ref(v___y_5389_);
v___x_5398_ = lean_apply_9(v_a_5387_, v___y_5389_, v___y_5390_, v___y_5391_, v___y_5392_, v___y_5393_, v___y_5394_, v___y_5395_, v___y_5396_, lean_box(0));
if (lean_obj_tag(v___x_5398_) == 0)
{
lean_object* v_a_5399_; lean_object* v___x_5401_; uint8_t v_isShared_5402_; uint8_t v_isSharedCheck_5407_; 
v_a_5399_ = lean_ctor_get(v___x_5398_, 0);
v_isSharedCheck_5407_ = !lean_is_exclusive(v___x_5398_);
if (v_isSharedCheck_5407_ == 0)
{
v___x_5401_ = v___x_5398_;
v_isShared_5402_ = v_isSharedCheck_5407_;
goto v_resetjp_5400_;
}
else
{
lean_inc(v_a_5399_);
lean_dec(v___x_5398_);
v___x_5401_ = lean_box(0);
v_isShared_5402_ = v_isSharedCheck_5407_;
goto v_resetjp_5400_;
}
v_resetjp_5400_:
{
lean_object* v___x_5403_; lean_object* v___x_5405_; 
v___x_5403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5403_, 0, v_a_5399_);
lean_ctor_set(v___x_5403_, 1, v_trees_5388_);
if (v_isShared_5402_ == 0)
{
lean_ctor_set(v___x_5401_, 0, v___x_5403_);
v___x_5405_ = v___x_5401_;
goto v_reusejp_5404_;
}
else
{
lean_object* v_reuseFailAlloc_5406_; 
v_reuseFailAlloc_5406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5406_, 0, v___x_5403_);
v___x_5405_ = v_reuseFailAlloc_5406_;
goto v_reusejp_5404_;
}
v_reusejp_5404_:
{
return v___x_5405_;
}
}
}
else
{
lean_object* v_a_5408_; lean_object* v___x_5410_; uint8_t v_isShared_5411_; uint8_t v_isSharedCheck_5415_; 
lean_dec_ref(v_trees_5388_);
v_a_5408_ = lean_ctor_get(v___x_5398_, 0);
v_isSharedCheck_5415_ = !lean_is_exclusive(v___x_5398_);
if (v_isSharedCheck_5415_ == 0)
{
v___x_5410_ = v___x_5398_;
v_isShared_5411_ = v_isSharedCheck_5415_;
goto v_resetjp_5409_;
}
else
{
lean_inc(v_a_5408_);
lean_dec(v___x_5398_);
v___x_5410_ = lean_box(0);
v_isShared_5411_ = v_isSharedCheck_5415_;
goto v_resetjp_5409_;
}
v_resetjp_5409_:
{
lean_object* v___x_5413_; 
if (v_isShared_5411_ == 0)
{
v___x_5413_ = v___x_5410_;
goto v_reusejp_5412_;
}
else
{
lean_object* v_reuseFailAlloc_5414_; 
v_reuseFailAlloc_5414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5414_, 0, v_a_5408_);
v___x_5413_ = v_reuseFailAlloc_5414_;
goto v_reusejp_5412_;
}
v_reusejp_5412_:
{
return v___x_5413_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1___boxed(lean_object* v_a_5416_, lean_object* v_trees_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_, lean_object* v___y_5422_, lean_object* v___y_5423_, lean_object* v___y_5424_, lean_object* v___y_5425_, lean_object* v___y_5426_){
_start:
{
lean_object* v_res_5427_; 
v_res_5427_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1(v_a_5416_, v_trees_5417_, v___y_5418_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_, v___y_5425_);
lean_dec(v___y_5425_);
lean_dec_ref(v___y_5424_);
lean_dec(v___y_5423_);
lean_dec_ref(v___y_5422_);
lean_dec(v___y_5421_);
lean_dec_ref(v___y_5420_);
lean_dec(v___y_5419_);
lean_dec_ref(v___y_5418_);
return v_res_5427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2(lean_object* v___x_5428_, lean_object* v_ref_5429_, lean_object* v_tactic_5430_, lean_object* v___y_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_, lean_object* v___y_5434_, lean_object* v___y_5435_, lean_object* v___y_5436_, lean_object* v___y_5437_, lean_object* v___y_5438_){
_start:
{
lean_object* v___x_5440_; 
v___x_5440_ = l_Lean_Elab_Tactic_setGoals___redArg(v___x_5428_, v___y_5432_);
if (lean_obj_tag(v___x_5440_) == 0)
{
lean_object* v___x_5441_; 
lean_dec_ref_known(v___x_5440_, 1);
v___x_5441_ = l_Lean_Elab_WF_applyCleanWfTactic(v___y_5431_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_, v___y_5436_, v___y_5437_, v___y_5438_);
if (lean_obj_tag(v___x_5441_) == 0)
{
lean_object* v___x_5442_; 
lean_dec_ref_known(v___x_5441_, 1);
v___x_5442_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v_ref_5429_, v___y_5431_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_, v___y_5436_, v___y_5437_, v___y_5438_);
if (lean_obj_tag(v___x_5442_) == 0)
{
lean_object* v_a_5443_; lean_object* v___f_5444_; lean_object* v___x_5445_; lean_object* v___x_5446_; 
v_a_5443_ = lean_ctor_get(v___x_5442_, 0);
lean_inc(v_a_5443_);
lean_dec_ref_known(v___x_5442_, 1);
v___f_5444_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1___boxed), 11, 1);
lean_closure_set(v___f_5444_, 0, v_a_5443_);
v___x_5445_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_5445_, 0, v_tactic_5430_);
v___x_5446_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v___x_5445_, v___f_5444_, v___y_5431_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_, v___y_5436_, v___y_5437_, v___y_5438_);
return v___x_5446_;
}
else
{
lean_object* v_a_5447_; lean_object* v___x_5449_; uint8_t v_isShared_5450_; uint8_t v_isSharedCheck_5454_; 
lean_dec(v_tactic_5430_);
v_a_5447_ = lean_ctor_get(v___x_5442_, 0);
v_isSharedCheck_5454_ = !lean_is_exclusive(v___x_5442_);
if (v_isSharedCheck_5454_ == 0)
{
v___x_5449_ = v___x_5442_;
v_isShared_5450_ = v_isSharedCheck_5454_;
goto v_resetjp_5448_;
}
else
{
lean_inc(v_a_5447_);
lean_dec(v___x_5442_);
v___x_5449_ = lean_box(0);
v_isShared_5450_ = v_isSharedCheck_5454_;
goto v_resetjp_5448_;
}
v_resetjp_5448_:
{
lean_object* v___x_5452_; 
if (v_isShared_5450_ == 0)
{
v___x_5452_ = v___x_5449_;
goto v_reusejp_5451_;
}
else
{
lean_object* v_reuseFailAlloc_5453_; 
v_reuseFailAlloc_5453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5453_, 0, v_a_5447_);
v___x_5452_ = v_reuseFailAlloc_5453_;
goto v_reusejp_5451_;
}
v_reusejp_5451_:
{
return v___x_5452_;
}
}
}
}
else
{
lean_dec(v_tactic_5430_);
lean_dec(v_ref_5429_);
return v___x_5441_;
}
}
else
{
lean_dec(v_tactic_5430_);
lean_dec(v_ref_5429_);
return v___x_5440_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2___boxed(lean_object* v___x_5455_, lean_object* v_ref_5456_, lean_object* v_tactic_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_, lean_object* v___y_5463_, lean_object* v___y_5464_, lean_object* v___y_5465_, lean_object* v___y_5466_){
_start:
{
lean_object* v_res_5467_; 
v_res_5467_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2(v___x_5455_, v_ref_5456_, v_tactic_5457_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_, v___y_5463_, v___y_5464_, v___y_5465_);
lean_dec(v___y_5465_);
lean_dec_ref(v___y_5464_);
lean_dec(v___y_5463_);
lean_dec_ref(v___y_5462_);
lean_dec(v___y_5461_);
lean_dec_ref(v___y_5460_);
lean_dec(v___y_5459_);
lean_dec_ref(v___y_5458_);
return v_res_5467_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5468_; lean_object* v___x_5469_; 
v___x_5468_ = lean_box(1);
v___x_5469_ = l_Lean_MessageData_ofFormat(v___x_5468_);
return v___x_5469_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5473_; lean_object* v___x_5474_; 
v___x_5473_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__2));
v___x_5474_ = l_Lean_MessageData_ofFormat(v___x_5473_);
return v___x_5474_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3(lean_object* v_x_5475_, lean_object* v_x_5476_){
_start:
{
if (lean_obj_tag(v_x_5476_) == 0)
{
return v_x_5475_;
}
else
{
lean_object* v_head_5477_; lean_object* v_tail_5478_; lean_object* v___x_5480_; uint8_t v_isShared_5481_; uint8_t v_isSharedCheck_5500_; 
v_head_5477_ = lean_ctor_get(v_x_5476_, 0);
v_tail_5478_ = lean_ctor_get(v_x_5476_, 1);
v_isSharedCheck_5500_ = !lean_is_exclusive(v_x_5476_);
if (v_isSharedCheck_5500_ == 0)
{
v___x_5480_ = v_x_5476_;
v_isShared_5481_ = v_isSharedCheck_5500_;
goto v_resetjp_5479_;
}
else
{
lean_inc(v_tail_5478_);
lean_inc(v_head_5477_);
lean_dec(v_x_5476_);
v___x_5480_ = lean_box(0);
v_isShared_5481_ = v_isSharedCheck_5500_;
goto v_resetjp_5479_;
}
v_resetjp_5479_:
{
lean_object* v_before_5482_; lean_object* v___x_5484_; uint8_t v_isShared_5485_; uint8_t v_isSharedCheck_5498_; 
v_before_5482_ = lean_ctor_get(v_head_5477_, 0);
v_isSharedCheck_5498_ = !lean_is_exclusive(v_head_5477_);
if (v_isSharedCheck_5498_ == 0)
{
lean_object* v_unused_5499_; 
v_unused_5499_ = lean_ctor_get(v_head_5477_, 1);
lean_dec(v_unused_5499_);
v___x_5484_ = v_head_5477_;
v_isShared_5485_ = v_isSharedCheck_5498_;
goto v_resetjp_5483_;
}
else
{
lean_inc(v_before_5482_);
lean_dec(v_head_5477_);
v___x_5484_ = lean_box(0);
v_isShared_5485_ = v_isSharedCheck_5498_;
goto v_resetjp_5483_;
}
v_resetjp_5483_:
{
lean_object* v___x_5486_; lean_object* v___x_5488_; 
v___x_5486_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_5485_ == 0)
{
lean_ctor_set_tag(v___x_5484_, 7);
lean_ctor_set(v___x_5484_, 1, v___x_5486_);
lean_ctor_set(v___x_5484_, 0, v_x_5475_);
v___x_5488_ = v___x_5484_;
goto v_reusejp_5487_;
}
else
{
lean_object* v_reuseFailAlloc_5497_; 
v_reuseFailAlloc_5497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5497_, 0, v_x_5475_);
lean_ctor_set(v_reuseFailAlloc_5497_, 1, v___x_5486_);
v___x_5488_ = v_reuseFailAlloc_5497_;
goto v_reusejp_5487_;
}
v_reusejp_5487_:
{
lean_object* v___x_5489_; lean_object* v___x_5491_; 
v___x_5489_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3);
if (v_isShared_5481_ == 0)
{
lean_ctor_set_tag(v___x_5480_, 7);
lean_ctor_set(v___x_5480_, 1, v___x_5489_);
lean_ctor_set(v___x_5480_, 0, v___x_5488_);
v___x_5491_ = v___x_5480_;
goto v_reusejp_5490_;
}
else
{
lean_object* v_reuseFailAlloc_5496_; 
v_reuseFailAlloc_5496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5496_, 0, v___x_5488_);
lean_ctor_set(v_reuseFailAlloc_5496_, 1, v___x_5489_);
v___x_5491_ = v_reuseFailAlloc_5496_;
goto v_reusejp_5490_;
}
v_reusejp_5490_:
{
lean_object* v___x_5492_; lean_object* v___x_5493_; lean_object* v___x_5494_; 
v___x_5492_ = l_Lean_MessageData_ofSyntax(v_before_5482_);
v___x_5493_ = l_Lean_indentD(v___x_5492_);
v___x_5494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5494_, 0, v___x_5491_);
lean_ctor_set(v___x_5494_, 1, v___x_5493_);
v_x_5475_ = v___x_5494_;
v_x_5476_ = v_tail_5478_;
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
lean_object* v___x_5504_; lean_object* v___x_5505_; 
v___x_5504_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__1));
v___x_5505_ = l_Lean_MessageData_ofFormat(v___x_5504_);
return v___x_5505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(lean_object* v_msgData_5506_, lean_object* v_macroStack_5507_, lean_object* v___y_5508_){
_start:
{
lean_object* v_toCold_5510_; lean_object* v_options_5511_; lean_object* v___x_5512_; uint8_t v___x_5513_; 
v_toCold_5510_ = lean_ctor_get(v___y_5508_, 0);
v_options_5511_ = lean_ctor_get(v_toCold_5510_, 2);
v___x_5512_ = l_Lean_Elab_pp_macroStack;
v___x_5513_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v_options_5511_, v___x_5512_);
if (v___x_5513_ == 0)
{
lean_object* v___x_5514_; 
lean_dec(v_macroStack_5507_);
v___x_5514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5514_, 0, v_msgData_5506_);
return v___x_5514_;
}
else
{
if (lean_obj_tag(v_macroStack_5507_) == 0)
{
lean_object* v___x_5515_; 
v___x_5515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5515_, 0, v_msgData_5506_);
return v___x_5515_;
}
else
{
lean_object* v_head_5516_; lean_object* v_after_5517_; lean_object* v___x_5519_; uint8_t v_isShared_5520_; uint8_t v_isSharedCheck_5532_; 
v_head_5516_ = lean_ctor_get(v_macroStack_5507_, 0);
lean_inc(v_head_5516_);
v_after_5517_ = lean_ctor_get(v_head_5516_, 1);
v_isSharedCheck_5532_ = !lean_is_exclusive(v_head_5516_);
if (v_isSharedCheck_5532_ == 0)
{
lean_object* v_unused_5533_; 
v_unused_5533_ = lean_ctor_get(v_head_5516_, 0);
lean_dec(v_unused_5533_);
v___x_5519_ = v_head_5516_;
v_isShared_5520_ = v_isSharedCheck_5532_;
goto v_resetjp_5518_;
}
else
{
lean_inc(v_after_5517_);
lean_dec(v_head_5516_);
v___x_5519_ = lean_box(0);
v_isShared_5520_ = v_isSharedCheck_5532_;
goto v_resetjp_5518_;
}
v_resetjp_5518_:
{
lean_object* v___x_5521_; lean_object* v___x_5523_; 
v___x_5521_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_5520_ == 0)
{
lean_ctor_set_tag(v___x_5519_, 7);
lean_ctor_set(v___x_5519_, 1, v___x_5521_);
lean_ctor_set(v___x_5519_, 0, v_msgData_5506_);
v___x_5523_ = v___x_5519_;
goto v_reusejp_5522_;
}
else
{
lean_object* v_reuseFailAlloc_5531_; 
v_reuseFailAlloc_5531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5531_, 0, v_msgData_5506_);
lean_ctor_set(v_reuseFailAlloc_5531_, 1, v___x_5521_);
v___x_5523_ = v_reuseFailAlloc_5531_;
goto v_reusejp_5522_;
}
v_reusejp_5522_:
{
lean_object* v___x_5524_; lean_object* v___x_5525_; lean_object* v___x_5526_; lean_object* v___x_5527_; lean_object* v_msgData_5528_; lean_object* v___x_5529_; lean_object* v___x_5530_; 
v___x_5524_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2);
v___x_5525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5525_, 0, v___x_5523_);
lean_ctor_set(v___x_5525_, 1, v___x_5524_);
v___x_5526_ = l_Lean_MessageData_ofSyntax(v_after_5517_);
v___x_5527_ = l_Lean_indentD(v___x_5526_);
v_msgData_5528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_5528_, 0, v___x_5525_);
lean_ctor_set(v_msgData_5528_, 1, v___x_5527_);
v___x_5529_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3(v_msgData_5528_, v_macroStack_5507_);
v___x_5530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5530_, 0, v___x_5529_);
return v___x_5530_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_5534_, lean_object* v_macroStack_5535_, lean_object* v___y_5536_, lean_object* v___y_5537_){
_start:
{
lean_object* v_res_5538_; 
v_res_5538_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_msgData_5534_, v_macroStack_5535_, v___y_5536_);
lean_dec_ref(v___y_5536_);
return v_res_5538_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(lean_object* v_msg_5539_, lean_object* v___y_5540_, lean_object* v___y_5541_, lean_object* v___y_5542_, lean_object* v___y_5543_, lean_object* v___y_5544_, lean_object* v___y_5545_){
_start:
{
lean_object* v_ref_5547_; lean_object* v___x_5548_; lean_object* v_a_5549_; lean_object* v_macroStack_5550_; lean_object* v___x_5551_; lean_object* v___x_5552_; lean_object* v_a_5553_; lean_object* v___x_5555_; uint8_t v_isShared_5556_; uint8_t v_isSharedCheck_5561_; 
v_ref_5547_ = lean_ctor_get(v___y_5544_, 2);
v___x_5548_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_5539_, v___y_5542_, v___y_5543_, v___y_5544_, v___y_5545_);
v_a_5549_ = lean_ctor_get(v___x_5548_, 0);
lean_inc(v_a_5549_);
lean_dec_ref(v___x_5548_);
v_macroStack_5550_ = lean_ctor_get(v___y_5540_, 1);
v___x_5551_ = l_Lean_Elab_getBetterRef(v_ref_5547_, v_macroStack_5550_);
lean_inc(v_macroStack_5550_);
v___x_5552_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_a_5549_, v_macroStack_5550_, v___y_5544_);
v_a_5553_ = lean_ctor_get(v___x_5552_, 0);
v_isSharedCheck_5561_ = !lean_is_exclusive(v___x_5552_);
if (v_isSharedCheck_5561_ == 0)
{
v___x_5555_ = v___x_5552_;
v_isShared_5556_ = v_isSharedCheck_5561_;
goto v_resetjp_5554_;
}
else
{
lean_inc(v_a_5553_);
lean_dec(v___x_5552_);
v___x_5555_ = lean_box(0);
v_isShared_5556_ = v_isSharedCheck_5561_;
goto v_resetjp_5554_;
}
v_resetjp_5554_:
{
lean_object* v___x_5557_; lean_object* v___x_5559_; 
v___x_5557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5557_, 0, v___x_5551_);
lean_ctor_set(v___x_5557_, 1, v_a_5553_);
if (v_isShared_5556_ == 0)
{
lean_ctor_set_tag(v___x_5555_, 1);
lean_ctor_set(v___x_5555_, 0, v___x_5557_);
v___x_5559_ = v___x_5555_;
goto v_reusejp_5558_;
}
else
{
lean_object* v_reuseFailAlloc_5560_; 
v_reuseFailAlloc_5560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5560_, 0, v___x_5557_);
v___x_5559_ = v_reuseFailAlloc_5560_;
goto v_reusejp_5558_;
}
v_reusejp_5558_:
{
return v___x_5559_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg___boxed(lean_object* v_msg_5562_, lean_object* v___y_5563_, lean_object* v___y_5564_, lean_object* v___y_5565_, lean_object* v___y_5566_, lean_object* v___y_5567_, lean_object* v___y_5568_, lean_object* v___y_5569_){
_start:
{
lean_object* v_res_5570_; 
v_res_5570_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v_msg_5562_, v___y_5563_, v___y_5564_, v___y_5565_, v___y_5566_, v___y_5567_, v___y_5568_);
lean_dec(v___y_5568_);
lean_dec_ref(v___y_5567_);
lean_dec(v___y_5566_);
lean_dec_ref(v___y_5565_);
lean_dec(v___y_5564_);
lean_dec_ref(v___y_5563_);
return v_res_5570_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1(void){
_start:
{
lean_object* v___x_5572_; lean_object* v___x_5573_; 
v___x_5572_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__0));
v___x_5573_ = l_Lean_stringToMessageData(v___x_5572_);
return v___x_5573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(lean_object* v_as_5574_, size_t v_sz_5575_, size_t v_i_5576_, lean_object* v_b_5577_, lean_object* v___y_5578_, lean_object* v___y_5579_, lean_object* v___y_5580_, lean_object* v___y_5581_, lean_object* v___y_5582_, lean_object* v___y_5583_){
_start:
{
lean_object* v_a_5586_; uint8_t v___x_5590_; 
v___x_5590_ = lean_usize_dec_lt(v_i_5576_, v_sz_5575_);
if (v___x_5590_ == 0)
{
lean_object* v___x_5591_; 
v___x_5591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5591_, 0, v_b_5577_);
return v___x_5591_;
}
else
{
lean_object* v_a_5592_; lean_object* v___x_5593_; 
v_a_5592_ = lean_array_uget_borrowed(v_as_5574_, v_i_5576_);
lean_inc(v_a_5592_);
v___x_5593_ = l_Lean_MVarId_getType(v_a_5592_, v___y_5580_, v___y_5581_, v___y_5582_, v___y_5583_);
if (lean_obj_tag(v___x_5593_) == 0)
{
lean_object* v_a_5594_; lean_object* v___x_5595_; 
v_a_5594_ = lean_ctor_get(v___x_5593_, 0);
lean_inc(v_a_5594_);
lean_dec_ref_known(v___x_5593_, 1);
lean_inc(v_a_5592_);
v___x_5595_ = l_Lean_MVarId_getType(v_a_5592_, v___y_5580_, v___y_5581_, v___y_5582_, v___y_5583_);
if (lean_obj_tag(v___x_5595_) == 0)
{
lean_object* v_a_5596_; lean_object* v___x_5597_; lean_object* v___x_5598_; 
v_a_5596_ = lean_ctor_get(v___x_5595_, 0);
lean_inc(v_a_5596_);
lean_dec_ref_known(v___x_5595_, 1);
v___x_5597_ = lean_box(0);
v___x_5598_ = l_Lean_getRecAppSyntax_x3f(v_a_5596_);
lean_dec(v_a_5596_);
if (lean_obj_tag(v___x_5598_) == 1)
{
lean_object* v_val_5599_; lean_object* v___x_5600_; lean_object* v___x_5601_; 
v_val_5599_ = lean_ctor_get(v___x_5598_, 0);
lean_inc(v_val_5599_);
lean_dec_ref_known(v___x_5598_, 1);
v___x_5600_ = l_Lean_Expr_mdataExpr_x21(v_a_5594_);
lean_dec(v_a_5594_);
lean_inc(v_a_5592_);
v___x_5601_ = l_Lean_MVarId_setType___redArg(v_a_5592_, v___x_5600_, v___y_5581_);
if (lean_obj_tag(v___x_5601_) == 0)
{
lean_object* v_toCold_5602_; lean_object* v_currRecDepth_5603_; lean_object* v_ref_5604_; uint8_t v_diag_5605_; uint8_t v_suppressElabErrors_5606_; lean_object* v_ref_5607_; lean_object* v___x_5608_; lean_object* v___x_5609_; 
lean_dec_ref_known(v___x_5601_, 1);
v_toCold_5602_ = lean_ctor_get(v___y_5582_, 0);
v_currRecDepth_5603_ = lean_ctor_get(v___y_5582_, 1);
v_ref_5604_ = lean_ctor_get(v___y_5582_, 2);
v_diag_5605_ = lean_ctor_get_uint8(v___y_5582_, sizeof(void*)*3);
v_suppressElabErrors_5606_ = lean_ctor_get_uint8(v___y_5582_, sizeof(void*)*3 + 1);
v_ref_5607_ = l_Lean_replaceRef(v_val_5599_, v_ref_5604_);
lean_dec(v_val_5599_);
lean_inc(v_currRecDepth_5603_);
lean_inc_ref(v_toCold_5602_);
v___x_5608_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5608_, 0, v_toCold_5602_);
lean_ctor_set(v___x_5608_, 1, v_currRecDepth_5603_);
lean_ctor_set(v___x_5608_, 2, v_ref_5607_);
lean_ctor_set_uint8(v___x_5608_, sizeof(void*)*3, v_diag_5605_);
lean_ctor_set_uint8(v___x_5608_, sizeof(void*)*3 + 1, v_suppressElabErrors_5606_);
lean_inc(v_a_5592_);
v___x_5609_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(v_a_5592_, v___y_5578_, v___y_5579_, v___y_5580_, v___y_5581_, v___x_5608_, v___y_5583_);
lean_dec_ref_known(v___x_5608_, 3);
if (lean_obj_tag(v___x_5609_) == 0)
{
lean_dec_ref_known(v___x_5609_, 1);
v_a_5586_ = v___x_5597_;
goto v___jp_5585_;
}
else
{
return v___x_5609_;
}
}
else
{
lean_dec(v_val_5599_);
return v___x_5601_;
}
}
else
{
lean_object* v___x_5610_; lean_object* v___x_5611_; lean_object* v___x_5612_; lean_object* v___x_5613_; 
lean_dec(v___x_5598_);
v___x_5610_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1);
v___x_5611_ = l_Lean_indentExpr(v_a_5594_);
v___x_5612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5612_, 0, v___x_5610_);
lean_ctor_set(v___x_5612_, 1, v___x_5611_);
v___x_5613_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v___x_5612_, v___y_5578_, v___y_5579_, v___y_5580_, v___y_5581_, v___y_5582_, v___y_5583_);
if (lean_obj_tag(v___x_5613_) == 0)
{
lean_dec_ref_known(v___x_5613_, 1);
v_a_5586_ = v___x_5597_;
goto v___jp_5585_;
}
else
{
return v___x_5613_;
}
}
}
else
{
lean_object* v_a_5614_; lean_object* v___x_5616_; uint8_t v_isShared_5617_; uint8_t v_isSharedCheck_5621_; 
lean_dec(v_a_5594_);
v_a_5614_ = lean_ctor_get(v___x_5595_, 0);
v_isSharedCheck_5621_ = !lean_is_exclusive(v___x_5595_);
if (v_isSharedCheck_5621_ == 0)
{
v___x_5616_ = v___x_5595_;
v_isShared_5617_ = v_isSharedCheck_5621_;
goto v_resetjp_5615_;
}
else
{
lean_inc(v_a_5614_);
lean_dec(v___x_5595_);
v___x_5616_ = lean_box(0);
v_isShared_5617_ = v_isSharedCheck_5621_;
goto v_resetjp_5615_;
}
v_resetjp_5615_:
{
lean_object* v___x_5619_; 
if (v_isShared_5617_ == 0)
{
v___x_5619_ = v___x_5616_;
goto v_reusejp_5618_;
}
else
{
lean_object* v_reuseFailAlloc_5620_; 
v_reuseFailAlloc_5620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5620_, 0, v_a_5614_);
v___x_5619_ = v_reuseFailAlloc_5620_;
goto v_reusejp_5618_;
}
v_reusejp_5618_:
{
return v___x_5619_;
}
}
}
}
else
{
lean_object* v_a_5622_; lean_object* v___x_5624_; uint8_t v_isShared_5625_; uint8_t v_isSharedCheck_5629_; 
v_a_5622_ = lean_ctor_get(v___x_5593_, 0);
v_isSharedCheck_5629_ = !lean_is_exclusive(v___x_5593_);
if (v_isSharedCheck_5629_ == 0)
{
v___x_5624_ = v___x_5593_;
v_isShared_5625_ = v_isSharedCheck_5629_;
goto v_resetjp_5623_;
}
else
{
lean_inc(v_a_5622_);
lean_dec(v___x_5593_);
v___x_5624_ = lean_box(0);
v_isShared_5625_ = v_isSharedCheck_5629_;
goto v_resetjp_5623_;
}
v_resetjp_5623_:
{
lean_object* v___x_5627_; 
if (v_isShared_5625_ == 0)
{
v___x_5627_ = v___x_5624_;
goto v_reusejp_5626_;
}
else
{
lean_object* v_reuseFailAlloc_5628_; 
v_reuseFailAlloc_5628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5628_, 0, v_a_5622_);
v___x_5627_ = v_reuseFailAlloc_5628_;
goto v_reusejp_5626_;
}
v_reusejp_5626_:
{
return v___x_5627_;
}
}
}
}
v___jp_5585_:
{
size_t v___x_5587_; size_t v___x_5588_; 
v___x_5587_ = ((size_t)1ULL);
v___x_5588_ = lean_usize_add(v_i_5576_, v___x_5587_);
v_i_5576_ = v___x_5588_;
v_b_5577_ = v_a_5586_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___boxed(lean_object* v_as_5630_, lean_object* v_sz_5631_, lean_object* v_i_5632_, lean_object* v_b_5633_, lean_object* v___y_5634_, lean_object* v___y_5635_, lean_object* v___y_5636_, lean_object* v___y_5637_, lean_object* v___y_5638_, lean_object* v___y_5639_, lean_object* v___y_5640_){
_start:
{
size_t v_sz_boxed_5641_; size_t v_i_boxed_5642_; lean_object* v_res_5643_; 
v_sz_boxed_5641_ = lean_unbox_usize(v_sz_5631_);
lean_dec(v_sz_5631_);
v_i_boxed_5642_ = lean_unbox_usize(v_i_5632_);
lean_dec(v_i_5632_);
v_res_5643_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(v_as_5630_, v_sz_boxed_5641_, v_i_boxed_5642_, v_b_5633_, v___y_5634_, v___y_5635_, v___y_5636_, v___y_5637_, v___y_5638_, v___y_5639_);
lean_dec(v___y_5639_);
lean_dec_ref(v___y_5638_);
lean_dec(v___y_5637_);
lean_dec_ref(v___y_5636_);
lean_dec(v___y_5635_);
lean_dec_ref(v___y_5634_);
lean_dec_ref(v_as_5630_);
return v_res_5643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(lean_object* v_as_5644_, size_t v_i_5645_, size_t v_stop_5646_, lean_object* v_b_5647_, lean_object* v___y_5648_, lean_object* v___y_5649_, lean_object* v___y_5650_, lean_object* v___y_5651_){
_start:
{
uint8_t v___x_5653_; 
v___x_5653_ = lean_usize_dec_eq(v_i_5645_, v_stop_5646_);
if (v___x_5653_ == 0)
{
lean_object* v___x_5654_; lean_object* v___x_5655_; 
v___x_5654_ = lean_array_uget_borrowed(v_as_5644_, v_i_5645_);
lean_inc(v___x_5654_);
v___x_5655_ = l_Lean_MVarId_getType(v___x_5654_, v___y_5648_, v___y_5649_, v___y_5650_, v___y_5651_);
if (lean_obj_tag(v___x_5655_) == 0)
{
lean_object* v_a_5656_; lean_object* v___x_5657_; lean_object* v___x_5658_; 
v_a_5656_ = lean_ctor_get(v___x_5655_, 0);
lean_inc(v_a_5656_);
lean_dec_ref_known(v___x_5655_, 1);
v___x_5657_ = l_Lean_Expr_mdataExpr_x21(v_a_5656_);
lean_dec(v_a_5656_);
lean_inc(v___x_5654_);
v___x_5658_ = l_Lean_MVarId_setType___redArg(v___x_5654_, v___x_5657_, v___y_5649_);
if (lean_obj_tag(v___x_5658_) == 0)
{
lean_object* v_a_5659_; size_t v___x_5660_; size_t v___x_5661_; 
v_a_5659_ = lean_ctor_get(v___x_5658_, 0);
lean_inc(v_a_5659_);
lean_dec_ref_known(v___x_5658_, 1);
v___x_5660_ = ((size_t)1ULL);
v___x_5661_ = lean_usize_add(v_i_5645_, v___x_5660_);
v_i_5645_ = v___x_5661_;
v_b_5647_ = v_a_5659_;
goto _start;
}
else
{
return v___x_5658_;
}
}
else
{
lean_object* v_a_5663_; lean_object* v___x_5665_; uint8_t v_isShared_5666_; uint8_t v_isSharedCheck_5670_; 
v_a_5663_ = lean_ctor_get(v___x_5655_, 0);
v_isSharedCheck_5670_ = !lean_is_exclusive(v___x_5655_);
if (v_isSharedCheck_5670_ == 0)
{
v___x_5665_ = v___x_5655_;
v_isShared_5666_ = v_isSharedCheck_5670_;
goto v_resetjp_5664_;
}
else
{
lean_inc(v_a_5663_);
lean_dec(v___x_5655_);
v___x_5665_ = lean_box(0);
v_isShared_5666_ = v_isSharedCheck_5670_;
goto v_resetjp_5664_;
}
v_resetjp_5664_:
{
lean_object* v___x_5668_; 
if (v_isShared_5666_ == 0)
{
v___x_5668_ = v___x_5665_;
goto v_reusejp_5667_;
}
else
{
lean_object* v_reuseFailAlloc_5669_; 
v_reuseFailAlloc_5669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5669_, 0, v_a_5663_);
v___x_5668_ = v_reuseFailAlloc_5669_;
goto v_reusejp_5667_;
}
v_reusejp_5667_:
{
return v___x_5668_;
}
}
}
}
else
{
lean_object* v___x_5671_; 
v___x_5671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5671_, 0, v_b_5647_);
return v___x_5671_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg___boxed(lean_object* v_as_5672_, lean_object* v_i_5673_, lean_object* v_stop_5674_, lean_object* v_b_5675_, lean_object* v___y_5676_, lean_object* v___y_5677_, lean_object* v___y_5678_, lean_object* v___y_5679_, lean_object* v___y_5680_){
_start:
{
size_t v_i_boxed_5681_; size_t v_stop_boxed_5682_; lean_object* v_res_5683_; 
v_i_boxed_5681_ = lean_unbox_usize(v_i_5673_);
lean_dec(v_i_5673_);
v_stop_boxed_5682_ = lean_unbox_usize(v_stop_5674_);
lean_dec(v_stop_5674_);
v_res_5683_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v_as_5672_, v_i_boxed_5681_, v_stop_boxed_5682_, v_b_5675_, v___y_5676_, v___y_5677_, v___y_5678_, v___y_5679_);
lean_dec(v___y_5679_);
lean_dec_ref(v___y_5678_);
lean_dec(v___y_5677_);
lean_dec_ref(v___y_5676_);
lean_dec_ref(v_as_5672_);
return v_res_5683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3(lean_object* v___x_5684_, lean_object* v___x_5685_, lean_object* v___x_5686_, lean_object* v___y_5687_, lean_object* v___y_5688_, lean_object* v___y_5689_, lean_object* v___y_5690_, lean_object* v___y_5691_, lean_object* v___y_5692_){
_start:
{
if (lean_obj_tag(v___x_5684_) == 0)
{
lean_object* v___x_5694_; size_t v_sz_5695_; size_t v___x_5696_; lean_object* v___x_5697_; 
v___x_5694_ = lean_box(0);
v_sz_5695_ = lean_array_size(v___x_5685_);
v___x_5696_ = ((size_t)0ULL);
v___x_5697_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(v___x_5685_, v_sz_5695_, v___x_5696_, v___x_5694_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_, v___y_5692_);
lean_dec_ref(v___x_5685_);
if (lean_obj_tag(v___x_5697_) == 0)
{
lean_object* v___x_5699_; uint8_t v_isShared_5700_; uint8_t v_isSharedCheck_5704_; 
v_isSharedCheck_5704_ = !lean_is_exclusive(v___x_5697_);
if (v_isSharedCheck_5704_ == 0)
{
lean_object* v_unused_5705_; 
v_unused_5705_ = lean_ctor_get(v___x_5697_, 0);
lean_dec(v_unused_5705_);
v___x_5699_ = v___x_5697_;
v_isShared_5700_ = v_isSharedCheck_5704_;
goto v_resetjp_5698_;
}
else
{
lean_dec(v___x_5697_);
v___x_5699_ = lean_box(0);
v_isShared_5700_ = v_isSharedCheck_5704_;
goto v_resetjp_5698_;
}
v_resetjp_5698_:
{
lean_object* v___x_5702_; 
if (v_isShared_5700_ == 0)
{
lean_ctor_set(v___x_5699_, 0, v___x_5694_);
v___x_5702_ = v___x_5699_;
goto v_reusejp_5701_;
}
else
{
lean_object* v_reuseFailAlloc_5703_; 
v_reuseFailAlloc_5703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5703_, 0, v___x_5694_);
v___x_5702_ = v_reuseFailAlloc_5703_;
goto v_reusejp_5701_;
}
v_reusejp_5701_:
{
return v___x_5702_;
}
}
}
else
{
return v___x_5697_;
}
}
else
{
lean_object* v_val_5706_; lean_object* v___x_5708_; uint8_t v_isShared_5709_; uint8_t v_isSharedCheck_5773_; 
v_val_5706_ = lean_ctor_get(v___x_5684_, 0);
v_isSharedCheck_5773_ = !lean_is_exclusive(v___x_5684_);
if (v_isSharedCheck_5773_ == 0)
{
v___x_5708_ = v___x_5684_;
v_isShared_5709_ = v_isSharedCheck_5773_;
goto v_resetjp_5707_;
}
else
{
lean_inc(v_val_5706_);
lean_dec(v___x_5684_);
v___x_5708_ = lean_box(0);
v_isShared_5709_ = v_isSharedCheck_5773_;
goto v_resetjp_5707_;
}
v_resetjp_5707_:
{
lean_object* v_ref_5710_; lean_object* v_tactic_5711_; lean_object* v_toCold_5712_; lean_object* v_currRecDepth_5713_; lean_object* v_ref_5714_; uint8_t v_diag_5715_; uint8_t v_suppressElabErrors_5716_; lean_object* v___x_5717_; lean_object* v___x_5718_; lean_object* v_ref_5719_; lean_object* v___x_5720_; lean_object* v___y_5746_; lean_object* v___y_5763_; uint8_t v___x_5764_; 
v_ref_5710_ = lean_ctor_get(v_val_5706_, 0);
lean_inc(v_ref_5710_);
v_tactic_5711_ = lean_ctor_get(v_val_5706_, 1);
lean_inc(v_tactic_5711_);
lean_dec(v_val_5706_);
v_toCold_5712_ = lean_ctor_get(v___y_5691_, 0);
v_currRecDepth_5713_ = lean_ctor_get(v___y_5691_, 1);
v_ref_5714_ = lean_ctor_get(v___y_5691_, 2);
v_diag_5715_ = lean_ctor_get_uint8(v___y_5691_, sizeof(void*)*3);
v_suppressElabErrors_5716_ = lean_ctor_get_uint8(v___y_5691_, sizeof(void*)*3 + 1);
v___x_5717_ = lean_unsigned_to_nat(0u);
v___x_5718_ = lean_array_get_size(v___x_5685_);
v_ref_5719_ = l_Lean_replaceRef(v_ref_5710_, v_ref_5714_);
lean_inc(v_currRecDepth_5713_);
lean_inc_ref(v_toCold_5712_);
v___x_5720_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5720_, 0, v_toCold_5712_);
lean_ctor_set(v___x_5720_, 1, v_currRecDepth_5713_);
lean_ctor_set(v___x_5720_, 2, v_ref_5719_);
lean_ctor_set_uint8(v___x_5720_, sizeof(void*)*3, v_diag_5715_);
lean_ctor_set_uint8(v___x_5720_, sizeof(void*)*3 + 1, v_suppressElabErrors_5716_);
v___x_5764_ = lean_nat_dec_lt(v___x_5717_, v___x_5718_);
if (v___x_5764_ == 0)
{
goto v___jp_5747_;
}
else
{
lean_object* v___x_5765_; uint8_t v___x_5766_; 
v___x_5765_ = lean_box(0);
v___x_5766_ = lean_nat_dec_le(v___x_5718_, v___x_5718_);
if (v___x_5766_ == 0)
{
if (v___x_5764_ == 0)
{
goto v___jp_5747_;
}
else
{
size_t v___x_5767_; size_t v___x_5768_; lean_object* v___x_5769_; 
v___x_5767_ = ((size_t)0ULL);
v___x_5768_ = lean_usize_of_nat(v___x_5718_);
v___x_5769_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v___x_5685_, v___x_5767_, v___x_5768_, v___x_5765_, v___y_5689_, v___y_5690_, v___x_5720_, v___y_5692_);
v___y_5763_ = v___x_5769_;
goto v___jp_5762_;
}
}
else
{
size_t v___x_5770_; size_t v___x_5771_; lean_object* v___x_5772_; 
v___x_5770_ = ((size_t)0ULL);
v___x_5771_ = lean_usize_of_nat(v___x_5718_);
v___x_5772_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v___x_5685_, v___x_5770_, v___x_5771_, v___x_5765_, v___y_5689_, v___y_5690_, v___x_5720_, v___y_5692_);
v___y_5763_ = v___x_5772_;
goto v___jp_5762_;
}
}
v___jp_5721_:
{
lean_object* v___x_5722_; lean_object* v___x_5723_; lean_object* v___f_5724_; lean_object* v___x_5725_; 
v___x_5722_ = lean_array_get(v___x_5686_, v___x_5685_, v___x_5717_);
v___x_5723_ = lean_array_to_list(v___x_5685_);
v___f_5724_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2___boxed), 12, 3);
lean_closure_set(v___f_5724_, 0, v___x_5723_);
lean_closure_set(v___f_5724_, 1, v_ref_5710_);
lean_closure_set(v___f_5724_, 2, v_tactic_5711_);
v___x_5725_ = l_Lean_Elab_Tactic_run(v___x_5722_, v___f_5724_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_, v___x_5720_, v___y_5692_);
if (lean_obj_tag(v___x_5725_) == 0)
{
lean_object* v_a_5726_; lean_object* v___x_5728_; uint8_t v_isShared_5729_; uint8_t v_isSharedCheck_5736_; 
v_a_5726_ = lean_ctor_get(v___x_5725_, 0);
v_isSharedCheck_5736_ = !lean_is_exclusive(v___x_5725_);
if (v_isSharedCheck_5736_ == 0)
{
v___x_5728_ = v___x_5725_;
v_isShared_5729_ = v_isSharedCheck_5736_;
goto v_resetjp_5727_;
}
else
{
lean_inc(v_a_5726_);
lean_dec(v___x_5725_);
v___x_5728_ = lean_box(0);
v_isShared_5729_ = v_isSharedCheck_5736_;
goto v_resetjp_5727_;
}
v_resetjp_5727_:
{
uint8_t v___x_5730_; 
v___x_5730_ = l_List_isEmpty___redArg(v_a_5726_);
if (v___x_5730_ == 0)
{
lean_object* v___x_5731_; 
lean_del_object(v___x_5728_);
v___x_5731_ = l_Lean_Elab_Term_reportUnsolvedGoals(v_a_5726_, v___y_5689_, v___y_5690_, v___x_5720_, v___y_5692_);
lean_dec_ref_known(v___x_5720_, 3);
return v___x_5731_;
}
else
{
lean_object* v___x_5732_; lean_object* v___x_5734_; 
lean_dec(v_a_5726_);
lean_dec_ref_known(v___x_5720_, 3);
v___x_5732_ = lean_box(0);
if (v_isShared_5729_ == 0)
{
lean_ctor_set(v___x_5728_, 0, v___x_5732_);
v___x_5734_ = v___x_5728_;
goto v_reusejp_5733_;
}
else
{
lean_object* v_reuseFailAlloc_5735_; 
v_reuseFailAlloc_5735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5735_, 0, v___x_5732_);
v___x_5734_ = v_reuseFailAlloc_5735_;
goto v_reusejp_5733_;
}
v_reusejp_5733_:
{
return v___x_5734_;
}
}
}
}
else
{
lean_object* v_a_5737_; lean_object* v___x_5739_; uint8_t v_isShared_5740_; uint8_t v_isSharedCheck_5744_; 
lean_dec_ref_known(v___x_5720_, 3);
v_a_5737_ = lean_ctor_get(v___x_5725_, 0);
v_isSharedCheck_5744_ = !lean_is_exclusive(v___x_5725_);
if (v_isSharedCheck_5744_ == 0)
{
v___x_5739_ = v___x_5725_;
v_isShared_5740_ = v_isSharedCheck_5744_;
goto v_resetjp_5738_;
}
else
{
lean_inc(v_a_5737_);
lean_dec(v___x_5725_);
v___x_5739_ = lean_box(0);
v_isShared_5740_ = v_isSharedCheck_5744_;
goto v_resetjp_5738_;
}
v_resetjp_5738_:
{
lean_object* v___x_5742_; 
if (v_isShared_5740_ == 0)
{
v___x_5742_ = v___x_5739_;
goto v_reusejp_5741_;
}
else
{
lean_object* v_reuseFailAlloc_5743_; 
v_reuseFailAlloc_5743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5743_, 0, v_a_5737_);
v___x_5742_ = v_reuseFailAlloc_5743_;
goto v_reusejp_5741_;
}
v_reusejp_5741_:
{
return v___x_5742_;
}
}
}
}
v___jp_5745_:
{
if (lean_obj_tag(v___y_5746_) == 0)
{
lean_dec_ref_known(v___y_5746_, 1);
goto v___jp_5721_;
}
else
{
lean_dec_ref_known(v___x_5720_, 3);
lean_dec(v_tactic_5711_);
lean_dec(v_ref_5710_);
lean_dec_ref(v___x_5685_);
return v___y_5746_;
}
}
v___jp_5747_:
{
uint8_t v___x_5748_; 
v___x_5748_ = lean_nat_dec_eq(v___x_5718_, v___x_5717_);
if (v___x_5748_ == 0)
{
uint8_t v___x_5749_; 
lean_del_object(v___x_5708_);
v___x_5749_ = lean_nat_dec_lt(v___x_5717_, v___x_5718_);
if (v___x_5749_ == 0)
{
goto v___jp_5721_;
}
else
{
lean_object* v___x_5750_; uint8_t v___x_5751_; 
v___x_5750_ = lean_box(0);
v___x_5751_ = lean_nat_dec_le(v___x_5718_, v___x_5718_);
if (v___x_5751_ == 0)
{
if (v___x_5749_ == 0)
{
goto v___jp_5721_;
}
else
{
size_t v___x_5752_; size_t v___x_5753_; lean_object* v___x_5754_; 
v___x_5752_ = ((size_t)0ULL);
v___x_5753_ = lean_usize_of_nat(v___x_5718_);
v___x_5754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v___x_5685_, v___x_5752_, v___x_5753_, v___x_5750_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_, v___x_5720_, v___y_5692_);
v___y_5746_ = v___x_5754_;
goto v___jp_5745_;
}
}
else
{
size_t v___x_5755_; size_t v___x_5756_; lean_object* v___x_5757_; 
v___x_5755_ = ((size_t)0ULL);
v___x_5756_ = lean_usize_of_nat(v___x_5718_);
v___x_5757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v___x_5685_, v___x_5755_, v___x_5756_, v___x_5750_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_, v___x_5720_, v___y_5692_);
v___y_5746_ = v___x_5757_;
goto v___jp_5745_;
}
}
}
else
{
lean_object* v___x_5758_; lean_object* v___x_5760_; 
lean_dec_ref_known(v___x_5720_, 3);
lean_dec(v_tactic_5711_);
lean_dec(v_ref_5710_);
lean_dec_ref(v___x_5685_);
v___x_5758_ = lean_box(0);
if (v_isShared_5709_ == 0)
{
lean_ctor_set_tag(v___x_5708_, 0);
lean_ctor_set(v___x_5708_, 0, v___x_5758_);
v___x_5760_ = v___x_5708_;
goto v_reusejp_5759_;
}
else
{
lean_object* v_reuseFailAlloc_5761_; 
v_reuseFailAlloc_5761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5761_, 0, v___x_5758_);
v___x_5760_ = v_reuseFailAlloc_5761_;
goto v_reusejp_5759_;
}
v_reusejp_5759_:
{
return v___x_5760_;
}
}
}
v___jp_5762_:
{
if (lean_obj_tag(v___y_5763_) == 0)
{
lean_dec_ref_known(v___y_5763_, 1);
goto v___jp_5747_;
}
else
{
lean_dec_ref_known(v___x_5720_, 3);
lean_dec(v_tactic_5711_);
lean_dec(v_ref_5710_);
lean_del_object(v___x_5708_);
lean_dec_ref(v___x_5685_);
return v___y_5763_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3___boxed(lean_object* v___x_5774_, lean_object* v___x_5775_, lean_object* v___x_5776_, lean_object* v___y_5777_, lean_object* v___y_5778_, lean_object* v___y_5779_, lean_object* v___y_5780_, lean_object* v___y_5781_, lean_object* v___y_5782_, lean_object* v___y_5783_){
_start:
{
lean_object* v_res_5784_; 
v_res_5784_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3(v___x_5774_, v___x_5775_, v___x_5776_, v___y_5777_, v___y_5778_, v___y_5779_, v___y_5780_, v___y_5781_, v___y_5782_);
lean_dec(v___y_5782_);
lean_dec_ref(v___y_5781_);
lean_dec(v___y_5780_);
lean_dec_ref(v___y_5779_);
lean_dec(v___y_5778_);
lean_dec_ref(v___y_5777_);
lean_dec(v___x_5776_);
return v_res_5784_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0(lean_object* v_x_5785_){
_start:
{
uint8_t v___x_5786_; 
v___x_5786_ = 0;
return v___x_5786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0___boxed(lean_object* v_x_5787_){
_start:
{
uint8_t v_res_5788_; lean_object* v_r_5789_; 
v_res_5788_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0(v_x_5787_);
lean_dec(v_x_5787_);
v_r_5789_ = lean_box(v_res_5788_);
return v_r_5789_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(lean_object* v_as_5796_, size_t v_sz_5797_, size_t v_i_5798_, lean_object* v_b_5799_, lean_object* v___y_5800_, lean_object* v___y_5801_, lean_object* v___y_5802_, lean_object* v___y_5803_){
_start:
{
uint8_t v___x_5805_; 
v___x_5805_ = lean_usize_dec_lt(v_i_5798_, v_sz_5797_);
if (v___x_5805_ == 0)
{
lean_object* v___x_5806_; 
v___x_5806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5806_, 0, v_b_5799_);
return v___x_5806_;
}
else
{
lean_object* v_snd_5807_; lean_object* v_fst_5808_; lean_object* v___x_5810_; uint8_t v_isShared_5811_; uint8_t v_isSharedCheck_5880_; 
v_snd_5807_ = lean_ctor_get(v_b_5799_, 1);
v_fst_5808_ = lean_ctor_get(v_b_5799_, 0);
v_isSharedCheck_5880_ = !lean_is_exclusive(v_b_5799_);
if (v_isSharedCheck_5880_ == 0)
{
v___x_5810_ = v_b_5799_;
v_isShared_5811_ = v_isSharedCheck_5880_;
goto v_resetjp_5809_;
}
else
{
lean_inc(v_snd_5807_);
lean_inc(v_fst_5808_);
lean_dec(v_b_5799_);
v___x_5810_ = lean_box(0);
v_isShared_5811_ = v_isSharedCheck_5880_;
goto v_resetjp_5809_;
}
v_resetjp_5809_:
{
lean_object* v_array_5812_; lean_object* v_start_5813_; lean_object* v_stop_5814_; uint8_t v___x_5815_; 
v_array_5812_ = lean_ctor_get(v_snd_5807_, 0);
v_start_5813_ = lean_ctor_get(v_snd_5807_, 1);
v_stop_5814_ = lean_ctor_get(v_snd_5807_, 2);
v___x_5815_ = lean_nat_dec_lt(v_start_5813_, v_stop_5814_);
if (v___x_5815_ == 0)
{
lean_object* v___x_5817_; 
if (v_isShared_5811_ == 0)
{
v___x_5817_ = v___x_5810_;
goto v_reusejp_5816_;
}
else
{
lean_object* v_reuseFailAlloc_5819_; 
v_reuseFailAlloc_5819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5819_, 0, v_fst_5808_);
lean_ctor_set(v_reuseFailAlloc_5819_, 1, v_snd_5807_);
v___x_5817_ = v_reuseFailAlloc_5819_;
goto v_reusejp_5816_;
}
v_reusejp_5816_:
{
lean_object* v___x_5818_; 
v___x_5818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5818_, 0, v___x_5817_);
return v___x_5818_;
}
}
else
{
lean_object* v___x_5821_; uint8_t v_isShared_5822_; uint8_t v_isSharedCheck_5876_; 
lean_inc(v_stop_5814_);
lean_inc(v_start_5813_);
lean_inc_ref(v_array_5812_);
v_isSharedCheck_5876_ = !lean_is_exclusive(v_snd_5807_);
if (v_isSharedCheck_5876_ == 0)
{
lean_object* v_unused_5877_; lean_object* v_unused_5878_; lean_object* v_unused_5879_; 
v_unused_5877_ = lean_ctor_get(v_snd_5807_, 2);
lean_dec(v_unused_5877_);
v_unused_5878_ = lean_ctor_get(v_snd_5807_, 1);
lean_dec(v_unused_5878_);
v_unused_5879_ = lean_ctor_get(v_snd_5807_, 0);
lean_dec(v_unused_5879_);
v___x_5821_ = v_snd_5807_;
v_isShared_5822_ = v_isSharedCheck_5876_;
goto v_resetjp_5820_;
}
else
{
lean_dec(v_snd_5807_);
v___x_5821_ = lean_box(0);
v_isShared_5822_ = v_isSharedCheck_5876_;
goto v_resetjp_5820_;
}
v_resetjp_5820_:
{
lean_object* v_array_5823_; lean_object* v_start_5824_; lean_object* v_stop_5825_; lean_object* v___x_5826_; lean_object* v___x_5827_; lean_object* v___x_5828_; lean_object* v___x_5830_; 
v_array_5823_ = lean_ctor_get(v_fst_5808_, 0);
v_start_5824_ = lean_ctor_get(v_fst_5808_, 1);
v_stop_5825_ = lean_ctor_get(v_fst_5808_, 2);
v___x_5826_ = lean_array_fget(v_array_5812_, v_start_5813_);
v___x_5827_ = lean_unsigned_to_nat(1u);
v___x_5828_ = lean_nat_add(v_start_5813_, v___x_5827_);
lean_dec(v_start_5813_);
if (v_isShared_5822_ == 0)
{
lean_ctor_set(v___x_5821_, 1, v___x_5828_);
v___x_5830_ = v___x_5821_;
goto v_reusejp_5829_;
}
else
{
lean_object* v_reuseFailAlloc_5875_; 
v_reuseFailAlloc_5875_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5875_, 0, v_array_5812_);
lean_ctor_set(v_reuseFailAlloc_5875_, 1, v___x_5828_);
lean_ctor_set(v_reuseFailAlloc_5875_, 2, v_stop_5814_);
v___x_5830_ = v_reuseFailAlloc_5875_;
goto v_reusejp_5829_;
}
v_reusejp_5829_:
{
uint8_t v___x_5831_; 
v___x_5831_ = lean_nat_dec_lt(v_start_5824_, v_stop_5825_);
if (v___x_5831_ == 0)
{
lean_object* v___x_5833_; 
lean_dec(v___x_5826_);
if (v_isShared_5811_ == 0)
{
lean_ctor_set(v___x_5810_, 1, v___x_5830_);
v___x_5833_ = v___x_5810_;
goto v_reusejp_5832_;
}
else
{
lean_object* v_reuseFailAlloc_5835_; 
v_reuseFailAlloc_5835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5835_, 0, v_fst_5808_);
lean_ctor_set(v_reuseFailAlloc_5835_, 1, v___x_5830_);
v___x_5833_ = v_reuseFailAlloc_5835_;
goto v_reusejp_5832_;
}
v_reusejp_5832_:
{
lean_object* v___x_5834_; 
v___x_5834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5834_, 0, v___x_5833_);
return v___x_5834_;
}
}
else
{
lean_object* v___x_5837_; uint8_t v_isShared_5838_; uint8_t v_isSharedCheck_5871_; 
lean_inc(v_stop_5825_);
lean_inc(v_start_5824_);
lean_inc_ref(v_array_5823_);
v_isSharedCheck_5871_ = !lean_is_exclusive(v_fst_5808_);
if (v_isSharedCheck_5871_ == 0)
{
lean_object* v_unused_5872_; lean_object* v_unused_5873_; lean_object* v_unused_5874_; 
v_unused_5872_ = lean_ctor_get(v_fst_5808_, 2);
lean_dec(v_unused_5872_);
v_unused_5873_ = lean_ctor_get(v_fst_5808_, 1);
lean_dec(v_unused_5873_);
v_unused_5874_ = lean_ctor_get(v_fst_5808_, 0);
lean_dec(v_unused_5874_);
v___x_5837_ = v_fst_5808_;
v_isShared_5838_ = v_isSharedCheck_5871_;
goto v_resetjp_5836_;
}
else
{
lean_dec(v_fst_5808_);
v___x_5837_ = lean_box(0);
v_isShared_5838_ = v_isSharedCheck_5871_;
goto v_resetjp_5836_;
}
v_resetjp_5836_:
{
lean_object* v___f_5839_; lean_object* v___x_5840_; lean_object* v_a_5841_; lean_object* v___x_5842_; lean_object* v___y_5843_; lean_object* v___x_5844_; lean_object* v___x_5845_; lean_object* v___x_5846_; lean_object* v___x_5847_; uint8_t v___x_5848_; lean_object* v___x_5849_; lean_object* v___x_5850_; lean_object* v___x_5851_; lean_object* v___x_5852_; 
v___f_5839_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__0));
v___x_5840_ = lean_box(0);
v_a_5841_ = lean_array_uget_borrowed(v_as_5796_, v_i_5798_);
v___x_5842_ = lean_array_fget_borrowed(v_array_5823_, v_start_5824_);
lean_inc(v___x_5842_);
v___y_5843_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3___boxed), 10, 3);
lean_closure_set(v___y_5843_, 0, v___x_5826_);
lean_closure_set(v___y_5843_, 1, v___x_5842_);
lean_closure_set(v___y_5843_, 2, v___x_5840_);
lean_inc(v_a_5841_);
v___x_5844_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withDeclName___boxed), 10, 3);
lean_closure_set(v___x_5844_, 0, lean_box(0));
lean_closure_set(v___x_5844_, 1, v_a_5841_);
lean_closure_set(v___x_5844_, 2, v___y_5843_);
v___x_5845_ = lean_box(0);
v___x_5846_ = lean_box(0);
v___x_5847_ = lean_box(1);
v___x_5848_ = 0;
v___x_5849_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__1));
v___x_5850_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_5850_, 0, v___x_5845_);
lean_ctor_set(v___x_5850_, 1, v___x_5846_);
lean_ctor_set(v___x_5850_, 2, v___x_5845_);
lean_ctor_set(v___x_5850_, 3, v___f_5839_);
lean_ctor_set(v___x_5850_, 4, v___x_5847_);
lean_ctor_set(v___x_5850_, 5, v___x_5847_);
lean_ctor_set(v___x_5850_, 6, v___x_5845_);
lean_ctor_set(v___x_5850_, 7, v___x_5849_);
lean_ctor_set_uint8(v___x_5850_, sizeof(void*)*8, v___x_5831_);
lean_ctor_set_uint8(v___x_5850_, sizeof(void*)*8 + 1, v___x_5831_);
lean_ctor_set_uint8(v___x_5850_, sizeof(void*)*8 + 2, v___x_5831_);
lean_ctor_set_uint8(v___x_5850_, sizeof(void*)*8 + 3, v___x_5831_);
lean_ctor_set_uint8(v___x_5850_, sizeof(void*)*8 + 4, v___x_5848_);
lean_ctor_set_uint8(v___x_5850_, sizeof(void*)*8 + 5, v___x_5848_);
lean_ctor_set_uint8(v___x_5850_, sizeof(void*)*8 + 6, v___x_5848_);
lean_ctor_set_uint8(v___x_5850_, sizeof(void*)*8 + 7, v___x_5848_);
lean_ctor_set_uint8(v___x_5850_, sizeof(void*)*8 + 8, v___x_5831_);
lean_ctor_set_uint8(v___x_5850_, sizeof(void*)*8 + 9, v___x_5848_);
lean_ctor_set_uint8(v___x_5850_, sizeof(void*)*8 + 10, v___x_5831_);
v___x_5851_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__2));
v___x_5852_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_5844_, v___x_5850_, v___x_5851_, v___y_5800_, v___y_5801_, v___y_5802_, v___y_5803_);
if (lean_obj_tag(v___x_5852_) == 0)
{
lean_object* v___x_5853_; lean_object* v___x_5855_; 
lean_dec_ref_known(v___x_5852_, 1);
v___x_5853_ = lean_nat_add(v_start_5824_, v___x_5827_);
lean_dec(v_start_5824_);
if (v_isShared_5838_ == 0)
{
lean_ctor_set(v___x_5837_, 1, v___x_5853_);
v___x_5855_ = v___x_5837_;
goto v_reusejp_5854_;
}
else
{
lean_object* v_reuseFailAlloc_5862_; 
v_reuseFailAlloc_5862_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5862_, 0, v_array_5823_);
lean_ctor_set(v_reuseFailAlloc_5862_, 1, v___x_5853_);
lean_ctor_set(v_reuseFailAlloc_5862_, 2, v_stop_5825_);
v___x_5855_ = v_reuseFailAlloc_5862_;
goto v_reusejp_5854_;
}
v_reusejp_5854_:
{
lean_object* v___x_5857_; 
if (v_isShared_5811_ == 0)
{
lean_ctor_set(v___x_5810_, 1, v___x_5830_);
lean_ctor_set(v___x_5810_, 0, v___x_5855_);
v___x_5857_ = v___x_5810_;
goto v_reusejp_5856_;
}
else
{
lean_object* v_reuseFailAlloc_5861_; 
v_reuseFailAlloc_5861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5861_, 0, v___x_5855_);
lean_ctor_set(v_reuseFailAlloc_5861_, 1, v___x_5830_);
v___x_5857_ = v_reuseFailAlloc_5861_;
goto v_reusejp_5856_;
}
v_reusejp_5856_:
{
size_t v___x_5858_; size_t v___x_5859_; 
v___x_5858_ = ((size_t)1ULL);
v___x_5859_ = lean_usize_add(v_i_5798_, v___x_5858_);
v_i_5798_ = v___x_5859_;
v_b_5799_ = v___x_5857_;
goto _start;
}
}
}
else
{
lean_object* v_a_5863_; lean_object* v___x_5865_; uint8_t v_isShared_5866_; uint8_t v_isSharedCheck_5870_; 
lean_del_object(v___x_5837_);
lean_dec_ref(v___x_5830_);
lean_dec(v_stop_5825_);
lean_dec(v_start_5824_);
lean_dec_ref(v_array_5823_);
lean_del_object(v___x_5810_);
v_a_5863_ = lean_ctor_get(v___x_5852_, 0);
v_isSharedCheck_5870_ = !lean_is_exclusive(v___x_5852_);
if (v_isSharedCheck_5870_ == 0)
{
v___x_5865_ = v___x_5852_;
v_isShared_5866_ = v_isSharedCheck_5870_;
goto v_resetjp_5864_;
}
else
{
lean_inc(v_a_5863_);
lean_dec(v___x_5852_);
v___x_5865_ = lean_box(0);
v_isShared_5866_ = v_isSharedCheck_5870_;
goto v_resetjp_5864_;
}
v_resetjp_5864_:
{
lean_object* v___x_5868_; 
if (v_isShared_5866_ == 0)
{
v___x_5868_ = v___x_5865_;
goto v_reusejp_5867_;
}
else
{
lean_object* v_reuseFailAlloc_5869_; 
v_reuseFailAlloc_5869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5869_, 0, v_a_5863_);
v___x_5868_ = v_reuseFailAlloc_5869_;
goto v_reusejp_5867_;
}
v_reusejp_5867_:
{
return v___x_5868_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___boxed(lean_object* v_as_5881_, lean_object* v_sz_5882_, lean_object* v_i_5883_, lean_object* v_b_5884_, lean_object* v___y_5885_, lean_object* v___y_5886_, lean_object* v___y_5887_, lean_object* v___y_5888_, lean_object* v___y_5889_){
_start:
{
size_t v_sz_boxed_5890_; size_t v_i_boxed_5891_; lean_object* v_res_5892_; 
v_sz_boxed_5890_ = lean_unbox_usize(v_sz_5882_);
lean_dec(v_sz_5882_);
v_i_boxed_5891_ = lean_unbox_usize(v_i_5883_);
lean_dec(v_i_5883_);
v_res_5892_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(v_as_5881_, v_sz_boxed_5890_, v_i_boxed_5891_, v_b_5884_, v___y_5885_, v___y_5886_, v___y_5887_, v___y_5888_);
lean_dec(v___y_5888_);
lean_dec_ref(v___y_5887_);
lean_dec(v___y_5886_);
lean_dec_ref(v___y_5885_);
lean_dec_ref(v_as_5881_);
return v_res_5892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___lam__0(lean_object* v_value_5893_, lean_object* v_decrTactics_5894_, lean_object* v_argsPacker_5895_, lean_object* v_funNames_5896_, lean_object* v___y_5897_, lean_object* v___y_5898_, lean_object* v___y_5899_, lean_object* v___y_5900_){
_start:
{
lean_object* v___x_5902_; 
lean_inc_ref(v_value_5893_);
v___x_5902_ = l_Lean_Meta_getMVarsNoDelayed(v_value_5893_, v___y_5897_, v___y_5898_, v___y_5899_, v___y_5900_);
if (lean_obj_tag(v___x_5902_) == 0)
{
lean_object* v_a_5903_; lean_object* v___x_5904_; 
v_a_5903_ = lean_ctor_get(v___x_5902_, 0);
lean_inc(v_a_5903_);
lean_dec_ref_known(v___x_5902_, 1);
v___x_5904_ = l_Lean_Elab_WF_assignSubsumed(v_a_5903_, v___y_5897_, v___y_5898_, v___y_5899_, v___y_5900_);
lean_dec(v_a_5903_);
if (lean_obj_tag(v___x_5904_) == 0)
{
lean_object* v_a_5905_; lean_object* v___x_5906_; lean_object* v___x_5907_; 
v_a_5905_ = lean_ctor_get(v___x_5904_, 0);
lean_inc(v_a_5905_);
lean_dec_ref_known(v___x_5904_, 1);
v___x_5906_ = lean_array_get_size(v_decrTactics_5894_);
v___x_5907_ = l_Lean_Elab_WF_groupGoalsByFunction(v_argsPacker_5895_, v___x_5906_, v_a_5905_, v___y_5897_, v___y_5898_, v___y_5899_, v___y_5900_);
lean_dec(v_a_5905_);
if (lean_obj_tag(v___x_5907_) == 0)
{
lean_object* v_a_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v___x_5913_; size_t v_sz_5914_; size_t v___x_5915_; lean_object* v___x_5916_; 
v_a_5908_ = lean_ctor_get(v___x_5907_, 0);
lean_inc(v_a_5908_);
lean_dec_ref_known(v___x_5907_, 1);
v___x_5909_ = lean_unsigned_to_nat(0u);
v___x_5910_ = lean_array_get_size(v_a_5908_);
v___x_5911_ = l_Array_toSubarray___redArg(v_a_5908_, v___x_5909_, v___x_5910_);
v___x_5912_ = l_Array_toSubarray___redArg(v_decrTactics_5894_, v___x_5909_, v___x_5906_);
v___x_5913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5913_, 0, v___x_5911_);
lean_ctor_set(v___x_5913_, 1, v___x_5912_);
v_sz_5914_ = lean_array_size(v_funNames_5896_);
v___x_5915_ = ((size_t)0ULL);
v___x_5916_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(v_funNames_5896_, v_sz_5914_, v___x_5915_, v___x_5913_, v___y_5897_, v___y_5898_, v___y_5899_, v___y_5900_);
if (lean_obj_tag(v___x_5916_) == 0)
{
lean_object* v___x_5917_; 
lean_dec_ref_known(v___x_5916_, 1);
v___x_5917_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_value_5893_, v___y_5898_);
return v___x_5917_;
}
else
{
lean_object* v_a_5918_; lean_object* v___x_5920_; uint8_t v_isShared_5921_; uint8_t v_isSharedCheck_5925_; 
lean_dec_ref(v_value_5893_);
v_a_5918_ = lean_ctor_get(v___x_5916_, 0);
v_isSharedCheck_5925_ = !lean_is_exclusive(v___x_5916_);
if (v_isSharedCheck_5925_ == 0)
{
v___x_5920_ = v___x_5916_;
v_isShared_5921_ = v_isSharedCheck_5925_;
goto v_resetjp_5919_;
}
else
{
lean_inc(v_a_5918_);
lean_dec(v___x_5916_);
v___x_5920_ = lean_box(0);
v_isShared_5921_ = v_isSharedCheck_5925_;
goto v_resetjp_5919_;
}
v_resetjp_5919_:
{
lean_object* v___x_5923_; 
if (v_isShared_5921_ == 0)
{
v___x_5923_ = v___x_5920_;
goto v_reusejp_5922_;
}
else
{
lean_object* v_reuseFailAlloc_5924_; 
v_reuseFailAlloc_5924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5924_, 0, v_a_5918_);
v___x_5923_ = v_reuseFailAlloc_5924_;
goto v_reusejp_5922_;
}
v_reusejp_5922_:
{
return v___x_5923_;
}
}
}
}
else
{
lean_object* v_a_5926_; lean_object* v___x_5928_; uint8_t v_isShared_5929_; uint8_t v_isSharedCheck_5933_; 
lean_dec_ref(v_decrTactics_5894_);
lean_dec_ref(v_value_5893_);
v_a_5926_ = lean_ctor_get(v___x_5907_, 0);
v_isSharedCheck_5933_ = !lean_is_exclusive(v___x_5907_);
if (v_isSharedCheck_5933_ == 0)
{
v___x_5928_ = v___x_5907_;
v_isShared_5929_ = v_isSharedCheck_5933_;
goto v_resetjp_5927_;
}
else
{
lean_inc(v_a_5926_);
lean_dec(v___x_5907_);
v___x_5928_ = lean_box(0);
v_isShared_5929_ = v_isSharedCheck_5933_;
goto v_resetjp_5927_;
}
v_resetjp_5927_:
{
lean_object* v___x_5931_; 
if (v_isShared_5929_ == 0)
{
v___x_5931_ = v___x_5928_;
goto v_reusejp_5930_;
}
else
{
lean_object* v_reuseFailAlloc_5932_; 
v_reuseFailAlloc_5932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5932_, 0, v_a_5926_);
v___x_5931_ = v_reuseFailAlloc_5932_;
goto v_reusejp_5930_;
}
v_reusejp_5930_:
{
return v___x_5931_;
}
}
}
}
else
{
lean_object* v_a_5934_; lean_object* v___x_5936_; uint8_t v_isShared_5937_; uint8_t v_isSharedCheck_5941_; 
lean_dec_ref(v_decrTactics_5894_);
lean_dec_ref(v_value_5893_);
v_a_5934_ = lean_ctor_get(v___x_5904_, 0);
v_isSharedCheck_5941_ = !lean_is_exclusive(v___x_5904_);
if (v_isSharedCheck_5941_ == 0)
{
v___x_5936_ = v___x_5904_;
v_isShared_5937_ = v_isSharedCheck_5941_;
goto v_resetjp_5935_;
}
else
{
lean_inc(v_a_5934_);
lean_dec(v___x_5904_);
v___x_5936_ = lean_box(0);
v_isShared_5937_ = v_isSharedCheck_5941_;
goto v_resetjp_5935_;
}
v_resetjp_5935_:
{
lean_object* v___x_5939_; 
if (v_isShared_5937_ == 0)
{
v___x_5939_ = v___x_5936_;
goto v_reusejp_5938_;
}
else
{
lean_object* v_reuseFailAlloc_5940_; 
v_reuseFailAlloc_5940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5940_, 0, v_a_5934_);
v___x_5939_ = v_reuseFailAlloc_5940_;
goto v_reusejp_5938_;
}
v_reusejp_5938_:
{
return v___x_5939_;
}
}
}
}
else
{
lean_object* v_a_5942_; lean_object* v___x_5944_; uint8_t v_isShared_5945_; uint8_t v_isSharedCheck_5949_; 
lean_dec_ref(v_decrTactics_5894_);
lean_dec_ref(v_value_5893_);
v_a_5942_ = lean_ctor_get(v___x_5902_, 0);
v_isSharedCheck_5949_ = !lean_is_exclusive(v___x_5902_);
if (v_isSharedCheck_5949_ == 0)
{
v___x_5944_ = v___x_5902_;
v_isShared_5945_ = v_isSharedCheck_5949_;
goto v_resetjp_5943_;
}
else
{
lean_inc(v_a_5942_);
lean_dec(v___x_5902_);
v___x_5944_ = lean_box(0);
v_isShared_5945_ = v_isSharedCheck_5949_;
goto v_resetjp_5943_;
}
v_resetjp_5943_:
{
lean_object* v___x_5947_; 
if (v_isShared_5945_ == 0)
{
v___x_5947_ = v___x_5944_;
goto v_reusejp_5946_;
}
else
{
lean_object* v_reuseFailAlloc_5948_; 
v_reuseFailAlloc_5948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5948_, 0, v_a_5942_);
v___x_5947_ = v_reuseFailAlloc_5948_;
goto v_reusejp_5946_;
}
v_reusejp_5946_:
{
return v___x_5947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___lam__0___boxed(lean_object* v_value_5950_, lean_object* v_decrTactics_5951_, lean_object* v_argsPacker_5952_, lean_object* v_funNames_5953_, lean_object* v___y_5954_, lean_object* v___y_5955_, lean_object* v___y_5956_, lean_object* v___y_5957_, lean_object* v___y_5958_){
_start:
{
lean_object* v_res_5959_; 
v_res_5959_ = l_Lean_Elab_WF_solveDecreasingGoals___lam__0(v_value_5950_, v_decrTactics_5951_, v_argsPacker_5952_, v_funNames_5953_, v___y_5954_, v___y_5955_, v___y_5956_, v___y_5957_);
lean_dec(v___y_5957_);
lean_dec_ref(v___y_5956_);
lean_dec(v___y_5955_);
lean_dec_ref(v___y_5954_);
lean_dec_ref(v_funNames_5953_);
lean_dec_ref(v_argsPacker_5952_);
return v_res_5959_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(lean_object* v___y_5960_, uint8_t v_isExporting_5961_, lean_object* v___x_5962_, lean_object* v___y_5963_, lean_object* v___x_5964_, lean_object* v_a_x3f_5965_){
_start:
{
lean_object* v___x_5967_; lean_object* v_env_5968_; lean_object* v_nextMacroScope_5969_; lean_object* v_ngen_5970_; lean_object* v_auxDeclNGen_5971_; lean_object* v_traceState_5972_; lean_object* v_messages_5973_; lean_object* v_infoState_5974_; lean_object* v_snapshotTasks_5975_; lean_object* v___x_5977_; uint8_t v_isShared_5978_; uint8_t v_isSharedCheck_6000_; 
v___x_5967_ = lean_st_ref_take(v___y_5960_);
v_env_5968_ = lean_ctor_get(v___x_5967_, 0);
v_nextMacroScope_5969_ = lean_ctor_get(v___x_5967_, 1);
v_ngen_5970_ = lean_ctor_get(v___x_5967_, 2);
v_auxDeclNGen_5971_ = lean_ctor_get(v___x_5967_, 3);
v_traceState_5972_ = lean_ctor_get(v___x_5967_, 4);
v_messages_5973_ = lean_ctor_get(v___x_5967_, 6);
v_infoState_5974_ = lean_ctor_get(v___x_5967_, 7);
v_snapshotTasks_5975_ = lean_ctor_get(v___x_5967_, 8);
v_isSharedCheck_6000_ = !lean_is_exclusive(v___x_5967_);
if (v_isSharedCheck_6000_ == 0)
{
lean_object* v_unused_6001_; 
v_unused_6001_ = lean_ctor_get(v___x_5967_, 5);
lean_dec(v_unused_6001_);
v___x_5977_ = v___x_5967_;
v_isShared_5978_ = v_isSharedCheck_6000_;
goto v_resetjp_5976_;
}
else
{
lean_inc(v_snapshotTasks_5975_);
lean_inc(v_infoState_5974_);
lean_inc(v_messages_5973_);
lean_inc(v_traceState_5972_);
lean_inc(v_auxDeclNGen_5971_);
lean_inc(v_ngen_5970_);
lean_inc(v_nextMacroScope_5969_);
lean_inc(v_env_5968_);
lean_dec(v___x_5967_);
v___x_5977_ = lean_box(0);
v_isShared_5978_ = v_isSharedCheck_6000_;
goto v_resetjp_5976_;
}
v_resetjp_5976_:
{
lean_object* v___x_5979_; lean_object* v___x_5981_; 
v___x_5979_ = l_Lean_Environment_setExporting(v_env_5968_, v_isExporting_5961_);
if (v_isShared_5978_ == 0)
{
lean_ctor_set(v___x_5977_, 5, v___x_5962_);
lean_ctor_set(v___x_5977_, 0, v___x_5979_);
v___x_5981_ = v___x_5977_;
goto v_reusejp_5980_;
}
else
{
lean_object* v_reuseFailAlloc_5999_; 
v_reuseFailAlloc_5999_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5999_, 0, v___x_5979_);
lean_ctor_set(v_reuseFailAlloc_5999_, 1, v_nextMacroScope_5969_);
lean_ctor_set(v_reuseFailAlloc_5999_, 2, v_ngen_5970_);
lean_ctor_set(v_reuseFailAlloc_5999_, 3, v_auxDeclNGen_5971_);
lean_ctor_set(v_reuseFailAlloc_5999_, 4, v_traceState_5972_);
lean_ctor_set(v_reuseFailAlloc_5999_, 5, v___x_5962_);
lean_ctor_set(v_reuseFailAlloc_5999_, 6, v_messages_5973_);
lean_ctor_set(v_reuseFailAlloc_5999_, 7, v_infoState_5974_);
lean_ctor_set(v_reuseFailAlloc_5999_, 8, v_snapshotTasks_5975_);
v___x_5981_ = v_reuseFailAlloc_5999_;
goto v_reusejp_5980_;
}
v_reusejp_5980_:
{
lean_object* v___x_5982_; lean_object* v___x_5983_; lean_object* v_mctx_5984_; lean_object* v_zetaDeltaFVarIds_5985_; lean_object* v_postponed_5986_; lean_object* v_diag_5987_; lean_object* v___x_5989_; uint8_t v_isShared_5990_; uint8_t v_isSharedCheck_5997_; 
v___x_5982_ = lean_st_ref_put(v___y_5960_, v___x_5981_);
v___x_5983_ = lean_st_ref_take(v___y_5963_);
v_mctx_5984_ = lean_ctor_get(v___x_5983_, 0);
v_zetaDeltaFVarIds_5985_ = lean_ctor_get(v___x_5983_, 2);
v_postponed_5986_ = lean_ctor_get(v___x_5983_, 3);
v_diag_5987_ = lean_ctor_get(v___x_5983_, 4);
v_isSharedCheck_5997_ = !lean_is_exclusive(v___x_5983_);
if (v_isSharedCheck_5997_ == 0)
{
lean_object* v_unused_5998_; 
v_unused_5998_ = lean_ctor_get(v___x_5983_, 1);
lean_dec(v_unused_5998_);
v___x_5989_ = v___x_5983_;
v_isShared_5990_ = v_isSharedCheck_5997_;
goto v_resetjp_5988_;
}
else
{
lean_inc(v_diag_5987_);
lean_inc(v_postponed_5986_);
lean_inc(v_zetaDeltaFVarIds_5985_);
lean_inc(v_mctx_5984_);
lean_dec(v___x_5983_);
v___x_5989_ = lean_box(0);
v_isShared_5990_ = v_isSharedCheck_5997_;
goto v_resetjp_5988_;
}
v_resetjp_5988_:
{
lean_object* v___x_5992_; 
if (v_isShared_5990_ == 0)
{
lean_ctor_set(v___x_5989_, 1, v___x_5964_);
v___x_5992_ = v___x_5989_;
goto v_reusejp_5991_;
}
else
{
lean_object* v_reuseFailAlloc_5996_; 
v_reuseFailAlloc_5996_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5996_, 0, v_mctx_5984_);
lean_ctor_set(v_reuseFailAlloc_5996_, 1, v___x_5964_);
lean_ctor_set(v_reuseFailAlloc_5996_, 2, v_zetaDeltaFVarIds_5985_);
lean_ctor_set(v_reuseFailAlloc_5996_, 3, v_postponed_5986_);
lean_ctor_set(v_reuseFailAlloc_5996_, 4, v_diag_5987_);
v___x_5992_ = v_reuseFailAlloc_5996_;
goto v_reusejp_5991_;
}
v_reusejp_5991_:
{
lean_object* v___x_5993_; lean_object* v___x_5994_; lean_object* v___x_5995_; 
v___x_5993_ = lean_st_ref_put(v___y_5963_, v___x_5992_);
v___x_5994_ = lean_box(0);
v___x_5995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5995_, 0, v___x_5994_);
return v___x_5995_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0___boxed(lean_object* v___y_6002_, lean_object* v_isExporting_6003_, lean_object* v___x_6004_, lean_object* v___y_6005_, lean_object* v___x_6006_, lean_object* v_a_x3f_6007_, lean_object* v___y_6008_){
_start:
{
uint8_t v_isExporting_boxed_6009_; lean_object* v_res_6010_; 
v_isExporting_boxed_6009_ = lean_unbox(v_isExporting_6003_);
v_res_6010_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6002_, v_isExporting_boxed_6009_, v___x_6004_, v___y_6005_, v___x_6006_, v_a_x3f_6007_);
lean_dec(v_a_x3f_6007_);
lean_dec(v___y_6005_);
lean_dec(v___y_6002_);
return v_res_6010_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_6011_; 
v___x_6011_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_6011_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_6012_; lean_object* v___x_6013_; 
v___x_6012_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0);
v___x_6013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6013_, 0, v___x_6012_);
return v___x_6013_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_6014_; lean_object* v___x_6015_; 
v___x_6014_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1);
v___x_6015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6015_, 0, v___x_6014_);
lean_ctor_set(v___x_6015_, 1, v___x_6014_);
return v___x_6015_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_6016_; lean_object* v___x_6017_; 
v___x_6016_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1);
v___x_6017_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6017_, 0, v___x_6016_);
lean_ctor_set(v___x_6017_, 1, v___x_6016_);
lean_ctor_set(v___x_6017_, 2, v___x_6016_);
lean_ctor_set(v___x_6017_, 3, v___x_6016_);
lean_ctor_set(v___x_6017_, 4, v___x_6016_);
lean_ctor_set(v___x_6017_, 5, v___x_6016_);
return v___x_6017_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(lean_object* v_x_6018_, uint8_t v_isExporting_6019_, lean_object* v___y_6020_, lean_object* v___y_6021_, lean_object* v___y_6022_, lean_object* v___y_6023_){
_start:
{
lean_object* v___x_6025_; lean_object* v_env_6026_; lean_object* v___x_6027_; uint8_t v_isModule_6028_; 
v___x_6025_ = lean_st_ref_get(v___y_6023_);
v_env_6026_ = lean_ctor_get(v___x_6025_, 0);
lean_inc_ref(v_env_6026_);
lean_dec(v___x_6025_);
v___x_6027_ = l_Lean_Environment_header(v_env_6026_);
v_isModule_6028_ = lean_ctor_get_uint8(v___x_6027_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_6027_);
if (v_isModule_6028_ == 0)
{
lean_object* v___x_6029_; 
lean_dec_ref(v_env_6026_);
lean_inc(v___y_6023_);
lean_inc_ref(v___y_6022_);
lean_inc(v___y_6021_);
lean_inc_ref(v___y_6020_);
v___x_6029_ = lean_apply_5(v_x_6018_, v___y_6020_, v___y_6021_, v___y_6022_, v___y_6023_, lean_box(0));
return v___x_6029_;
}
else
{
uint8_t v_isExporting_6030_; 
v_isExporting_6030_ = lean_ctor_get_uint8(v_env_6026_, sizeof(void*)*8);
lean_dec_ref(v_env_6026_);
if (v_isExporting_6019_ == 0)
{
if (v_isExporting_6030_ == 0)
{
lean_object* v___x_6096_; 
lean_inc(v___y_6023_);
lean_inc_ref(v___y_6022_);
lean_inc(v___y_6021_);
lean_inc_ref(v___y_6020_);
v___x_6096_ = lean_apply_5(v_x_6018_, v___y_6020_, v___y_6021_, v___y_6022_, v___y_6023_, lean_box(0));
return v___x_6096_;
}
else
{
goto v___jp_6031_;
}
}
else
{
if (v_isExporting_6030_ == 0)
{
goto v___jp_6031_;
}
else
{
lean_object* v___x_6097_; 
lean_inc(v___y_6023_);
lean_inc_ref(v___y_6022_);
lean_inc(v___y_6021_);
lean_inc_ref(v___y_6020_);
v___x_6097_ = lean_apply_5(v_x_6018_, v___y_6020_, v___y_6021_, v___y_6022_, v___y_6023_, lean_box(0));
return v___x_6097_;
}
}
v___jp_6031_:
{
lean_object* v___x_6032_; lean_object* v_env_6033_; lean_object* v_nextMacroScope_6034_; lean_object* v_ngen_6035_; lean_object* v_auxDeclNGen_6036_; lean_object* v_traceState_6037_; lean_object* v_messages_6038_; lean_object* v_infoState_6039_; lean_object* v_snapshotTasks_6040_; lean_object* v___x_6042_; uint8_t v_isShared_6043_; uint8_t v_isSharedCheck_6094_; 
v___x_6032_ = lean_st_ref_take(v___y_6023_);
v_env_6033_ = lean_ctor_get(v___x_6032_, 0);
v_nextMacroScope_6034_ = lean_ctor_get(v___x_6032_, 1);
v_ngen_6035_ = lean_ctor_get(v___x_6032_, 2);
v_auxDeclNGen_6036_ = lean_ctor_get(v___x_6032_, 3);
v_traceState_6037_ = lean_ctor_get(v___x_6032_, 4);
v_messages_6038_ = lean_ctor_get(v___x_6032_, 6);
v_infoState_6039_ = lean_ctor_get(v___x_6032_, 7);
v_snapshotTasks_6040_ = lean_ctor_get(v___x_6032_, 8);
v_isSharedCheck_6094_ = !lean_is_exclusive(v___x_6032_);
if (v_isSharedCheck_6094_ == 0)
{
lean_object* v_unused_6095_; 
v_unused_6095_ = lean_ctor_get(v___x_6032_, 5);
lean_dec(v_unused_6095_);
v___x_6042_ = v___x_6032_;
v_isShared_6043_ = v_isSharedCheck_6094_;
goto v_resetjp_6041_;
}
else
{
lean_inc(v_snapshotTasks_6040_);
lean_inc(v_infoState_6039_);
lean_inc(v_messages_6038_);
lean_inc(v_traceState_6037_);
lean_inc(v_auxDeclNGen_6036_);
lean_inc(v_ngen_6035_);
lean_inc(v_nextMacroScope_6034_);
lean_inc(v_env_6033_);
lean_dec(v___x_6032_);
v___x_6042_ = lean_box(0);
v_isShared_6043_ = v_isSharedCheck_6094_;
goto v_resetjp_6041_;
}
v_resetjp_6041_:
{
lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___x_6047_; 
v___x_6044_ = l_Lean_Environment_setExporting(v_env_6033_, v_isExporting_6019_);
v___x_6045_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2);
if (v_isShared_6043_ == 0)
{
lean_ctor_set(v___x_6042_, 5, v___x_6045_);
lean_ctor_set(v___x_6042_, 0, v___x_6044_);
v___x_6047_ = v___x_6042_;
goto v_reusejp_6046_;
}
else
{
lean_object* v_reuseFailAlloc_6093_; 
v_reuseFailAlloc_6093_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6093_, 0, v___x_6044_);
lean_ctor_set(v_reuseFailAlloc_6093_, 1, v_nextMacroScope_6034_);
lean_ctor_set(v_reuseFailAlloc_6093_, 2, v_ngen_6035_);
lean_ctor_set(v_reuseFailAlloc_6093_, 3, v_auxDeclNGen_6036_);
lean_ctor_set(v_reuseFailAlloc_6093_, 4, v_traceState_6037_);
lean_ctor_set(v_reuseFailAlloc_6093_, 5, v___x_6045_);
lean_ctor_set(v_reuseFailAlloc_6093_, 6, v_messages_6038_);
lean_ctor_set(v_reuseFailAlloc_6093_, 7, v_infoState_6039_);
lean_ctor_set(v_reuseFailAlloc_6093_, 8, v_snapshotTasks_6040_);
v___x_6047_ = v_reuseFailAlloc_6093_;
goto v_reusejp_6046_;
}
v_reusejp_6046_:
{
lean_object* v___x_6048_; lean_object* v___x_6049_; lean_object* v_mctx_6050_; lean_object* v_zetaDeltaFVarIds_6051_; lean_object* v_postponed_6052_; lean_object* v_diag_6053_; lean_object* v___x_6055_; uint8_t v_isShared_6056_; uint8_t v_isSharedCheck_6091_; 
v___x_6048_ = lean_st_ref_put(v___y_6023_, v___x_6047_);
v___x_6049_ = lean_st_ref_take(v___y_6021_);
v_mctx_6050_ = lean_ctor_get(v___x_6049_, 0);
v_zetaDeltaFVarIds_6051_ = lean_ctor_get(v___x_6049_, 2);
v_postponed_6052_ = lean_ctor_get(v___x_6049_, 3);
v_diag_6053_ = lean_ctor_get(v___x_6049_, 4);
v_isSharedCheck_6091_ = !lean_is_exclusive(v___x_6049_);
if (v_isSharedCheck_6091_ == 0)
{
lean_object* v_unused_6092_; 
v_unused_6092_ = lean_ctor_get(v___x_6049_, 1);
lean_dec(v_unused_6092_);
v___x_6055_ = v___x_6049_;
v_isShared_6056_ = v_isSharedCheck_6091_;
goto v_resetjp_6054_;
}
else
{
lean_inc(v_diag_6053_);
lean_inc(v_postponed_6052_);
lean_inc(v_zetaDeltaFVarIds_6051_);
lean_inc(v_mctx_6050_);
lean_dec(v___x_6049_);
v___x_6055_ = lean_box(0);
v_isShared_6056_ = v_isSharedCheck_6091_;
goto v_resetjp_6054_;
}
v_resetjp_6054_:
{
lean_object* v___x_6057_; lean_object* v___x_6059_; 
v___x_6057_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3);
if (v_isShared_6056_ == 0)
{
lean_ctor_set(v___x_6055_, 1, v___x_6057_);
v___x_6059_ = v___x_6055_;
goto v_reusejp_6058_;
}
else
{
lean_object* v_reuseFailAlloc_6090_; 
v_reuseFailAlloc_6090_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6090_, 0, v_mctx_6050_);
lean_ctor_set(v_reuseFailAlloc_6090_, 1, v___x_6057_);
lean_ctor_set(v_reuseFailAlloc_6090_, 2, v_zetaDeltaFVarIds_6051_);
lean_ctor_set(v_reuseFailAlloc_6090_, 3, v_postponed_6052_);
lean_ctor_set(v_reuseFailAlloc_6090_, 4, v_diag_6053_);
v___x_6059_ = v_reuseFailAlloc_6090_;
goto v_reusejp_6058_;
}
v_reusejp_6058_:
{
lean_object* v___x_6060_; lean_object* v_r_6061_; 
v___x_6060_ = lean_st_ref_put(v___y_6021_, v___x_6059_);
lean_inc(v___y_6023_);
lean_inc_ref(v___y_6022_);
lean_inc(v___y_6021_);
lean_inc_ref(v___y_6020_);
v_r_6061_ = lean_apply_5(v_x_6018_, v___y_6020_, v___y_6021_, v___y_6022_, v___y_6023_, lean_box(0));
if (lean_obj_tag(v_r_6061_) == 0)
{
lean_object* v_a_6062_; lean_object* v___x_6064_; uint8_t v_isShared_6065_; uint8_t v_isSharedCheck_6078_; 
v_a_6062_ = lean_ctor_get(v_r_6061_, 0);
v_isSharedCheck_6078_ = !lean_is_exclusive(v_r_6061_);
if (v_isSharedCheck_6078_ == 0)
{
v___x_6064_ = v_r_6061_;
v_isShared_6065_ = v_isSharedCheck_6078_;
goto v_resetjp_6063_;
}
else
{
lean_inc(v_a_6062_);
lean_dec(v_r_6061_);
v___x_6064_ = lean_box(0);
v_isShared_6065_ = v_isSharedCheck_6078_;
goto v_resetjp_6063_;
}
v_resetjp_6063_:
{
lean_object* v___x_6067_; 
lean_inc(v_a_6062_);
if (v_isShared_6065_ == 0)
{
lean_ctor_set_tag(v___x_6064_, 1);
v___x_6067_ = v___x_6064_;
goto v_reusejp_6066_;
}
else
{
lean_object* v_reuseFailAlloc_6077_; 
v_reuseFailAlloc_6077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6077_, 0, v_a_6062_);
v___x_6067_ = v_reuseFailAlloc_6077_;
goto v_reusejp_6066_;
}
v_reusejp_6066_:
{
lean_object* v___x_6068_; lean_object* v___x_6070_; uint8_t v_isShared_6071_; uint8_t v_isSharedCheck_6075_; 
v___x_6068_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6023_, v_isExporting_6030_, v___x_6045_, v___y_6021_, v___x_6057_, v___x_6067_);
lean_dec_ref(v___x_6067_);
v_isSharedCheck_6075_ = !lean_is_exclusive(v___x_6068_);
if (v_isSharedCheck_6075_ == 0)
{
lean_object* v_unused_6076_; 
v_unused_6076_ = lean_ctor_get(v___x_6068_, 0);
lean_dec(v_unused_6076_);
v___x_6070_ = v___x_6068_;
v_isShared_6071_ = v_isSharedCheck_6075_;
goto v_resetjp_6069_;
}
else
{
lean_dec(v___x_6068_);
v___x_6070_ = lean_box(0);
v_isShared_6071_ = v_isSharedCheck_6075_;
goto v_resetjp_6069_;
}
v_resetjp_6069_:
{
lean_object* v___x_6073_; 
if (v_isShared_6071_ == 0)
{
lean_ctor_set(v___x_6070_, 0, v_a_6062_);
v___x_6073_ = v___x_6070_;
goto v_reusejp_6072_;
}
else
{
lean_object* v_reuseFailAlloc_6074_; 
v_reuseFailAlloc_6074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6074_, 0, v_a_6062_);
v___x_6073_ = v_reuseFailAlloc_6074_;
goto v_reusejp_6072_;
}
v_reusejp_6072_:
{
return v___x_6073_;
}
}
}
}
}
else
{
lean_object* v_a_6079_; lean_object* v___x_6080_; lean_object* v___x_6081_; lean_object* v___x_6083_; uint8_t v_isShared_6084_; uint8_t v_isSharedCheck_6088_; 
v_a_6079_ = lean_ctor_get(v_r_6061_, 0);
lean_inc(v_a_6079_);
lean_dec_ref_known(v_r_6061_, 1);
v___x_6080_ = lean_box(0);
v___x_6081_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6023_, v_isExporting_6030_, v___x_6045_, v___y_6021_, v___x_6057_, v___x_6080_);
v_isSharedCheck_6088_ = !lean_is_exclusive(v___x_6081_);
if (v_isSharedCheck_6088_ == 0)
{
lean_object* v_unused_6089_; 
v_unused_6089_ = lean_ctor_get(v___x_6081_, 0);
lean_dec(v_unused_6089_);
v___x_6083_ = v___x_6081_;
v_isShared_6084_ = v_isSharedCheck_6088_;
goto v_resetjp_6082_;
}
else
{
lean_dec(v___x_6081_);
v___x_6083_ = lean_box(0);
v_isShared_6084_ = v_isSharedCheck_6088_;
goto v_resetjp_6082_;
}
v_resetjp_6082_:
{
lean_object* v___x_6086_; 
if (v_isShared_6084_ == 0)
{
lean_ctor_set_tag(v___x_6083_, 1);
lean_ctor_set(v___x_6083_, 0, v_a_6079_);
v___x_6086_ = v___x_6083_;
goto v_reusejp_6085_;
}
else
{
lean_object* v_reuseFailAlloc_6087_; 
v_reuseFailAlloc_6087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6087_, 0, v_a_6079_);
v___x_6086_ = v_reuseFailAlloc_6087_;
goto v_reusejp_6085_;
}
v_reusejp_6085_:
{
return v___x_6086_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___boxed(lean_object* v_x_6098_, lean_object* v_isExporting_6099_, lean_object* v___y_6100_, lean_object* v___y_6101_, lean_object* v___y_6102_, lean_object* v___y_6103_, lean_object* v___y_6104_){
_start:
{
uint8_t v_isExporting_boxed_6105_; lean_object* v_res_6106_; 
v_isExporting_boxed_6105_ = lean_unbox(v_isExporting_6099_);
v_res_6106_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6098_, v_isExporting_boxed_6105_, v___y_6100_, v___y_6101_, v___y_6102_, v___y_6103_);
lean_dec(v___y_6103_);
lean_dec_ref(v___y_6102_);
lean_dec(v___y_6101_);
lean_dec_ref(v___y_6100_);
return v_res_6106_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(lean_object* v_x_6107_, uint8_t v_when_6108_, lean_object* v___y_6109_, lean_object* v___y_6110_, lean_object* v___y_6111_, lean_object* v___y_6112_){
_start:
{
if (v_when_6108_ == 0)
{
lean_object* v___x_6114_; 
lean_inc(v___y_6112_);
lean_inc_ref(v___y_6111_);
lean_inc(v___y_6110_);
lean_inc_ref(v___y_6109_);
v___x_6114_ = lean_apply_5(v_x_6107_, v___y_6109_, v___y_6110_, v___y_6111_, v___y_6112_, lean_box(0));
return v___x_6114_;
}
else
{
uint8_t v___x_6115_; lean_object* v___x_6116_; 
v___x_6115_ = 0;
v___x_6116_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6107_, v___x_6115_, v___y_6109_, v___y_6110_, v___y_6111_, v___y_6112_);
return v___x_6116_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg___boxed(lean_object* v_x_6117_, lean_object* v_when_6118_, lean_object* v___y_6119_, lean_object* v___y_6120_, lean_object* v___y_6121_, lean_object* v___y_6122_, lean_object* v___y_6123_){
_start:
{
uint8_t v_when_boxed_6124_; lean_object* v_res_6125_; 
v_when_boxed_6124_ = lean_unbox(v_when_6118_);
v_res_6125_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v_x_6117_, v_when_boxed_6124_, v___y_6119_, v___y_6120_, v___y_6121_, v___y_6122_);
lean_dec(v___y_6122_);
lean_dec_ref(v___y_6121_);
lean_dec(v___y_6120_);
lean_dec_ref(v___y_6119_);
return v_res_6125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals(lean_object* v_funNames_6126_, lean_object* v_argsPacker_6127_, lean_object* v_decrTactics_6128_, lean_object* v_value_6129_, lean_object* v_a_6130_, lean_object* v_a_6131_, lean_object* v_a_6132_, lean_object* v_a_6133_){
_start:
{
lean_object* v___f_6135_; uint8_t v___x_6136_; lean_object* v___x_6137_; 
v___f_6135_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_solveDecreasingGoals___lam__0___boxed), 9, 4);
lean_closure_set(v___f_6135_, 0, v_value_6129_);
lean_closure_set(v___f_6135_, 1, v_decrTactics_6128_);
lean_closure_set(v___f_6135_, 2, v_argsPacker_6127_);
lean_closure_set(v___f_6135_, 3, v_funNames_6126_);
v___x_6136_ = 1;
v___x_6137_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v___f_6135_, v___x_6136_, v_a_6130_, v_a_6131_, v_a_6132_, v_a_6133_);
return v___x_6137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___boxed(lean_object* v_funNames_6138_, lean_object* v_argsPacker_6139_, lean_object* v_decrTactics_6140_, lean_object* v_value_6141_, lean_object* v_a_6142_, lean_object* v_a_6143_, lean_object* v_a_6144_, lean_object* v_a_6145_, lean_object* v_a_6146_){
_start:
{
lean_object* v_res_6147_; 
v_res_6147_ = l_Lean_Elab_WF_solveDecreasingGoals(v_funNames_6138_, v_argsPacker_6139_, v_decrTactics_6140_, v_value_6141_, v_a_6142_, v_a_6143_, v_a_6144_, v_a_6145_);
lean_dec(v_a_6145_);
lean_dec_ref(v_a_6144_);
lean_dec(v_a_6143_);
lean_dec_ref(v_a_6142_);
return v_res_6147_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1(lean_object* v_00_u03b1_6148_, lean_object* v_msg_6149_, lean_object* v___y_6150_, lean_object* v___y_6151_, lean_object* v___y_6152_, lean_object* v___y_6153_, lean_object* v___y_6154_, lean_object* v___y_6155_){
_start:
{
lean_object* v___x_6157_; 
v___x_6157_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v_msg_6149_, v___y_6150_, v___y_6151_, v___y_6152_, v___y_6153_, v___y_6154_, v___y_6155_);
return v___x_6157_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___boxed(lean_object* v_00_u03b1_6158_, lean_object* v_msg_6159_, lean_object* v___y_6160_, lean_object* v___y_6161_, lean_object* v___y_6162_, lean_object* v___y_6163_, lean_object* v___y_6164_, lean_object* v___y_6165_, lean_object* v___y_6166_){
_start:
{
lean_object* v_res_6167_; 
v_res_6167_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1(v_00_u03b1_6158_, v_msg_6159_, v___y_6160_, v___y_6161_, v___y_6162_, v___y_6163_, v___y_6164_, v___y_6165_);
lean_dec(v___y_6165_);
lean_dec_ref(v___y_6164_);
lean_dec(v___y_6163_);
lean_dec_ref(v___y_6162_);
lean_dec(v___y_6161_);
lean_dec_ref(v___y_6160_);
return v_res_6167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4(lean_object* v___y_6168_, lean_object* v___y_6169_, lean_object* v___y_6170_, lean_object* v___y_6171_, lean_object* v___y_6172_, lean_object* v___y_6173_, lean_object* v___y_6174_, lean_object* v___y_6175_){
_start:
{
lean_object* v___x_6177_; 
v___x_6177_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_6175_);
return v___x_6177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___boxed(lean_object* v___y_6178_, lean_object* v___y_6179_, lean_object* v___y_6180_, lean_object* v___y_6181_, lean_object* v___y_6182_, lean_object* v___y_6183_, lean_object* v___y_6184_, lean_object* v___y_6185_, lean_object* v___y_6186_){
_start:
{
lean_object* v_res_6187_; 
v_res_6187_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4(v___y_6178_, v___y_6179_, v___y_6180_, v___y_6181_, v___y_6182_, v___y_6183_, v___y_6184_, v___y_6185_);
lean_dec(v___y_6185_);
lean_dec_ref(v___y_6184_);
lean_dec(v___y_6183_);
lean_dec_ref(v___y_6182_);
lean_dec(v___y_6181_);
lean_dec_ref(v___y_6180_);
lean_dec(v___y_6179_);
lean_dec_ref(v___y_6178_);
return v_res_6187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3(lean_object* v_00_u03b1_6188_, lean_object* v_x_6189_, lean_object* v_mkInfoTree_6190_, lean_object* v___y_6191_, lean_object* v___y_6192_, lean_object* v___y_6193_, lean_object* v___y_6194_, lean_object* v___y_6195_, lean_object* v___y_6196_, lean_object* v___y_6197_, lean_object* v___y_6198_){
_start:
{
lean_object* v___x_6200_; 
v___x_6200_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v_x_6189_, v_mkInfoTree_6190_, v___y_6191_, v___y_6192_, v___y_6193_, v___y_6194_, v___y_6195_, v___y_6196_, v___y_6197_, v___y_6198_);
return v___x_6200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___boxed(lean_object* v_00_u03b1_6201_, lean_object* v_x_6202_, lean_object* v_mkInfoTree_6203_, lean_object* v___y_6204_, lean_object* v___y_6205_, lean_object* v___y_6206_, lean_object* v___y_6207_, lean_object* v___y_6208_, lean_object* v___y_6209_, lean_object* v___y_6210_, lean_object* v___y_6211_, lean_object* v___y_6212_){
_start:
{
lean_object* v_res_6213_; 
v_res_6213_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3(v_00_u03b1_6201_, v_x_6202_, v_mkInfoTree_6203_, v___y_6204_, v___y_6205_, v___y_6206_, v___y_6207_, v___y_6208_, v___y_6209_, v___y_6210_, v___y_6211_);
lean_dec(v___y_6211_);
lean_dec_ref(v___y_6210_);
lean_dec(v___y_6209_);
lean_dec_ref(v___y_6208_);
lean_dec(v___y_6207_);
lean_dec_ref(v___y_6206_);
lean_dec(v___y_6205_);
lean_dec_ref(v___y_6204_);
return v_res_6213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5(lean_object* v_as_6214_, size_t v_i_6215_, size_t v_stop_6216_, lean_object* v_b_6217_, lean_object* v___y_6218_, lean_object* v___y_6219_, lean_object* v___y_6220_, lean_object* v___y_6221_, lean_object* v___y_6222_, lean_object* v___y_6223_){
_start:
{
lean_object* v___x_6225_; 
v___x_6225_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v_as_6214_, v_i_6215_, v_stop_6216_, v_b_6217_, v___y_6220_, v___y_6221_, v___y_6222_, v___y_6223_);
return v___x_6225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___boxed(lean_object* v_as_6226_, lean_object* v_i_6227_, lean_object* v_stop_6228_, lean_object* v_b_6229_, lean_object* v___y_6230_, lean_object* v___y_6231_, lean_object* v___y_6232_, lean_object* v___y_6233_, lean_object* v___y_6234_, lean_object* v___y_6235_, lean_object* v___y_6236_){
_start:
{
size_t v_i_boxed_6237_; size_t v_stop_boxed_6238_; lean_object* v_res_6239_; 
v_i_boxed_6237_ = lean_unbox_usize(v_i_6227_);
lean_dec(v_i_6227_);
v_stop_boxed_6238_ = lean_unbox_usize(v_stop_6228_);
lean_dec(v_stop_6228_);
v_res_6239_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5(v_as_6226_, v_i_boxed_6237_, v_stop_boxed_6238_, v_b_6229_, v___y_6230_, v___y_6231_, v___y_6232_, v___y_6233_, v___y_6234_, v___y_6235_);
lean_dec(v___y_6235_);
lean_dec_ref(v___y_6234_);
lean_dec(v___y_6233_);
lean_dec_ref(v___y_6232_);
lean_dec(v___y_6231_);
lean_dec_ref(v___y_6230_);
lean_dec_ref(v_as_6226_);
return v_res_6239_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10(lean_object* v_00_u03b1_6240_, lean_object* v_x_6241_, uint8_t v_isExporting_6242_, lean_object* v___y_6243_, lean_object* v___y_6244_, lean_object* v___y_6245_, lean_object* v___y_6246_){
_start:
{
lean_object* v___x_6248_; 
v___x_6248_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6241_, v_isExporting_6242_, v___y_6243_, v___y_6244_, v___y_6245_, v___y_6246_);
return v___x_6248_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___boxed(lean_object* v_00_u03b1_6249_, lean_object* v_x_6250_, lean_object* v_isExporting_6251_, lean_object* v___y_6252_, lean_object* v___y_6253_, lean_object* v___y_6254_, lean_object* v___y_6255_, lean_object* v___y_6256_){
_start:
{
uint8_t v_isExporting_boxed_6257_; lean_object* v_res_6258_; 
v_isExporting_boxed_6257_ = lean_unbox(v_isExporting_6251_);
v_res_6258_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10(v_00_u03b1_6249_, v_x_6250_, v_isExporting_boxed_6257_, v___y_6252_, v___y_6253_, v___y_6254_, v___y_6255_);
lean_dec(v___y_6255_);
lean_dec_ref(v___y_6254_);
lean_dec(v___y_6253_);
lean_dec_ref(v___y_6252_);
return v_res_6258_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8(lean_object* v_00_u03b1_6259_, lean_object* v_x_6260_, uint8_t v_when_6261_, lean_object* v___y_6262_, lean_object* v___y_6263_, lean_object* v___y_6264_, lean_object* v___y_6265_){
_start:
{
lean_object* v___x_6267_; 
v___x_6267_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v_x_6260_, v_when_6261_, v___y_6262_, v___y_6263_, v___y_6264_, v___y_6265_);
return v___x_6267_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___boxed(lean_object* v_00_u03b1_6268_, lean_object* v_x_6269_, lean_object* v_when_6270_, lean_object* v___y_6271_, lean_object* v___y_6272_, lean_object* v___y_6273_, lean_object* v___y_6274_, lean_object* v___y_6275_){
_start:
{
uint8_t v_when_boxed_6276_; lean_object* v_res_6277_; 
v_when_boxed_6276_ = lean_unbox(v_when_6270_);
v_res_6277_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8(v_00_u03b1_6268_, v_x_6269_, v_when_boxed_6276_, v___y_6271_, v___y_6272_, v___y_6273_, v___y_6274_);
lean_dec(v___y_6274_);
lean_dec_ref(v___y_6273_);
lean_dec(v___y_6272_);
lean_dec_ref(v___y_6271_);
return v_res_6277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1(lean_object* v_msgData_6278_, lean_object* v_macroStack_6279_, lean_object* v___y_6280_, lean_object* v___y_6281_, lean_object* v___y_6282_, lean_object* v___y_6283_, lean_object* v___y_6284_, lean_object* v___y_6285_){
_start:
{
lean_object* v___x_6287_; 
v___x_6287_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_msgData_6278_, v_macroStack_6279_, v___y_6284_);
return v___x_6287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___boxed(lean_object* v_msgData_6288_, lean_object* v_macroStack_6289_, lean_object* v___y_6290_, lean_object* v___y_6291_, lean_object* v___y_6292_, lean_object* v___y_6293_, lean_object* v___y_6294_, lean_object* v___y_6295_, lean_object* v___y_6296_){
_start:
{
lean_object* v_res_6297_; 
v_res_6297_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1(v_msgData_6288_, v_macroStack_6289_, v___y_6290_, v___y_6291_, v___y_6292_, v___y_6293_, v___y_6294_, v___y_6295_);
lean_dec(v___y_6295_);
lean_dec_ref(v___y_6294_);
lean_dec(v___y_6293_);
lean_dec_ref(v___y_6292_);
lean_dec(v___y_6291_);
lean_dec_ref(v___y_6290_);
return v_res_6297_;
}
}
static lean_object* _init_l_Lean_Elab_WF_isNatLtWF___closed__4(void){
_start:
{
lean_object* v___x_6304_; lean_object* v___x_6305_; lean_object* v___x_6306_; 
v___x_6304_ = lean_box(0);
v___x_6305_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__3));
v___x_6306_ = l_Lean_mkConst(v___x_6305_, v___x_6304_);
return v___x_6306_;
}
}
static lean_object* _init_l_Lean_Elab_WF_isNatLtWF___closed__7(void){
_start:
{
lean_object* v___x_6311_; lean_object* v___x_6312_; lean_object* v___x_6313_; 
v___x_6311_ = lean_box(0);
v___x_6312_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__6));
v___x_6313_ = l_Lean_mkConst(v___x_6312_, v___x_6311_);
return v___x_6313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isNatLtWF(lean_object* v_wfRel_6314_, lean_object* v_a_6315_, lean_object* v_a_6316_, lean_object* v_a_6317_, lean_object* v_a_6318_){
_start:
{
lean_object* v___x_6320_; 
v___x_6320_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_wfRel_6314_, v_a_6316_);
if (lean_obj_tag(v___x_6320_) == 0)
{
lean_object* v_a_6321_; lean_object* v___x_6323_; uint8_t v_isShared_6324_; uint8_t v_isSharedCheck_6388_; 
v_a_6321_ = lean_ctor_get(v___x_6320_, 0);
v_isSharedCheck_6388_ = !lean_is_exclusive(v___x_6320_);
if (v_isSharedCheck_6388_ == 0)
{
v___x_6323_ = v___x_6320_;
v_isShared_6324_ = v_isSharedCheck_6388_;
goto v_resetjp_6322_;
}
else
{
lean_inc(v_a_6321_);
lean_dec(v___x_6320_);
v___x_6323_ = lean_box(0);
v_isShared_6324_ = v_isSharedCheck_6388_;
goto v_resetjp_6322_;
}
v_resetjp_6322_:
{
lean_object* v___x_6330_; uint8_t v___x_6331_; 
v___x_6330_ = l_Lean_Expr_cleanupAnnotations(v_a_6321_);
v___x_6331_ = l_Lean_Expr_isApp(v___x_6330_);
if (v___x_6331_ == 0)
{
lean_dec_ref(v___x_6330_);
goto v___jp_6325_;
}
else
{
lean_object* v_arg_6332_; lean_object* v___x_6333_; uint8_t v___x_6334_; 
v_arg_6332_ = lean_ctor_get(v___x_6330_, 1);
lean_inc_ref(v_arg_6332_);
v___x_6333_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6330_);
v___x_6334_ = l_Lean_Expr_isApp(v___x_6333_);
if (v___x_6334_ == 0)
{
lean_dec_ref(v___x_6333_);
lean_dec_ref(v_arg_6332_);
goto v___jp_6325_;
}
else
{
lean_object* v_arg_6335_; lean_object* v___x_6336_; uint8_t v___x_6337_; 
v_arg_6335_ = lean_ctor_get(v___x_6333_, 1);
lean_inc_ref(v_arg_6335_);
v___x_6336_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6333_);
v___x_6337_ = l_Lean_Expr_isApp(v___x_6336_);
if (v___x_6337_ == 0)
{
lean_dec_ref(v___x_6336_);
lean_dec_ref(v_arg_6335_);
lean_dec_ref(v_arg_6332_);
goto v___jp_6325_;
}
else
{
lean_object* v_arg_6338_; lean_object* v___x_6339_; uint8_t v___x_6340_; 
v_arg_6338_ = lean_ctor_get(v___x_6336_, 1);
lean_inc_ref(v_arg_6338_);
v___x_6339_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6336_);
v___x_6340_ = l_Lean_Expr_isApp(v___x_6339_);
if (v___x_6340_ == 0)
{
lean_dec_ref(v___x_6339_);
lean_dec_ref(v_arg_6338_);
lean_dec_ref(v_arg_6335_);
lean_dec_ref(v_arg_6332_);
goto v___jp_6325_;
}
else
{
lean_object* v___x_6341_; lean_object* v___x_6342_; uint8_t v___x_6343_; 
v___x_6341_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6339_);
v___x_6342_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__1));
v___x_6343_ = l_Lean_Expr_isConstOf(v___x_6341_, v___x_6342_);
lean_dec_ref(v___x_6341_);
if (v___x_6343_ == 0)
{
lean_dec_ref(v_arg_6338_);
lean_dec_ref(v_arg_6335_);
lean_dec_ref(v_arg_6332_);
goto v___jp_6325_;
}
else
{
lean_object* v___x_6344_; lean_object* v___x_6345_; 
lean_del_object(v___x_6323_);
v___x_6344_ = lean_obj_once(&l_Lean_Elab_WF_isNatLtWF___closed__4, &l_Lean_Elab_WF_isNatLtWF___closed__4_once, _init_l_Lean_Elab_WF_isNatLtWF___closed__4);
v___x_6345_ = l_Lean_Meta_isExprDefEq(v_arg_6338_, v___x_6344_, v_a_6315_, v_a_6316_, v_a_6317_, v_a_6318_);
if (lean_obj_tag(v___x_6345_) == 0)
{
lean_object* v_a_6346_; lean_object* v___x_6348_; uint8_t v_isShared_6349_; uint8_t v_isSharedCheck_6379_; 
v_a_6346_ = lean_ctor_get(v___x_6345_, 0);
v_isSharedCheck_6379_ = !lean_is_exclusive(v___x_6345_);
if (v_isSharedCheck_6379_ == 0)
{
v___x_6348_ = v___x_6345_;
v_isShared_6349_ = v_isSharedCheck_6379_;
goto v_resetjp_6347_;
}
else
{
lean_inc(v_a_6346_);
lean_dec(v___x_6345_);
v___x_6348_ = lean_box(0);
v_isShared_6349_ = v_isSharedCheck_6379_;
goto v_resetjp_6347_;
}
v_resetjp_6347_:
{
uint8_t v___x_6350_; 
v___x_6350_ = lean_unbox(v_a_6346_);
lean_dec(v_a_6346_);
if (v___x_6350_ == 0)
{
lean_object* v___x_6351_; lean_object* v___x_6353_; 
lean_dec_ref(v_arg_6335_);
lean_dec_ref(v_arg_6332_);
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
else
{
lean_object* v___x_6355_; lean_object* v___x_6356_; 
lean_del_object(v___x_6348_);
v___x_6355_ = lean_obj_once(&l_Lean_Elab_WF_isNatLtWF___closed__7, &l_Lean_Elab_WF_isNatLtWF___closed__7_once, _init_l_Lean_Elab_WF_isNatLtWF___closed__7);
v___x_6356_ = l_Lean_Meta_isExprDefEq(v_arg_6332_, v___x_6355_, v_a_6315_, v_a_6316_, v_a_6317_, v_a_6318_);
if (lean_obj_tag(v___x_6356_) == 0)
{
lean_object* v_a_6357_; lean_object* v___x_6359_; uint8_t v_isShared_6360_; uint8_t v_isSharedCheck_6370_; 
v_a_6357_ = lean_ctor_get(v___x_6356_, 0);
v_isSharedCheck_6370_ = !lean_is_exclusive(v___x_6356_);
if (v_isSharedCheck_6370_ == 0)
{
v___x_6359_ = v___x_6356_;
v_isShared_6360_ = v_isSharedCheck_6370_;
goto v_resetjp_6358_;
}
else
{
lean_inc(v_a_6357_);
lean_dec(v___x_6356_);
v___x_6359_ = lean_box(0);
v_isShared_6360_ = v_isSharedCheck_6370_;
goto v_resetjp_6358_;
}
v_resetjp_6358_:
{
uint8_t v___x_6361_; 
v___x_6361_ = lean_unbox(v_a_6357_);
lean_dec(v_a_6357_);
if (v___x_6361_ == 0)
{
lean_object* v___x_6362_; lean_object* v___x_6364_; 
lean_dec_ref(v_arg_6335_);
v___x_6362_ = lean_box(0);
if (v_isShared_6360_ == 0)
{
lean_ctor_set(v___x_6359_, 0, v___x_6362_);
v___x_6364_ = v___x_6359_;
goto v_reusejp_6363_;
}
else
{
lean_object* v_reuseFailAlloc_6365_; 
v_reuseFailAlloc_6365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6365_, 0, v___x_6362_);
v___x_6364_ = v_reuseFailAlloc_6365_;
goto v_reusejp_6363_;
}
v_reusejp_6363_:
{
return v___x_6364_;
}
}
else
{
lean_object* v___x_6366_; lean_object* v___x_6368_; 
v___x_6366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6366_, 0, v_arg_6335_);
if (v_isShared_6360_ == 0)
{
lean_ctor_set(v___x_6359_, 0, v___x_6366_);
v___x_6368_ = v___x_6359_;
goto v_reusejp_6367_;
}
else
{
lean_object* v_reuseFailAlloc_6369_; 
v_reuseFailAlloc_6369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6369_, 0, v___x_6366_);
v___x_6368_ = v_reuseFailAlloc_6369_;
goto v_reusejp_6367_;
}
v_reusejp_6367_:
{
return v___x_6368_;
}
}
}
}
else
{
lean_object* v_a_6371_; lean_object* v___x_6373_; uint8_t v_isShared_6374_; uint8_t v_isSharedCheck_6378_; 
lean_dec_ref(v_arg_6335_);
v_a_6371_ = lean_ctor_get(v___x_6356_, 0);
v_isSharedCheck_6378_ = !lean_is_exclusive(v___x_6356_);
if (v_isSharedCheck_6378_ == 0)
{
v___x_6373_ = v___x_6356_;
v_isShared_6374_ = v_isSharedCheck_6378_;
goto v_resetjp_6372_;
}
else
{
lean_inc(v_a_6371_);
lean_dec(v___x_6356_);
v___x_6373_ = lean_box(0);
v_isShared_6374_ = v_isSharedCheck_6378_;
goto v_resetjp_6372_;
}
v_resetjp_6372_:
{
lean_object* v___x_6376_; 
if (v_isShared_6374_ == 0)
{
v___x_6376_ = v___x_6373_;
goto v_reusejp_6375_;
}
else
{
lean_object* v_reuseFailAlloc_6377_; 
v_reuseFailAlloc_6377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6377_, 0, v_a_6371_);
v___x_6376_ = v_reuseFailAlloc_6377_;
goto v_reusejp_6375_;
}
v_reusejp_6375_:
{
return v___x_6376_;
}
}
}
}
}
}
else
{
lean_object* v_a_6380_; lean_object* v___x_6382_; uint8_t v_isShared_6383_; uint8_t v_isSharedCheck_6387_; 
lean_dec_ref(v_arg_6335_);
lean_dec_ref(v_arg_6332_);
v_a_6380_ = lean_ctor_get(v___x_6345_, 0);
v_isSharedCheck_6387_ = !lean_is_exclusive(v___x_6345_);
if (v_isSharedCheck_6387_ == 0)
{
v___x_6382_ = v___x_6345_;
v_isShared_6383_ = v_isSharedCheck_6387_;
goto v_resetjp_6381_;
}
else
{
lean_inc(v_a_6380_);
lean_dec(v___x_6345_);
v___x_6382_ = lean_box(0);
v_isShared_6383_ = v_isSharedCheck_6387_;
goto v_resetjp_6381_;
}
v_resetjp_6381_:
{
lean_object* v___x_6385_; 
if (v_isShared_6383_ == 0)
{
v___x_6385_ = v___x_6382_;
goto v_reusejp_6384_;
}
else
{
lean_object* v_reuseFailAlloc_6386_; 
v_reuseFailAlloc_6386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6386_, 0, v_a_6380_);
v___x_6385_ = v_reuseFailAlloc_6386_;
goto v_reusejp_6384_;
}
v_reusejp_6384_:
{
return v___x_6385_;
}
}
}
}
}
}
}
}
v___jp_6325_:
{
lean_object* v___x_6326_; lean_object* v___x_6328_; 
v___x_6326_ = lean_box(0);
if (v_isShared_6324_ == 0)
{
lean_ctor_set(v___x_6323_, 0, v___x_6326_);
v___x_6328_ = v___x_6323_;
goto v_reusejp_6327_;
}
else
{
lean_object* v_reuseFailAlloc_6329_; 
v_reuseFailAlloc_6329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6329_, 0, v___x_6326_);
v___x_6328_ = v_reuseFailAlloc_6329_;
goto v_reusejp_6327_;
}
v_reusejp_6327_:
{
return v___x_6328_;
}
}
}
}
else
{
lean_object* v_a_6389_; lean_object* v___x_6391_; uint8_t v_isShared_6392_; uint8_t v_isSharedCheck_6396_; 
v_a_6389_ = lean_ctor_get(v___x_6320_, 0);
v_isSharedCheck_6396_ = !lean_is_exclusive(v___x_6320_);
if (v_isSharedCheck_6396_ == 0)
{
v___x_6391_ = v___x_6320_;
v_isShared_6392_ = v_isSharedCheck_6396_;
goto v_resetjp_6390_;
}
else
{
lean_inc(v_a_6389_);
lean_dec(v___x_6320_);
v___x_6391_ = lean_box(0);
v_isShared_6392_ = v_isSharedCheck_6396_;
goto v_resetjp_6390_;
}
v_resetjp_6390_:
{
lean_object* v___x_6394_; 
if (v_isShared_6392_ == 0)
{
v___x_6394_ = v___x_6391_;
goto v_reusejp_6393_;
}
else
{
lean_object* v_reuseFailAlloc_6395_; 
v_reuseFailAlloc_6395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6395_, 0, v_a_6389_);
v___x_6394_ = v_reuseFailAlloc_6395_;
goto v_reusejp_6393_;
}
v_reusejp_6393_:
{
return v___x_6394_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isNatLtWF___boxed(lean_object* v_wfRel_6397_, lean_object* v_a_6398_, lean_object* v_a_6399_, lean_object* v_a_6400_, lean_object* v_a_6401_, lean_object* v_a_6402_){
_start:
{
lean_object* v_res_6403_; 
v_res_6403_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_6397_, v_a_6398_, v_a_6399_, v_a_6400_, v_a_6401_);
lean_dec(v_a_6401_);
lean_dec_ref(v_a_6400_);
lean_dec(v_a_6399_);
lean_dec_ref(v_a_6398_);
return v_res_6403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(lean_object* v_type_6404_, lean_object* v_maxFVars_x3f_6405_, lean_object* v_k_6406_, uint8_t v_cleanupAnnotations_6407_, uint8_t v_whnfType_6408_, lean_object* v___y_6409_, lean_object* v___y_6410_, lean_object* v___y_6411_, lean_object* v___y_6412_, lean_object* v___y_6413_, lean_object* v___y_6414_){
_start:
{
lean_object* v___f_6416_; lean_object* v___x_6417_; 
lean_inc(v___y_6410_);
lean_inc_ref(v___y_6409_);
v___f_6416_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_6416_, 0, v_k_6406_);
lean_closure_set(v___f_6416_, 1, v___y_6409_);
lean_closure_set(v___f_6416_, 2, v___y_6410_);
v___x_6417_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_6404_, v_maxFVars_x3f_6405_, v___f_6416_, v_cleanupAnnotations_6407_, v_whnfType_6408_, v___y_6411_, v___y_6412_, v___y_6413_, v___y_6414_);
if (lean_obj_tag(v___x_6417_) == 0)
{
return v___x_6417_;
}
else
{
lean_object* v_a_6418_; lean_object* v___x_6420_; uint8_t v_isShared_6421_; uint8_t v_isSharedCheck_6425_; 
v_a_6418_ = lean_ctor_get(v___x_6417_, 0);
v_isSharedCheck_6425_ = !lean_is_exclusive(v___x_6417_);
if (v_isSharedCheck_6425_ == 0)
{
v___x_6420_ = v___x_6417_;
v_isShared_6421_ = v_isSharedCheck_6425_;
goto v_resetjp_6419_;
}
else
{
lean_inc(v_a_6418_);
lean_dec(v___x_6417_);
v___x_6420_ = lean_box(0);
v_isShared_6421_ = v_isSharedCheck_6425_;
goto v_resetjp_6419_;
}
v_resetjp_6419_:
{
lean_object* v___x_6423_; 
if (v_isShared_6421_ == 0)
{
v___x_6423_ = v___x_6420_;
goto v_reusejp_6422_;
}
else
{
lean_object* v_reuseFailAlloc_6424_; 
v_reuseFailAlloc_6424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6424_, 0, v_a_6418_);
v___x_6423_ = v_reuseFailAlloc_6424_;
goto v_reusejp_6422_;
}
v_reusejp_6422_:
{
return v___x_6423_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg___boxed(lean_object* v_type_6426_, lean_object* v_maxFVars_x3f_6427_, lean_object* v_k_6428_, lean_object* v_cleanupAnnotations_6429_, lean_object* v_whnfType_6430_, lean_object* v___y_6431_, lean_object* v___y_6432_, lean_object* v___y_6433_, lean_object* v___y_6434_, lean_object* v___y_6435_, lean_object* v___y_6436_, lean_object* v___y_6437_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_6438_; uint8_t v_whnfType_boxed_6439_; lean_object* v_res_6440_; 
v_cleanupAnnotations_boxed_6438_ = lean_unbox(v_cleanupAnnotations_6429_);
v_whnfType_boxed_6439_ = lean_unbox(v_whnfType_6430_);
v_res_6440_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_type_6426_, v_maxFVars_x3f_6427_, v_k_6428_, v_cleanupAnnotations_boxed_6438_, v_whnfType_boxed_6439_, v___y_6431_, v___y_6432_, v___y_6433_, v___y_6434_, v___y_6435_, v___y_6436_);
lean_dec(v___y_6436_);
lean_dec_ref(v___y_6435_);
lean_dec(v___y_6434_);
lean_dec_ref(v___y_6433_);
lean_dec(v___y_6432_);
lean_dec_ref(v___y_6431_);
return v_res_6440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0(lean_object* v_00_u03b1_6441_, lean_object* v_type_6442_, lean_object* v_maxFVars_x3f_6443_, lean_object* v_k_6444_, uint8_t v_cleanupAnnotations_6445_, uint8_t v_whnfType_6446_, lean_object* v___y_6447_, lean_object* v___y_6448_, lean_object* v___y_6449_, lean_object* v___y_6450_, lean_object* v___y_6451_, lean_object* v___y_6452_){
_start:
{
lean_object* v___x_6454_; 
v___x_6454_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_type_6442_, v_maxFVars_x3f_6443_, v_k_6444_, v_cleanupAnnotations_6445_, v_whnfType_6446_, v___y_6447_, v___y_6448_, v___y_6449_, v___y_6450_, v___y_6451_, v___y_6452_);
return v___x_6454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___boxed(lean_object* v_00_u03b1_6455_, lean_object* v_type_6456_, lean_object* v_maxFVars_x3f_6457_, lean_object* v_k_6458_, lean_object* v_cleanupAnnotations_6459_, lean_object* v_whnfType_6460_, lean_object* v___y_6461_, lean_object* v___y_6462_, lean_object* v___y_6463_, lean_object* v___y_6464_, lean_object* v___y_6465_, lean_object* v___y_6466_, lean_object* v___y_6467_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_6468_; uint8_t v_whnfType_boxed_6469_; lean_object* v_res_6470_; 
v_cleanupAnnotations_boxed_6468_ = lean_unbox(v_cleanupAnnotations_6459_);
v_whnfType_boxed_6469_ = lean_unbox(v_whnfType_6460_);
v_res_6470_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0(v_00_u03b1_6455_, v_type_6456_, v_maxFVars_x3f_6457_, v_k_6458_, v_cleanupAnnotations_boxed_6468_, v_whnfType_boxed_6469_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_, v___y_6465_, v___y_6466_);
lean_dec(v___y_6466_);
lean_dec_ref(v___y_6465_);
lean_dec(v___y_6464_);
lean_dec_ref(v___y_6463_);
lean_dec(v___y_6462_);
lean_dec_ref(v___y_6461_);
return v_res_6470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(lean_object* v_lctx_6471_, lean_object* v_x_6472_, lean_object* v___y_6473_, lean_object* v___y_6474_, lean_object* v___y_6475_, lean_object* v___y_6476_, lean_object* v___y_6477_, lean_object* v___y_6478_){
_start:
{
lean_object* v_keyedConfig_6480_; uint8_t v_trackZetaDelta_6481_; lean_object* v_zetaDeltaSet_6482_; lean_object* v_localInstances_6483_; lean_object* v_defEqCtx_x3f_6484_; lean_object* v_synthPendingDepth_6485_; lean_object* v_customCanUnfoldPredicate_x3f_6486_; uint8_t v_univApprox_6487_; uint8_t v_inTypeClassResolution_6488_; uint8_t v_cacheInferType_6489_; lean_object* v___x_6490_; lean_object* v___x_6491_; 
v_keyedConfig_6480_ = lean_ctor_get(v___y_6475_, 0);
v_trackZetaDelta_6481_ = lean_ctor_get_uint8(v___y_6475_, sizeof(void*)*7);
v_zetaDeltaSet_6482_ = lean_ctor_get(v___y_6475_, 1);
v_localInstances_6483_ = lean_ctor_get(v___y_6475_, 3);
v_defEqCtx_x3f_6484_ = lean_ctor_get(v___y_6475_, 4);
v_synthPendingDepth_6485_ = lean_ctor_get(v___y_6475_, 5);
v_customCanUnfoldPredicate_x3f_6486_ = lean_ctor_get(v___y_6475_, 6);
v_univApprox_6487_ = lean_ctor_get_uint8(v___y_6475_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_6488_ = lean_ctor_get_uint8(v___y_6475_, sizeof(void*)*7 + 2);
v_cacheInferType_6489_ = lean_ctor_get_uint8(v___y_6475_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_6486_);
lean_inc(v_synthPendingDepth_6485_);
lean_inc(v_defEqCtx_x3f_6484_);
lean_inc_ref(v_localInstances_6483_);
lean_inc(v_zetaDeltaSet_6482_);
lean_inc_ref(v_keyedConfig_6480_);
v___x_6490_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6490_, 0, v_keyedConfig_6480_);
lean_ctor_set(v___x_6490_, 1, v_zetaDeltaSet_6482_);
lean_ctor_set(v___x_6490_, 2, v_lctx_6471_);
lean_ctor_set(v___x_6490_, 3, v_localInstances_6483_);
lean_ctor_set(v___x_6490_, 4, v_defEqCtx_x3f_6484_);
lean_ctor_set(v___x_6490_, 5, v_synthPendingDepth_6485_);
lean_ctor_set(v___x_6490_, 6, v_customCanUnfoldPredicate_x3f_6486_);
lean_ctor_set_uint8(v___x_6490_, sizeof(void*)*7, v_trackZetaDelta_6481_);
lean_ctor_set_uint8(v___x_6490_, sizeof(void*)*7 + 1, v_univApprox_6487_);
lean_ctor_set_uint8(v___x_6490_, sizeof(void*)*7 + 2, v_inTypeClassResolution_6488_);
lean_ctor_set_uint8(v___x_6490_, sizeof(void*)*7 + 3, v_cacheInferType_6489_);
lean_inc(v___y_6478_);
lean_inc_ref(v___y_6477_);
lean_inc(v___y_6476_);
lean_inc(v___y_6474_);
lean_inc_ref(v___y_6473_);
v___x_6491_ = lean_apply_7(v_x_6472_, v___y_6473_, v___y_6474_, v___x_6490_, v___y_6476_, v___y_6477_, v___y_6478_, lean_box(0));
if (lean_obj_tag(v___x_6491_) == 0)
{
lean_object* v_a_6492_; lean_object* v___x_6494_; uint8_t v_isShared_6495_; uint8_t v_isSharedCheck_6499_; 
v_a_6492_ = lean_ctor_get(v___x_6491_, 0);
v_isSharedCheck_6499_ = !lean_is_exclusive(v___x_6491_);
if (v_isSharedCheck_6499_ == 0)
{
v___x_6494_ = v___x_6491_;
v_isShared_6495_ = v_isSharedCheck_6499_;
goto v_resetjp_6493_;
}
else
{
lean_inc(v_a_6492_);
lean_dec(v___x_6491_);
v___x_6494_ = lean_box(0);
v_isShared_6495_ = v_isSharedCheck_6499_;
goto v_resetjp_6493_;
}
v_resetjp_6493_:
{
lean_object* v___x_6497_; 
if (v_isShared_6495_ == 0)
{
v___x_6497_ = v___x_6494_;
goto v_reusejp_6496_;
}
else
{
lean_object* v_reuseFailAlloc_6498_; 
v_reuseFailAlloc_6498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6498_, 0, v_a_6492_);
v___x_6497_ = v_reuseFailAlloc_6498_;
goto v_reusejp_6496_;
}
v_reusejp_6496_:
{
return v___x_6497_;
}
}
}
else
{
return v___x_6491_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg___boxed(lean_object* v_lctx_6500_, lean_object* v_x_6501_, lean_object* v___y_6502_, lean_object* v___y_6503_, lean_object* v___y_6504_, lean_object* v___y_6505_, lean_object* v___y_6506_, lean_object* v___y_6507_, lean_object* v___y_6508_){
_start:
{
lean_object* v_res_6509_; 
v_res_6509_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v_lctx_6500_, v_x_6501_, v___y_6502_, v___y_6503_, v___y_6504_, v___y_6505_, v___y_6506_, v___y_6507_);
lean_dec(v___y_6507_);
lean_dec_ref(v___y_6506_);
lean_dec(v___y_6505_);
lean_dec_ref(v___y_6504_);
lean_dec(v___y_6503_);
lean_dec_ref(v___y_6502_);
return v_res_6509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1(lean_object* v_00_u03b1_6510_, lean_object* v_lctx_6511_, lean_object* v_x_6512_, lean_object* v___y_6513_, lean_object* v___y_6514_, lean_object* v___y_6515_, lean_object* v___y_6516_, lean_object* v___y_6517_, lean_object* v___y_6518_){
_start:
{
lean_object* v___x_6520_; 
v___x_6520_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v_lctx_6511_, v_x_6512_, v___y_6513_, v___y_6514_, v___y_6515_, v___y_6516_, v___y_6517_, v___y_6518_);
return v___x_6520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___boxed(lean_object* v_00_u03b1_6521_, lean_object* v_lctx_6522_, lean_object* v_x_6523_, lean_object* v___y_6524_, lean_object* v___y_6525_, lean_object* v___y_6526_, lean_object* v___y_6527_, lean_object* v___y_6528_, lean_object* v___y_6529_, lean_object* v___y_6530_){
_start:
{
lean_object* v_res_6531_; 
v_res_6531_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1(v_00_u03b1_6521_, v_lctx_6522_, v_x_6523_, v___y_6524_, v___y_6525_, v___y_6526_, v___y_6527_, v___y_6528_, v___y_6529_);
lean_dec(v___y_6529_);
lean_dec_ref(v___y_6528_);
lean_dec(v___y_6527_);
lean_dec_ref(v___y_6526_);
lean_dec(v___y_6525_);
lean_dec_ref(v___y_6524_);
return v_res_6531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__0(lean_object* v___x_6548_, lean_object* v___x_6549_, lean_object* v_wfRel_6550_, lean_object* v_x_6551_, lean_object* v_type_6552_, lean_object* v___y_6553_, lean_object* v___y_6554_, lean_object* v___y_6555_, lean_object* v___y_6556_, lean_object* v___y_6557_, lean_object* v___y_6558_){
_start:
{
lean_object* v___x_6560_; lean_object* v___x_6561_; lean_object* v___x_6562_; lean_object* v___x_6563_; 
v___x_6560_ = lean_unsigned_to_nat(0u);
v___x_6561_ = lean_array_get_borrowed(v___x_6548_, v_x_6551_, v___x_6560_);
v___x_6562_ = l_Lean_Expr_fvarId_x21(v___x_6561_);
v___x_6563_ = l_Lean_FVarId_getUserName___redArg(v___x_6562_, v___y_6555_, v___y_6557_, v___y_6558_);
if (lean_obj_tag(v___x_6563_) == 0)
{
lean_object* v_a_6564_; lean_object* v___x_6565_; 
v_a_6564_ = lean_ctor_get(v___x_6563_, 0);
lean_inc(v_a_6564_);
lean_dec_ref_known(v___x_6563_, 1);
lean_inc(v___y_6558_);
lean_inc_ref(v___y_6557_);
lean_inc(v___y_6556_);
lean_inc_ref(v___y_6555_);
lean_inc(v___x_6561_);
v___x_6565_ = lean_infer_type(v___x_6561_, v___y_6555_, v___y_6556_, v___y_6557_, v___y_6558_);
if (lean_obj_tag(v___x_6565_) == 0)
{
lean_object* v_a_6566_; lean_object* v___x_6567_; 
v_a_6566_ = lean_ctor_get(v___x_6565_, 0);
lean_inc_n(v_a_6566_, 2);
lean_dec_ref_known(v___x_6565_, 1);
v___x_6567_ = l_Lean_Meta_getLevel(v_a_6566_, v___y_6555_, v___y_6556_, v___y_6557_, v___y_6558_);
if (lean_obj_tag(v___x_6567_) == 0)
{
lean_object* v_a_6568_; lean_object* v___x_6569_; 
v_a_6568_ = lean_ctor_get(v___x_6567_, 0);
lean_inc(v_a_6568_);
lean_dec_ref_known(v___x_6567_, 1);
lean_inc_ref(v_type_6552_);
v___x_6569_ = l_Lean_Meta_getLevel(v_type_6552_, v___y_6555_, v___y_6556_, v___y_6557_, v___y_6558_);
if (lean_obj_tag(v___x_6569_) == 0)
{
lean_object* v_a_6570_; lean_object* v___x_6571_; lean_object* v___x_6572_; uint8_t v___x_6573_; uint8_t v___x_6574_; uint8_t v___x_6575_; lean_object* v___x_6576_; 
v_a_6570_ = lean_ctor_get(v___x_6569_, 0);
lean_inc(v_a_6570_);
lean_dec_ref_known(v___x_6569_, 1);
v___x_6571_ = lean_mk_empty_array_with_capacity(v___x_6549_);
lean_inc(v___x_6561_);
lean_inc_ref(v___x_6571_);
v___x_6572_ = lean_array_push(v___x_6571_, v___x_6561_);
v___x_6573_ = 0;
v___x_6574_ = 1;
v___x_6575_ = 1;
v___x_6576_ = l_Lean_Meta_mkLambdaFVars(v___x_6572_, v_type_6552_, v___x_6573_, v___x_6574_, v___x_6573_, v___x_6574_, v___x_6575_, v___y_6555_, v___y_6556_, v___y_6557_, v___y_6558_);
lean_dec_ref(v___x_6572_);
if (lean_obj_tag(v___x_6576_) == 0)
{
lean_object* v_a_6577_; lean_object* v___x_6578_; 
v_a_6577_ = lean_ctor_get(v___x_6576_, 0);
lean_inc(v_a_6577_);
lean_dec_ref_known(v___x_6576_, 1);
lean_inc_ref(v_wfRel_6550_);
v___x_6578_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_6550_, v___y_6555_, v___y_6556_, v___y_6557_, v___y_6558_);
if (lean_obj_tag(v___x_6578_) == 0)
{
lean_object* v_a_6579_; lean_object* v___x_6581_; uint8_t v_isShared_6582_; uint8_t v_isSharedCheck_6623_; 
v_a_6579_ = lean_ctor_get(v___x_6578_, 0);
v_isSharedCheck_6623_ = !lean_is_exclusive(v___x_6578_);
if (v_isSharedCheck_6623_ == 0)
{
v___x_6581_ = v___x_6578_;
v_isShared_6582_ = v_isSharedCheck_6623_;
goto v_resetjp_6580_;
}
else
{
lean_inc(v_a_6579_);
lean_dec(v___x_6578_);
v___x_6581_ = lean_box(0);
v_isShared_6582_ = v_isSharedCheck_6623_;
goto v_resetjp_6580_;
}
v_resetjp_6580_:
{
if (lean_obj_tag(v_a_6579_) == 1)
{
lean_object* v_val_6583_; lean_object* v___x_6584_; lean_object* v___x_6585_; lean_object* v___x_6586_; lean_object* v___x_6587_; lean_object* v___x_6588_; lean_object* v___x_6589_; lean_object* v___x_6590_; lean_object* v___x_6592_; 
lean_dec_ref(v___x_6571_);
lean_dec_ref(v_wfRel_6550_);
lean_dec(v___x_6549_);
v_val_6583_ = lean_ctor_get(v_a_6579_, 0);
lean_inc(v_val_6583_);
lean_dec_ref_known(v_a_6579_, 1);
v___x_6584_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__2));
v___x_6585_ = lean_box(0);
v___x_6586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6586_, 0, v_a_6570_);
lean_ctor_set(v___x_6586_, 1, v___x_6585_);
v___x_6587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6587_, 0, v_a_6568_);
lean_ctor_set(v___x_6587_, 1, v___x_6586_);
v___x_6588_ = l_Lean_mkConst(v___x_6584_, v___x_6587_);
v___x_6589_ = l_Lean_mkApp3(v___x_6588_, v_a_6566_, v_a_6577_, v_val_6583_);
v___x_6590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6590_, 0, v___x_6589_);
lean_ctor_set(v___x_6590_, 1, v_a_6564_);
if (v_isShared_6582_ == 0)
{
lean_ctor_set(v___x_6581_, 0, v___x_6590_);
v___x_6592_ = v___x_6581_;
goto v_reusejp_6591_;
}
else
{
lean_object* v_reuseFailAlloc_6593_; 
v_reuseFailAlloc_6593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6593_, 0, v___x_6590_);
v___x_6592_ = v_reuseFailAlloc_6593_;
goto v_reusejp_6591_;
}
v_reusejp_6591_:
{
return v___x_6592_;
}
}
else
{
lean_object* v___x_6594_; lean_object* v___x_6595_; lean_object* v___x_6596_; lean_object* v___x_6597_; lean_object* v___x_6598_; lean_object* v___x_6599_; 
lean_del_object(v___x_6581_);
lean_dec(v_a_6579_);
v___x_6594_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__4));
lean_inc_ref(v_wfRel_6550_);
v___x_6595_ = l_Lean_mkProj(v___x_6594_, v___x_6560_, v_wfRel_6550_);
v___x_6596_ = l_Lean_mkProj(v___x_6594_, v___x_6549_, v_wfRel_6550_);
v___x_6597_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__6));
v___x_6598_ = lean_array_push(v___x_6571_, v___x_6596_);
v___x_6599_ = l_Lean_Meta_mkAppM(v___x_6597_, v___x_6598_, v___y_6555_, v___y_6556_, v___y_6557_, v___y_6558_);
if (lean_obj_tag(v___x_6599_) == 0)
{
lean_object* v_a_6600_; lean_object* v___x_6602_; uint8_t v_isShared_6603_; uint8_t v_isSharedCheck_6614_; 
v_a_6600_ = lean_ctor_get(v___x_6599_, 0);
v_isSharedCheck_6614_ = !lean_is_exclusive(v___x_6599_);
if (v_isSharedCheck_6614_ == 0)
{
v___x_6602_ = v___x_6599_;
v_isShared_6603_ = v_isSharedCheck_6614_;
goto v_resetjp_6601_;
}
else
{
lean_inc(v_a_6600_);
lean_dec(v___x_6599_);
v___x_6602_ = lean_box(0);
v_isShared_6603_ = v_isSharedCheck_6614_;
goto v_resetjp_6601_;
}
v_resetjp_6601_:
{
lean_object* v___x_6604_; lean_object* v___x_6605_; lean_object* v___x_6606_; lean_object* v___x_6607_; lean_object* v___x_6608_; lean_object* v___x_6609_; lean_object* v___x_6610_; lean_object* v___x_6612_; 
v___x_6604_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__7));
v___x_6605_ = lean_box(0);
v___x_6606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6606_, 0, v_a_6570_);
lean_ctor_set(v___x_6606_, 1, v___x_6605_);
v___x_6607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6607_, 0, v_a_6568_);
lean_ctor_set(v___x_6607_, 1, v___x_6606_);
v___x_6608_ = l_Lean_mkConst(v___x_6604_, v___x_6607_);
v___x_6609_ = l_Lean_mkApp4(v___x_6608_, v_a_6566_, v_a_6577_, v___x_6595_, v_a_6600_);
v___x_6610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6610_, 0, v___x_6609_);
lean_ctor_set(v___x_6610_, 1, v_a_6564_);
if (v_isShared_6603_ == 0)
{
lean_ctor_set(v___x_6602_, 0, v___x_6610_);
v___x_6612_ = v___x_6602_;
goto v_reusejp_6611_;
}
else
{
lean_object* v_reuseFailAlloc_6613_; 
v_reuseFailAlloc_6613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6613_, 0, v___x_6610_);
v___x_6612_ = v_reuseFailAlloc_6613_;
goto v_reusejp_6611_;
}
v_reusejp_6611_:
{
return v___x_6612_;
}
}
}
else
{
lean_object* v_a_6615_; lean_object* v___x_6617_; uint8_t v_isShared_6618_; uint8_t v_isSharedCheck_6622_; 
lean_dec_ref(v___x_6595_);
lean_dec(v_a_6577_);
lean_dec(v_a_6570_);
lean_dec(v_a_6568_);
lean_dec(v_a_6566_);
lean_dec(v_a_6564_);
v_a_6615_ = lean_ctor_get(v___x_6599_, 0);
v_isSharedCheck_6622_ = !lean_is_exclusive(v___x_6599_);
if (v_isSharedCheck_6622_ == 0)
{
v___x_6617_ = v___x_6599_;
v_isShared_6618_ = v_isSharedCheck_6622_;
goto v_resetjp_6616_;
}
else
{
lean_inc(v_a_6615_);
lean_dec(v___x_6599_);
v___x_6617_ = lean_box(0);
v_isShared_6618_ = v_isSharedCheck_6622_;
goto v_resetjp_6616_;
}
v_resetjp_6616_:
{
lean_object* v___x_6620_; 
if (v_isShared_6618_ == 0)
{
v___x_6620_ = v___x_6617_;
goto v_reusejp_6619_;
}
else
{
lean_object* v_reuseFailAlloc_6621_; 
v_reuseFailAlloc_6621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6621_, 0, v_a_6615_);
v___x_6620_ = v_reuseFailAlloc_6621_;
goto v_reusejp_6619_;
}
v_reusejp_6619_:
{
return v___x_6620_;
}
}
}
}
}
}
else
{
lean_object* v_a_6624_; lean_object* v___x_6626_; uint8_t v_isShared_6627_; uint8_t v_isSharedCheck_6631_; 
lean_dec(v_a_6577_);
lean_dec_ref(v___x_6571_);
lean_dec(v_a_6570_);
lean_dec(v_a_6568_);
lean_dec(v_a_6566_);
lean_dec(v_a_6564_);
lean_dec_ref(v_wfRel_6550_);
lean_dec(v___x_6549_);
v_a_6624_ = lean_ctor_get(v___x_6578_, 0);
v_isSharedCheck_6631_ = !lean_is_exclusive(v___x_6578_);
if (v_isSharedCheck_6631_ == 0)
{
v___x_6626_ = v___x_6578_;
v_isShared_6627_ = v_isSharedCheck_6631_;
goto v_resetjp_6625_;
}
else
{
lean_inc(v_a_6624_);
lean_dec(v___x_6578_);
v___x_6626_ = lean_box(0);
v_isShared_6627_ = v_isSharedCheck_6631_;
goto v_resetjp_6625_;
}
v_resetjp_6625_:
{
lean_object* v___x_6629_; 
if (v_isShared_6627_ == 0)
{
v___x_6629_ = v___x_6626_;
goto v_reusejp_6628_;
}
else
{
lean_object* v_reuseFailAlloc_6630_; 
v_reuseFailAlloc_6630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6630_, 0, v_a_6624_);
v___x_6629_ = v_reuseFailAlloc_6630_;
goto v_reusejp_6628_;
}
v_reusejp_6628_:
{
return v___x_6629_;
}
}
}
}
else
{
lean_object* v_a_6632_; lean_object* v___x_6634_; uint8_t v_isShared_6635_; uint8_t v_isSharedCheck_6639_; 
lean_dec_ref(v___x_6571_);
lean_dec(v_a_6570_);
lean_dec(v_a_6568_);
lean_dec(v_a_6566_);
lean_dec(v_a_6564_);
lean_dec_ref(v_wfRel_6550_);
lean_dec(v___x_6549_);
v_a_6632_ = lean_ctor_get(v___x_6576_, 0);
v_isSharedCheck_6639_ = !lean_is_exclusive(v___x_6576_);
if (v_isSharedCheck_6639_ == 0)
{
v___x_6634_ = v___x_6576_;
v_isShared_6635_ = v_isSharedCheck_6639_;
goto v_resetjp_6633_;
}
else
{
lean_inc(v_a_6632_);
lean_dec(v___x_6576_);
v___x_6634_ = lean_box(0);
v_isShared_6635_ = v_isSharedCheck_6639_;
goto v_resetjp_6633_;
}
v_resetjp_6633_:
{
lean_object* v___x_6637_; 
if (v_isShared_6635_ == 0)
{
v___x_6637_ = v___x_6634_;
goto v_reusejp_6636_;
}
else
{
lean_object* v_reuseFailAlloc_6638_; 
v_reuseFailAlloc_6638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6638_, 0, v_a_6632_);
v___x_6637_ = v_reuseFailAlloc_6638_;
goto v_reusejp_6636_;
}
v_reusejp_6636_:
{
return v___x_6637_;
}
}
}
}
else
{
lean_object* v_a_6640_; lean_object* v___x_6642_; uint8_t v_isShared_6643_; uint8_t v_isSharedCheck_6647_; 
lean_dec(v_a_6568_);
lean_dec(v_a_6566_);
lean_dec(v_a_6564_);
lean_dec_ref(v_type_6552_);
lean_dec_ref(v_wfRel_6550_);
lean_dec(v___x_6549_);
v_a_6640_ = lean_ctor_get(v___x_6569_, 0);
v_isSharedCheck_6647_ = !lean_is_exclusive(v___x_6569_);
if (v_isSharedCheck_6647_ == 0)
{
v___x_6642_ = v___x_6569_;
v_isShared_6643_ = v_isSharedCheck_6647_;
goto v_resetjp_6641_;
}
else
{
lean_inc(v_a_6640_);
lean_dec(v___x_6569_);
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
else
{
lean_object* v_a_6648_; lean_object* v___x_6650_; uint8_t v_isShared_6651_; uint8_t v_isSharedCheck_6655_; 
lean_dec(v_a_6566_);
lean_dec(v_a_6564_);
lean_dec_ref(v_type_6552_);
lean_dec_ref(v_wfRel_6550_);
lean_dec(v___x_6549_);
v_a_6648_ = lean_ctor_get(v___x_6567_, 0);
v_isSharedCheck_6655_ = !lean_is_exclusive(v___x_6567_);
if (v_isSharedCheck_6655_ == 0)
{
v___x_6650_ = v___x_6567_;
v_isShared_6651_ = v_isSharedCheck_6655_;
goto v_resetjp_6649_;
}
else
{
lean_inc(v_a_6648_);
lean_dec(v___x_6567_);
v___x_6650_ = lean_box(0);
v_isShared_6651_ = v_isSharedCheck_6655_;
goto v_resetjp_6649_;
}
v_resetjp_6649_:
{
lean_object* v___x_6653_; 
if (v_isShared_6651_ == 0)
{
v___x_6653_ = v___x_6650_;
goto v_reusejp_6652_;
}
else
{
lean_object* v_reuseFailAlloc_6654_; 
v_reuseFailAlloc_6654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6654_, 0, v_a_6648_);
v___x_6653_ = v_reuseFailAlloc_6654_;
goto v_reusejp_6652_;
}
v_reusejp_6652_:
{
return v___x_6653_;
}
}
}
}
else
{
lean_object* v_a_6656_; lean_object* v___x_6658_; uint8_t v_isShared_6659_; uint8_t v_isSharedCheck_6663_; 
lean_dec(v_a_6564_);
lean_dec_ref(v_type_6552_);
lean_dec_ref(v_wfRel_6550_);
lean_dec(v___x_6549_);
v_a_6656_ = lean_ctor_get(v___x_6565_, 0);
v_isSharedCheck_6663_ = !lean_is_exclusive(v___x_6565_);
if (v_isSharedCheck_6663_ == 0)
{
v___x_6658_ = v___x_6565_;
v_isShared_6659_ = v_isSharedCheck_6663_;
goto v_resetjp_6657_;
}
else
{
lean_inc(v_a_6656_);
lean_dec(v___x_6565_);
v___x_6658_ = lean_box(0);
v_isShared_6659_ = v_isSharedCheck_6663_;
goto v_resetjp_6657_;
}
v_resetjp_6657_:
{
lean_object* v___x_6661_; 
if (v_isShared_6659_ == 0)
{
v___x_6661_ = v___x_6658_;
goto v_reusejp_6660_;
}
else
{
lean_object* v_reuseFailAlloc_6662_; 
v_reuseFailAlloc_6662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6662_, 0, v_a_6656_);
v___x_6661_ = v_reuseFailAlloc_6662_;
goto v_reusejp_6660_;
}
v_reusejp_6660_:
{
return v___x_6661_;
}
}
}
}
else
{
lean_object* v_a_6664_; lean_object* v___x_6666_; uint8_t v_isShared_6667_; uint8_t v_isSharedCheck_6671_; 
lean_dec_ref(v_type_6552_);
lean_dec_ref(v_wfRel_6550_);
lean_dec(v___x_6549_);
v_a_6664_ = lean_ctor_get(v___x_6563_, 0);
v_isSharedCheck_6671_ = !lean_is_exclusive(v___x_6563_);
if (v_isSharedCheck_6671_ == 0)
{
v___x_6666_ = v___x_6563_;
v_isShared_6667_ = v_isSharedCheck_6671_;
goto v_resetjp_6665_;
}
else
{
lean_inc(v_a_6664_);
lean_dec(v___x_6563_);
v___x_6666_ = lean_box(0);
v_isShared_6667_ = v_isSharedCheck_6671_;
goto v_resetjp_6665_;
}
v_resetjp_6665_:
{
lean_object* v___x_6669_; 
if (v_isShared_6667_ == 0)
{
v___x_6669_ = v___x_6666_;
goto v_reusejp_6668_;
}
else
{
lean_object* v_reuseFailAlloc_6670_; 
v_reuseFailAlloc_6670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6670_, 0, v_a_6664_);
v___x_6669_ = v_reuseFailAlloc_6670_;
goto v_reusejp_6668_;
}
v_reusejp_6668_:
{
return v___x_6669_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__0___boxed(lean_object* v___x_6672_, lean_object* v___x_6673_, lean_object* v_wfRel_6674_, lean_object* v_x_6675_, lean_object* v_type_6676_, lean_object* v___y_6677_, lean_object* v___y_6678_, lean_object* v___y_6679_, lean_object* v___y_6680_, lean_object* v___y_6681_, lean_object* v___y_6682_, lean_object* v___y_6683_){
_start:
{
lean_object* v_res_6684_; 
v_res_6684_ = l_Lean_Elab_WF_mkFix___lam__0(v___x_6672_, v___x_6673_, v_wfRel_6674_, v_x_6675_, v_type_6676_, v___y_6677_, v___y_6678_, v___y_6679_, v___y_6680_, v___y_6681_, v___y_6682_);
lean_dec(v___y_6682_);
lean_dec_ref(v___y_6681_);
lean_dec(v___y_6680_);
lean_dec_ref(v___y_6679_);
lean_dec(v___y_6678_);
lean_dec_ref(v___y_6677_);
lean_dec_ref(v_x_6675_);
lean_dec_ref(v___x_6672_);
return v_res_6684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__1(lean_object* v_prefixArgs_6685_, lean_object* v_declName_6686_, lean_object* v_x_6687_, lean_object* v_F_6688_, lean_object* v_val_6689_, lean_object* v___y_6690_, lean_object* v___y_6691_, lean_object* v___y_6692_, lean_object* v___y_6693_, lean_object* v___y_6694_, lean_object* v___y_6695_){
_start:
{
lean_object* v___x_6697_; lean_object* v___x_6698_; lean_object* v___x_6699_; 
v___x_6697_ = lean_array_get_size(v_prefixArgs_6685_);
v___x_6698_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___boxed), 11, 2);
lean_closure_set(v___x_6698_, 0, v_declName_6686_);
lean_closure_set(v___x_6698_, 1, v___x_6697_);
v___x_6699_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v_x_6687_, v_F_6688_, v_val_6689_, v___x_6698_, v___y_6690_, v___y_6691_, v___y_6692_, v___y_6693_, v___y_6694_, v___y_6695_);
return v___x_6699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__1___boxed(lean_object* v_prefixArgs_6700_, lean_object* v_declName_6701_, lean_object* v_x_6702_, lean_object* v_F_6703_, lean_object* v_val_6704_, lean_object* v___y_6705_, lean_object* v___y_6706_, lean_object* v___y_6707_, lean_object* v___y_6708_, lean_object* v___y_6709_, lean_object* v___y_6710_, lean_object* v___y_6711_){
_start:
{
lean_object* v_res_6712_; 
v_res_6712_ = l_Lean_Elab_WF_mkFix___lam__1(v_prefixArgs_6700_, v_declName_6701_, v_x_6702_, v_F_6703_, v_val_6704_, v___y_6705_, v___y_6706_, v___y_6707_, v___y_6708_, v___y_6709_, v___y_6710_);
lean_dec(v___y_6710_);
lean_dec_ref(v___y_6709_);
lean_dec(v___y_6708_);
lean_dec_ref(v___y_6707_);
lean_dec(v___y_6706_);
lean_dec_ref(v___y_6705_);
lean_dec_ref(v_prefixArgs_6700_);
return v_res_6712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__2(lean_object* v___x_6713_, lean_object* v___x_6714_, lean_object* v___x_6715_, lean_object* v___f_6716_, lean_object* v_funNames_6717_, lean_object* v_argsPacker_6718_, lean_object* v_decrTactics_6719_, uint8_t v___x_6720_, lean_object* v_fst_6721_, lean_object* v_prefixArgs_6722_, lean_object* v___y_6723_, lean_object* v___y_6724_, lean_object* v___y_6725_, lean_object* v___y_6726_, lean_object* v___y_6727_, lean_object* v___y_6728_){
_start:
{
lean_object* v___x_6730_; 
lean_inc_ref(v___x_6714_);
lean_inc_ref(v___x_6713_);
v___x_6730_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v___x_6713_, v___x_6714_, v___x_6715_, v___f_6716_, v___y_6723_, v___y_6724_, v___y_6725_, v___y_6726_, v___y_6727_, v___y_6728_);
if (lean_obj_tag(v___x_6730_) == 0)
{
lean_object* v_a_6731_; lean_object* v___x_6732_; 
v_a_6731_ = lean_ctor_get(v___x_6730_, 0);
lean_inc(v_a_6731_);
lean_dec_ref_known(v___x_6730_, 1);
v___x_6732_ = l_Lean_Elab_WF_solveDecreasingGoals(v_funNames_6717_, v_argsPacker_6718_, v_decrTactics_6719_, v_a_6731_, v___y_6725_, v___y_6726_, v___y_6727_, v___y_6728_);
if (lean_obj_tag(v___x_6732_) == 0)
{
lean_object* v_a_6733_; lean_object* v___x_6734_; lean_object* v___x_6735_; lean_object* v___x_6736_; lean_object* v___x_6737_; uint8_t v___x_6738_; uint8_t v___x_6739_; lean_object* v___x_6740_; 
v_a_6733_ = lean_ctor_get(v___x_6732_, 0);
lean_inc(v_a_6733_);
lean_dec_ref_known(v___x_6732_, 1);
v___x_6734_ = lean_unsigned_to_nat(2u);
v___x_6735_ = lean_mk_empty_array_with_capacity(v___x_6734_);
v___x_6736_ = lean_array_push(v___x_6735_, v___x_6713_);
v___x_6737_ = lean_array_push(v___x_6736_, v___x_6714_);
v___x_6738_ = 1;
v___x_6739_ = 1;
v___x_6740_ = l_Lean_Meta_mkLambdaFVars(v___x_6737_, v_a_6733_, v___x_6720_, v___x_6738_, v___x_6720_, v___x_6738_, v___x_6739_, v___y_6725_, v___y_6726_, v___y_6727_, v___y_6728_);
lean_dec_ref(v___x_6737_);
if (lean_obj_tag(v___x_6740_) == 0)
{
lean_object* v_a_6741_; lean_object* v___x_6742_; lean_object* v___x_6743_; 
v_a_6741_ = lean_ctor_get(v___x_6740_, 0);
lean_inc(v_a_6741_);
lean_dec_ref_known(v___x_6740_, 1);
v___x_6742_ = l_Lean_Expr_app___override(v_fst_6721_, v_a_6741_);
v___x_6743_ = l_Lean_Meta_mkLambdaFVars(v_prefixArgs_6722_, v___x_6742_, v___x_6720_, v___x_6738_, v___x_6720_, v___x_6738_, v___x_6739_, v___y_6725_, v___y_6726_, v___y_6727_, v___y_6728_);
return v___x_6743_;
}
else
{
lean_dec_ref(v_fst_6721_);
return v___x_6740_;
}
}
else
{
lean_dec_ref(v_fst_6721_);
lean_dec_ref(v___x_6714_);
lean_dec_ref(v___x_6713_);
return v___x_6732_;
}
}
else
{
lean_dec_ref(v_fst_6721_);
lean_dec_ref(v_decrTactics_6719_);
lean_dec_ref(v_argsPacker_6718_);
lean_dec_ref(v_funNames_6717_);
lean_dec_ref(v___x_6714_);
lean_dec_ref(v___x_6713_);
return v___x_6730_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__2___boxed(lean_object** _args){
lean_object* v___x_6744_ = _args[0];
lean_object* v___x_6745_ = _args[1];
lean_object* v___x_6746_ = _args[2];
lean_object* v___f_6747_ = _args[3];
lean_object* v_funNames_6748_ = _args[4];
lean_object* v_argsPacker_6749_ = _args[5];
lean_object* v_decrTactics_6750_ = _args[6];
lean_object* v___x_6751_ = _args[7];
lean_object* v_fst_6752_ = _args[8];
lean_object* v_prefixArgs_6753_ = _args[9];
lean_object* v___y_6754_ = _args[10];
lean_object* v___y_6755_ = _args[11];
lean_object* v___y_6756_ = _args[12];
lean_object* v___y_6757_ = _args[13];
lean_object* v___y_6758_ = _args[14];
lean_object* v___y_6759_ = _args[15];
lean_object* v___y_6760_ = _args[16];
_start:
{
uint8_t v___x_5938__boxed_6761_; lean_object* v_res_6762_; 
v___x_5938__boxed_6761_ = lean_unbox(v___x_6751_);
v_res_6762_ = l_Lean_Elab_WF_mkFix___lam__2(v___x_6744_, v___x_6745_, v___x_6746_, v___f_6747_, v_funNames_6748_, v_argsPacker_6749_, v_decrTactics_6750_, v___x_5938__boxed_6761_, v_fst_6752_, v_prefixArgs_6753_, v___y_6754_, v___y_6755_, v___y_6756_, v___y_6757_, v___y_6758_, v___y_6759_);
lean_dec(v___y_6759_);
lean_dec_ref(v___y_6758_);
lean_dec(v___y_6757_);
lean_dec_ref(v___y_6756_);
lean_dec(v___y_6755_);
lean_dec_ref(v___y_6754_);
lean_dec_ref(v_prefixArgs_6753_);
return v_res_6762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__3(lean_object* v___x_6763_, lean_object* v_snd_6764_, lean_object* v___x_6765_, lean_object* v_prefixArgs_6766_, lean_object* v_value_6767_, lean_object* v___f_6768_, lean_object* v_funNames_6769_, lean_object* v_argsPacker_6770_, lean_object* v_decrTactics_6771_, uint8_t v___x_6772_, lean_object* v_fst_6773_, lean_object* v_xs_6774_, lean_object* v_x_6775_, lean_object* v___y_6776_, lean_object* v___y_6777_, lean_object* v___y_6778_, lean_object* v___y_6779_, lean_object* v___y_6780_, lean_object* v___y_6781_){
_start:
{
lean_object* v_lctx_6783_; lean_object* v___x_6784_; lean_object* v___x_6785_; lean_object* v___x_6786_; lean_object* v___x_6787_; lean_object* v___x_6788_; lean_object* v___x_6789_; lean_object* v___x_6790_; lean_object* v___x_6791_; lean_object* v___f_6792_; lean_object* v___x_6793_; 
v_lctx_6783_ = lean_ctor_get(v___y_6778_, 2);
v___x_6784_ = lean_unsigned_to_nat(0u);
v___x_6785_ = lean_array_get_borrowed(v___x_6763_, v_xs_6774_, v___x_6784_);
v___x_6786_ = l_Lean_Expr_fvarId_x21(v___x_6785_);
lean_inc_ref(v_lctx_6783_);
v___x_6787_ = l_Lean_LocalContext_setUserName(v_lctx_6783_, v___x_6786_, v_snd_6764_);
v___x_6788_ = lean_array_get_borrowed(v___x_6763_, v_xs_6774_, v___x_6765_);
lean_inc_n(v___x_6785_, 2);
lean_inc_ref(v_prefixArgs_6766_);
v___x_6789_ = lean_array_push(v_prefixArgs_6766_, v___x_6785_);
v___x_6790_ = l_Lean_Expr_beta(v_value_6767_, v___x_6789_);
v___x_6791_ = lean_box(v___x_6772_);
lean_inc(v___x_6788_);
v___f_6792_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__2___boxed), 17, 10);
lean_closure_set(v___f_6792_, 0, v___x_6785_);
lean_closure_set(v___f_6792_, 1, v___x_6788_);
lean_closure_set(v___f_6792_, 2, v___x_6790_);
lean_closure_set(v___f_6792_, 3, v___f_6768_);
lean_closure_set(v___f_6792_, 4, v_funNames_6769_);
lean_closure_set(v___f_6792_, 5, v_argsPacker_6770_);
lean_closure_set(v___f_6792_, 6, v_decrTactics_6771_);
lean_closure_set(v___f_6792_, 7, v___x_6791_);
lean_closure_set(v___f_6792_, 8, v_fst_6773_);
lean_closure_set(v___f_6792_, 9, v_prefixArgs_6766_);
v___x_6793_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v___x_6787_, v___f_6792_, v___y_6776_, v___y_6777_, v___y_6778_, v___y_6779_, v___y_6780_, v___y_6781_);
return v___x_6793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__3___boxed(lean_object** _args){
lean_object* v___x_6794_ = _args[0];
lean_object* v_snd_6795_ = _args[1];
lean_object* v___x_6796_ = _args[2];
lean_object* v_prefixArgs_6797_ = _args[3];
lean_object* v_value_6798_ = _args[4];
lean_object* v___f_6799_ = _args[5];
lean_object* v_funNames_6800_ = _args[6];
lean_object* v_argsPacker_6801_ = _args[7];
lean_object* v_decrTactics_6802_ = _args[8];
lean_object* v___x_6803_ = _args[9];
lean_object* v_fst_6804_ = _args[10];
lean_object* v_xs_6805_ = _args[11];
lean_object* v_x_6806_ = _args[12];
lean_object* v___y_6807_ = _args[13];
lean_object* v___y_6808_ = _args[14];
lean_object* v___y_6809_ = _args[15];
lean_object* v___y_6810_ = _args[16];
lean_object* v___y_6811_ = _args[17];
lean_object* v___y_6812_ = _args[18];
lean_object* v___y_6813_ = _args[19];
_start:
{
uint8_t v___x_6008__boxed_6814_; lean_object* v_res_6815_; 
v___x_6008__boxed_6814_ = lean_unbox(v___x_6803_);
v_res_6815_ = l_Lean_Elab_WF_mkFix___lam__3(v___x_6794_, v_snd_6795_, v___x_6796_, v_prefixArgs_6797_, v_value_6798_, v___f_6799_, v_funNames_6800_, v_argsPacker_6801_, v_decrTactics_6802_, v___x_6008__boxed_6814_, v_fst_6804_, v_xs_6805_, v_x_6806_, v___y_6807_, v___y_6808_, v___y_6809_, v___y_6810_, v___y_6811_, v___y_6812_);
lean_dec(v___y_6812_);
lean_dec_ref(v___y_6811_);
lean_dec(v___y_6810_);
lean_dec_ref(v___y_6809_);
lean_dec(v___y_6808_);
lean_dec_ref(v___y_6807_);
lean_dec_ref(v_x_6806_);
lean_dec_ref(v_xs_6805_);
lean_dec(v___x_6796_);
lean_dec_ref(v___x_6794_);
return v_res_6815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix(lean_object* v_preDef_6820_, lean_object* v_prefixArgs_6821_, lean_object* v_argsPacker_6822_, lean_object* v_wfRel_6823_, lean_object* v_funNames_6824_, lean_object* v_decrTactics_6825_, lean_object* v_a_6826_, lean_object* v_a_6827_, lean_object* v_a_6828_, lean_object* v_a_6829_, lean_object* v_a_6830_, lean_object* v_a_6831_){
_start:
{
lean_object* v_declName_6833_; lean_object* v_type_6834_; lean_object* v_value_6835_; lean_object* v___x_6836_; 
v_declName_6833_ = lean_ctor_get(v_preDef_6820_, 3);
lean_inc(v_declName_6833_);
v_type_6834_ = lean_ctor_get(v_preDef_6820_, 6);
lean_inc_ref(v_type_6834_);
v_value_6835_ = lean_ctor_get(v_preDef_6820_, 7);
lean_inc_ref(v_value_6835_);
lean_dec_ref(v_preDef_6820_);
v___x_6836_ = l_Lean_Meta_instantiateForall(v_type_6834_, v_prefixArgs_6821_, v_a_6828_, v_a_6829_, v_a_6830_, v_a_6831_);
if (lean_obj_tag(v___x_6836_) == 0)
{
lean_object* v_a_6837_; lean_object* v___x_6838_; lean_object* v___x_6839_; lean_object* v___f_6840_; lean_object* v___x_6841_; uint8_t v___x_6842_; lean_object* v___x_6843_; 
v_a_6837_ = lean_ctor_get(v___x_6836_, 0);
lean_inc(v_a_6837_);
lean_dec_ref_known(v___x_6836_, 1);
v___x_6838_ = l_Lean_instInhabitedExpr;
v___x_6839_ = lean_unsigned_to_nat(1u);
v___f_6840_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__0___boxed), 12, 3);
lean_closure_set(v___f_6840_, 0, v___x_6838_);
lean_closure_set(v___f_6840_, 1, v___x_6839_);
lean_closure_set(v___f_6840_, 2, v_wfRel_6823_);
v___x_6841_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___closed__0));
v___x_6842_ = 0;
v___x_6843_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_a_6837_, v___x_6841_, v___f_6840_, v___x_6842_, v___x_6842_, v_a_6826_, v_a_6827_, v_a_6828_, v_a_6829_, v_a_6830_, v_a_6831_);
if (lean_obj_tag(v___x_6843_) == 0)
{
lean_object* v_a_6844_; lean_object* v_fst_6845_; lean_object* v_snd_6846_; lean_object* v___x_6847_; 
v_a_6844_ = lean_ctor_get(v___x_6843_, 0);
lean_inc(v_a_6844_);
lean_dec_ref_known(v___x_6843_, 1);
v_fst_6845_ = lean_ctor_get(v_a_6844_, 0);
lean_inc_n(v_fst_6845_, 2);
v_snd_6846_ = lean_ctor_get(v_a_6844_, 1);
lean_inc(v_snd_6846_);
lean_dec(v_a_6844_);
lean_inc(v_a_6831_);
lean_inc_ref(v_a_6830_);
lean_inc(v_a_6829_);
lean_inc_ref(v_a_6828_);
v___x_6847_ = lean_infer_type(v_fst_6845_, v_a_6828_, v_a_6829_, v_a_6830_, v_a_6831_);
if (lean_obj_tag(v___x_6847_) == 0)
{
lean_object* v_a_6848_; lean_object* v___x_6849_; 
v_a_6848_ = lean_ctor_get(v___x_6847_, 0);
lean_inc(v_a_6848_);
lean_dec_ref_known(v___x_6847_, 1);
lean_inc(v_a_6831_);
lean_inc_ref(v_a_6830_);
lean_inc(v_a_6829_);
lean_inc_ref(v_a_6828_);
v___x_6849_ = lean_whnf(v_a_6848_, v_a_6828_, v_a_6829_, v_a_6830_, v_a_6831_);
if (lean_obj_tag(v___x_6849_) == 0)
{
lean_object* v_a_6850_; lean_object* v___f_6851_; lean_object* v___x_6852_; lean_object* v___f_6853_; lean_object* v___x_6854_; lean_object* v___x_6855_; lean_object* v___x_6856_; 
v_a_6850_ = lean_ctor_get(v___x_6849_, 0);
lean_inc(v_a_6850_);
lean_dec_ref_known(v___x_6849_, 1);
lean_inc_ref(v_prefixArgs_6821_);
v___f_6851_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__1___boxed), 12, 2);
lean_closure_set(v___f_6851_, 0, v_prefixArgs_6821_);
lean_closure_set(v___f_6851_, 1, v_declName_6833_);
v___x_6852_ = lean_box(v___x_6842_);
v___f_6853_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__3___boxed), 20, 11);
lean_closure_set(v___f_6853_, 0, v___x_6838_);
lean_closure_set(v___f_6853_, 1, v_snd_6846_);
lean_closure_set(v___f_6853_, 2, v___x_6839_);
lean_closure_set(v___f_6853_, 3, v_prefixArgs_6821_);
lean_closure_set(v___f_6853_, 4, v_value_6835_);
lean_closure_set(v___f_6853_, 5, v___f_6851_);
lean_closure_set(v___f_6853_, 6, v_funNames_6824_);
lean_closure_set(v___f_6853_, 7, v_argsPacker_6822_);
lean_closure_set(v___f_6853_, 8, v_decrTactics_6825_);
lean_closure_set(v___f_6853_, 9, v___x_6852_);
lean_closure_set(v___f_6853_, 10, v_fst_6845_);
v___x_6854_ = l_Lean_Expr_bindingDomain_x21(v_a_6850_);
lean_dec(v_a_6850_);
v___x_6855_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___closed__1));
v___x_6856_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v___x_6854_, v___x_6855_, v___f_6853_, v___x_6842_, v___x_6842_, v_a_6826_, v_a_6827_, v_a_6828_, v_a_6829_, v_a_6830_, v_a_6831_);
return v___x_6856_;
}
else
{
lean_dec(v_snd_6846_);
lean_dec(v_fst_6845_);
lean_dec_ref(v_value_6835_);
lean_dec(v_declName_6833_);
lean_dec_ref(v_decrTactics_6825_);
lean_dec_ref(v_funNames_6824_);
lean_dec_ref(v_argsPacker_6822_);
lean_dec_ref(v_prefixArgs_6821_);
return v___x_6849_;
}
}
else
{
lean_dec(v_snd_6846_);
lean_dec(v_fst_6845_);
lean_dec_ref(v_value_6835_);
lean_dec(v_declName_6833_);
lean_dec_ref(v_decrTactics_6825_);
lean_dec_ref(v_funNames_6824_);
lean_dec_ref(v_argsPacker_6822_);
lean_dec_ref(v_prefixArgs_6821_);
return v___x_6847_;
}
}
else
{
lean_object* v_a_6857_; lean_object* v___x_6859_; uint8_t v_isShared_6860_; uint8_t v_isSharedCheck_6864_; 
lean_dec_ref(v_value_6835_);
lean_dec(v_declName_6833_);
lean_dec_ref(v_decrTactics_6825_);
lean_dec_ref(v_funNames_6824_);
lean_dec_ref(v_argsPacker_6822_);
lean_dec_ref(v_prefixArgs_6821_);
v_a_6857_ = lean_ctor_get(v___x_6843_, 0);
v_isSharedCheck_6864_ = !lean_is_exclusive(v___x_6843_);
if (v_isSharedCheck_6864_ == 0)
{
v___x_6859_ = v___x_6843_;
v_isShared_6860_ = v_isSharedCheck_6864_;
goto v_resetjp_6858_;
}
else
{
lean_inc(v_a_6857_);
lean_dec(v___x_6843_);
v___x_6859_ = lean_box(0);
v_isShared_6860_ = v_isSharedCheck_6864_;
goto v_resetjp_6858_;
}
v_resetjp_6858_:
{
lean_object* v___x_6862_; 
if (v_isShared_6860_ == 0)
{
v___x_6862_ = v___x_6859_;
goto v_reusejp_6861_;
}
else
{
lean_object* v_reuseFailAlloc_6863_; 
v_reuseFailAlloc_6863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6863_, 0, v_a_6857_);
v___x_6862_ = v_reuseFailAlloc_6863_;
goto v_reusejp_6861_;
}
v_reusejp_6861_:
{
return v___x_6862_;
}
}
}
}
else
{
lean_dec_ref(v_value_6835_);
lean_dec(v_declName_6833_);
lean_dec_ref(v_decrTactics_6825_);
lean_dec_ref(v_funNames_6824_);
lean_dec_ref(v_wfRel_6823_);
lean_dec_ref(v_argsPacker_6822_);
lean_dec_ref(v_prefixArgs_6821_);
return v___x_6836_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___boxed(lean_object* v_preDef_6865_, lean_object* v_prefixArgs_6866_, lean_object* v_argsPacker_6867_, lean_object* v_wfRel_6868_, lean_object* v_funNames_6869_, lean_object* v_decrTactics_6870_, lean_object* v_a_6871_, lean_object* v_a_6872_, lean_object* v_a_6873_, lean_object* v_a_6874_, lean_object* v_a_6875_, lean_object* v_a_6876_, lean_object* v_a_6877_){
_start:
{
lean_object* v_res_6878_; 
v_res_6878_ = l_Lean_Elab_WF_mkFix(v_preDef_6865_, v_prefixArgs_6866_, v_argsPacker_6867_, v_wfRel_6868_, v_funNames_6869_, v_decrTactics_6870_, v_a_6871_, v_a_6872_, v_a_6873_, v_a_6874_, v_a_6875_, v_a_6876_);
lean_dec(v_a_6876_);
lean_dec_ref(v_a_6875_);
lean_dec(v_a_6874_);
lean_dec_ref(v_a_6873_);
lean_dec(v_a_6872_);
lean_dec_ref(v_a_6871_);
return v_res_6878_;
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
