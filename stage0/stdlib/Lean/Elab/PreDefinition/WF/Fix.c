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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0(lean_object* v_a_544_, lean_object* v_e_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___x_637_; 
lean_inc_ref(v_a_544_);
v___x_637_ = l_Lean_Meta_isTypeCorrect(v_a_544_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; uint8_t v___x_639_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_a_638_);
lean_dec_ref_known(v___x_637_, 1);
v___x_639_ = lean_unbox(v_a_638_);
lean_dec(v_a_638_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_640_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__9, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__9);
lean_inc_ref(v_e_545_);
v___x_641_ = l_Lean_indentExpr(v_e_545_);
v___x_642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_640_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
v___x_643_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3);
v___x_644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_642_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
lean_inc_ref(v_a_544_);
v___x_645_ = l_Lean_indentExpr(v_a_544_);
v___x_646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_644_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
v___x_647_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v___x_646_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_dec_ref_known(v___x_647_, 1);
v___y_556_ = v___y_546_;
v___y_557_ = v___y_547_;
v___y_558_ = v___y_548_;
v___y_559_ = v___y_549_;
v___y_560_ = v___y_550_;
v___y_561_ = v___y_551_;
v___y_562_ = v___y_552_;
v___y_563_ = v___y_553_;
goto v___jp_555_;
}
else
{
lean_dec_ref(v_e_545_);
lean_dec_ref(v_a_544_);
return v___x_647_;
}
}
else
{
v___y_556_ = v___y_546_;
v___y_557_ = v___y_547_;
v___y_558_ = v___y_548_;
v___y_559_ = v___y_549_;
v___y_560_ = v___y_550_;
v___y_561_ = v___y_551_;
v___y_562_ = v___y_552_;
v___y_563_ = v___y_553_;
goto v___jp_555_;
}
}
else
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
lean_dec_ref(v_e_545_);
lean_dec_ref(v_a_544_);
v_a_648_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v___x_637_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_637_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_648_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
v___jp_555_:
{
lean_object* v___x_564_; 
lean_inc(v___y_563_);
lean_inc_ref(v___y_562_);
lean_inc(v___y_561_);
lean_inc_ref(v___y_560_);
lean_inc_ref(v_e_545_);
v___x_564_ = lean_infer_type(v_e_545_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v___x_566_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_a_565_);
lean_dec_ref_known(v___x_564_, 1);
lean_inc(v___y_563_);
lean_inc_ref(v___y_562_);
lean_inc(v___y_561_);
lean_inc_ref(v___y_560_);
lean_inc_ref(v_a_544_);
v___x_566_ = lean_infer_type(v_a_544_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v_a_567_; lean_object* v___x_568_; 
v_a_567_ = lean_ctor_get(v___x_566_, 0);
lean_inc_n(v_a_567_, 2);
lean_dec_ref_known(v___x_566_, 1);
lean_inc(v_a_565_);
v___x_568_ = l_Lean_Meta_isExprDefEq(v_a_565_, v_a_567_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_612_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_612_ == 0)
{
v___x_571_ = v___x_568_;
v_isShared_572_ = v_isSharedCheck_612_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_568_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_612_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
uint8_t v___x_573_; 
v___x_573_ = lean_unbox(v_a_569_);
lean_dec(v_a_569_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; 
lean_del_object(v___x_571_);
v___x_574_ = l_Lean_Meta_addPPExplicitToExposeDiff(v_a_565_, v_a_567_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; lean_object* v_fst_576_; lean_object* v_snd_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_599_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_a_575_);
lean_dec_ref_known(v___x_574_, 1);
v_fst_576_ = lean_ctor_get(v_a_575_, 0);
v_snd_577_ = lean_ctor_get(v_a_575_, 1);
v_isSharedCheck_599_ = !lean_is_exclusive(v_a_575_);
if (v_isSharedCheck_599_ == 0)
{
v___x_579_ = v_a_575_;
v_isShared_580_ = v_isSharedCheck_599_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_snd_577_);
lean_inc(v_fst_576_);
lean_dec(v_a_575_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_599_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_584_; 
v___x_581_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__1);
v___x_582_ = l_Lean_indentExpr(v_e_545_);
if (v_isShared_580_ == 0)
{
lean_ctor_set_tag(v___x_579_, 7);
lean_ctor_set(v___x_579_, 1, v___x_582_);
lean_ctor_set(v___x_579_, 0, v___x_581_);
v___x_584_ = v___x_579_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_581_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v___x_582_);
v___x_584_ = v_reuseFailAlloc_598_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_585_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__3);
v___x_586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_584_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
v___x_587_ = l_Lean_indentExpr(v_a_544_);
v___x_588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_586_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
v___x_589_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__5);
v___x_590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_588_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = l_Lean_indentExpr(v_fst_576_);
v___x_592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_590_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
v___x_593_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__7, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___closed__7);
v___x_594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_592_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
v___x_595_ = l_Lean_indentExpr(v_snd_577_);
v___x_596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_594_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
v___x_597_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v___x_596_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
return v___x_597_;
}
}
}
else
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
lean_dec_ref(v_e_545_);
lean_dec_ref(v_a_544_);
v_a_600_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_607_ == 0)
{
v___x_602_ = v___x_574_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_574_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_600_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
else
{
lean_object* v___x_608_; lean_object* v___x_610_; 
lean_dec(v_a_567_);
lean_dec(v_a_565_);
lean_dec_ref(v_e_545_);
lean_dec_ref(v_a_544_);
v___x_608_ = lean_box(0);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v___x_608_);
v___x_610_ = v___x_571_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_608_);
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
lean_dec(v_a_567_);
lean_dec(v_a_565_);
lean_dec_ref(v_e_545_);
lean_dec_ref(v_a_544_);
v_a_613_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_620_ == 0)
{
v___x_615_ = v___x_568_;
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_dec(v___x_568_);
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
lean_dec(v_a_565_);
lean_dec_ref(v_e_545_);
lean_dec_ref(v_a_544_);
v_a_621_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v___x_566_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_566_);
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
else
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
lean_dec_ref(v_e_545_);
lean_dec_ref(v_a_544_);
v_a_629_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v___x_564_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_564_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_a_629_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___boxed(lean_object* v_a_656_, lean_object* v_e_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0(v_a_656_, v_e_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec(v___y_658_);
return v_res_667_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0(void){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_668_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1(void){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__0);
v___x_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
return v___x_670_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__2(void){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_671_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1);
v___x_672_ = lean_unsigned_to_nat(0u);
v___x_673_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
lean_ctor_set(v___x_673_, 2, v___x_672_);
lean_ctor_set(v___x_673_, 3, v___x_672_);
lean_ctor_set(v___x_673_, 4, v___x_671_);
lean_ctor_set(v___x_673_, 5, v___x_671_);
lean_ctor_set(v___x_673_, 6, v___x_671_);
lean_ctor_set(v___x_673_, 7, v___x_671_);
lean_ctor_set(v___x_673_, 8, v___x_671_);
lean_ctor_set(v___x_673_, 9, v___x_671_);
lean_ctor_set(v___x_673_, 10, v___x_671_);
return v___x_673_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__3(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_674_ = lean_unsigned_to_nat(32u);
v___x_675_ = lean_mk_empty_array_with_capacity(v___x_674_);
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
return v___x_676_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__4(void){
_start:
{
size_t v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_677_ = ((size_t)5ULL);
v___x_678_ = lean_unsigned_to_nat(0u);
v___x_679_ = lean_unsigned_to_nat(32u);
v___x_680_ = lean_mk_empty_array_with_capacity(v___x_679_);
v___x_681_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__3);
v___x_682_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_682_, 0, v___x_681_);
lean_ctor_set(v___x_682_, 1, v___x_680_);
lean_ctor_set(v___x_682_, 2, v___x_678_);
lean_ctor_set(v___x_682_, 3, v___x_678_);
lean_ctor_set_usize(v___x_682_, 4, v___x_677_);
return v___x_682_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__5(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_683_ = lean_box(1);
v___x_684_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__4);
v___x_685_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__1);
v___x_686_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
lean_ctor_set(v___x_686_, 1, v___x_684_);
lean_ctor_set(v___x_686_, 2, v___x_683_);
return v___x_686_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7(void){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__6));
v___x_689_ = l_Lean_stringToMessageData(v___x_688_);
return v___x_689_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__9(void){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__8));
v___x_692_ = l_Lean_stringToMessageData(v___x_691_);
return v___x_692_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__11(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__10));
v___x_695_ = l_Lean_stringToMessageData(v___x_694_);
return v___x_695_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__13(void){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__12));
v___x_698_ = l_Lean_stringToMessageData(v___x_697_);
return v___x_698_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__15(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__14));
v___x_701_ = l_Lean_stringToMessageData(v___x_700_);
return v___x_701_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__17(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__16));
v___x_704_ = l_Lean_stringToMessageData(v___x_703_);
return v___x_704_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__19(void){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_706_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__18));
v___x_707_ = l_Lean_stringToMessageData(v___x_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(lean_object* v_msg_708_, lean_object* v_declHint_709_, lean_object* v___y_710_){
_start:
{
lean_object* v___x_712_; lean_object* v_env_713_; uint8_t v___x_714_; 
v___x_712_ = lean_st_ref_get(v___y_710_);
v_env_713_ = lean_ctor_get(v___x_712_, 0);
lean_inc_ref(v_env_713_);
lean_dec(v___x_712_);
v___x_714_ = l_Lean_Name_isAnonymous(v_declHint_709_);
if (v___x_714_ == 0)
{
uint8_t v_isExporting_715_; 
v_isExporting_715_ = lean_ctor_get_uint8(v_env_713_, sizeof(void*)*8);
if (v_isExporting_715_ == 0)
{
lean_object* v___x_716_; 
lean_dec_ref(v_env_713_);
lean_dec(v_declHint_709_);
v___x_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_716_, 0, v_msg_708_);
return v___x_716_;
}
else
{
lean_object* v___x_717_; uint8_t v___x_718_; 
lean_inc_ref(v_env_713_);
v___x_717_ = l_Lean_Environment_setExporting(v_env_713_, v___x_714_);
lean_inc(v_declHint_709_);
lean_inc_ref(v___x_717_);
v___x_718_ = l_Lean_Environment_contains(v___x_717_, v_declHint_709_, v_isExporting_715_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; 
lean_dec_ref(v___x_717_);
lean_dec_ref(v_env_713_);
lean_dec(v_declHint_709_);
v___x_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_719_, 0, v_msg_708_);
return v___x_719_;
}
else
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v_c_725_; lean_object* v___x_726_; 
v___x_720_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__2);
v___x_721_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__5);
v___x_722_ = l_Lean_Options_empty;
v___x_723_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_723_, 0, v___x_717_);
lean_ctor_set(v___x_723_, 1, v___x_720_);
lean_ctor_set(v___x_723_, 2, v___x_721_);
lean_ctor_set(v___x_723_, 3, v___x_722_);
lean_inc(v_declHint_709_);
v___x_724_ = l_Lean_MessageData_ofConstName(v_declHint_709_, v___x_714_);
v_c_725_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_725_, 0, v___x_723_);
lean_ctor_set(v_c_725_, 1, v___x_724_);
v___x_726_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_713_, v_declHint_709_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
lean_dec_ref(v_env_713_);
lean_dec(v_declHint_709_);
v___x_727_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7);
v___x_728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
lean_ctor_set(v___x_728_, 1, v_c_725_);
v___x_729_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__9);
v___x_730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_728_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v___x_731_ = l_Lean_MessageData_note(v___x_730_);
v___x_732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_732_, 0, v_msg_708_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
v___x_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
return v___x_733_;
}
else
{
lean_object* v_val_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_769_; 
v_val_734_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_769_ == 0)
{
v___x_736_ = v___x_726_;
v_isShared_737_ = v_isSharedCheck_769_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_val_734_);
lean_dec(v___x_726_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_769_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v_mod_741_; uint8_t v___x_742_; 
v___x_738_ = lean_box(0);
v___x_739_ = l_Lean_Environment_header(v_env_713_);
lean_dec_ref(v_env_713_);
v___x_740_ = l_Lean_EnvironmentHeader_moduleNames(v___x_739_);
v_mod_741_ = lean_array_get(v___x_738_, v___x_740_, v_val_734_);
lean_dec(v_val_734_);
lean_dec_ref(v___x_740_);
v___x_742_ = l_Lean_isPrivateName(v_declHint_709_);
lean_dec(v_declHint_709_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_754_; 
v___x_743_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__11);
v___x_744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
lean_ctor_set(v___x_744_, 1, v_c_725_);
v___x_745_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__13);
v___x_746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_744_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
v___x_747_ = l_Lean_MessageData_ofName(v_mod_741_);
v___x_748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_746_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
v___x_749_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__15);
v___x_750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_748_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
v___x_751_ = l_Lean_MessageData_note(v___x_750_);
v___x_752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_752_, 0, v_msg_708_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
if (v_isShared_737_ == 0)
{
lean_ctor_set_tag(v___x_736_, 0);
lean_ctor_set(v___x_736_, 0, v___x_752_);
v___x_754_ = v___x_736_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_752_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
else
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_767_; 
v___x_756_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__7);
v___x_757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
lean_ctor_set(v___x_757_, 1, v_c_725_);
v___x_758_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__17);
v___x_759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_759_, 0, v___x_757_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
v___x_760_ = l_Lean_MessageData_ofName(v_mod_741_);
v___x_761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_761_, 0, v___x_759_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
v___x_762_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___closed__19);
v___x_763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_763_, 0, v___x_761_);
lean_ctor_set(v___x_763_, 1, v___x_762_);
v___x_764_ = l_Lean_MessageData_note(v___x_763_);
v___x_765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_765_, 0, v_msg_708_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
if (v_isShared_737_ == 0)
{
lean_ctor_set_tag(v___x_736_, 0);
lean_ctor_set(v___x_736_, 0, v___x_765_);
v___x_767_ = v___x_736_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_765_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_770_; 
lean_dec_ref(v_env_713_);
lean_dec(v_declHint_709_);
v___x_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_770_, 0, v_msg_708_);
return v___x_770_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg___boxed(lean_object* v_msg_771_, lean_object* v_declHint_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(v_msg_771_, v_declHint_772_, v___y_773_);
lean_dec(v___y_773_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30(lean_object* v_msg_776_, lean_object* v_declHint_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v___x_787_; lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_797_; 
v___x_787_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(v_msg_776_, v_declHint_777_, v___y_785_);
v_a_788_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_797_ == 0)
{
v___x_790_ = v___x_787_;
v_isShared_791_ = v_isSharedCheck_797_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_787_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_797_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_795_; 
v___x_792_ = l_Lean_unknownIdentifierMessageTag;
v___x_793_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
lean_ctor_set(v___x_793_, 1, v_a_788_);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v___x_793_);
v___x_795_ = v___x_790_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30___boxed(lean_object* v_msg_798_, lean_object* v_declHint_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30(v_msg_798_, v_declHint_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec(v___y_800_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(lean_object* v_ref_810_, lean_object* v_msg_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v_toCold_821_; lean_object* v_currRecDepth_822_; lean_object* v_ref_823_; uint8_t v_diag_824_; uint8_t v_suppressElabErrors_825_; lean_object* v_ref_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v_toCold_821_ = lean_ctor_get(v___y_818_, 0);
v_currRecDepth_822_ = lean_ctor_get(v___y_818_, 1);
v_ref_823_ = lean_ctor_get(v___y_818_, 2);
v_diag_824_ = lean_ctor_get_uint8(v___y_818_, sizeof(void*)*3);
v_suppressElabErrors_825_ = lean_ctor_get_uint8(v___y_818_, sizeof(void*)*3 + 1);
v_ref_826_ = l_Lean_replaceRef(v_ref_810_, v_ref_823_);
lean_inc(v_currRecDepth_822_);
lean_inc_ref(v_toCold_821_);
v___x_827_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_827_, 0, v_toCold_821_);
lean_ctor_set(v___x_827_, 1, v_currRecDepth_822_);
lean_ctor_set(v___x_827_, 2, v_ref_826_);
lean_ctor_set_uint8(v___x_827_, sizeof(void*)*3, v_diag_824_);
lean_ctor_set_uint8(v___x_827_, sizeof(void*)*3 + 1, v_suppressElabErrors_825_);
v___x_828_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v_msg_811_, v___y_816_, v___y_817_, v___x_827_, v___y_819_);
lean_dec_ref_known(v___x_827_, 3);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg___boxed(lean_object* v_ref_829_, lean_object* v_msg_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(v_ref_829_, v_msg_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec(v___y_831_);
lean_dec(v_ref_829_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(lean_object* v_ref_841_, lean_object* v_msg_842_, lean_object* v_declHint_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v___x_853_; lean_object* v_a_854_; lean_object* v___x_855_; 
v___x_853_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30(v_msg_842_, v_declHint_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
v_a_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_854_);
lean_dec_ref(v___x_853_);
v___x_855_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(v_ref_841_, v_a_854_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg___boxed(lean_object* v_ref_856_, lean_object* v_msg_857_, lean_object* v_declHint_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(v_ref_856_, v_msg_857_, v_declHint_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec(v___y_859_);
lean_dec(v_ref_856_);
return v_res_868_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1(void){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__0));
v___x_871_ = l_Lean_stringToMessageData(v___x_870_);
return v___x_871_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3(void){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__2));
v___x_874_ = l_Lean_stringToMessageData(v___x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(lean_object* v_ref_875_, lean_object* v_constName_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v___x_886_; uint8_t v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_886_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1);
v___x_887_ = 0;
lean_inc(v_constName_876_);
v___x_888_ = l_Lean_MessageData_ofConstName(v_constName_876_, v___x_887_);
v___x_889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_886_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
v___x_890_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3);
v___x_891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_889_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(v_ref_875_, v___x_891_, v_constName_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___boxed(lean_object* v_ref_893_, lean_object* v_constName_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(v_ref_893_, v_constName_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
lean_dec(v___y_895_);
lean_dec(v_ref_893_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(lean_object* v_constName_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v_ref_915_; lean_object* v___x_916_; 
v_ref_915_ = lean_ctor_get(v___y_912_, 2);
v___x_916_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(v_ref_915_, v_constName_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg___boxed(lean_object* v_constName_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(v_constName_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec(v___y_918_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(lean_object* v_constName_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v___x_938_; lean_object* v_env_939_; uint8_t v___x_940_; lean_object* v___x_941_; 
v___x_938_ = lean_st_ref_get(v___y_936_);
v_env_939_ = lean_ctor_get(v___x_938_, 0);
lean_inc_ref(v_env_939_);
lean_dec(v___x_938_);
v___x_940_ = 0;
lean_inc(v_constName_928_);
v___x_941_ = l_Lean_Environment_find_x3f(v_env_939_, v_constName_928_, v___x_940_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v___x_942_; 
v___x_942_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(v_constName_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
return v___x_942_;
}
else
{
lean_object* v_val_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_950_; 
lean_dec(v_constName_928_);
v_val_943_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_950_ == 0)
{
v___x_945_ = v___x_941_;
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_val_943_);
lean_dec(v___x_941_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_948_; 
if (v_isShared_946_ == 0)
{
lean_ctor_set_tag(v___x_945_, 0);
v___x_948_ = v___x_945_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_val_943_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18___boxed(lean_object* v_constName_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(v_constName_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec(v___y_952_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(lean_object* v_declName_962_, lean_object* v___y_963_){
_start:
{
lean_object* v___x_965_; lean_object* v_env_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_965_ = lean_st_ref_get(v___y_963_);
v_env_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc_ref(v_env_966_);
lean_dec(v___x_965_);
v___x_967_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_966_, v_declName_962_);
v___x_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg___boxed(lean_object* v_declName_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(v_declName_969_, v___y_970_);
lean_dec(v___y_970_);
return v_res_972_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0(void){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = l_instMonadEIO(lean_box(0));
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19(lean_object* v_msg_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v_toApplicative_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1085_; 
v___x_990_ = lean_obj_once(&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0, &l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0_once, _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0);
v___x_991_ = l_StateRefT_x27_instMonad___redArg(v___x_990_);
v_toApplicative_992_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1085_ == 0)
{
lean_object* v_unused_1086_; 
v_unused_1086_ = lean_ctor_get(v___x_991_, 1);
lean_dec(v_unused_1086_);
v___x_994_ = v___x_991_;
v_isShared_995_ = v_isSharedCheck_1085_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_toApplicative_992_);
lean_dec(v___x_991_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1085_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v_toFunctor_996_; lean_object* v_toSeq_997_; lean_object* v_toSeqLeft_998_; lean_object* v_toSeqRight_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1083_; 
v_toFunctor_996_ = lean_ctor_get(v_toApplicative_992_, 0);
v_toSeq_997_ = lean_ctor_get(v_toApplicative_992_, 2);
v_toSeqLeft_998_ = lean_ctor_get(v_toApplicative_992_, 3);
v_toSeqRight_999_ = lean_ctor_get(v_toApplicative_992_, 4);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_toApplicative_992_);
if (v_isSharedCheck_1083_ == 0)
{
lean_object* v_unused_1084_; 
v_unused_1084_ = lean_ctor_get(v_toApplicative_992_, 1);
lean_dec(v_unused_1084_);
v___x_1001_ = v_toApplicative_992_;
v_isShared_1002_ = v_isSharedCheck_1083_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_toSeqRight_999_);
lean_inc(v_toSeqLeft_998_);
lean_inc(v_toSeq_997_);
lean_inc(v_toFunctor_996_);
lean_dec(v_toApplicative_992_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1083_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___f_1003_; lean_object* v___f_1004_; lean_object* v___f_1005_; lean_object* v___f_1006_; lean_object* v___x_1007_; lean_object* v___f_1008_; lean_object* v___f_1009_; lean_object* v___f_1010_; lean_object* v___x_1012_; 
v___f_1003_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__1));
v___f_1004_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__2));
lean_inc_ref(v_toFunctor_996_);
v___f_1005_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1005_, 0, v_toFunctor_996_);
v___f_1006_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1006_, 0, v_toFunctor_996_);
v___x_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___f_1005_);
lean_ctor_set(v___x_1007_, 1, v___f_1006_);
v___f_1008_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1008_, 0, v_toSeqRight_999_);
v___f_1009_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1009_, 0, v_toSeqLeft_998_);
v___f_1010_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1010_, 0, v_toSeq_997_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 4, v___f_1008_);
lean_ctor_set(v___x_1001_, 3, v___f_1009_);
lean_ctor_set(v___x_1001_, 2, v___f_1010_);
lean_ctor_set(v___x_1001_, 1, v___f_1003_);
lean_ctor_set(v___x_1001_, 0, v___x_1007_);
v___x_1012_ = v___x_1001_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1007_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v___f_1003_);
lean_ctor_set(v_reuseFailAlloc_1082_, 2, v___f_1010_);
lean_ctor_set(v_reuseFailAlloc_1082_, 3, v___f_1009_);
lean_ctor_set(v_reuseFailAlloc_1082_, 4, v___f_1008_);
v___x_1012_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
lean_object* v___x_1014_; 
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 1, v___f_1004_);
lean_ctor_set(v___x_994_, 0, v___x_1012_);
v___x_1014_ = v___x_994_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1012_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v___f_1004_);
v___x_1014_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
lean_object* v___x_1015_; lean_object* v_toApplicative_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1079_; 
v___x_1015_ = l_StateRefT_x27_instMonad___redArg(v___x_1014_);
v_toApplicative_1016_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1079_ == 0)
{
lean_object* v_unused_1080_; 
v_unused_1080_ = lean_ctor_get(v___x_1015_, 1);
lean_dec(v_unused_1080_);
v___x_1018_ = v___x_1015_;
v_isShared_1019_ = v_isSharedCheck_1079_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_toApplicative_1016_);
lean_dec(v___x_1015_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1079_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v_toFunctor_1020_; lean_object* v_toSeq_1021_; lean_object* v_toSeqLeft_1022_; lean_object* v_toSeqRight_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1077_; 
v_toFunctor_1020_ = lean_ctor_get(v_toApplicative_1016_, 0);
v_toSeq_1021_ = lean_ctor_get(v_toApplicative_1016_, 2);
v_toSeqLeft_1022_ = lean_ctor_get(v_toApplicative_1016_, 3);
v_toSeqRight_1023_ = lean_ctor_get(v_toApplicative_1016_, 4);
v_isSharedCheck_1077_ = !lean_is_exclusive(v_toApplicative_1016_);
if (v_isSharedCheck_1077_ == 0)
{
lean_object* v_unused_1078_; 
v_unused_1078_ = lean_ctor_get(v_toApplicative_1016_, 1);
lean_dec(v_unused_1078_);
v___x_1025_ = v_toApplicative_1016_;
v_isShared_1026_ = v_isSharedCheck_1077_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_toSeqRight_1023_);
lean_inc(v_toSeqLeft_1022_);
lean_inc(v_toSeq_1021_);
lean_inc(v_toFunctor_1020_);
lean_dec(v_toApplicative_1016_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1077_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___f_1027_; lean_object* v___f_1028_; lean_object* v___f_1029_; lean_object* v___f_1030_; lean_object* v___x_1031_; lean_object* v___f_1032_; lean_object* v___f_1033_; lean_object* v___f_1034_; lean_object* v___x_1036_; 
v___f_1027_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__3));
v___f_1028_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__4));
lean_inc_ref(v_toFunctor_1020_);
v___f_1029_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1029_, 0, v_toFunctor_1020_);
v___f_1030_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1030_, 0, v_toFunctor_1020_);
v___x_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___f_1029_);
lean_ctor_set(v___x_1031_, 1, v___f_1030_);
v___f_1032_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1032_, 0, v_toSeqRight_1023_);
v___f_1033_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1033_, 0, v_toSeqLeft_1022_);
v___f_1034_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1034_, 0, v_toSeq_1021_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 4, v___f_1032_);
lean_ctor_set(v___x_1025_, 3, v___f_1033_);
lean_ctor_set(v___x_1025_, 2, v___f_1034_);
lean_ctor_set(v___x_1025_, 1, v___f_1027_);
lean_ctor_set(v___x_1025_, 0, v___x_1031_);
v___x_1036_ = v___x_1025_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1031_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v___f_1027_);
lean_ctor_set(v_reuseFailAlloc_1076_, 2, v___f_1034_);
lean_ctor_set(v_reuseFailAlloc_1076_, 3, v___f_1033_);
lean_ctor_set(v_reuseFailAlloc_1076_, 4, v___f_1032_);
v___x_1036_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
lean_object* v___x_1038_; 
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 1, v___f_1028_);
lean_ctor_set(v___x_1018_, 0, v___x_1036_);
v___x_1038_ = v___x_1018_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v___f_1028_);
v___x_1038_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
lean_object* v___x_1039_; lean_object* v_toApplicative_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1073_; 
v___x_1039_ = l_StateRefT_x27_instMonad___redArg(v___x_1038_);
v_toApplicative_1040_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1073_ == 0)
{
lean_object* v_unused_1074_; 
v_unused_1074_ = lean_ctor_get(v___x_1039_, 1);
lean_dec(v_unused_1074_);
v___x_1042_ = v___x_1039_;
v_isShared_1043_ = v_isSharedCheck_1073_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_toApplicative_1040_);
lean_dec(v___x_1039_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1073_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v_toFunctor_1044_; lean_object* v_toSeq_1045_; lean_object* v_toSeqLeft_1046_; lean_object* v_toSeqRight_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1071_; 
v_toFunctor_1044_ = lean_ctor_get(v_toApplicative_1040_, 0);
v_toSeq_1045_ = lean_ctor_get(v_toApplicative_1040_, 2);
v_toSeqLeft_1046_ = lean_ctor_get(v_toApplicative_1040_, 3);
v_toSeqRight_1047_ = lean_ctor_get(v_toApplicative_1040_, 4);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_toApplicative_1040_);
if (v_isSharedCheck_1071_ == 0)
{
lean_object* v_unused_1072_; 
v_unused_1072_ = lean_ctor_get(v_toApplicative_1040_, 1);
lean_dec(v_unused_1072_);
v___x_1049_ = v_toApplicative_1040_;
v_isShared_1050_ = v_isSharedCheck_1071_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_toSeqRight_1047_);
lean_inc(v_toSeqLeft_1046_);
lean_inc(v_toSeq_1045_);
lean_inc(v_toFunctor_1044_);
lean_dec(v_toApplicative_1040_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1071_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___f_1051_; lean_object* v___f_1052_; lean_object* v___f_1053_; lean_object* v___f_1054_; lean_object* v___x_1055_; lean_object* v___f_1056_; lean_object* v___f_1057_; lean_object* v___f_1058_; lean_object* v___x_1060_; 
v___f_1051_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__5));
v___f_1052_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__6));
lean_inc_ref(v_toFunctor_1044_);
v___f_1053_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1053_, 0, v_toFunctor_1044_);
v___f_1054_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1054_, 0, v_toFunctor_1044_);
v___x_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___f_1053_);
lean_ctor_set(v___x_1055_, 1, v___f_1054_);
v___f_1056_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1056_, 0, v_toSeqRight_1047_);
v___f_1057_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1057_, 0, v_toSeqLeft_1046_);
v___f_1058_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1058_, 0, v_toSeq_1045_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 4, v___f_1056_);
lean_ctor_set(v___x_1049_, 3, v___f_1057_);
lean_ctor_set(v___x_1049_, 2, v___f_1058_);
lean_ctor_set(v___x_1049_, 1, v___f_1051_);
lean_ctor_set(v___x_1049_, 0, v___x_1055_);
v___x_1060_ = v___x_1049_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1055_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v___f_1051_);
lean_ctor_set(v_reuseFailAlloc_1070_, 2, v___f_1058_);
lean_ctor_set(v_reuseFailAlloc_1070_, 3, v___f_1057_);
lean_ctor_set(v_reuseFailAlloc_1070_, 4, v___f_1056_);
v___x_1060_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
lean_object* v___x_1062_; 
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 1, v___f_1052_);
lean_ctor_set(v___x_1042_, 0, v___x_1060_);
v___x_1062_ = v___x_1042_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1060_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v___f_1052_);
v___x_1062_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_49652__overap_1067_; lean_object* v___x_1068_; 
v___x_1063_ = l_StateRefT_x27_instMonad___redArg(v___x_1062_);
v___x_1064_ = l_StateRefT_x27_instMonad___redArg(v___x_1063_);
v___x_1065_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_1066_ = l_instInhabitedOfMonad___redArg(v___x_1064_, v___x_1065_);
v___x_49652__overap_1067_ = lean_panic_fn_borrowed(v___x_1066_, v_msg_980_);
lean_dec(v___x_1066_);
lean_inc(v___y_988_);
lean_inc_ref(v___y_987_);
lean_inc(v___y_986_);
lean_inc_ref(v___y_985_);
lean_inc(v___y_984_);
lean_inc_ref(v___y_983_);
lean_inc(v___y_982_);
lean_inc(v___y_981_);
v___x_1068_ = lean_apply_9(v___x_49652__overap_1067_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, lean_box(0));
return v___x_1068_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___boxed(lean_object* v_msg_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19(v_msg_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec(v___y_1089_);
lean_dec(v___y_1088_);
return v_res_1097_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3(void){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1101_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__2));
v___x_1102_ = lean_unsigned_to_nat(53u);
v___x_1103_ = lean_unsigned_to_nat(62u);
v___x_1104_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__1));
v___x_1105_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__0));
v___x_1106_ = l_mkPanicMessageWithDecl(v___x_1105_, v___x_1104_, v___x_1103_, v___x_1102_, v___x_1101_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21(size_t v_sz_1107_, size_t v_i_1108_, lean_object* v_bs_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
uint8_t v___x_1119_; 
v___x_1119_ = lean_usize_dec_lt(v_i_1108_, v_sz_1107_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1120_; 
v___x_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1120_, 0, v_bs_1109_);
return v___x_1120_;
}
else
{
lean_object* v_v_1121_; lean_object* v___x_1122_; 
v_v_1121_ = lean_array_uget_borrowed(v_bs_1109_, v_i_1108_);
lean_inc(v_v_1121_);
v___x_1122_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(v_v_1121_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_a_1123_; lean_object* v___x_1124_; lean_object* v_bs_x27_1125_; lean_object* v_a_1127_; 
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_a_1123_);
lean_dec_ref_known(v___x_1122_, 1);
v___x_1124_ = lean_unsigned_to_nat(0u);
v_bs_x27_1125_ = lean_array_uset(v_bs_1109_, v_i_1108_, v___x_1124_);
if (lean_obj_tag(v_a_1123_) == 6)
{
lean_object* v_val_1132_; lean_object* v_numFields_1133_; uint8_t v___x_1134_; lean_object* v___x_1135_; 
v_val_1132_ = lean_ctor_get(v_a_1123_, 0);
lean_inc_ref(v_val_1132_);
lean_dec_ref_known(v_a_1123_, 1);
v_numFields_1133_ = lean_ctor_get(v_val_1132_, 4);
lean_inc(v_numFields_1133_);
lean_dec_ref(v_val_1132_);
v___x_1134_ = 0;
v___x_1135_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1135_, 0, v_numFields_1133_);
lean_ctor_set(v___x_1135_, 1, v___x_1124_);
lean_ctor_set_uint8(v___x_1135_, sizeof(void*)*2, v___x_1134_);
v_a_1127_ = v___x_1135_;
goto v___jp_1126_;
}
else
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
lean_dec(v_a_1123_);
v___x_1136_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3);
v___x_1137_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19(v___x_1136_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
lean_inc(v_a_1138_);
lean_dec_ref_known(v___x_1137_, 1);
v_a_1127_ = v_a_1138_;
goto v___jp_1126_;
}
else
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
lean_dec_ref(v_bs_x27_1125_);
v_a_1139_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1141_ = v___x_1137_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1137_);
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
}
v___jp_1126_:
{
size_t v___x_1128_; size_t v___x_1129_; lean_object* v___x_1130_; 
v___x_1128_ = ((size_t)1ULL);
v___x_1129_ = lean_usize_add(v_i_1108_, v___x_1128_);
v___x_1130_ = lean_array_uset(v_bs_x27_1125_, v_i_1108_, v_a_1127_);
v_i_1108_ = v___x_1129_;
v_bs_1109_ = v___x_1130_;
goto _start;
}
}
else
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
lean_dec_ref(v_bs_1109_);
v_a_1147_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_1122_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1122_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1147_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___boxed(lean_object* v_sz_1155_, lean_object* v_i_1156_, lean_object* v_bs_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
size_t v_sz_boxed_1167_; size_t v_i_boxed_1168_; lean_object* v_res_1169_; 
v_sz_boxed_1167_ = lean_unbox_usize(v_sz_1155_);
lean_dec(v_sz_1155_);
v_i_boxed_1168_ = lean_unbox_usize(v_i_1156_);
lean_dec(v_i_1156_);
v_res_1169_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21(v_sz_boxed_1167_, v_i_boxed_1168_, v_bs_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec(v___y_1158_);
return v_res_1169_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0(void){
_start:
{
lean_object* v___x_1170_; lean_object* v_dummy_1171_; 
v___x_1170_ = lean_box(0);
v_dummy_1171_ = l_Lean_Expr_sort___override(v___x_1170_);
return v_dummy_1171_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1(void){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1172_ = lean_box(0);
v___x_1173_ = lean_unsigned_to_nat(16u);
v___x_1174_ = lean_mk_array(v___x_1173_, v___x_1172_);
return v___x_1174_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2(void){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1175_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1);
v___x_1176_ = lean_unsigned_to_nat(0u);
v___x_1177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1176_);
lean_ctor_set(v___x_1177_, 1, v___x_1175_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(lean_object* v_e_1180_, uint8_t v_alsoCasesOn_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
uint8_t v___x_1194_; 
v___x_1194_ = l_Lean_Expr_isApp(v_e_1180_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
lean_dec_ref(v_e_1180_);
v___x_1195_ = lean_box(0);
v___x_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
return v___x_1196_;
}
else
{
lean_object* v___x_1197_; 
v___x_1197_ = l_Lean_Expr_getAppFn(v_e_1180_);
if (lean_obj_tag(v___x_1197_) == 4)
{
lean_object* v_declName_1198_; lean_object* v_us_1199_; lean_object* v___x_1200_; lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1354_; 
v_declName_1198_ = lean_ctor_get(v___x_1197_, 0);
lean_inc_n(v_declName_1198_, 2);
v_us_1199_ = lean_ctor_get(v___x_1197_, 1);
lean_inc(v_us_1199_);
lean_dec_ref_known(v___x_1197_, 2);
v___x_1200_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(v_declName_1198_, v___y_1189_);
v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1203_ = v___x_1200_;
v_isShared_1204_ = v_isSharedCheck_1354_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1200_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1354_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1205_; 
v___x_1205_ = l_Lean_instInhabitedExpr;
if (lean_obj_tag(v_a_1201_) == 1)
{
lean_object* v_val_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1247_; 
v_val_1206_ = lean_ctor_get(v_a_1201_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v_a_1201_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1208_ = v_a_1201_;
v_isShared_1209_ = v_isSharedCheck_1247_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_val_1206_);
lean_dec(v_a_1201_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1247_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v_dummy_1210_; lean_object* v_nargs_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v_args_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; uint8_t v___x_1218_; 
v_dummy_1210_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
v_nargs_1211_ = l_Lean_Expr_getAppNumArgs(v_e_1180_);
lean_inc(v_nargs_1211_);
v___x_1212_ = lean_mk_array(v_nargs_1211_, v_dummy_1210_);
v___x_1213_ = lean_unsigned_to_nat(1u);
v___x_1214_ = lean_nat_sub(v_nargs_1211_, v___x_1213_);
lean_dec(v_nargs_1211_);
v_args_1215_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1180_, v___x_1212_, v___x_1214_);
v___x_1216_ = lean_array_get_size(v_args_1215_);
v___x_1217_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_1206_);
v___x_1218_ = lean_nat_dec_lt(v___x_1216_, v___x_1217_);
lean_dec(v___x_1217_);
if (v___x_1218_ == 0)
{
lean_object* v_numParams_1219_; lean_object* v_numDiscrs_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1238_; 
v_numParams_1219_ = lean_ctor_get(v_val_1206_, 0);
v_numDiscrs_1220_ = lean_ctor_get(v_val_1206_, 1);
v___x_1221_ = lean_array_mk(v_us_1199_);
v___x_1222_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1219_);
v___x_1223_ = l_Array_extract___redArg(v_args_1215_, v___x_1222_, v_numParams_1219_);
v___x_1224_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_1206_);
v___x_1225_ = lean_array_get(v___x_1205_, v_args_1215_, v___x_1224_);
lean_dec(v___x_1224_);
v___x_1226_ = lean_nat_add(v_numParams_1219_, v___x_1213_);
v___x_1227_ = lean_nat_add(v___x_1226_, v_numDiscrs_1220_);
lean_inc(v___x_1227_);
lean_inc_ref_n(v_args_1215_, 2);
v___x_1228_ = l_Array_toSubarray___redArg(v_args_1215_, v___x_1226_, v___x_1227_);
v___x_1229_ = l_Subarray_copy___redArg(v___x_1228_);
v___x_1230_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1206_);
v___x_1231_ = lean_nat_add(v___x_1227_, v___x_1230_);
lean_dec(v___x_1230_);
lean_inc(v___x_1231_);
v___x_1232_ = l_Array_toSubarray___redArg(v_args_1215_, v___x_1227_, v___x_1231_);
v___x_1233_ = l_Subarray_copy___redArg(v___x_1232_);
v___x_1234_ = l_Array_toSubarray___redArg(v_args_1215_, v___x_1231_, v___x_1216_);
v___x_1235_ = l_Subarray_copy___redArg(v___x_1234_);
v___x_1236_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1236_, 0, v_val_1206_);
lean_ctor_set(v___x_1236_, 1, v_declName_1198_);
lean_ctor_set(v___x_1236_, 2, v___x_1221_);
lean_ctor_set(v___x_1236_, 3, v___x_1223_);
lean_ctor_set(v___x_1236_, 4, v___x_1225_);
lean_ctor_set(v___x_1236_, 5, v___x_1229_);
lean_ctor_set(v___x_1236_, 6, v___x_1233_);
lean_ctor_set(v___x_1236_, 7, v___x_1235_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v___x_1236_);
v___x_1238_ = v___x_1208_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1236_);
v___x_1238_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
lean_object* v___x_1240_; 
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 0, v___x_1238_);
v___x_1240_ = v___x_1203_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1238_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
else
{
lean_object* v___x_1243_; lean_object* v___x_1245_; 
lean_dec_ref(v_args_1215_);
lean_del_object(v___x_1208_);
lean_dec(v_val_1206_);
lean_dec(v_us_1199_);
lean_dec(v_declName_1198_);
v___x_1243_ = lean_box(0);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 0, v___x_1243_);
v___x_1245_ = v___x_1203_;
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
}
else
{
lean_object* v___x_1248_; 
lean_del_object(v___x_1203_);
lean_dec(v_a_1201_);
v___x_1248_ = lean_st_ref_get(v___y_1189_);
if (v_alsoCasesOn_1181_ == 0)
{
lean_dec(v___x_1248_);
lean_dec(v_us_1199_);
lean_dec(v_declName_1198_);
lean_dec_ref(v_e_1180_);
goto v___jp_1191_;
}
else
{
lean_object* v_env_1249_; uint8_t v___x_1250_; 
v_env_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc_ref(v_env_1249_);
lean_dec(v___x_1248_);
lean_inc(v_declName_1198_);
v___x_1250_ = l_Lean_isCasesOnRecursor(v_env_1249_, v_declName_1198_);
if (v___x_1250_ == 0)
{
lean_dec(v_us_1199_);
lean_dec(v_declName_1198_);
lean_dec_ref(v_e_1180_);
goto v___jp_1191_;
}
else
{
lean_object* v_indName_1251_; lean_object* v___x_1252_; 
v_indName_1251_ = l_Lean_Name_getPrefix(v_declName_1198_);
v___x_1252_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(v_indName_1251_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1345_; 
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1255_ = v___x_1252_;
v_isShared_1256_ = v_isSharedCheck_1345_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___x_1252_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1345_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
if (lean_obj_tag(v_a_1253_) == 5)
{
lean_object* v_val_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1340_; 
v_val_1257_ = lean_ctor_get(v_a_1253_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v_a_1253_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1259_ = v_a_1253_;
v_isShared_1260_ = v_isSharedCheck_1340_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_val_1257_);
lean_dec(v_a_1253_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1340_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v_toConstantVal_1261_; lean_object* v_numParams_1262_; lean_object* v_numIndices_1263_; lean_object* v_ctors_1264_; lean_object* v_nargs_1265_; lean_object* v_dummy_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v_args_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; uint8_t v___x_1277_; 
v_toConstantVal_1261_ = lean_ctor_get(v_val_1257_, 0);
lean_inc_ref(v_toConstantVal_1261_);
v_numParams_1262_ = lean_ctor_get(v_val_1257_, 1);
lean_inc(v_numParams_1262_);
v_numIndices_1263_ = lean_ctor_get(v_val_1257_, 2);
lean_inc(v_numIndices_1263_);
v_ctors_1264_ = lean_ctor_get(v_val_1257_, 4);
lean_inc(v_ctors_1264_);
v_nargs_1265_ = l_Lean_Expr_getAppNumArgs(v_e_1180_);
v_dummy_1266_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v_nargs_1265_);
v___x_1267_ = lean_mk_array(v_nargs_1265_, v_dummy_1266_);
v___x_1268_ = lean_unsigned_to_nat(1u);
v___x_1269_ = lean_nat_sub(v_nargs_1265_, v___x_1268_);
lean_dec(v_nargs_1265_);
v_args_1270_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1180_, v___x_1267_, v___x_1269_);
v___x_1271_ = lean_nat_add(v_numParams_1262_, v___x_1268_);
v___x_1272_ = lean_nat_add(v___x_1271_, v_numIndices_1263_);
v___x_1273_ = lean_nat_add(v___x_1272_, v___x_1268_);
lean_dec(v___x_1272_);
v___x_1274_ = l_Lean_InductiveVal_numCtors(v_val_1257_);
lean_dec_ref(v_val_1257_);
v___x_1275_ = lean_nat_add(v___x_1273_, v___x_1274_);
lean_dec(v___x_1274_);
v___x_1276_ = lean_array_get_size(v_args_1270_);
v___x_1277_ = lean_nat_dec_le(v___x_1275_, v___x_1276_);
if (v___x_1277_ == 0)
{
lean_object* v___x_1278_; lean_object* v___x_1280_; 
lean_dec(v___x_1275_);
lean_dec(v___x_1273_);
lean_dec(v___x_1271_);
lean_dec_ref(v_args_1270_);
lean_dec(v_ctors_1264_);
lean_dec(v_numIndices_1263_);
lean_dec(v_numParams_1262_);
lean_dec_ref(v_toConstantVal_1261_);
lean_del_object(v___x_1259_);
lean_dec(v_us_1199_);
lean_dec(v_declName_1198_);
v___x_1278_ = lean_box(0);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 0, v___x_1278_);
v___x_1280_ = v___x_1255_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1278_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
else
{
lean_object* v___x_1282_; lean_object* v_params_1283_; lean_object* v_motive_1284_; lean_object* v_discrs_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v_discrInfos_1288_; lean_object* v_alts_1289_; lean_object* v___y_1291_; lean_object* v___y_1292_; lean_object* v_lower_1331_; lean_object* v_upper_1332_; uint8_t v___x_1339_; 
lean_del_object(v___x_1255_);
v___x_1282_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1262_);
lean_inc_ref_n(v_args_1270_, 3);
v_params_1283_ = l_Array_toSubarray___redArg(v_args_1270_, v___x_1282_, v_numParams_1262_);
v_motive_1284_ = lean_array_get(v___x_1205_, v_args_1270_, v_numParams_1262_);
lean_dec(v_numParams_1262_);
lean_inc(v___x_1273_);
v_discrs_1285_ = l_Array_toSubarray___redArg(v_args_1270_, v___x_1271_, v___x_1273_);
v___x_1286_ = lean_nat_add(v_numIndices_1263_, v___x_1268_);
lean_dec(v_numIndices_1263_);
v___x_1287_ = lean_box(0);
v_discrInfos_1288_ = lean_mk_array(v___x_1286_, v___x_1287_);
lean_inc(v___x_1275_);
v_alts_1289_ = l_Array_toSubarray___redArg(v_args_1270_, v___x_1273_, v___x_1275_);
v___x_1339_ = lean_nat_dec_le(v___x_1275_, v___x_1282_);
if (v___x_1339_ == 0)
{
v_lower_1331_ = v___x_1275_;
v_upper_1332_ = v___x_1276_;
goto v___jp_1330_;
}
else
{
lean_dec(v___x_1275_);
v_lower_1331_ = v___x_1282_;
v_upper_1332_ = v___x_1276_;
goto v___jp_1330_;
}
v___jp_1290_:
{
lean_object* v___x_1293_; size_t v_sz_1294_; size_t v___x_1295_; lean_object* v___x_1296_; 
v___x_1293_ = lean_array_mk(v_ctors_1264_);
v_sz_1294_ = lean_array_size(v___x_1293_);
v___x_1295_ = ((size_t)0ULL);
v___x_1296_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21(v_sz_1294_, v___x_1295_, v___x_1293_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1321_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1299_ = v___x_1296_;
v_isShared_1300_ = v_isSharedCheck_1321_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1296_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1321_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v_start_1301_; lean_object* v_stop_1302_; lean_object* v_start_1303_; lean_object* v_stop_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1316_; 
v_start_1301_ = lean_ctor_get(v_params_1283_, 1);
lean_inc(v_start_1301_);
v_stop_1302_ = lean_ctor_get(v_params_1283_, 2);
lean_inc(v_stop_1302_);
v_start_1303_ = lean_ctor_get(v_discrs_1285_, 1);
lean_inc(v_start_1303_);
v_stop_1304_ = lean_ctor_get(v_discrs_1285_, 2);
lean_inc(v_stop_1304_);
v___x_1305_ = lean_nat_sub(v_stop_1302_, v_start_1301_);
lean_dec(v_start_1301_);
lean_dec(v_stop_1302_);
v___x_1306_ = lean_nat_sub(v_stop_1304_, v_start_1303_);
lean_dec(v_start_1303_);
lean_dec(v_stop_1304_);
v___x_1307_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2);
v___x_1308_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1305_);
lean_ctor_set(v___x_1308_, 1, v___x_1306_);
lean_ctor_set(v___x_1308_, 2, v_a_1297_);
lean_ctor_set(v___x_1308_, 3, v___y_1292_);
lean_ctor_set(v___x_1308_, 4, v_discrInfos_1288_);
lean_ctor_set(v___x_1308_, 5, v___x_1307_);
v___x_1309_ = lean_array_mk(v_us_1199_);
v___x_1310_ = l_Subarray_copy___redArg(v_params_1283_);
v___x_1311_ = l_Subarray_copy___redArg(v_discrs_1285_);
v___x_1312_ = l_Subarray_copy___redArg(v_alts_1289_);
v___x_1313_ = l_Subarray_copy___redArg(v___y_1291_);
v___x_1314_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1308_);
lean_ctor_set(v___x_1314_, 1, v_declName_1198_);
lean_ctor_set(v___x_1314_, 2, v___x_1309_);
lean_ctor_set(v___x_1314_, 3, v___x_1310_);
lean_ctor_set(v___x_1314_, 4, v_motive_1284_);
lean_ctor_set(v___x_1314_, 5, v___x_1311_);
lean_ctor_set(v___x_1314_, 6, v___x_1312_);
lean_ctor_set(v___x_1314_, 7, v___x_1313_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set_tag(v___x_1259_, 1);
lean_ctor_set(v___x_1259_, 0, v___x_1314_);
v___x_1316_ = v___x_1259_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1314_);
v___x_1316_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
lean_object* v___x_1318_; 
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 0, v___x_1316_);
v___x_1318_ = v___x_1299_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1316_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
else
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1329_; 
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec_ref(v_alts_1289_);
lean_dec_ref(v_discrInfos_1288_);
lean_dec_ref(v_discrs_1285_);
lean_dec(v_motive_1284_);
lean_dec_ref(v_params_1283_);
lean_del_object(v___x_1259_);
lean_dec(v_us_1199_);
lean_dec(v_declName_1198_);
v_a_1322_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1324_ = v___x_1296_;
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1296_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1325_ == 0)
{
v___x_1327_ = v___x_1324_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1322_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
}
v___jp_1330_:
{
lean_object* v_levelParams_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; uint8_t v___x_1337_; 
v_levelParams_1333_ = lean_ctor_get(v_toConstantVal_1261_, 1);
lean_inc(v_levelParams_1333_);
lean_dec_ref(v_toConstantVal_1261_);
v___x_1334_ = l_Array_toSubarray___redArg(v_args_1270_, v_lower_1331_, v_upper_1332_);
v___x_1335_ = l_List_lengthTR___redArg(v_levelParams_1333_);
lean_dec(v_levelParams_1333_);
v___x_1336_ = l_List_lengthTR___redArg(v_us_1199_);
v___x_1337_ = lean_nat_dec_eq(v___x_1335_, v___x_1336_);
lean_dec(v___x_1336_);
lean_dec(v___x_1335_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1338_; 
v___x_1338_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__3));
v___y_1291_ = v___x_1334_;
v___y_1292_ = v___x_1338_;
goto v___jp_1290_;
}
else
{
v___y_1291_ = v___x_1334_;
v___y_1292_ = v___x_1287_;
goto v___jp_1290_;
}
}
}
}
}
else
{
lean_object* v___x_1341_; lean_object* v___x_1343_; 
lean_dec(v_a_1253_);
lean_dec(v_us_1199_);
lean_dec(v_declName_1198_);
lean_dec_ref(v_e_1180_);
v___x_1341_ = lean_box(0);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 0, v___x_1341_);
v___x_1343_ = v___x_1255_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1341_);
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
else
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1353_; 
lean_dec(v_us_1199_);
lean_dec(v_declName_1198_);
lean_dec_ref(v_e_1180_);
v_a_1346_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1348_ = v___x_1252_;
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1252_);
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
}
}
}
else
{
lean_dec_ref(v___x_1197_);
lean_dec_ref(v_e_1180_);
goto v___jp_1191_;
}
}
v___jp_1191_:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1192_ = lean_box(0);
v___x_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
return v___x_1193_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___boxed(lean_object* v_e_1355_, lean_object* v_alsoCasesOn_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
uint8_t v_alsoCasesOn_boxed_1366_; lean_object* v_res_1367_; 
v_alsoCasesOn_boxed_1366_ = lean_unbox(v_alsoCasesOn_1356_);
v_res_1367_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(v_e_1355_, v_alsoCasesOn_boxed_1366_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec(v___y_1358_);
lean_dec(v___y_1357_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0(lean_object* v_k_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v_b_1373_, lean_object* v_c_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v___x_1380_; 
lean_inc(v___y_1378_);
lean_inc_ref(v___y_1377_);
lean_inc(v___y_1376_);
lean_inc_ref(v___y_1375_);
lean_inc(v___y_1372_);
lean_inc_ref(v___y_1371_);
lean_inc(v___y_1370_);
lean_inc(v___y_1369_);
v___x_1380_ = lean_apply_11(v_k_1368_, v_b_1373_, v_c_1374_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, lean_box(0));
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0___boxed(lean_object* v_k_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v_b_1386_, lean_object* v_c_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0(v_k_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v_b_1386_, v_c_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec(v___y_1382_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(lean_object* v_e_1394_, lean_object* v_maxFVars_1395_, lean_object* v_k_1396_, uint8_t v_cleanupAnnotations_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v___f_1407_; uint8_t v___x_1408_; uint8_t v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
lean_inc(v___y_1401_);
lean_inc_ref(v___y_1400_);
lean_inc(v___y_1399_);
lean_inc(v___y_1398_);
v___f_1407_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1407_, 0, v_k_1396_);
lean_closure_set(v___f_1407_, 1, v___y_1398_);
lean_closure_set(v___f_1407_, 2, v___y_1399_);
lean_closure_set(v___f_1407_, 3, v___y_1400_);
lean_closure_set(v___f_1407_, 4, v___y_1401_);
v___x_1408_ = 1;
v___x_1409_ = 0;
v___x_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1410_, 0, v_maxFVars_1395_);
v___x_1411_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1394_, v___x_1408_, v___x_1409_, v___x_1408_, v___x_1409_, v___x_1410_, v___f_1407_, v_cleanupAnnotations_1397_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
lean_dec_ref_known(v___x_1410_, 1);
if (lean_obj_tag(v___x_1411_) == 0)
{
return v___x_1411_;
}
else
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1414_ = v___x_1411_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1411_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1412_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___boxed(lean_object* v_e_1420_, lean_object* v_maxFVars_1421_, lean_object* v_k_1422_, lean_object* v_cleanupAnnotations_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1433_; lean_object* v_res_1434_; 
v_cleanupAnnotations_boxed_1433_ = lean_unbox(v_cleanupAnnotations_1423_);
v_res_1434_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(v_e_1420_, v_maxFVars_1421_, v_k_1422_, v_cleanupAnnotations_boxed_1433_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v___y_1425_);
lean_dec(v___y_1424_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0(lean_object* v_k_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v_b_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v___x_1446_; 
lean_inc(v___y_1444_);
lean_inc_ref(v___y_1443_);
lean_inc(v___y_1442_);
lean_inc_ref(v___y_1441_);
lean_inc(v___y_1439_);
lean_inc_ref(v___y_1438_);
lean_inc(v___y_1437_);
lean_inc(v___y_1436_);
v___x_1446_ = lean_apply_10(v_k_1435_, v_b_1440_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, lean_box(0));
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0___boxed(lean_object* v_k_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v_b_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0(v_k_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v_b_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec(v___y_1449_);
lean_dec(v___y_1448_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(lean_object* v_name_1459_, lean_object* v_type_1460_, lean_object* v_val_1461_, lean_object* v_k_1462_, uint8_t v_nondep_1463_, uint8_t v_kind_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v___f_1474_; lean_object* v___x_1475_; 
lean_inc(v___y_1468_);
lean_inc_ref(v___y_1467_);
lean_inc(v___y_1466_);
lean_inc(v___y_1465_);
v___f_1474_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1474_, 0, v_k_1462_);
lean_closure_set(v___f_1474_, 1, v___y_1465_);
lean_closure_set(v___f_1474_, 2, v___y_1466_);
lean_closure_set(v___f_1474_, 3, v___y_1467_);
lean_closure_set(v___f_1474_, 4, v___y_1468_);
v___x_1475_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1459_, v_type_1460_, v_val_1461_, v___f_1474_, v_nondep_1463_, v_kind_1464_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
if (lean_obj_tag(v___x_1475_) == 0)
{
return v___x_1475_;
}
else
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1475_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1475_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1476_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg___boxed(lean_object* v_name_1484_, lean_object* v_type_1485_, lean_object* v_val_1486_, lean_object* v_k_1487_, lean_object* v_nondep_1488_, lean_object* v_kind_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
uint8_t v_nondep_boxed_1499_; uint8_t v_kind_boxed_1500_; lean_object* v_res_1501_; 
v_nondep_boxed_1499_ = lean_unbox(v_nondep_1488_);
v_kind_boxed_1500_ = lean_unbox(v_kind_1489_);
v_res_1501_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(v_name_1484_, v_type_1485_, v_val_1486_, v_k_1487_, v_nondep_boxed_1499_, v_kind_boxed_1500_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec(v___y_1490_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0(lean_object* v_k_1502_, uint8_t v_usedLetOnly_1503_, lean_object* v_x_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v___x_1514_; 
lean_inc(v___y_1512_);
lean_inc_ref(v___y_1511_);
lean_inc(v___y_1510_);
lean_inc_ref(v___y_1509_);
lean_inc(v___y_1508_);
lean_inc_ref(v___y_1507_);
lean_inc(v___y_1506_);
lean_inc(v___y_1505_);
lean_inc_ref(v_x_1504_);
v___x_1514_ = lean_apply_10(v_k_1502_, v_x_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, lean_box(0));
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; uint8_t v___x_1519_; uint8_t v___x_1520_; lean_object* v___x_1521_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_a_1515_);
lean_dec_ref_known(v___x_1514_, 1);
v___x_1516_ = lean_unsigned_to_nat(1u);
v___x_1517_ = lean_mk_empty_array_with_capacity(v___x_1516_);
v___x_1518_ = lean_array_push(v___x_1517_, v_x_1504_);
v___x_1519_ = 0;
v___x_1520_ = 1;
v___x_1521_ = l_Lean_Meta_mkLetFVars(v___x_1518_, v_a_1515_, v_usedLetOnly_1503_, v___x_1519_, v___x_1520_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
lean_dec_ref(v___x_1518_);
return v___x_1521_;
}
else
{
lean_dec_ref(v_x_1504_);
return v___x_1514_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0___boxed(lean_object* v_k_1522_, lean_object* v_usedLetOnly_1523_, lean_object* v_x_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
uint8_t v_usedLetOnly_boxed_1534_; lean_object* v_res_1535_; 
v_usedLetOnly_boxed_1534_ = lean_unbox(v_usedLetOnly_1523_);
v_res_1535_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0(v_k_1522_, v_usedLetOnly_boxed_1534_, v_x_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec(v___y_1525_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(lean_object* v_name_1536_, lean_object* v_type_1537_, lean_object* v_val_1538_, lean_object* v_k_1539_, uint8_t v_nondep_1540_, uint8_t v_kind_1541_, uint8_t v_usedLetOnly_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v___x_1552_; lean_object* v___f_1553_; lean_object* v___x_1554_; 
v___x_1552_ = lean_box(v_usedLetOnly_1542_);
v___f_1553_ = lean_alloc_closure((void*)(l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0___boxed), 12, 2);
lean_closure_set(v___f_1553_, 0, v_k_1539_);
lean_closure_set(v___f_1553_, 1, v___x_1552_);
v___x_1554_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(v_name_1536_, v_type_1537_, v_val_1538_, v___f_1553_, v_nondep_1540_, v_kind_1541_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___boxed(lean_object* v_name_1555_, lean_object* v_type_1556_, lean_object* v_val_1557_, lean_object* v_k_1558_, lean_object* v_nondep_1559_, lean_object* v_kind_1560_, lean_object* v_usedLetOnly_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
uint8_t v_nondep_boxed_1571_; uint8_t v_kind_boxed_1572_; uint8_t v_usedLetOnly_boxed_1573_; lean_object* v_res_1574_; 
v_nondep_boxed_1571_ = lean_unbox(v_nondep_1559_);
v_kind_boxed_1572_ = lean_unbox(v_kind_1560_);
v_usedLetOnly_boxed_1573_ = lean_unbox(v_usedLetOnly_1561_);
v_res_1574_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(v_name_1555_, v_type_1556_, v_val_1557_, v_k_1558_, v_nondep_boxed_1571_, v_kind_boxed_1572_, v_usedLetOnly_boxed_1573_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
lean_dec(v___y_1563_);
lean_dec(v___y_1562_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(lean_object* v_name_1575_, uint8_t v_bi_1576_, lean_object* v_type_1577_, lean_object* v_k_1578_, uint8_t v_kind_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v___f_1589_; lean_object* v___x_1590_; 
lean_inc(v___y_1583_);
lean_inc_ref(v___y_1582_);
lean_inc(v___y_1581_);
lean_inc(v___y_1580_);
v___f_1589_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1589_, 0, v_k_1578_);
lean_closure_set(v___f_1589_, 1, v___y_1580_);
lean_closure_set(v___f_1589_, 2, v___y_1581_);
lean_closure_set(v___f_1589_, 3, v___y_1582_);
lean_closure_set(v___f_1589_, 4, v___y_1583_);
v___x_1590_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1575_, v_bi_1576_, v_type_1577_, v___f_1589_, v_kind_1579_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
if (lean_obj_tag(v___x_1590_) == 0)
{
return v___x_1590_;
}
else
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1593_ = v___x_1590_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1590_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1591_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___boxed(lean_object* v_name_1599_, lean_object* v_bi_1600_, lean_object* v_type_1601_, lean_object* v_k_1602_, lean_object* v_kind_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
uint8_t v_bi_boxed_1613_; uint8_t v_kind_boxed_1614_; lean_object* v_res_1615_; 
v_bi_boxed_1613_ = lean_unbox(v_bi_1600_);
v_kind_boxed_1614_ = lean_unbox(v_kind_1603_);
v_res_1615_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_name_1599_, v_bi_boxed_1613_, v_type_1601_, v_k_1602_, v_kind_boxed_1614_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1605_);
lean_dec(v___y_1604_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0(lean_object* v_k_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v___x_1626_; 
lean_inc(v___y_1620_);
lean_inc_ref(v___y_1619_);
lean_inc(v___y_1618_);
lean_inc(v___y_1617_);
v___x_1626_ = lean_apply_9(v_k_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, lean_box(0));
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0___boxed(lean_object* v_k_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0(v_k_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec(v___y_1628_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(lean_object* v_k_1638_, uint8_t v_allowLevelAssignments_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
lean_object* v___f_1649_; lean_object* v___x_1650_; 
lean_inc(v___y_1643_);
lean_inc_ref(v___y_1642_);
lean_inc(v___y_1641_);
lean_inc(v___y_1640_);
v___f_1649_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1649_, 0, v_k_1638_);
lean_closure_set(v___f_1649_, 1, v___y_1640_);
lean_closure_set(v___f_1649_, 2, v___y_1641_);
lean_closure_set(v___f_1649_, 3, v___y_1642_);
lean_closure_set(v___f_1649_, 4, v___y_1643_);
v___x_1650_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1639_, v___f_1649_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
if (lean_obj_tag(v___x_1650_) == 0)
{
return v___x_1650_;
}
else
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1653_ = v___x_1650_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1650_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1651_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___boxed(lean_object* v_k_1659_, lean_object* v_allowLevelAssignments_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1670_; lean_object* v_res_1671_; 
v_allowLevelAssignments_boxed_1670_ = lean_unbox(v_allowLevelAssignments_1660_);
v_res_1671_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v_k_1659_, v_allowLevelAssignments_boxed_1670_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec(v___y_1662_);
lean_dec(v___y_1661_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(lean_object* v_a_1672_, lean_object* v_x_1673_){
_start:
{
if (lean_obj_tag(v_x_1673_) == 0)
{
lean_object* v___x_1674_; 
v___x_1674_ = lean_box(0);
return v___x_1674_;
}
else
{
lean_object* v_key_1675_; lean_object* v_value_1676_; lean_object* v_tail_1677_; uint8_t v___x_1678_; 
v_key_1675_ = lean_ctor_get(v_x_1673_, 0);
v_value_1676_ = lean_ctor_get(v_x_1673_, 1);
v_tail_1677_ = lean_ctor_get(v_x_1673_, 2);
v___x_1678_ = lean_expr_eqv(v_key_1675_, v_a_1672_);
if (v___x_1678_ == 0)
{
v_x_1673_ = v_tail_1677_;
goto _start;
}
else
{
lean_object* v___x_1680_; 
lean_inc(v_value_1676_);
v___x_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1680_, 0, v_value_1676_);
return v___x_1680_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg___boxed(lean_object* v_a_1681_, lean_object* v_x_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(v_a_1681_, v_x_1682_);
lean_dec(v_x_1682_);
lean_dec_ref(v_a_1681_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(lean_object* v_m_1684_, lean_object* v_a_1685_){
_start:
{
lean_object* v_buckets_1686_; lean_object* v___x_1687_; uint64_t v___x_1688_; uint64_t v___x_1689_; uint64_t v___x_1690_; uint64_t v_fold_1691_; uint64_t v___x_1692_; uint64_t v___x_1693_; uint64_t v___x_1694_; size_t v___x_1695_; size_t v___x_1696_; size_t v___x_1697_; size_t v___x_1698_; size_t v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v_buckets_1686_ = lean_ctor_get(v_m_1684_, 1);
v___x_1687_ = lean_array_get_size(v_buckets_1686_);
v___x_1688_ = l_Lean_Expr_hash(v_a_1685_);
v___x_1689_ = 32ULL;
v___x_1690_ = lean_uint64_shift_right(v___x_1688_, v___x_1689_);
v_fold_1691_ = lean_uint64_xor(v___x_1688_, v___x_1690_);
v___x_1692_ = 16ULL;
v___x_1693_ = lean_uint64_shift_right(v_fold_1691_, v___x_1692_);
v___x_1694_ = lean_uint64_xor(v_fold_1691_, v___x_1693_);
v___x_1695_ = lean_uint64_to_usize(v___x_1694_);
v___x_1696_ = lean_usize_of_nat(v___x_1687_);
v___x_1697_ = ((size_t)1ULL);
v___x_1698_ = lean_usize_sub(v___x_1696_, v___x_1697_);
v___x_1699_ = lean_usize_land(v___x_1695_, v___x_1698_);
v___x_1700_ = lean_array_uget_borrowed(v_buckets_1686_, v___x_1699_);
v___x_1701_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(v_a_1685_, v___x_1700_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg___boxed(lean_object* v_m_1702_, lean_object* v_a_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v_m_1702_, v_a_1703_);
lean_dec_ref(v_a_1703_);
lean_dec_ref(v_m_1702_);
return v_res_1704_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(lean_object* v_opts_1705_, lean_object* v_opt_1706_){
_start:
{
lean_object* v_name_1707_; lean_object* v_defValue_1708_; lean_object* v_map_1709_; lean_object* v___x_1710_; 
v_name_1707_ = lean_ctor_get(v_opt_1706_, 0);
v_defValue_1708_ = lean_ctor_get(v_opt_1706_, 1);
v_map_1709_ = lean_ctor_get(v_opts_1705_, 0);
v___x_1710_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1709_, v_name_1707_);
if (lean_obj_tag(v___x_1710_) == 0)
{
uint8_t v___x_1711_; 
v___x_1711_ = lean_unbox(v_defValue_1708_);
return v___x_1711_;
}
else
{
lean_object* v_val_1712_; 
v_val_1712_ = lean_ctor_get(v___x_1710_, 0);
lean_inc(v_val_1712_);
lean_dec_ref_known(v___x_1710_, 1);
if (lean_obj_tag(v_val_1712_) == 1)
{
uint8_t v_v_1713_; 
v_v_1713_ = lean_ctor_get_uint8(v_val_1712_, 0);
lean_dec_ref_known(v_val_1712_, 0);
return v_v_1713_;
}
else
{
uint8_t v___x_1714_; 
lean_dec(v_val_1712_);
v___x_1714_ = lean_unbox(v_defValue_1708_);
return v___x_1714_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5___boxed(lean_object* v_opts_1715_, lean_object* v_opt_1716_){
_start:
{
uint8_t v_res_1717_; lean_object* v_r_1718_; 
v_res_1717_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v_opts_1715_, v_opt_1716_);
lean_dec_ref(v_opt_1716_);
lean_dec_ref(v_opts_1715_);
v_r_1718_ = lean_box(v_res_1717_);
return v_r_1718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(lean_object* v_a_1719_, lean_object* v_b_1720_){
_start:
{
lean_object* v_array_1721_; lean_object* v_start_1722_; lean_object* v_stop_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1736_; 
v_array_1721_ = lean_ctor_get(v_a_1719_, 0);
v_start_1722_ = lean_ctor_get(v_a_1719_, 1);
v_stop_1723_ = lean_ctor_get(v_a_1719_, 2);
v_isSharedCheck_1736_ = !lean_is_exclusive(v_a_1719_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1725_ = v_a_1719_;
v_isShared_1726_ = v_isSharedCheck_1736_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_stop_1723_);
lean_inc(v_start_1722_);
lean_inc(v_array_1721_);
lean_dec(v_a_1719_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1736_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
uint8_t v___x_1727_; 
v___x_1727_ = lean_nat_dec_lt(v_start_1722_, v_stop_1723_);
if (v___x_1727_ == 0)
{
lean_del_object(v___x_1725_);
lean_dec(v_stop_1723_);
lean_dec(v_start_1722_);
lean_dec_ref(v_array_1721_);
return v_b_1720_;
}
else
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1731_; 
v___x_1728_ = lean_unsigned_to_nat(1u);
v___x_1729_ = lean_nat_add(v_start_1722_, v___x_1728_);
lean_inc_ref(v_array_1721_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 1, v___x_1729_);
v___x_1731_ = v___x_1725_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_array_1721_);
lean_ctor_set(v_reuseFailAlloc_1735_, 1, v___x_1729_);
lean_ctor_set(v_reuseFailAlloc_1735_, 2, v_stop_1723_);
v___x_1731_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1732_ = lean_array_fget(v_array_1721_, v_start_1722_);
lean_dec(v_start_1722_);
lean_dec_ref(v_array_1721_);
v___x_1733_ = lean_array_push(v_b_1720_, v___x_1732_);
v_a_1719_ = v___x_1731_;
v_b_1720_ = v___x_1733_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0(lean_object* v_body_1737_, lean_object* v_recFnName_1738_, lean_object* v_fixedPrefixSize_1739_, lean_object* v_F_1740_, lean_object* v_x_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1751_ = lean_expr_instantiate1(v_body_1737_, v_x_1741_);
v___x_1752_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1738_, v_fixedPrefixSize_1739_, v_F_1740_, v___x_1751_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; uint8_t v___x_1757_; uint8_t v___x_1758_; uint8_t v___x_1759_; lean_object* v___x_1760_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1753_);
lean_dec_ref_known(v___x_1752_, 1);
v___x_1754_ = lean_unsigned_to_nat(1u);
v___x_1755_ = lean_mk_empty_array_with_capacity(v___x_1754_);
v___x_1756_ = lean_array_push(v___x_1755_, v_x_1741_);
v___x_1757_ = 0;
v___x_1758_ = 1;
v___x_1759_ = 1;
v___x_1760_ = l_Lean_Meta_mkLambdaFVars(v___x_1756_, v_a_1753_, v___x_1757_, v___x_1758_, v___x_1757_, v___x_1758_, v___x_1759_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
lean_dec_ref(v___x_1756_);
return v___x_1760_;
}
else
{
lean_dec_ref(v_x_1741_);
return v___x_1752_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0___boxed(lean_object* v_body_1761_, lean_object* v_recFnName_1762_, lean_object* v_fixedPrefixSize_1763_, lean_object* v_F_1764_, lean_object* v_x_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0(v_body_1761_, v_recFnName_1762_, v_fixedPrefixSize_1763_, v_F_1764_, v_x_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
lean_dec(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v_body_1761_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1(lean_object* v_body_1776_, lean_object* v_recFnName_1777_, lean_object* v_fixedPrefixSize_1778_, lean_object* v_F_1779_, lean_object* v_x_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1790_ = lean_expr_instantiate1(v_body_1776_, v_x_1780_);
v___x_1791_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1777_, v_fixedPrefixSize_1778_, v_F_1779_, v___x_1790_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v_a_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; uint8_t v___x_1796_; uint8_t v___x_1797_; uint8_t v___x_1798_; lean_object* v___x_1799_; 
v_a_1792_ = lean_ctor_get(v___x_1791_, 0);
lean_inc(v_a_1792_);
lean_dec_ref_known(v___x_1791_, 1);
v___x_1793_ = lean_unsigned_to_nat(1u);
v___x_1794_ = lean_mk_empty_array_with_capacity(v___x_1793_);
v___x_1795_ = lean_array_push(v___x_1794_, v_x_1780_);
v___x_1796_ = 0;
v___x_1797_ = 1;
v___x_1798_ = 1;
v___x_1799_ = l_Lean_Meta_mkForallFVars(v___x_1795_, v_a_1792_, v___x_1796_, v___x_1797_, v___x_1797_, v___x_1798_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
lean_dec_ref(v___x_1795_);
return v___x_1799_;
}
else
{
lean_dec_ref(v_x_1780_);
return v___x_1791_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1___boxed(lean_object* v_body_1800_, lean_object* v_recFnName_1801_, lean_object* v_fixedPrefixSize_1802_, lean_object* v_F_1803_, lean_object* v_x_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1(v_body_1800_, v_recFnName_1801_, v_fixedPrefixSize_1802_, v_F_1803_, v_x_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v_body_1800_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2___boxed(lean_object* v_body_1815_, lean_object* v_recFnName_1816_, lean_object* v_fixedPrefixSize_1817_, lean_object* v_F_1818_, lean_object* v_x_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2(v_body_1815_, v_recFnName_1816_, v_fixedPrefixSize_1817_, v_F_1818_, v_x_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1821_);
lean_dec(v___y_1820_);
lean_dec_ref(v_x_1819_);
lean_dec_ref(v_body_1815_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(lean_object* v_recFnName_1832_, lean_object* v_fixedPrefixSize_1833_, lean_object* v_F_1834_, size_t v_sz_1835_, size_t v_i_1836_, lean_object* v_bs_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
uint8_t v___x_1847_; 
v___x_1847_ = lean_usize_dec_lt(v_i_1836_, v_sz_1835_);
if (v___x_1847_ == 0)
{
lean_object* v___x_1848_; 
lean_dec_ref(v_F_1834_);
lean_dec(v_fixedPrefixSize_1833_);
lean_dec(v_recFnName_1832_);
v___x_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1848_, 0, v_bs_1837_);
return v___x_1848_;
}
else
{
lean_object* v_v_1849_; lean_object* v___x_1850_; 
v_v_1849_ = lean_array_uget_borrowed(v_bs_1837_, v_i_1836_);
lean_inc(v_v_1849_);
lean_inc_ref(v_F_1834_);
lean_inc(v_fixedPrefixSize_1833_);
lean_inc(v_recFnName_1832_);
v___x_1850_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1832_, v_fixedPrefixSize_1833_, v_F_1834_, v_v_1849_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v_a_1851_; lean_object* v___x_1852_; lean_object* v_bs_x27_1853_; size_t v___x_1854_; size_t v___x_1855_; lean_object* v___x_1856_; 
v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
lean_inc(v_a_1851_);
lean_dec_ref_known(v___x_1850_, 1);
v___x_1852_ = lean_unsigned_to_nat(0u);
v_bs_x27_1853_ = lean_array_uset(v_bs_1837_, v_i_1836_, v___x_1852_);
v___x_1854_ = ((size_t)1ULL);
v___x_1855_ = lean_usize_add(v_i_1836_, v___x_1854_);
v___x_1856_ = lean_array_uset(v_bs_x27_1853_, v_i_1836_, v_a_1851_);
v_i_1836_ = v___x_1855_;
v_bs_1837_ = v___x_1856_;
goto _start;
}
else
{
lean_object* v_a_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1865_; 
lean_dec_ref(v_bs_1837_);
lean_dec_ref(v_F_1834_);
lean_dec(v_fixedPrefixSize_1833_);
lean_dec(v_recFnName_1832_);
v_a_1858_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1860_ = v___x_1850_;
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_a_1858_);
lean_dec(v___x_1850_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1863_; 
if (v_isShared_1861_ == 0)
{
v___x_1863_ = v___x_1860_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_a_1858_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4(void){
_start:
{
lean_object* v_cls_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v_cls_1873_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_1874_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__3));
v___x_1875_ = l_Lean_Name_append(v___x_1874_, v_cls_1873_);
return v___x_1875_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6(void){
_start:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1877_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5));
v___x_1878_ = l_Lean_stringToMessageData(v___x_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(lean_object* v_recFnName_1879_, lean_object* v_fixedPrefixSize_1880_, lean_object* v_F_1881_, lean_object* v_e_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_){
_start:
{
lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; uint8_t v___x_1907_; 
v___x_1904_ = l_Lean_Expr_getAppNumArgs(v_e_1882_);
v___x_1905_ = lean_unsigned_to_nat(1u);
v___x_1906_ = lean_nat_add(v_fixedPrefixSize_1880_, v___x_1905_);
v___x_1907_ = lean_nat_dec_lt(v___x_1904_, v___x_1906_);
if (v___x_1907_ == 0)
{
lean_object* v___x_1908_; lean_object* v_dummy_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v_args_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1908_ = l_Lean_instInhabitedExpr;
v_dummy_1909_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_1904_);
v___x_1910_ = lean_mk_array(v___x_1904_, v_dummy_1909_);
v___x_1911_ = lean_nat_sub(v___x_1904_, v___x_1905_);
lean_dec(v___x_1904_);
v_args_1912_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1882_, v___x_1910_, v___x_1911_);
v___x_1913_ = lean_array_get(v___x_1908_, v_args_1912_, v_fixedPrefixSize_1880_);
lean_inc_ref(v_F_1881_);
lean_inc(v_fixedPrefixSize_1880_);
lean_inc(v_recFnName_1879_);
v___x_1914_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1879_, v_fixedPrefixSize_1880_, v_F_1881_, v___x_1913_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_a_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
lean_inc(v_a_1915_);
lean_dec_ref_known(v___x_1914_, 1);
lean_inc_ref(v_F_1881_);
v___x_1916_ = l_Lean_Expr_app___override(v_F_1881_, v_a_1915_);
lean_inc(v_a_1890_);
lean_inc_ref(v_a_1889_);
lean_inc(v_a_1888_);
lean_inc_ref(v_a_1887_);
lean_inc_ref(v___x_1916_);
v___x_1917_ = lean_infer_type(v___x_1916_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v___x_1919_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
lean_dec_ref_known(v___x_1917_, 1);
lean_inc(v_a_1890_);
lean_inc_ref(v_a_1889_);
lean_inc(v_a_1888_);
lean_inc_ref(v_a_1887_);
v___x_1919_ = lean_whnf(v_a_1918_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_a_1920_);
lean_dec_ref_known(v___x_1919_, 1);
v___x_1921_ = l_Lean_Expr_bindingDomain_x21(v_a_1920_);
lean_dec(v_a_1920_);
v___x_1922_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg(v___x_1921_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v_a_1923_; lean_object* v___x_1924_; lean_object* v_lower_1926_; lean_object* v_upper_1927_; lean_object* v___x_1951_; lean_object* v___x_1952_; uint8_t v___x_1953_; 
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
lean_inc(v_a_1923_);
lean_dec_ref_known(v___x_1922_, 1);
v___x_1924_ = l_Lean_Expr_app___override(v___x_1916_, v_a_1923_);
v___x_1951_ = lean_unsigned_to_nat(0u);
v___x_1952_ = lean_array_get_size(v_args_1912_);
v___x_1953_ = lean_nat_dec_le(v___x_1906_, v___x_1951_);
if (v___x_1953_ == 0)
{
v_lower_1926_ = v___x_1906_;
v_upper_1927_ = v___x_1952_;
goto v___jp_1925_;
}
else
{
lean_dec(v___x_1906_);
v_lower_1926_ = v___x_1951_;
v_upper_1927_ = v___x_1952_;
goto v___jp_1925_;
}
v___jp_1925_:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; size_t v_sz_1931_; size_t v___x_1932_; lean_object* v___x_1933_; 
v___x_1928_ = l_Array_toSubarray___redArg(v_args_1912_, v_lower_1926_, v_upper_1927_);
v___x_1929_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
v___x_1930_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(v___x_1928_, v___x_1929_);
v_sz_1931_ = lean_array_size(v___x_1930_);
v___x_1932_ = ((size_t)0ULL);
v___x_1933_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_1879_, v_fixedPrefixSize_1880_, v_F_1881_, v_sz_1931_, v___x_1932_, v___x_1930_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1942_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1936_ = v___x_1933_;
v_isShared_1937_ = v_isSharedCheck_1942_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1933_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1942_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1938_; lean_object* v___x_1940_; 
v___x_1938_ = l_Lean_mkAppN(v___x_1924_, v_a_1934_);
lean_dec(v_a_1934_);
if (v_isShared_1937_ == 0)
{
lean_ctor_set(v___x_1936_, 0, v___x_1938_);
v___x_1940_ = v___x_1936_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v___x_1938_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
}
else
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
lean_dec_ref(v___x_1924_);
v_a_1943_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v___x_1933_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1933_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1943_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1916_);
lean_dec_ref(v_args_1912_);
lean_dec(v___x_1906_);
lean_dec_ref(v_F_1881_);
lean_dec(v_fixedPrefixSize_1880_);
lean_dec(v_recFnName_1879_);
return v___x_1922_;
}
}
else
{
lean_dec_ref(v___x_1916_);
lean_dec_ref(v_args_1912_);
lean_dec(v___x_1906_);
lean_dec_ref(v_F_1881_);
lean_dec(v_fixedPrefixSize_1880_);
lean_dec(v_recFnName_1879_);
return v___x_1919_;
}
}
else
{
lean_dec_ref(v___x_1916_);
lean_dec_ref(v_args_1912_);
lean_dec(v___x_1906_);
lean_dec_ref(v_F_1881_);
lean_dec(v_fixedPrefixSize_1880_);
lean_dec(v_recFnName_1879_);
return v___x_1917_;
}
}
else
{
lean_dec_ref(v_args_1912_);
lean_dec(v___x_1906_);
lean_dec_ref(v_F_1881_);
lean_dec(v_fixedPrefixSize_1880_);
lean_dec(v_recFnName_1879_);
return v___x_1914_;
}
}
else
{
lean_object* v_toCold_1954_; lean_object* v_options_1955_; uint8_t v_hasTrace_1956_; 
lean_dec(v___x_1906_);
lean_dec(v___x_1904_);
v_toCold_1954_ = lean_ctor_get(v_a_1889_, 0);
v_options_1955_ = lean_ctor_get(v_toCold_1954_, 2);
v_hasTrace_1956_ = lean_ctor_get_uint8(v_options_1955_, sizeof(void*)*1);
if (v_hasTrace_1956_ == 0)
{
v___y_1893_ = v_a_1883_;
v___y_1894_ = v_a_1884_;
v___y_1895_ = v_a_1885_;
v___y_1896_ = v_a_1886_;
v___y_1897_ = v_a_1887_;
v___y_1898_ = v_a_1888_;
v___y_1899_ = v_a_1889_;
v___y_1900_ = v_a_1890_;
goto v___jp_1892_;
}
else
{
lean_object* v_inheritedTraceOptions_1957_; lean_object* v_cls_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; 
v_inheritedTraceOptions_1957_ = lean_ctor_get(v_toCold_1954_, 11);
v_cls_1958_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_1959_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_1960_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1957_, v_options_1955_, v___x_1959_);
if (v___x_1960_ == 0)
{
v___y_1893_ = v_a_1883_;
v___y_1894_ = v_a_1884_;
v___y_1895_ = v_a_1885_;
v___y_1896_ = v_a_1886_;
v___y_1897_ = v_a_1887_;
v___y_1898_ = v_a_1888_;
v___y_1899_ = v_a_1889_;
v___y_1900_ = v_a_1890_;
goto v___jp_1892_;
}
else
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1961_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6);
lean_inc_ref(v_e_1882_);
v___x_1962_ = l_Lean_indentExpr(v_e_1882_);
v___x_1963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1961_);
lean_ctor_set(v___x_1963_, 1, v___x_1962_);
v___x_1964_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(v_cls_1958_, v___x_1963_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_dec_ref_known(v___x_1964_, 1);
v___y_1893_ = v_a_1883_;
v___y_1894_ = v_a_1884_;
v___y_1895_ = v_a_1885_;
v___y_1896_ = v_a_1886_;
v___y_1897_ = v_a_1887_;
v___y_1898_ = v_a_1888_;
v___y_1899_ = v_a_1889_;
v___y_1900_ = v_a_1890_;
goto v___jp_1892_;
}
else
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1972_; 
lean_dec_ref(v_e_1882_);
lean_dec_ref(v_F_1881_);
lean_dec(v_fixedPrefixSize_1880_);
lean_dec(v_recFnName_1879_);
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1967_ = v___x_1964_;
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1964_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1970_; 
if (v_isShared_1968_ == 0)
{
v___x_1970_ = v___x_1967_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_a_1965_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
}
}
v___jp_1892_:
{
lean_object* v___x_1901_; 
v___x_1901_ = l_Lean_Meta_etaExpand(v_e_1882_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1903_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
lean_inc(v_a_1902_);
lean_dec_ref_known(v___x_1901_, 1);
v___x_1903_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1879_, v_fixedPrefixSize_1880_, v_F_1881_, v_a_1902_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
return v___x_1903_;
}
else
{
lean_dec_ref(v_F_1881_);
lean_dec(v_fixedPrefixSize_1880_);
lean_dec(v_recFnName_1879_);
return v___x_1901_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(lean_object* v_recFnName_1973_, lean_object* v_fixedPrefixSize_1974_, lean_object* v_F_1975_, lean_object* v_x_1976_, lean_object* v_x_1977_, lean_object* v_x_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
if (lean_obj_tag(v_x_1976_) == 5)
{
lean_object* v_fn_1988_; lean_object* v_arg_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v_fn_1988_ = lean_ctor_get(v_x_1976_, 0);
lean_inc_ref(v_fn_1988_);
v_arg_1989_ = lean_ctor_get(v_x_1976_, 1);
lean_inc_ref(v_arg_1989_);
lean_dec_ref_known(v_x_1976_, 2);
v___x_1990_ = lean_array_set(v_x_1977_, v_x_1978_, v_arg_1989_);
v___x_1991_ = lean_unsigned_to_nat(1u);
v___x_1992_ = lean_nat_sub(v_x_1978_, v___x_1991_);
lean_dec(v_x_1978_);
v_x_1976_ = v_fn_1988_;
v_x_1977_ = v___x_1990_;
v_x_1978_ = v___x_1992_;
goto _start;
}
else
{
lean_object* v___x_1994_; 
lean_dec(v_x_1978_);
lean_inc_ref(v_F_1975_);
lean_inc(v_fixedPrefixSize_1974_);
lean_inc(v_recFnName_1973_);
v___x_1994_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1973_, v_fixedPrefixSize_1974_, v_F_1975_, v_x_1976_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v_a_1995_; size_t v_sz_1996_; size_t v___x_1997_; lean_object* v___x_1998_; 
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
lean_inc(v_a_1995_);
lean_dec_ref_known(v___x_1994_, 1);
v_sz_1996_ = lean_array_size(v_x_1977_);
v___x_1997_ = ((size_t)0ULL);
v___x_1998_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_1973_, v_fixedPrefixSize_1974_, v_F_1975_, v_sz_1996_, v___x_1997_, v_x_1977_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2007_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2001_ = v___x_1998_;
v_isShared_2002_ = v_isSharedCheck_2007_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1998_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2007_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2003_; lean_object* v___x_2005_; 
v___x_2003_ = l_Lean_mkAppN(v_a_1995_, v_a_1999_);
lean_dec(v_a_1999_);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 0, v___x_2003_);
v___x_2005_ = v___x_2001_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_2003_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
else
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
lean_dec(v_a_1995_);
v_a_2008_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2010_ = v___x_1998_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_1998_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2008_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
else
{
lean_dec_ref(v_x_1977_);
lean_dec_ref(v_F_1975_);
lean_dec(v_fixedPrefixSize_1974_);
lean_dec(v_recFnName_1973_);
return v___x_1994_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(lean_object* v_recFnName_2016_, lean_object* v_fixedPrefixSize_2017_, lean_object* v_F_2018_, lean_object* v_e_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_){
_start:
{
uint8_t v___x_2029_; 
v___x_2029_ = l_Lean_Expr_isAppOf(v_e_2019_, v_recFnName_2016_);
if (v___x_2029_ == 0)
{
lean_object* v_dummy_2030_; lean_object* v_nargs_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
v_dummy_2030_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
v_nargs_2031_ = l_Lean_Expr_getAppNumArgs(v_e_2019_);
lean_inc(v_nargs_2031_);
v___x_2032_ = lean_mk_array(v_nargs_2031_, v_dummy_2030_);
v___x_2033_ = lean_unsigned_to_nat(1u);
v___x_2034_ = lean_nat_sub(v_nargs_2031_, v___x_2033_);
lean_dec(v_nargs_2031_);
v___x_2035_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(v_recFnName_2016_, v_fixedPrefixSize_2017_, v_F_2018_, v_e_2019_, v___x_2032_, v___x_2034_, v_a_2020_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_);
return v___x_2035_;
}
else
{
lean_object* v___x_2036_; 
v___x_2036_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2016_, v_fixedPrefixSize_2017_, v_F_2018_, v_e_2019_, v_a_2020_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_);
return v___x_2036_;
}
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2038_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__0));
v___x_2039_ = l_Lean_stringToMessageData(v___x_2038_);
return v___x_2039_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2041_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__2));
v___x_2042_ = l_Lean_stringToMessageData(v___x_2041_);
return v___x_2042_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0(lean_object* v___x_2043_, lean_object* v_b_2044_, lean_object* v_recFnName_2045_, lean_object* v_fixedPrefixSize_2046_, uint8_t v___x_2047_, lean_object* v___x_2048_, lean_object* v_a_2049_, lean_object* v_e_2050_, lean_object* v_xs_2051_, lean_object* v_altBody_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_){
_start:
{
lean_object* v___x_2069_; uint8_t v___x_2070_; 
v___x_2069_ = lean_array_get_size(v_xs_2051_);
v___x_2070_ = lean_nat_dec_eq(v___x_2069_, v___x_2048_);
if (v___x_2070_ == 0)
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2086_; 
lean_dec_ref(v_altBody_2052_);
lean_dec(v_fixedPrefixSize_2046_);
lean_dec(v_recFnName_2045_);
v___x_2071_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1);
v___x_2072_ = l_Lean_indentExpr(v_a_2049_);
v___x_2073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2071_);
lean_ctor_set(v___x_2073_, 1, v___x_2072_);
v___x_2074_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3);
v___x_2075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2073_);
lean_ctor_set(v___x_2075_, 1, v___x_2074_);
v___x_2076_ = l_Lean_indentExpr(v_e_2050_);
v___x_2077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2075_);
lean_ctor_set(v___x_2077_, 1, v___x_2076_);
v___x_2078_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v___x_2077_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2081_ = v___x_2078_;
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2078_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2084_; 
if (v_isShared_2082_ == 0)
{
v___x_2084_ = v___x_2081_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_a_2079_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
else
{
lean_dec_ref(v_e_2050_);
lean_dec_ref(v_a_2049_);
goto v___jp_2062_;
}
v___jp_2062_:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2063_ = lean_array_get_borrowed(v___x_2043_, v_xs_2051_, v_b_2044_);
lean_inc(v___x_2063_);
v___x_2064_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2045_, v_fixedPrefixSize_2046_, v___x_2063_, v_altBody_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v_a_2065_; uint8_t v___x_2066_; uint8_t v___x_2067_; lean_object* v___x_2068_; 
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_a_2065_);
lean_dec_ref_known(v___x_2064_, 1);
v___x_2066_ = 0;
v___x_2067_ = 1;
v___x_2068_ = l_Lean_Meta_mkLambdaFVars(v_xs_2051_, v_a_2065_, v___x_2066_, v___x_2047_, v___x_2066_, v___x_2047_, v___x_2067_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
return v___x_2068_;
}
else
{
return v___x_2064_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___boxed(lean_object** _args){
lean_object* v___x_2087_ = _args[0];
lean_object* v_b_2088_ = _args[1];
lean_object* v_recFnName_2089_ = _args[2];
lean_object* v_fixedPrefixSize_2090_ = _args[3];
lean_object* v___x_2091_ = _args[4];
lean_object* v___x_2092_ = _args[5];
lean_object* v_a_2093_ = _args[6];
lean_object* v_e_2094_ = _args[7];
lean_object* v_xs_2095_ = _args[8];
lean_object* v_altBody_2096_ = _args[9];
lean_object* v___y_2097_ = _args[10];
lean_object* v___y_2098_ = _args[11];
lean_object* v___y_2099_ = _args[12];
lean_object* v___y_2100_ = _args[13];
lean_object* v___y_2101_ = _args[14];
lean_object* v___y_2102_ = _args[15];
lean_object* v___y_2103_ = _args[16];
lean_object* v___y_2104_ = _args[17];
lean_object* v___y_2105_ = _args[18];
_start:
{
uint8_t v___x_57595__boxed_2106_; lean_object* v_res_2107_; 
v___x_57595__boxed_2106_ = lean_unbox(v___x_2091_);
v_res_2107_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0(v___x_2087_, v_b_2088_, v_recFnName_2089_, v_fixedPrefixSize_2090_, v___x_57595__boxed_2106_, v___x_2092_, v_a_2093_, v_e_2094_, v_xs_2095_, v_altBody_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
lean_dec(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec_ref(v_xs_2095_);
lean_dec(v___x_2092_);
lean_dec(v_b_2088_);
lean_dec_ref(v___x_2087_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(lean_object* v_recFnName_2108_, lean_object* v_fixedPrefixSize_2109_, lean_object* v_e_2110_, lean_object* v_as_2111_, lean_object* v_bs_2112_, lean_object* v_i_2113_, lean_object* v_cs_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v___x_2124_; uint8_t v___x_2125_; 
v___x_2124_ = lean_array_get_size(v_as_2111_);
v___x_2125_ = lean_nat_dec_lt(v_i_2113_, v___x_2124_);
if (v___x_2125_ == 0)
{
lean_object* v___x_2126_; 
lean_dec(v_i_2113_);
lean_dec_ref(v_e_2110_);
lean_dec(v_fixedPrefixSize_2109_);
lean_dec(v_recFnName_2108_);
v___x_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2126_, 0, v_cs_2114_);
return v___x_2126_;
}
else
{
lean_object* v___x_2127_; uint8_t v___x_2128_; 
v___x_2127_ = lean_array_get_size(v_bs_2112_);
v___x_2128_ = lean_nat_dec_lt(v_i_2113_, v___x_2127_);
if (v___x_2128_ == 0)
{
lean_object* v___x_2129_; 
lean_dec(v_i_2113_);
lean_dec_ref(v_e_2110_);
lean_dec(v_fixedPrefixSize_2109_);
lean_dec(v_recFnName_2108_);
v___x_2129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2129_, 0, v_cs_2114_);
return v___x_2129_;
}
else
{
lean_object* v___x_2130_; lean_object* v_a_2131_; lean_object* v_b_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___f_2136_; uint8_t v___x_2137_; lean_object* v___x_2138_; 
v___x_2130_ = l_Lean_instInhabitedExpr;
v_a_2131_ = lean_array_fget_borrowed(v_as_2111_, v_i_2113_);
v_b_2132_ = lean_array_fget_borrowed(v_bs_2112_, v_i_2113_);
v___x_2133_ = lean_unsigned_to_nat(1u);
v___x_2134_ = lean_nat_add(v_b_2132_, v___x_2133_);
v___x_2135_ = lean_box(v___x_2128_);
lean_inc_ref(v_e_2110_);
lean_inc_n(v_a_2131_, 2);
lean_inc(v___x_2134_);
lean_inc(v_fixedPrefixSize_2109_);
lean_inc(v_recFnName_2108_);
lean_inc(v_b_2132_);
v___f_2136_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___boxed), 19, 8);
lean_closure_set(v___f_2136_, 0, v___x_2130_);
lean_closure_set(v___f_2136_, 1, v_b_2132_);
lean_closure_set(v___f_2136_, 2, v_recFnName_2108_);
lean_closure_set(v___f_2136_, 3, v_fixedPrefixSize_2109_);
lean_closure_set(v___f_2136_, 4, v___x_2135_);
lean_closure_set(v___f_2136_, 5, v___x_2134_);
lean_closure_set(v___f_2136_, 6, v_a_2131_);
lean_closure_set(v___f_2136_, 7, v_e_2110_);
v___x_2137_ = 0;
v___x_2138_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(v_a_2131_, v___x_2134_, v___f_2136_, v___x_2137_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2139_);
lean_dec_ref_known(v___x_2138_, 1);
v___x_2140_ = lean_nat_add(v_i_2113_, v___x_2133_);
lean_dec(v_i_2113_);
v___x_2141_ = lean_array_push(v_cs_2114_, v_a_2139_);
v_i_2113_ = v___x_2140_;
v_cs_2114_ = v___x_2141_;
goto _start;
}
else
{
lean_object* v_a_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2150_; 
lean_dec_ref(v_cs_2114_);
lean_dec(v_i_2113_);
lean_dec_ref(v_e_2110_);
lean_dec(v_fixedPrefixSize_2109_);
lean_dec(v_recFnName_2108_);
v_a_2143_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2145_ = v___x_2138_;
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_a_2143_);
lean_dec(v___x_2138_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2148_; 
if (v_isShared_2146_ == 0)
{
v___x_2148_ = v___x_2145_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_a_2143_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(lean_object* v_recFnName_2151_, lean_object* v_fixedPrefixSize_2152_, lean_object* v_F_2153_, lean_object* v_e_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_){
_start:
{
switch(lean_obj_tag(v_e_2154_))
{
case 6:
{
lean_object* v_binderName_2164_; lean_object* v_binderType_2165_; lean_object* v_body_2166_; uint8_t v_binderInfo_2167_; lean_object* v___x_2168_; 
v_binderName_2164_ = lean_ctor_get(v_e_2154_, 0);
lean_inc(v_binderName_2164_);
v_binderType_2165_ = lean_ctor_get(v_e_2154_, 1);
lean_inc_ref(v_binderType_2165_);
v_body_2166_ = lean_ctor_get(v_e_2154_, 2);
lean_inc_ref(v_body_2166_);
v_binderInfo_2167_ = lean_ctor_get_uint8(v_e_2154_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2154_, 3);
lean_inc_ref(v_F_2153_);
lean_inc(v_fixedPrefixSize_2152_);
lean_inc(v_recFnName_2151_);
v___x_2168_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2151_, v_fixedPrefixSize_2152_, v_F_2153_, v_binderType_2165_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_object* v_a_2169_; lean_object* v___f_2170_; uint8_t v___x_2171_; lean_object* v___x_2172_; 
v_a_2169_ = lean_ctor_get(v___x_2168_, 0);
lean_inc(v_a_2169_);
lean_dec_ref_known(v___x_2168_, 1);
v___f_2170_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0___boxed), 14, 4);
lean_closure_set(v___f_2170_, 0, v_body_2166_);
lean_closure_set(v___f_2170_, 1, v_recFnName_2151_);
lean_closure_set(v___f_2170_, 2, v_fixedPrefixSize_2152_);
lean_closure_set(v___f_2170_, 3, v_F_2153_);
v___x_2171_ = 0;
v___x_2172_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_binderName_2164_, v_binderInfo_2167_, v_a_2169_, v___f_2170_, v___x_2171_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_);
return v___x_2172_;
}
else
{
lean_dec_ref(v_body_2166_);
lean_dec(v_binderName_2164_);
lean_dec_ref(v_F_2153_);
lean_dec(v_fixedPrefixSize_2152_);
lean_dec(v_recFnName_2151_);
return v___x_2168_;
}
}
case 7:
{
lean_object* v_binderName_2173_; lean_object* v_binderType_2174_; lean_object* v_body_2175_; uint8_t v_binderInfo_2176_; lean_object* v___x_2177_; 
v_binderName_2173_ = lean_ctor_get(v_e_2154_, 0);
lean_inc(v_binderName_2173_);
v_binderType_2174_ = lean_ctor_get(v_e_2154_, 1);
lean_inc_ref(v_binderType_2174_);
v_body_2175_ = lean_ctor_get(v_e_2154_, 2);
lean_inc_ref(v_body_2175_);
v_binderInfo_2176_ = lean_ctor_get_uint8(v_e_2154_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2154_, 3);
lean_inc_ref(v_F_2153_);
lean_inc(v_fixedPrefixSize_2152_);
lean_inc(v_recFnName_2151_);
v___x_2177_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2151_, v_fixedPrefixSize_2152_, v_F_2153_, v_binderType_2174_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v___f_2179_; uint8_t v___x_2180_; lean_object* v___x_2181_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_a_2178_);
lean_dec_ref_known(v___x_2177_, 1);
v___f_2179_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1___boxed), 14, 4);
lean_closure_set(v___f_2179_, 0, v_body_2175_);
lean_closure_set(v___f_2179_, 1, v_recFnName_2151_);
lean_closure_set(v___f_2179_, 2, v_fixedPrefixSize_2152_);
lean_closure_set(v___f_2179_, 3, v_F_2153_);
v___x_2180_ = 0;
v___x_2181_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_binderName_2173_, v_binderInfo_2176_, v_a_2178_, v___f_2179_, v___x_2180_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_);
return v___x_2181_;
}
else
{
lean_dec_ref(v_body_2175_);
lean_dec(v_binderName_2173_);
lean_dec_ref(v_F_2153_);
lean_dec(v_fixedPrefixSize_2152_);
lean_dec(v_recFnName_2151_);
return v___x_2177_;
}
}
case 8:
{
lean_object* v_declName_2182_; lean_object* v_type_2183_; lean_object* v_value_2184_; lean_object* v_body_2185_; uint8_t v_nondep_2186_; lean_object* v___x_2187_; 
v_declName_2182_ = lean_ctor_get(v_e_2154_, 0);
lean_inc(v_declName_2182_);
v_type_2183_ = lean_ctor_get(v_e_2154_, 1);
lean_inc_ref(v_type_2183_);
v_value_2184_ = lean_ctor_get(v_e_2154_, 2);
lean_inc_ref(v_value_2184_);
v_body_2185_ = lean_ctor_get(v_e_2154_, 3);
lean_inc_ref(v_body_2185_);
v_nondep_2186_ = lean_ctor_get_uint8(v_e_2154_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2154_, 4);
lean_inc_ref(v_F_2153_);
lean_inc(v_fixedPrefixSize_2152_);
lean_inc(v_recFnName_2151_);
v___x_2187_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2151_, v_fixedPrefixSize_2152_, v_F_2153_, v_type_2183_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_);
if (lean_obj_tag(v___x_2187_) == 0)
{
lean_object* v_a_2188_; lean_object* v___x_2189_; 
v_a_2188_ = lean_ctor_get(v___x_2187_, 0);
lean_inc(v_a_2188_);
lean_dec_ref_known(v___x_2187_, 1);
lean_inc_ref(v_F_2153_);
lean_inc(v_fixedPrefixSize_2152_);
lean_inc(v_recFnName_2151_);
v___x_2189_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2151_, v_fixedPrefixSize_2152_, v_F_2153_, v_value_2184_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_a_2190_; lean_object* v___f_2191_; uint8_t v___x_2192_; uint8_t v___x_2193_; lean_object* v___x_2194_; 
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_a_2190_);
lean_dec_ref_known(v___x_2189_, 1);
v___f_2191_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2___boxed), 14, 4);
lean_closure_set(v___f_2191_, 0, v_body_2185_);
lean_closure_set(v___f_2191_, 1, v_recFnName_2151_);
lean_closure_set(v___f_2191_, 2, v_fixedPrefixSize_2152_);
lean_closure_set(v___f_2191_, 3, v_F_2153_);
v___x_2192_ = 0;
v___x_2193_ = 0;
v___x_2194_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(v_declName_2182_, v_a_2188_, v_a_2190_, v___f_2191_, v_nondep_2186_, v___x_2192_, v___x_2193_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_);
return v___x_2194_;
}
else
{
lean_dec(v_a_2188_);
lean_dec_ref(v_body_2185_);
lean_dec(v_declName_2182_);
lean_dec_ref(v_F_2153_);
lean_dec(v_fixedPrefixSize_2152_);
lean_dec(v_recFnName_2151_);
return v___x_2189_;
}
}
else
{
lean_dec_ref(v_body_2185_);
lean_dec_ref(v_value_2184_);
lean_dec(v_declName_2182_);
lean_dec_ref(v_F_2153_);
lean_dec(v_fixedPrefixSize_2152_);
lean_dec(v_recFnName_2151_);
return v___x_2187_;
}
}
case 10:
{
lean_object* v_data_2195_; lean_object* v_expr_2196_; lean_object* v___x_2197_; 
v_data_2195_ = lean_ctor_get(v_e_2154_, 0);
lean_inc(v_data_2195_);
v_expr_2196_ = lean_ctor_get(v_e_2154_, 1);
lean_inc_ref(v_expr_2196_);
v___x_2197_ = l_Lean_getRecAppSyntax_x3f(v_e_2154_);
lean_dec_ref_known(v_e_2154_, 2);
if (lean_obj_tag(v___x_2197_) == 1)
{
lean_object* v_val_2198_; lean_object* v_toCold_2199_; lean_object* v_currRecDepth_2200_; lean_object* v_ref_2201_; uint8_t v_diag_2202_; uint8_t v_suppressElabErrors_2203_; lean_object* v_ref_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
lean_dec(v_data_2195_);
v_val_2198_ = lean_ctor_get(v___x_2197_, 0);
lean_inc(v_val_2198_);
lean_dec_ref_known(v___x_2197_, 1);
v_toCold_2199_ = lean_ctor_get(v_a_2161_, 0);
v_currRecDepth_2200_ = lean_ctor_get(v_a_2161_, 1);
v_ref_2201_ = lean_ctor_get(v_a_2161_, 2);
v_diag_2202_ = lean_ctor_get_uint8(v_a_2161_, sizeof(void*)*3);
v_suppressElabErrors_2203_ = lean_ctor_get_uint8(v_a_2161_, sizeof(void*)*3 + 1);
v_ref_2204_ = l_Lean_replaceRef(v_val_2198_, v_ref_2201_);
lean_dec(v_val_2198_);
lean_inc(v_currRecDepth_2200_);
lean_inc_ref(v_toCold_2199_);
v___x_2205_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2205_, 0, v_toCold_2199_);
lean_ctor_set(v___x_2205_, 1, v_currRecDepth_2200_);
lean_ctor_set(v___x_2205_, 2, v_ref_2204_);
lean_ctor_set_uint8(v___x_2205_, sizeof(void*)*3, v_diag_2202_);
lean_ctor_set_uint8(v___x_2205_, sizeof(void*)*3 + 1, v_suppressElabErrors_2203_);
v___x_2206_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2151_, v_fixedPrefixSize_2152_, v_F_2153_, v_expr_2196_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v___x_2205_, v_a_2162_);
lean_dec_ref_known(v___x_2205_, 3);
return v___x_2206_;
}
else
{
lean_object* v___x_2207_; 
lean_dec(v___x_2197_);
v___x_2207_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2151_, v_fixedPrefixSize_2152_, v_F_2153_, v_expr_2196_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2216_; 
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2210_ = v___x_2207_;
v_isShared_2211_ = v_isSharedCheck_2216_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2207_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2216_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2212_; lean_object* v___x_2214_; 
v___x_2212_ = l_Lean_mkMData(v_data_2195_, v_a_2208_);
if (v_isShared_2211_ == 0)
{
lean_ctor_set(v___x_2210_, 0, v___x_2212_);
v___x_2214_ = v___x_2210_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v___x_2212_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
else
{
lean_dec(v_data_2195_);
return v___x_2207_;
}
}
}
case 11:
{
lean_object* v_typeName_2217_; lean_object* v_idx_2218_; lean_object* v_struct_2219_; lean_object* v___x_2220_; 
v_typeName_2217_ = lean_ctor_get(v_e_2154_, 0);
lean_inc(v_typeName_2217_);
v_idx_2218_ = lean_ctor_get(v_e_2154_, 1);
lean_inc(v_idx_2218_);
v_struct_2219_ = lean_ctor_get(v_e_2154_, 2);
lean_inc_ref(v_struct_2219_);
lean_dec_ref_known(v_e_2154_, 3);
v___x_2220_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2151_, v_fixedPrefixSize_2152_, v_F_2153_, v_struct_2219_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2229_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2223_ = v___x_2220_;
v_isShared_2224_ = v_isSharedCheck_2229_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2220_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2229_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2225_; lean_object* v___x_2227_; 
v___x_2225_ = l_Lean_mkProj(v_typeName_2217_, v_idx_2218_, v_a_2221_);
if (v_isShared_2224_ == 0)
{
lean_ctor_set(v___x_2223_, 0, v___x_2225_);
v___x_2227_ = v___x_2223_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2225_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
else
{
lean_dec(v_idx_2218_);
lean_dec(v_typeName_2217_);
return v___x_2220_;
}
}
case 4:
{
uint8_t v___x_2230_; 
v___x_2230_ = l_Lean_Expr_isConstOf(v_e_2154_, v_recFnName_2151_);
if (v___x_2230_ == 0)
{
lean_object* v___x_2231_; 
lean_dec_ref(v_F_2153_);
lean_dec(v_fixedPrefixSize_2152_);
lean_dec(v_recFnName_2151_);
v___x_2231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2231_, 0, v_e_2154_);
return v___x_2231_;
}
else
{
lean_object* v___x_2232_; 
v___x_2232_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2151_, v_fixedPrefixSize_2152_, v_F_2153_, v_e_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_);
return v___x_2232_;
}
}
case 5:
{
uint8_t v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = 1;
lean_inc_ref(v_e_2154_);
v___x_2234_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(v_e_2154_, v___x_2233_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_a_2235_; 
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc(v_a_2235_);
lean_dec_ref_known(v___x_2234_, 1);
if (lean_obj_tag(v_a_2235_) == 0)
{
lean_object* v___x_2236_; 
v___x_2236_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2151_, v_fixedPrefixSize_2152_, v_F_2153_, v_e_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_);
return v___x_2236_;
}
else
{
lean_object* v_val_2237_; lean_object* v___x_2238_; 
v_val_2237_ = lean_ctor_get(v_a_2235_, 0);
lean_inc(v_val_2237_);
lean_dec_ref_known(v_a_2235_, 1);
lean_inc_ref(v_F_2153_);
v___x_2238_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_val_2237_, v_F_2153_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_a_2239_);
lean_dec_ref_known(v___x_2238_, 1);
if (lean_obj_tag(v_a_2239_) == 1)
{
lean_object* v_val_2240_; lean_object* v_toMatcherInfo_2241_; lean_object* v_matcherName_2242_; lean_object* v_matcherLevels_2243_; lean_object* v_params_2244_; lean_object* v_motive_2245_; lean_object* v_discrs_2246_; lean_object* v_alts_2247_; lean_object* v_remaining_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v_val_2240_ = lean_ctor_get(v_a_2239_, 0);
lean_inc(v_val_2240_);
lean_dec_ref_known(v_a_2239_, 1);
v_toMatcherInfo_2241_ = lean_ctor_get(v_val_2240_, 0);
lean_inc_ref(v_toMatcherInfo_2241_);
v_matcherName_2242_ = lean_ctor_get(v_val_2240_, 1);
lean_inc(v_matcherName_2242_);
v_matcherLevels_2243_ = lean_ctor_get(v_val_2240_, 2);
lean_inc_ref(v_matcherLevels_2243_);
v_params_2244_ = lean_ctor_get(v_val_2240_, 3);
lean_inc_ref(v_params_2244_);
v_motive_2245_ = lean_ctor_get(v_val_2240_, 4);
lean_inc_ref(v_motive_2245_);
v_discrs_2246_ = lean_ctor_get(v_val_2240_, 5);
lean_inc_ref(v_discrs_2246_);
v_alts_2247_ = lean_ctor_get(v_val_2240_, 6);
lean_inc_ref(v_alts_2247_);
v_remaining_2248_ = lean_ctor_get(v_val_2240_, 7);
lean_inc_ref(v_remaining_2248_);
v___x_2249_ = l_Lean_Meta_MatcherApp_altNumParams(v_val_2240_);
v___x_2250_ = lean_unsigned_to_nat(0u);
v___x_2251_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
lean_inc(v_fixedPrefixSize_2152_);
lean_inc(v_recFnName_2151_);
v___x_2252_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(v_recFnName_2151_, v_fixedPrefixSize_2152_, v_e_2154_, v_alts_2247_, v___x_2249_, v___x_2250_, v___x_2251_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_);
lean_dec_ref(v___x_2249_);
lean_dec_ref(v_alts_2247_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_object* v_a_2253_; size_t v_sz_2254_; size_t v___x_2255_; lean_object* v___x_2256_; 
v_a_2253_ = lean_ctor_get(v___x_2252_, 0);
lean_inc(v_a_2253_);
lean_dec_ref_known(v___x_2252_, 1);
v_sz_2254_ = lean_array_size(v_discrs_2246_);
v___x_2255_ = ((size_t)0ULL);
v___x_2256_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_2151_, v_fixedPrefixSize_2152_, v_F_2153_, v_sz_2254_, v___x_2255_, v_discrs_2246_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2266_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2259_ = v___x_2256_;
v_isShared_2260_ = v_isSharedCheck_2266_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2256_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2266_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2264_; 
v___x_2261_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2261_, 0, v_toMatcherInfo_2241_);
lean_ctor_set(v___x_2261_, 1, v_matcherName_2242_);
lean_ctor_set(v___x_2261_, 2, v_matcherLevels_2243_);
lean_ctor_set(v___x_2261_, 3, v_params_2244_);
lean_ctor_set(v___x_2261_, 4, v_motive_2245_);
lean_ctor_set(v___x_2261_, 5, v_a_2257_);
lean_ctor_set(v___x_2261_, 6, v_a_2253_);
lean_ctor_set(v___x_2261_, 7, v_remaining_2248_);
v___x_2262_ = l_Lean_Meta_MatcherApp_toExpr(v___x_2261_);
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 0, v___x_2262_);
v___x_2264_ = v___x_2259_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2262_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
else
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2274_; 
lean_dec(v_a_2253_);
lean_dec_ref(v_remaining_2248_);
lean_dec_ref(v_motive_2245_);
lean_dec_ref(v_params_2244_);
lean_dec_ref(v_matcherLevels_2243_);
lean_dec(v_matcherName_2242_);
lean_dec_ref(v_toMatcherInfo_2241_);
v_a_2267_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2269_ = v___x_2256_;
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2256_);
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
lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2282_; 
lean_dec_ref(v_remaining_2248_);
lean_dec_ref(v_discrs_2246_);
lean_dec_ref(v_motive_2245_);
lean_dec_ref(v_params_2244_);
lean_dec_ref(v_matcherLevels_2243_);
lean_dec(v_matcherName_2242_);
lean_dec_ref(v_toMatcherInfo_2241_);
lean_dec_ref(v_F_2153_);
lean_dec(v_fixedPrefixSize_2152_);
lean_dec(v_recFnName_2151_);
v_a_2275_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2277_ = v___x_2252_;
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_dec(v___x_2252_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2280_; 
if (v_isShared_2278_ == 0)
{
v___x_2280_ = v___x_2277_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_a_2275_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
}
else
{
lean_object* v___x_2283_; 
lean_dec(v_a_2239_);
v___x_2283_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2151_, v_fixedPrefixSize_2152_, v_F_2153_, v_e_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_);
return v___x_2283_;
}
}
else
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2291_; 
lean_dec_ref_known(v_e_2154_, 2);
lean_dec_ref(v_F_2153_);
lean_dec(v_fixedPrefixSize_2152_);
lean_dec(v_recFnName_2151_);
v_a_2284_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2286_ = v___x_2238_;
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2238_);
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
}
else
{
lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2299_; 
lean_dec_ref_known(v_e_2154_, 2);
lean_dec_ref(v_F_2153_);
lean_dec(v_fixedPrefixSize_2152_);
lean_dec(v_recFnName_2151_);
v_a_2292_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2294_ = v___x_2234_;
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2234_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2297_; 
if (v_isShared_2295_ == 0)
{
v___x_2297_ = v___x_2294_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2292_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
default: 
{
lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
lean_dec_ref(v_F_2153_);
lean_dec(v_fixedPrefixSize_2152_);
v___x_2300_ = lean_unsigned_to_nat(1u);
v___x_2301_ = lean_mk_empty_array_with_capacity(v___x_2300_);
v___x_2302_ = lean_array_push(v___x_2301_, v_recFnName_2151_);
lean_inc_ref(v_e_2154_);
v___x_2303_ = l_Lean_Elab_ensureNoRecFn(v___x_2302_, v_e_2154_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2310_; 
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2310_ == 0)
{
lean_object* v_unused_2311_; 
v_unused_2311_ = lean_ctor_get(v___x_2303_, 0);
lean_dec(v_unused_2311_);
v___x_2305_ = v___x_2303_;
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
else
{
lean_dec(v___x_2303_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2308_; 
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 0, v_e_2154_);
v___x_2308_ = v___x_2305_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_e_2154_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
else
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2319_; 
lean_dec_ref(v_e_2154_);
v_a_2312_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2314_ = v___x_2303_;
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___x_2303_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(lean_object* v_recFnName_2320_, lean_object* v_fixedPrefixSize_2321_, lean_object* v_F_2322_, lean_object* v_e_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_){
_start:
{
lean_object* v___y_2334_; lean_object* v___y_2335_; lean_object* v___x_2352_; 
lean_inc_ref(v_e_2323_);
lean_inc(v_recFnName_2320_);
v___x_2352_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___redArg(v_recFnName_2320_, v_e_2323_, v_a_2324_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2441_; 
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2355_ = v___x_2352_;
v_isShared_2356_ = v_isSharedCheck_2441_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2352_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2441_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
uint8_t v___x_2357_; 
v___x_2357_ = lean_unbox(v_a_2353_);
lean_dec(v_a_2353_);
if (v___x_2357_ == 0)
{
lean_object* v___x_2359_; 
lean_dec_ref(v_F_2322_);
lean_dec(v_fixedPrefixSize_2321_);
lean_dec(v_recFnName_2320_);
if (v_isShared_2356_ == 0)
{
lean_ctor_set(v___x_2355_, 0, v_e_2323_);
v___x_2359_ = v___x_2355_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_e_2323_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
else
{
lean_object* v___x_2361_; uint8_t v___x_2362_; lean_object* v___y_2364_; lean_object* v___y_2365_; lean_object* v___y_2366_; lean_object* v___y_2367_; lean_object* v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___x_2419_; 
lean_del_object(v___x_2355_);
v___x_2361_ = lean_st_ref_get(v_a_2325_);
v___x_2362_ = 0;
v___x_2419_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v___x_2361_, v_e_2323_);
lean_dec(v___x_2361_);
if (lean_obj_tag(v___x_2419_) == 1)
{
lean_object* v_val_2420_; lean_object* v_fst_2421_; lean_object* v_snd_2422_; lean_object* v___x_2423_; 
v_val_2420_ = lean_ctor_get(v___x_2419_, 0);
lean_inc(v_val_2420_);
lean_dec_ref_known(v___x_2419_, 1);
v_fst_2421_ = lean_ctor_get(v_val_2420_, 0);
lean_inc(v_fst_2421_);
v_snd_2422_ = lean_ctor_get(v_val_2420_, 1);
lean_inc(v_snd_2422_);
lean_dec(v_val_2420_);
v___x_2423_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___redArg(v_snd_2422_, v_a_2328_);
lean_dec(v_snd_2422_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2432_; 
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2426_ = v___x_2423_;
v_isShared_2427_ = v_isSharedCheck_2432_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2423_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2432_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
uint8_t v___x_2428_; 
v___x_2428_ = lean_unbox(v_a_2424_);
lean_dec(v_a_2424_);
if (v___x_2428_ == 0)
{
lean_del_object(v___x_2426_);
lean_dec(v_fst_2421_);
v___y_2364_ = v_a_2324_;
v___y_2365_ = v_a_2325_;
v___y_2366_ = v_a_2326_;
v___y_2367_ = v_a_2327_;
v___y_2368_ = v_a_2328_;
v___y_2369_ = v_a_2329_;
v___y_2370_ = v_a_2330_;
v___y_2371_ = v_a_2331_;
goto v___jp_2363_;
}
else
{
lean_object* v___x_2430_; 
lean_dec_ref(v_e_2323_);
lean_dec_ref(v_F_2322_);
lean_dec(v_fixedPrefixSize_2321_);
lean_dec(v_recFnName_2320_);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 0, v_fst_2421_);
v___x_2430_ = v___x_2426_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_fst_2421_);
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
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2440_; 
lean_dec(v_fst_2421_);
lean_dec_ref(v_e_2323_);
lean_dec_ref(v_F_2322_);
lean_dec(v_fixedPrefixSize_2321_);
lean_dec(v_recFnName_2320_);
v_a_2433_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2435_ = v___x_2423_;
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2423_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2438_; 
if (v_isShared_2436_ == 0)
{
v___x_2438_ = v___x_2435_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2433_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
}
else
{
lean_dec(v___x_2419_);
v___y_2364_ = v_a_2324_;
v___y_2365_ = v_a_2325_;
v___y_2366_ = v_a_2326_;
v___y_2367_ = v_a_2327_;
v___y_2368_ = v_a_2328_;
v___y_2369_ = v_a_2329_;
v___y_2370_ = v_a_2330_;
v___y_2371_ = v_a_2331_;
goto v___jp_2363_;
}
v___jp_2363_:
{
lean_object* v___x_2372_; 
lean_inc_ref(v_e_2323_);
v___x_2372_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(v_recFnName_2320_, v_fixedPrefixSize_2321_, v_F_2322_, v_e_2323_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v_a_2373_; lean_object* v___x_2374_; 
v_a_2373_ = lean_ctor_get(v___x_2372_, 0);
lean_inc(v_a_2373_);
lean_dec_ref_known(v___x_2372_, 1);
v___x_2374_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId(v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2410_; 
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2410_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2410_ == 0)
{
v___x_2377_ = v___x_2374_;
v_isShared_2378_ = v_isSharedCheck_2410_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2374_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2410_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v_toCold_2383_; lean_object* v_options_2384_; lean_object* v___x_2385_; uint8_t v___x_2386_; 
v___x_2379_ = lean_st_ref_take(v___y_2365_);
lean_inc(v_a_2373_);
v___x_2380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2380_, 0, v_a_2373_);
lean_ctor_set(v___x_2380_, 1, v_a_2375_);
lean_inc_ref(v_e_2323_);
v___x_2381_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4___redArg(v___x_2379_, v_e_2323_, v___x_2380_);
v___x_2382_ = lean_st_ref_put(v___y_2365_, v___x_2381_);
v_toCold_2383_ = lean_ctor_get(v___y_2370_, 0);
v_options_2384_ = lean_ctor_get(v_toCold_2383_, 2);
v___x_2385_ = l_Lean_Elab_WF_debug_definition_wf_replaceRecApps;
v___x_2386_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v_options_2384_, v___x_2385_);
if (v___x_2386_ == 0)
{
lean_object* v___x_2388_; 
lean_dec_ref(v_e_2323_);
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 0, v_a_2373_);
v___x_2388_ = v___x_2377_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_a_2373_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
}
}
else
{
lean_object* v___x_2390_; uint8_t v_transparency_2391_; lean_object* v___f_2392_; uint8_t v___x_2393_; uint8_t v___x_2394_; 
lean_del_object(v___x_2377_);
v___x_2390_ = l_Lean_Meta_Context_config(v___y_2368_);
v_transparency_2391_ = lean_ctor_get_uint8(v___x_2390_, 9);
lean_dec_ref(v___x_2390_);
lean_inc(v_a_2373_);
v___f_2392_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___boxed), 11, 2);
lean_closure_set(v___f_2392_, 0, v_a_2373_);
lean_closure_set(v___f_2392_, 1, v_e_2323_);
v___x_2393_ = 0;
v___x_2394_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2391_, v___x_2393_);
if (v___x_2394_ == 0)
{
lean_object* v_keyedConfig_2395_; uint8_t v_trackZetaDelta_2396_; lean_object* v_zetaDeltaSet_2397_; lean_object* v_lctx_2398_; lean_object* v_localInstances_2399_; lean_object* v_defEqCtx_x3f_2400_; lean_object* v_synthPendingDepth_2401_; lean_object* v_customCanUnfoldPredicate_x3f_2402_; uint8_t v_univApprox_2403_; uint8_t v_inTypeClassResolution_2404_; uint8_t v_cacheInferType_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v_keyedConfig_2395_ = lean_ctor_get(v___y_2368_, 0);
v_trackZetaDelta_2396_ = lean_ctor_get_uint8(v___y_2368_, sizeof(void*)*7);
v_zetaDeltaSet_2397_ = lean_ctor_get(v___y_2368_, 1);
v_lctx_2398_ = lean_ctor_get(v___y_2368_, 2);
v_localInstances_2399_ = lean_ctor_get(v___y_2368_, 3);
v_defEqCtx_x3f_2400_ = lean_ctor_get(v___y_2368_, 4);
v_synthPendingDepth_2401_ = lean_ctor_get(v___y_2368_, 5);
v_customCanUnfoldPredicate_x3f_2402_ = lean_ctor_get(v___y_2368_, 6);
v_univApprox_2403_ = lean_ctor_get_uint8(v___y_2368_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2404_ = lean_ctor_get_uint8(v___y_2368_, sizeof(void*)*7 + 2);
v_cacheInferType_2405_ = lean_ctor_get_uint8(v___y_2368_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2395_);
v___x_2406_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2393_, v_keyedConfig_2395_);
lean_inc(v_customCanUnfoldPredicate_x3f_2402_);
lean_inc(v_synthPendingDepth_2401_);
lean_inc(v_defEqCtx_x3f_2400_);
lean_inc_ref(v_localInstances_2399_);
lean_inc_ref(v_lctx_2398_);
lean_inc(v_zetaDeltaSet_2397_);
v___x_2407_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2407_, 0, v___x_2406_);
lean_ctor_set(v___x_2407_, 1, v_zetaDeltaSet_2397_);
lean_ctor_set(v___x_2407_, 2, v_lctx_2398_);
lean_ctor_set(v___x_2407_, 3, v_localInstances_2399_);
lean_ctor_set(v___x_2407_, 4, v_defEqCtx_x3f_2400_);
lean_ctor_set(v___x_2407_, 5, v_synthPendingDepth_2401_);
lean_ctor_set(v___x_2407_, 6, v_customCanUnfoldPredicate_x3f_2402_);
lean_ctor_set_uint8(v___x_2407_, sizeof(void*)*7, v_trackZetaDelta_2396_);
lean_ctor_set_uint8(v___x_2407_, sizeof(void*)*7 + 1, v_univApprox_2403_);
lean_ctor_set_uint8(v___x_2407_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2404_);
lean_ctor_set_uint8(v___x_2407_, sizeof(void*)*7 + 3, v_cacheInferType_2405_);
v___x_2408_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v___f_2392_, v___x_2362_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___x_2407_, v___y_2369_, v___y_2370_, v___y_2371_);
lean_dec_ref_known(v___x_2407_, 7);
v___y_2334_ = v_a_2373_;
v___y_2335_ = v___x_2408_;
goto v___jp_2333_;
}
else
{
lean_object* v___x_2409_; 
v___x_2409_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v___f_2392_, v___x_2362_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_);
v___y_2334_ = v_a_2373_;
v___y_2335_ = v___x_2409_;
goto v___jp_2333_;
}
}
}
}
else
{
lean_object* v_a_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2418_; 
lean_dec(v_a_2373_);
lean_dec_ref(v_e_2323_);
v_a_2411_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2413_ = v___x_2374_;
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_a_2411_);
lean_dec(v___x_2374_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2416_; 
if (v_isShared_2414_ == 0)
{
v___x_2416_ = v___x_2413_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_a_2411_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
}
else
{
lean_dec_ref(v_e_2323_);
return v___x_2372_;
}
}
}
}
}
else
{
lean_object* v_a_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2449_; 
lean_dec_ref(v_e_2323_);
lean_dec_ref(v_F_2322_);
lean_dec(v_fixedPrefixSize_2321_);
lean_dec(v_recFnName_2320_);
v_a_2442_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2444_ = v___x_2352_;
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_a_2442_);
lean_dec(v___x_2352_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2447_; 
if (v_isShared_2445_ == 0)
{
v___x_2447_ = v___x_2444_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_a_2442_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
return v___x_2447_;
}
}
}
v___jp_2333_:
{
if (lean_obj_tag(v___y_2335_) == 0)
{
lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
v_isSharedCheck_2342_ = !lean_is_exclusive(v___y_2335_);
if (v_isSharedCheck_2342_ == 0)
{
lean_object* v_unused_2343_; 
v_unused_2343_ = lean_ctor_get(v___y_2335_, 0);
lean_dec(v_unused_2343_);
v___x_2337_ = v___y_2335_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_dec(v___y_2335_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
lean_ctor_set(v___x_2337_, 0, v___y_2334_);
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___y_2334_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
else
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2351_; 
lean_dec_ref(v___y_2334_);
v_a_2344_ = lean_ctor_get(v___y_2335_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___y_2335_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2346_ = v___y_2335_;
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___y_2335_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2349_; 
if (v_isShared_2347_ == 0)
{
v___x_2349_ = v___x_2346_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_a_2344_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2(lean_object* v_body_2450_, lean_object* v_recFnName_2451_, lean_object* v_fixedPrefixSize_2452_, lean_object* v_F_2453_, lean_object* v_x_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_){
_start:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2464_ = lean_expr_instantiate1(v_body_2450_, v_x_2454_);
v___x_2465_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2451_, v_fixedPrefixSize_2452_, v_F_2453_, v___x_2464_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_);
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp___boxed(lean_object* v_recFnName_2466_, lean_object* v_fixedPrefixSize_2467_, lean_object* v_F_2468_, lean_object* v_e_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2466_, v_fixedPrefixSize_2467_, v_F_2468_, v_e_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_);
lean_dec(v_a_2477_);
lean_dec_ref(v_a_2476_);
lean_dec(v_a_2475_);
lean_dec_ref(v_a_2474_);
lean_dec(v_a_2473_);
lean_dec_ref(v_a_2472_);
lean_dec(v_a_2471_);
lean_dec(v_a_2470_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1___boxed(lean_object* v_recFnName_2480_, lean_object* v_fixedPrefixSize_2481_, lean_object* v_F_2482_, lean_object* v_sz_2483_, lean_object* v_i_2484_, lean_object* v_bs_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
size_t v_sz_boxed_2495_; size_t v_i_boxed_2496_; lean_object* v_res_2497_; 
v_sz_boxed_2495_ = lean_unbox_usize(v_sz_2483_);
lean_dec(v_sz_2483_);
v_i_boxed_2496_ = lean_unbox_usize(v_i_2484_);
lean_dec(v_i_2484_);
v_res_2497_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_2480_, v_fixedPrefixSize_2481_, v_F_2482_, v_sz_boxed_2495_, v_i_boxed_2496_, v_bs_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec(v___y_2486_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16___boxed(lean_object* v_recFnName_2498_, lean_object* v_fixedPrefixSize_2499_, lean_object* v_F_2500_, lean_object* v_x_2501_, lean_object* v_x_2502_, lean_object* v_x_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
lean_object* v_res_2513_; 
v_res_2513_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(v_recFnName_2498_, v_fixedPrefixSize_2499_, v_F_2500_, v_x_2501_, v_x_2502_, v_x_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
lean_dec(v___y_2509_);
lean_dec_ref(v___y_2508_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec(v___y_2505_);
lean_dec(v___y_2504_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___boxed(lean_object* v_recFnName_2514_, lean_object* v_fixedPrefixSize_2515_, lean_object* v_e_2516_, lean_object* v_as_2517_, lean_object* v_bs_2518_, lean_object* v_i_2519_, lean_object* v_cs_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(v_recFnName_2514_, v_fixedPrefixSize_2515_, v_e_2516_, v_as_2517_, v_bs_2518_, v_i_2519_, v_cs_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec(v___y_2522_);
lean_dec(v___y_2521_);
lean_dec_ref(v_bs_2518_);
lean_dec_ref(v_as_2517_);
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___boxed(lean_object* v_recFnName_2531_, lean_object* v_fixedPrefixSize_2532_, lean_object* v_F_2533_, lean_object* v_e_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2531_, v_fixedPrefixSize_2532_, v_F_2533_, v_e_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_);
lean_dec(v_a_2542_);
lean_dec_ref(v_a_2541_);
lean_dec(v_a_2540_);
lean_dec_ref(v_a_2539_);
lean_dec(v_a_2538_);
lean_dec_ref(v_a_2537_);
lean_dec(v_a_2536_);
lean_dec(v_a_2535_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___boxed(lean_object* v_recFnName_2545_, lean_object* v_fixedPrefixSize_2546_, lean_object* v_F_2547_, lean_object* v_e_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2545_, v_fixedPrefixSize_2546_, v_F_2547_, v_e_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
lean_dec(v_a_2556_);
lean_dec_ref(v_a_2555_);
lean_dec(v_a_2554_);
lean_dec_ref(v_a_2553_);
lean_dec(v_a_2552_);
lean_dec_ref(v_a_2551_);
lean_dec(v_a_2550_);
lean_dec(v_a_2549_);
return v_res_2558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___boxed(lean_object* v_recFnName_2559_, lean_object* v_fixedPrefixSize_2560_, lean_object* v_F_2561_, lean_object* v_e_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(v_recFnName_2559_, v_fixedPrefixSize_2560_, v_F_2561_, v_e_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_);
lean_dec(v_a_2570_);
lean_dec_ref(v_a_2569_);
lean_dec(v_a_2568_);
lean_dec_ref(v_a_2567_);
lean_dec(v_a_2566_);
lean_dec_ref(v_a_2565_);
lean_dec(v_a_2564_);
lean_dec(v_a_2563_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7(lean_object* v_00_u03b1_2573_, lean_object* v_k_2574_, uint8_t v_allowLevelAssignments_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_){
_start:
{
lean_object* v___x_2585_; 
v___x_2585_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v_k_2574_, v_allowLevelAssignments_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
return v___x_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___boxed(lean_object* v_00_u03b1_2586_, lean_object* v_k_2587_, lean_object* v_allowLevelAssignments_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2598_; lean_object* v_res_2599_; 
v_allowLevelAssignments_boxed_2598_ = lean_unbox(v_allowLevelAssignments_2588_);
v_res_2599_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7(v_00_u03b1_2586_, v_k_2587_, v_allowLevelAssignments_boxed_2598_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2590_);
lean_dec(v___y_2589_);
return v_res_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10(lean_object* v_00_u03b1_2600_, lean_object* v_name_2601_, uint8_t v_bi_2602_, lean_object* v_type_2603_, lean_object* v_k_2604_, uint8_t v_kind_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_){
_start:
{
lean_object* v___x_2615_; 
v___x_2615_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_name_2601_, v_bi_2602_, v_type_2603_, v_k_2604_, v_kind_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_);
return v___x_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___boxed(lean_object* v_00_u03b1_2616_, lean_object* v_name_2617_, lean_object* v_bi_2618_, lean_object* v_type_2619_, lean_object* v_k_2620_, lean_object* v_kind_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_){
_start:
{
uint8_t v_bi_boxed_2631_; uint8_t v_kind_boxed_2632_; lean_object* v_res_2633_; 
v_bi_boxed_2631_ = lean_unbox(v_bi_2618_);
v_kind_boxed_2632_ = lean_unbox(v_kind_2621_);
v_res_2633_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10(v_00_u03b1_2616_, v_name_2617_, v_bi_boxed_2631_, v_type_2619_, v_k_2620_, v_kind_boxed_2632_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
lean_dec(v___y_2623_);
lean_dec(v___y_2622_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(lean_object* v_00_u03b1_2634_, lean_object* v_e_2635_, lean_object* v_maxFVars_2636_, lean_object* v_k_2637_, uint8_t v_cleanupAnnotations_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v___x_2648_; 
v___x_2648_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(v_e_2635_, v_maxFVars_2636_, v_k_2637_, v_cleanupAnnotations_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___boxed(lean_object* v_00_u03b1_2649_, lean_object* v_e_2650_, lean_object* v_maxFVars_2651_, lean_object* v_k_2652_, lean_object* v_cleanupAnnotations_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2663_; lean_object* v_res_2664_; 
v_cleanupAnnotations_boxed_2663_ = lean_unbox(v_cleanupAnnotations_2653_);
v_res_2664_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(v_00_u03b1_2649_, v_e_2650_, v_maxFVars_2651_, v_k_2652_, v_cleanupAnnotations_boxed_2663_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
lean_dec(v___y_2661_);
lean_dec_ref(v___y_2660_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec(v___y_2655_);
lean_dec(v___y_2654_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0(lean_object* v_inst_2665_, lean_object* v_R_2666_, lean_object* v_a_2667_, lean_object* v_b_2668_){
_start:
{
lean_object* v___x_2669_; 
v___x_2669_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(v_a_2667_, v_b_2668_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2(lean_object* v_cls_2670_, lean_object* v_msg_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
lean_object* v___x_2681_; 
v___x_2681_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(v_cls_2670_, v_msg_2671_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_);
return v___x_2681_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___boxed(lean_object* v_cls_2682_, lean_object* v_msg_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_){
_start:
{
lean_object* v_res_2693_; 
v_res_2693_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2(v_cls_2682_, v_msg_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec(v___y_2685_);
lean_dec(v___y_2684_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4(lean_object* v_00_u03b2_2694_, lean_object* v_m_2695_, lean_object* v_a_2696_, lean_object* v_b_2697_){
_start:
{
lean_object* v___x_2698_; 
v___x_2698_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4___redArg(v_m_2695_, v_a_2696_, v_b_2697_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(lean_object* v_00_u03b1_2699_, lean_object* v_msg_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_){
_start:
{
lean_object* v___x_2710_; 
v___x_2710_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v_msg_2700_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_);
return v___x_2710_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___boxed(lean_object* v_00_u03b1_2711_, lean_object* v_msg_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_){
_start:
{
lean_object* v_res_2722_; 
v_res_2722_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(v_00_u03b1_2711_, v_msg_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec(v___y_2716_);
lean_dec_ref(v___y_2715_);
lean_dec(v___y_2714_);
lean_dec(v___y_2713_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8(lean_object* v_00_u03b2_2723_, lean_object* v_m_2724_, lean_object* v_a_2725_){
_start:
{
lean_object* v___x_2726_; 
v___x_2726_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v_m_2724_, v_a_2725_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___boxed(lean_object* v_00_u03b2_2727_, lean_object* v_m_2728_, lean_object* v_a_2729_){
_start:
{
lean_object* v_res_2730_; 
v_res_2730_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8(v_00_u03b2_2727_, v_m_2728_, v_a_2729_);
lean_dec_ref(v_a_2729_);
lean_dec_ref(v_m_2728_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15(lean_object* v_00_u03b1_2731_, lean_object* v_name_2732_, lean_object* v_type_2733_, lean_object* v_val_2734_, lean_object* v_k_2735_, uint8_t v_nondep_2736_, uint8_t v_kind_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_){
_start:
{
lean_object* v___x_2747_; 
v___x_2747_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(v_name_2732_, v_type_2733_, v_val_2734_, v_k_2735_, v_nondep_2736_, v_kind_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___boxed(lean_object* v_00_u03b1_2748_, lean_object* v_name_2749_, lean_object* v_type_2750_, lean_object* v_val_2751_, lean_object* v_k_2752_, lean_object* v_nondep_2753_, lean_object* v_kind_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
uint8_t v_nondep_boxed_2764_; uint8_t v_kind_boxed_2765_; lean_object* v_res_2766_; 
v_nondep_boxed_2764_ = lean_unbox(v_nondep_2753_);
v_kind_boxed_2765_ = lean_unbox(v_kind_2754_);
v_res_2766_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15(v_00_u03b1_2748_, v_name_2749_, v_type_2750_, v_val_2751_, v_k_2752_, v_nondep_boxed_2764_, v_kind_boxed_2765_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec(v___y_2758_);
lean_dec_ref(v___y_2757_);
lean_dec(v___y_2756_);
lean_dec(v___y_2755_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20(lean_object* v_declName_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_){
_start:
{
lean_object* v___x_2777_; 
v___x_2777_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(v_declName_2767_, v___y_2775_);
return v___x_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___boxed(lean_object* v_declName_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_){
_start:
{
lean_object* v_res_2788_; 
v_res_2788_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20(v_declName_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
lean_dec(v___y_2784_);
lean_dec_ref(v___y_2783_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec(v___y_2780_);
lean_dec(v___y_2779_);
return v_res_2788_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4(lean_object* v_00_u03b2_2789_, lean_object* v_a_2790_, lean_object* v_x_2791_){
_start:
{
uint8_t v___x_2792_; 
v___x_2792_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg(v_a_2790_, v_x_2791_);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___boxed(lean_object* v_00_u03b2_2793_, lean_object* v_a_2794_, lean_object* v_x_2795_){
_start:
{
uint8_t v_res_2796_; lean_object* v_r_2797_; 
v_res_2796_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4(v_00_u03b2_2793_, v_a_2794_, v_x_2795_);
lean_dec(v_x_2795_);
lean_dec_ref(v_a_2794_);
v_r_2797_ = lean_box(v_res_2796_);
return v_r_2797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5(lean_object* v_00_u03b2_2798_, lean_object* v_data_2799_){
_start:
{
lean_object* v___x_2800_; 
v___x_2800_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5___redArg(v_data_2799_);
return v___x_2800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6(lean_object* v_00_u03b2_2801_, lean_object* v_a_2802_, lean_object* v_b_2803_, lean_object* v_x_2804_){
_start:
{
lean_object* v___x_2805_; 
v___x_2805_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6___redArg(v_a_2802_, v_b_2803_, v_x_2804_);
return v___x_2805_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11(lean_object* v_00_u03b2_2806_, lean_object* v_a_2807_, lean_object* v_x_2808_){
_start:
{
lean_object* v___x_2809_; 
v___x_2809_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(v_a_2807_, v_x_2808_);
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___boxed(lean_object* v_00_u03b2_2810_, lean_object* v_a_2811_, lean_object* v_x_2812_){
_start:
{
lean_object* v_res_2813_; 
v_res_2813_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11(v_00_u03b2_2810_, v_a_2811_, v_x_2812_);
lean_dec(v_x_2812_);
lean_dec_ref(v_a_2811_);
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12(lean_object* v_00_u03b2_2814_, lean_object* v_i_2815_, lean_object* v_source_2816_, lean_object* v_target_2817_){
_start:
{
lean_object* v___x_2818_; 
v___x_2818_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12___redArg(v_i_2815_, v_source_2816_, v_target_2817_);
return v___x_2818_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21(lean_object* v_00_u03b1_2819_, lean_object* v_constName_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
lean_object* v___x_2830_; 
v___x_2830_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(v_constName_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___boxed(lean_object* v_00_u03b1_2831_, lean_object* v_constName_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_){
_start:
{
lean_object* v_res_2842_; 
v_res_2842_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21(v_00_u03b1_2831_, v_constName_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2838_);
lean_dec_ref(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2833_);
return v_res_2842_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12_spec__22(lean_object* v_00_u03b2_2843_, lean_object* v_x_2844_, lean_object* v_x_2845_){
_start:
{
lean_object* v___x_2846_; 
v___x_2846_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12_spec__22___redArg(v_x_2844_, v_x_2845_);
return v___x_2846_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27(lean_object* v_00_u03b1_2847_, lean_object* v_ref_2848_, lean_object* v_constName_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_){
_start:
{
lean_object* v___x_2859_; 
v___x_2859_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(v_ref_2848_, v_constName_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_);
return v___x_2859_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___boxed(lean_object* v_00_u03b1_2860_, lean_object* v_ref_2861_, lean_object* v_constName_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_){
_start:
{
lean_object* v_res_2872_; 
v_res_2872_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27(v_00_u03b1_2860_, v_ref_2861_, v_constName_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
lean_dec(v___y_2866_);
lean_dec_ref(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec(v_ref_2861_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29(lean_object* v_00_u03b1_2873_, lean_object* v_ref_2874_, lean_object* v_msg_2875_, lean_object* v_declHint_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_){
_start:
{
lean_object* v___x_2886_; 
v___x_2886_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(v_ref_2874_, v_msg_2875_, v_declHint_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___boxed(lean_object* v_00_u03b1_2887_, lean_object* v_ref_2888_, lean_object* v_msg_2889_, lean_object* v_declHint_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_){
_start:
{
lean_object* v_res_2900_; 
v_res_2900_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29(v_00_u03b1_2887_, v_ref_2888_, v_msg_2889_, v_declHint_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_);
lean_dec(v___y_2898_);
lean_dec_ref(v___y_2897_);
lean_dec(v___y_2896_);
lean_dec_ref(v___y_2895_);
lean_dec(v___y_2894_);
lean_dec_ref(v___y_2893_);
lean_dec(v___y_2892_);
lean_dec(v___y_2891_);
lean_dec(v_ref_2888_);
return v_res_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31(lean_object* v_msg_2901_, lean_object* v_declHint_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_){
_start:
{
lean_object* v___x_2912_; 
v___x_2912_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(v_msg_2901_, v_declHint_2902_, v___y_2910_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___boxed(lean_object* v_msg_2913_, lean_object* v_declHint_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_){
_start:
{
lean_object* v_res_2924_; 
v_res_2924_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31(v_msg_2913_, v_declHint_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v___y_2920_);
lean_dec_ref(v___y_2919_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec(v___y_2916_);
lean_dec(v___y_2915_);
return v_res_2924_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31(lean_object* v_00_u03b1_2925_, lean_object* v_ref_2926_, lean_object* v_msg_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_){
_start:
{
lean_object* v___x_2937_; 
v___x_2937_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(v_ref_2926_, v_msg_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___boxed(lean_object* v_00_u03b1_2938_, lean_object* v_ref_2939_, lean_object* v_msg_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_){
_start:
{
lean_object* v_res_2950_; 
v_res_2950_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31(v_00_u03b1_2938_, v_ref_2939_, v_msg_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec_ref(v___y_2945_);
lean_dec(v___y_2944_);
lean_dec_ref(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec(v_ref_2939_);
return v_res_2950_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(lean_object* v_cls_2951_, lean_object* v_msg_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_){
_start:
{
lean_object* v_ref_2958_; lean_object* v___x_2959_; lean_object* v_a_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_3004_; 
v_ref_2958_ = lean_ctor_get(v___y_2955_, 2);
v___x_2959_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
v_a_2960_ = lean_ctor_get(v___x_2959_, 0);
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2962_ = v___x_2959_;
v_isShared_2963_ = v_isSharedCheck_3004_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_a_2960_);
lean_dec(v___x_2959_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_3004_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2964_; lean_object* v_traceState_2965_; lean_object* v_env_2966_; lean_object* v_nextMacroScope_2967_; lean_object* v_ngen_2968_; lean_object* v_auxDeclNGen_2969_; lean_object* v_cache_2970_; lean_object* v_messages_2971_; lean_object* v_infoState_2972_; lean_object* v_snapshotTasks_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_3003_; 
v___x_2964_ = lean_st_ref_take(v___y_2956_);
v_traceState_2965_ = lean_ctor_get(v___x_2964_, 4);
v_env_2966_ = lean_ctor_get(v___x_2964_, 0);
v_nextMacroScope_2967_ = lean_ctor_get(v___x_2964_, 1);
v_ngen_2968_ = lean_ctor_get(v___x_2964_, 2);
v_auxDeclNGen_2969_ = lean_ctor_get(v___x_2964_, 3);
v_cache_2970_ = lean_ctor_get(v___x_2964_, 5);
v_messages_2971_ = lean_ctor_get(v___x_2964_, 6);
v_infoState_2972_ = lean_ctor_get(v___x_2964_, 7);
v_snapshotTasks_2973_ = lean_ctor_get(v___x_2964_, 8);
v_isSharedCheck_3003_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2975_ = v___x_2964_;
v_isShared_2976_ = v_isSharedCheck_3003_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_snapshotTasks_2973_);
lean_inc(v_infoState_2972_);
lean_inc(v_messages_2971_);
lean_inc(v_cache_2970_);
lean_inc(v_traceState_2965_);
lean_inc(v_auxDeclNGen_2969_);
lean_inc(v_ngen_2968_);
lean_inc(v_nextMacroScope_2967_);
lean_inc(v_env_2966_);
lean_dec(v___x_2964_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_3003_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
uint64_t v_tid_2977_; lean_object* v_traces_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_3002_; 
v_tid_2977_ = lean_ctor_get_uint64(v_traceState_2965_, sizeof(void*)*1);
v_traces_2978_ = lean_ctor_get(v_traceState_2965_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v_traceState_2965_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2980_ = v_traceState_2965_;
v_isShared_2981_ = v_isSharedCheck_3002_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_traces_2978_);
lean_dec(v_traceState_2965_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_3002_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2982_; double v___x_2983_; uint8_t v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2992_; 
v___x_2982_ = lean_box(0);
v___x_2983_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0);
v___x_2984_ = 0;
v___x_2985_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__1));
v___x_2986_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2986_, 0, v_cls_2951_);
lean_ctor_set(v___x_2986_, 1, v___x_2982_);
lean_ctor_set(v___x_2986_, 2, v___x_2985_);
lean_ctor_set_float(v___x_2986_, sizeof(void*)*3, v___x_2983_);
lean_ctor_set_float(v___x_2986_, sizeof(void*)*3 + 8, v___x_2983_);
lean_ctor_set_uint8(v___x_2986_, sizeof(void*)*3 + 16, v___x_2984_);
v___x_2987_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__2));
v___x_2988_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2986_);
lean_ctor_set(v___x_2988_, 1, v_a_2960_);
lean_ctor_set(v___x_2988_, 2, v___x_2987_);
lean_inc(v_ref_2958_);
v___x_2989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2989_, 0, v_ref_2958_);
lean_ctor_set(v___x_2989_, 1, v___x_2988_);
v___x_2990_ = l_Lean_PersistentArray_push___redArg(v_traces_2978_, v___x_2989_);
if (v_isShared_2981_ == 0)
{
lean_ctor_set(v___x_2980_, 0, v___x_2990_);
v___x_2992_ = v___x_2980_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v___x_2990_);
lean_ctor_set_uint64(v_reuseFailAlloc_3001_, sizeof(void*)*1, v_tid_2977_);
v___x_2992_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
lean_object* v___x_2994_; 
if (v_isShared_2976_ == 0)
{
lean_ctor_set(v___x_2975_, 4, v___x_2992_);
v___x_2994_ = v___x_2975_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_env_2966_);
lean_ctor_set(v_reuseFailAlloc_3000_, 1, v_nextMacroScope_2967_);
lean_ctor_set(v_reuseFailAlloc_3000_, 2, v_ngen_2968_);
lean_ctor_set(v_reuseFailAlloc_3000_, 3, v_auxDeclNGen_2969_);
lean_ctor_set(v_reuseFailAlloc_3000_, 4, v___x_2992_);
lean_ctor_set(v_reuseFailAlloc_3000_, 5, v_cache_2970_);
lean_ctor_set(v_reuseFailAlloc_3000_, 6, v_messages_2971_);
lean_ctor_set(v_reuseFailAlloc_3000_, 7, v_infoState_2972_);
lean_ctor_set(v_reuseFailAlloc_3000_, 8, v_snapshotTasks_2973_);
v___x_2994_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2998_; 
v___x_2995_ = lean_st_ref_put(v___y_2956_, v___x_2994_);
v___x_2996_ = lean_box(0);
if (v_isShared_2963_ == 0)
{
lean_ctor_set(v___x_2962_, 0, v___x_2996_);
v___x_2998_ = v___x_2962_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v___x_2996_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg___boxed(lean_object* v_cls_3005_, lean_object* v_msg_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3005_, v_msg_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3009_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
return v_res_3012_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0(void){
_start:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3013_ = lean_box(0);
v___x_3014_ = lean_unsigned_to_nat(16u);
v___x_3015_ = lean_mk_array(v___x_3014_, v___x_3013_);
return v___x_3015_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1(void){
_start:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3016_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0);
v___x_3017_ = lean_unsigned_to_nat(0u);
v___x_3018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3017_);
lean_ctor_set(v___x_3018_, 1, v___x_3016_);
return v___x_3018_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3(void){
_start:
{
lean_object* v___x_3020_; lean_object* v___x_3021_; 
v___x_3020_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__2));
v___x_3021_ = l_Lean_stringToMessageData(v___x_3020_);
return v___x_3021_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5(void){
_start:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3023_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__4));
v___x_3024_ = l_Lean_stringToMessageData(v___x_3023_);
return v___x_3024_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7(void){
_start:
{
lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3026_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__6));
v___x_3027_ = l_Lean_stringToMessageData(v___x_3026_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(lean_object* v_recFnName_3028_, lean_object* v_fixedPrefixSize_3029_, lean_object* v_F_3030_, lean_object* v_e_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_){
_start:
{
lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v_toCold_3060_; lean_object* v_options_3061_; uint8_t v_hasTrace_3062_; 
v_toCold_3060_ = lean_ctor_get(v_a_3036_, 0);
v_options_3061_ = lean_ctor_get(v_toCold_3060_, 2);
v_hasTrace_3062_ = lean_ctor_get_uint8(v_options_3061_, sizeof(void*)*1);
if (v_hasTrace_3062_ == 0)
{
v___y_3040_ = v_a_3032_;
v___y_3041_ = v_a_3033_;
v___y_3042_ = v_a_3034_;
v___y_3043_ = v_a_3035_;
v___y_3044_ = v_a_3036_;
v___y_3045_ = v_a_3037_;
goto v___jp_3039_;
}
else
{
lean_object* v_inheritedTraceOptions_3063_; lean_object* v_cls_3064_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v_options_3071_; lean_object* v_inheritedTraceOptions_3072_; lean_object* v___y_3073_; lean_object* v___x_3094_; uint8_t v___x_3095_; 
v_inheritedTraceOptions_3063_ = lean_ctor_get(v_toCold_3060_, 11);
v_cls_3064_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_3094_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_3095_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3063_, v_options_3061_, v___x_3094_);
if (v___x_3095_ == 0)
{
v___y_3066_ = v_a_3032_;
v___y_3067_ = v_a_3033_;
v___y_3068_ = v_a_3034_;
v___y_3069_ = v_a_3035_;
v___y_3070_ = v_a_3036_;
v_options_3071_ = v_options_3061_;
v_inheritedTraceOptions_3072_ = v_inheritedTraceOptions_3063_;
v___y_3073_ = v_a_3037_;
goto v___jp_3065_;
}
else
{
lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3096_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7);
lean_inc_ref(v_e_3031_);
v___x_3097_ = l_Lean_indentExpr(v_e_3031_);
v___x_3098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3096_);
lean_ctor_set(v___x_3098_, 1, v___x_3097_);
v___x_3099_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3064_, v___x_3098_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_);
if (lean_obj_tag(v___x_3099_) == 0)
{
lean_dec_ref_known(v___x_3099_, 1);
v___y_3066_ = v_a_3032_;
v___y_3067_ = v_a_3033_;
v___y_3068_ = v_a_3034_;
v___y_3069_ = v_a_3035_;
v___y_3070_ = v_a_3036_;
v_options_3071_ = v_options_3061_;
v_inheritedTraceOptions_3072_ = v_inheritedTraceOptions_3063_;
v___y_3073_ = v_a_3037_;
goto v___jp_3065_;
}
else
{
lean_object* v_a_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3107_; 
lean_dec_ref(v_e_3031_);
lean_dec_ref(v_F_3030_);
lean_dec(v_fixedPrefixSize_3029_);
lean_dec(v_recFnName_3028_);
v_a_3100_ = lean_ctor_get(v___x_3099_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3102_ = v___x_3099_;
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_dec(v___x_3099_);
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
v___jp_3065_:
{
lean_object* v___x_3074_; uint8_t v___x_3075_; 
v___x_3074_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_3075_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3072_, v_options_3071_, v___x_3074_);
if (v___x_3075_ == 0)
{
v___y_3040_ = v___y_3066_;
v___y_3041_ = v___y_3067_;
v___y_3042_ = v___y_3068_;
v___y_3043_ = v___y_3069_;
v___y_3044_ = v___y_3070_;
v___y_3045_ = v___y_3073_;
goto v___jp_3039_;
}
else
{
lean_object* v___x_3076_; 
lean_inc(v___y_3073_);
lean_inc_ref(v___y_3070_);
lean_inc(v___y_3069_);
lean_inc_ref(v___y_3068_);
lean_inc_ref(v_F_3030_);
v___x_3076_ = lean_infer_type(v_F_3030_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3073_);
if (lean_obj_tag(v___x_3076_) == 0)
{
lean_object* v_a_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v_a_3077_ = lean_ctor_get(v___x_3076_, 0);
lean_inc(v_a_3077_);
lean_dec_ref_known(v___x_3076_, 1);
v___x_3078_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3);
lean_inc_ref(v_F_3030_);
v___x_3079_ = l_Lean_MessageData_ofExpr(v_F_3030_);
v___x_3080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3080_, 0, v___x_3078_);
lean_ctor_set(v___x_3080_, 1, v___x_3079_);
v___x_3081_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5);
v___x_3082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3080_);
lean_ctor_set(v___x_3082_, 1, v___x_3081_);
v___x_3083_ = l_Lean_indentExpr(v_a_3077_);
v___x_3084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3084_, 0, v___x_3082_);
lean_ctor_set(v___x_3084_, 1, v___x_3083_);
v___x_3085_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3064_, v___x_3084_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3073_);
if (lean_obj_tag(v___x_3085_) == 0)
{
lean_dec_ref_known(v___x_3085_, 1);
v___y_3040_ = v___y_3066_;
v___y_3041_ = v___y_3067_;
v___y_3042_ = v___y_3068_;
v___y_3043_ = v___y_3069_;
v___y_3044_ = v___y_3070_;
v___y_3045_ = v___y_3073_;
goto v___jp_3039_;
}
else
{
lean_object* v_a_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3093_; 
lean_dec_ref(v_e_3031_);
lean_dec_ref(v_F_3030_);
lean_dec(v_fixedPrefixSize_3029_);
lean_dec(v_recFnName_3028_);
v_a_3086_ = lean_ctor_get(v___x_3085_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3088_ = v___x_3085_;
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_dec(v___x_3085_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3091_; 
if (v_isShared_3089_ == 0)
{
v___x_3091_ = v___x_3088_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_a_3086_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
}
else
{
lean_dec_ref(v_e_3031_);
lean_dec_ref(v_F_3030_);
lean_dec(v_fixedPrefixSize_3029_);
lean_dec(v_recFnName_3028_);
return v___x_3076_;
}
}
}
}
v___jp_3039_:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; 
v___x_3046_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1);
v___x_3047_ = lean_st_mk_ref(v___x_3046_);
v___x_3048_ = lean_st_mk_ref(v___x_3046_);
v___x_3049_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_3028_, v_fixedPrefixSize_3029_, v_F_3030_, v_e_3031_, v___x_3048_, v___x_3047_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3059_; 
v_a_3050_ = lean_ctor_get(v___x_3049_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3052_ = v___x_3049_;
v_isShared_3053_ = v_isSharedCheck_3059_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_3049_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3059_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3057_; 
v___x_3054_ = lean_st_ref_get(v___x_3048_);
lean_dec(v___x_3048_);
lean_dec(v___x_3054_);
v___x_3055_ = lean_st_ref_get(v___x_3047_);
lean_dec(v___x_3047_);
lean_dec(v___x_3055_);
if (v_isShared_3053_ == 0)
{
v___x_3057_ = v___x_3052_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_a_3050_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
}
else
{
lean_dec(v___x_3048_);
lean_dec(v___x_3047_);
return v___x_3049_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___boxed(lean_object* v_recFnName_3108_, lean_object* v_fixedPrefixSize_3109_, lean_object* v_F_3110_, lean_object* v_e_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_){
_start:
{
lean_object* v_res_3119_; 
v_res_3119_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(v_recFnName_3108_, v_fixedPrefixSize_3109_, v_F_3110_, v_e_3111_, v_a_3112_, v_a_3113_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_);
lean_dec(v_a_3117_);
lean_dec_ref(v_a_3116_);
lean_dec(v_a_3115_);
lean_dec_ref(v_a_3114_);
lean_dec(v_a_3113_);
lean_dec_ref(v_a_3112_);
return v_res_3119_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0(lean_object* v_cls_3120_, lean_object* v_msg_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_){
_start:
{
lean_object* v___x_3129_; 
v___x_3129_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3120_, v_msg_3121_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
return v___x_3129_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___boxed(lean_object* v_cls_3130_, lean_object* v_msg_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_){
_start:
{
lean_object* v_res_3139_; 
v_res_3139_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0(v_cls_3130_, v_msg_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
lean_dec(v___y_3137_);
lean_dec_ref(v___y_3136_);
lean_dec(v___y_3135_);
lean_dec_ref(v___y_3134_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
return v_res_3139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0(lean_object* v_k_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v_b_3143_, lean_object* v_c_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_){
_start:
{
lean_object* v___x_3150_; 
lean_inc(v___y_3148_);
lean_inc_ref(v___y_3147_);
lean_inc(v___y_3146_);
lean_inc_ref(v___y_3145_);
lean_inc(v___y_3142_);
lean_inc_ref(v___y_3141_);
v___x_3150_ = lean_apply_9(v_k_3140_, v_b_3143_, v_c_3144_, v___y_3141_, v___y_3142_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, lean_box(0));
return v___x_3150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed(lean_object* v_k_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v_b_3154_, lean_object* v_c_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_){
_start:
{
lean_object* v_res_3161_; 
v_res_3161_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0(v_k_3151_, v___y_3152_, v___y_3153_, v_b_3154_, v_c_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(lean_object* v_e_3162_, lean_object* v_k_3163_, uint8_t v_cleanupAnnotations_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
lean_object* v___f_3172_; uint8_t v___x_3173_; uint8_t v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; 
lean_inc(v___y_3166_);
lean_inc_ref(v___y_3165_);
v___f_3172_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3172_, 0, v_k_3163_);
lean_closure_set(v___f_3172_, 1, v___y_3165_);
lean_closure_set(v___f_3172_, 2, v___y_3166_);
v___x_3173_ = 1;
v___x_3174_ = 0;
v___x_3175_ = lean_box(0);
v___x_3176_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3162_, v___x_3173_, v___x_3174_, v___x_3173_, v___x_3174_, v___x_3175_, v___f_3172_, v_cleanupAnnotations_3164_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
if (lean_obj_tag(v___x_3176_) == 0)
{
return v___x_3176_;
}
else
{
lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3184_; 
v_a_3177_ = lean_ctor_get(v___x_3176_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3176_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3179_ = v___x_3176_;
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_a_3177_);
lean_dec(v___x_3176_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___x_3182_; 
if (v_isShared_3180_ == 0)
{
v___x_3182_ = v___x_3179_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_a_3177_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___boxed(lean_object* v_e_3185_, lean_object* v_k_3186_, lean_object* v_cleanupAnnotations_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3195_; lean_object* v_res_3196_; 
v_cleanupAnnotations_boxed_3195_ = lean_unbox(v_cleanupAnnotations_3187_);
v_res_3196_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v_e_3185_, v_k_3186_, v_cleanupAnnotations_boxed_3195_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0(lean_object* v_00_u03b1_3197_, lean_object* v_e_3198_, lean_object* v_k_3199_, uint8_t v_cleanupAnnotations_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_){
_start:
{
lean_object* v___x_3208_; 
v___x_3208_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v_e_3198_, v_k_3199_, v_cleanupAnnotations_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___boxed(lean_object* v_00_u03b1_3209_, lean_object* v_e_3210_, lean_object* v_k_3211_, lean_object* v_cleanupAnnotations_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3220_; lean_object* v_res_3221_; 
v_cleanupAnnotations_boxed_3220_ = lean_unbox(v_cleanupAnnotations_3212_);
v_res_3221_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0(v_00_u03b1_3209_, v_e_3210_, v_k_3211_, v_cleanupAnnotations_boxed_3220_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
lean_dec(v___y_3218_);
lean_dec_ref(v___y_3217_);
lean_dec(v___y_3216_);
lean_dec_ref(v___y_3215_);
lean_dec(v___y_3214_);
lean_dec_ref(v___y_3213_);
return v_res_3221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(lean_object* v_e_3222_, lean_object* v_maxFVars_3223_, lean_object* v_k_3224_, uint8_t v_cleanupAnnotations_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_){
_start:
{
lean_object* v___f_3233_; uint8_t v___x_3234_; uint8_t v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; 
lean_inc(v___y_3227_);
lean_inc_ref(v___y_3226_);
v___f_3233_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3233_, 0, v_k_3224_);
lean_closure_set(v___f_3233_, 1, v___y_3226_);
lean_closure_set(v___f_3233_, 2, v___y_3227_);
v___x_3234_ = 1;
v___x_3235_ = 0;
v___x_3236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3236_, 0, v_maxFVars_3223_);
v___x_3237_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3222_, v___x_3234_, v___x_3235_, v___x_3234_, v___x_3235_, v___x_3236_, v___f_3233_, v_cleanupAnnotations_3225_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_);
lean_dec_ref_known(v___x_3236_, 1);
if (lean_obj_tag(v___x_3237_) == 0)
{
return v___x_3237_;
}
else
{
lean_object* v_a_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3245_; 
v_a_3238_ = lean_ctor_get(v___x_3237_, 0);
v_isSharedCheck_3245_ = !lean_is_exclusive(v___x_3237_);
if (v_isSharedCheck_3245_ == 0)
{
v___x_3240_ = v___x_3237_;
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_a_3238_);
lean_dec(v___x_3237_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v___x_3243_; 
if (v_isShared_3241_ == 0)
{
v___x_3243_ = v___x_3240_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v_a_3238_);
v___x_3243_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
return v___x_3243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg___boxed(lean_object* v_e_3246_, lean_object* v_maxFVars_3247_, lean_object* v_k_3248_, lean_object* v_cleanupAnnotations_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3257_; lean_object* v_res_3258_; 
v_cleanupAnnotations_boxed_3257_ = lean_unbox(v_cleanupAnnotations_3249_);
v_res_3258_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_e_3246_, v_maxFVars_3247_, v_k_3248_, v_cleanupAnnotations_boxed_3257_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_);
lean_dec(v___y_3255_);
lean_dec_ref(v___y_3254_);
lean_dec(v___y_3253_);
lean_dec_ref(v___y_3252_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2(lean_object* v_00_u03b1_3259_, lean_object* v_e_3260_, lean_object* v_maxFVars_3261_, lean_object* v_k_3262_, uint8_t v_cleanupAnnotations_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_){
_start:
{
lean_object* v___x_3271_; 
v___x_3271_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_e_3260_, v_maxFVars_3261_, v_k_3262_, v_cleanupAnnotations_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_);
return v___x_3271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___boxed(lean_object* v_00_u03b1_3272_, lean_object* v_e_3273_, lean_object* v_maxFVars_3274_, lean_object* v_k_3275_, lean_object* v_cleanupAnnotations_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3284_; lean_object* v_res_3285_; 
v_cleanupAnnotations_boxed_3284_ = lean_unbox(v_cleanupAnnotations_3276_);
v_res_3285_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2(v_00_u03b1_3272_, v_e_3273_, v_maxFVars_3274_, v_k_3275_, v_cleanupAnnotations_boxed_3284_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
lean_dec(v___y_3282_);
lean_dec_ref(v___y_3281_);
lean_dec(v___y_3280_);
lean_dec_ref(v___y_3279_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0(lean_object* v_a_3286_, lean_object* v___x_3287_, lean_object* v___x_3288_, lean_object* v_x_3289_, uint8_t v___x_3290_, lean_object* v_xs_3291_, lean_object* v_type_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_){
_start:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
v___x_3300_ = l_Lean_LocalDecl_type(v_a_3286_);
v___x_3301_ = lean_array_get_borrowed(v___x_3287_, v_xs_3291_, v___x_3288_);
v___x_3302_ = l_Lean_Expr_replaceFVar(v___x_3300_, v_x_3289_, v___x_3301_);
lean_dec_ref(v___x_3300_);
v___x_3303_ = l_Lean_mkArrow(v___x_3302_, v_type_3292_, v___y_3297_, v___y_3298_);
if (lean_obj_tag(v___x_3303_) == 0)
{
lean_object* v_a_3304_; uint8_t v___x_3305_; uint8_t v___x_3306_; lean_object* v___x_3307_; 
v_a_3304_ = lean_ctor_get(v___x_3303_, 0);
lean_inc_n(v_a_3304_, 2);
lean_dec_ref_known(v___x_3303_, 1);
v___x_3305_ = 0;
v___x_3306_ = 1;
v___x_3307_ = l_Lean_Meta_mkLambdaFVars(v_xs_3291_, v_a_3304_, v___x_3305_, v___x_3290_, v___x_3305_, v___x_3290_, v___x_3306_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_);
if (lean_obj_tag(v___x_3307_) == 0)
{
lean_object* v_a_3308_; lean_object* v___x_3309_; 
v_a_3308_ = lean_ctor_get(v___x_3307_, 0);
lean_inc(v_a_3308_);
lean_dec_ref_known(v___x_3307_, 1);
v___x_3309_ = l_Lean_Meta_getLevel(v_a_3304_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_);
if (lean_obj_tag(v___x_3309_) == 0)
{
lean_object* v_a_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3318_; 
v_a_3310_ = lean_ctor_get(v___x_3309_, 0);
v_isSharedCheck_3318_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3312_ = v___x_3309_;
v_isShared_3313_ = v_isSharedCheck_3318_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_a_3310_);
lean_dec(v___x_3309_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3318_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
lean_object* v___x_3314_; lean_object* v___x_3316_; 
v___x_3314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3314_, 0, v_a_3308_);
lean_ctor_set(v___x_3314_, 1, v_a_3310_);
if (v_isShared_3313_ == 0)
{
lean_ctor_set(v___x_3312_, 0, v___x_3314_);
v___x_3316_ = v___x_3312_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v___x_3314_);
v___x_3316_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
return v___x_3316_;
}
}
}
else
{
lean_object* v_a_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3326_; 
lean_dec(v_a_3308_);
v_a_3319_ = lean_ctor_get(v___x_3309_, 0);
v_isSharedCheck_3326_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3321_ = v___x_3309_;
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_a_3319_);
lean_dec(v___x_3309_);
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
lean_dec(v_a_3304_);
v_a_3327_ = lean_ctor_get(v___x_3307_, 0);
v_isSharedCheck_3334_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3329_ = v___x_3307_;
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_a_3327_);
lean_dec(v___x_3307_);
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
else
{
lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3342_; 
v_a_3335_ = lean_ctor_get(v___x_3303_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3303_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3337_ = v___x_3303_;
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_a_3335_);
lean_dec(v___x_3303_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v___x_3340_; 
if (v_isShared_3338_ == 0)
{
v___x_3340_ = v___x_3337_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_a_3335_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
return v___x_3340_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed(lean_object* v_a_3343_, lean_object* v___x_3344_, lean_object* v___x_3345_, lean_object* v_x_3346_, lean_object* v___x_3347_, lean_object* v_xs_3348_, lean_object* v_type_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_){
_start:
{
uint8_t v___x_6244__boxed_3357_; lean_object* v_res_3358_; 
v___x_6244__boxed_3357_ = lean_unbox(v___x_3347_);
v_res_3358_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0(v_a_3343_, v___x_3344_, v___x_3345_, v_x_3346_, v___x_6244__boxed_3357_, v_xs_3348_, v_type_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_);
lean_dec(v___y_3355_);
lean_dec_ref(v___y_3354_);
lean_dec(v___y_3353_);
lean_dec_ref(v___y_3352_);
lean_dec(v___y_3351_);
lean_dec_ref(v___y_3350_);
lean_dec_ref(v_xs_3348_);
lean_dec(v___x_3345_);
lean_dec_ref(v___x_3344_);
lean_dec_ref(v_a_3343_);
return v_res_3358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0(lean_object* v_k_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v_b_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_){
_start:
{
lean_object* v___x_3368_; 
lean_inc(v___y_3366_);
lean_inc_ref(v___y_3365_);
lean_inc(v___y_3364_);
lean_inc_ref(v___y_3363_);
lean_inc(v___y_3361_);
lean_inc_ref(v___y_3360_);
v___x_3368_ = lean_apply_8(v_k_3359_, v_b_3362_, v___y_3360_, v___y_3361_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_, lean_box(0));
return v___x_3368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_k_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v_b_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_){
_start:
{
lean_object* v_res_3378_; 
v_res_3378_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0(v_k_3369_, v___y_3370_, v___y_3371_, v_b_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_);
lean_dec(v___y_3376_);
lean_dec_ref(v___y_3375_);
lean_dec(v___y_3374_);
lean_dec_ref(v___y_3373_);
lean_dec(v___y_3371_);
lean_dec_ref(v___y_3370_);
return v_res_3378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(lean_object* v_name_3379_, uint8_t v_bi_3380_, lean_object* v_type_3381_, lean_object* v_k_3382_, uint8_t v_kind_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_){
_start:
{
lean_object* v___f_3391_; lean_object* v___x_3392_; 
lean_inc(v___y_3385_);
lean_inc_ref(v___y_3384_);
v___f_3391_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3391_, 0, v_k_3382_);
lean_closure_set(v___f_3391_, 1, v___y_3384_);
lean_closure_set(v___f_3391_, 2, v___y_3385_);
v___x_3392_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3379_, v_bi_3380_, v_type_3381_, v___f_3391_, v_kind_3383_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_);
if (lean_obj_tag(v___x_3392_) == 0)
{
return v___x_3392_;
}
else
{
lean_object* v_a_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3400_; 
v_a_3393_ = lean_ctor_get(v___x_3392_, 0);
v_isSharedCheck_3400_ = !lean_is_exclusive(v___x_3392_);
if (v_isSharedCheck_3400_ == 0)
{
v___x_3395_ = v___x_3392_;
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_a_3393_);
lean_dec(v___x_3392_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v___x_3398_; 
if (v_isShared_3396_ == 0)
{
v___x_3398_ = v___x_3395_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v_a_3393_);
v___x_3398_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
return v___x_3398_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___boxed(lean_object* v_name_3401_, lean_object* v_bi_3402_, lean_object* v_type_3403_, lean_object* v_k_3404_, lean_object* v_kind_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
uint8_t v_bi_boxed_3413_; uint8_t v_kind_boxed_3414_; lean_object* v_res_3415_; 
v_bi_boxed_3413_ = lean_unbox(v_bi_3402_);
v_kind_boxed_3414_ = lean_unbox(v_kind_3405_);
v_res_3415_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(v_name_3401_, v_bi_boxed_3413_, v_type_3403_, v_k_3404_, v_kind_boxed_3414_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
return v_res_3415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(lean_object* v_name_3416_, lean_object* v_type_3417_, lean_object* v_k_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_){
_start:
{
uint8_t v___x_3426_; uint8_t v___x_3427_; lean_object* v___x_3428_; 
v___x_3426_ = 0;
v___x_3427_ = 0;
v___x_3428_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(v_name_3416_, v___x_3426_, v_type_3417_, v_k_3418_, v___x_3427_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_);
return v___x_3428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___boxed(lean_object* v_name_3429_, lean_object* v_type_3430_, lean_object* v_k_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_){
_start:
{
lean_object* v_res_3439_; 
v_res_3439_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_name_3429_, v_type_3430_, v_k_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_);
lean_dec(v___y_3437_);
lean_dec_ref(v___y_3436_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
return v_res_3439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(lean_object* v_x_3453_, lean_object* v_F_3454_, lean_object* v_val_3455_, lean_object* v_k_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_){
_start:
{
lean_object* v___x_3464_; uint8_t v___y_3466_; uint8_t v___x_3580_; 
v___x_3464_ = l_Lean_instInhabitedExpr;
v___x_3580_ = l_Lean_Expr_isFVar(v_x_3453_);
if (v___x_3580_ == 0)
{
v___y_3466_ = v___x_3580_;
goto v___jp_3465_;
}
else
{
lean_object* v___x_3581_; lean_object* v___x_3582_; uint8_t v___x_3583_; 
v___x_3581_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6));
v___x_3582_ = lean_unsigned_to_nat(6u);
v___x_3583_ = l_Lean_Expr_isAppOfArity(v_val_3455_, v___x_3581_, v___x_3582_);
v___y_3466_ = v___x_3583_;
goto v___jp_3465_;
}
v___jp_3465_:
{
if (v___y_3466_ == 0)
{
lean_object* v___x_3467_; 
lean_inc(v_a_3462_);
lean_inc_ref(v_a_3461_);
lean_inc(v_a_3460_);
lean_inc_ref(v_a_3459_);
lean_inc(v_a_3458_);
lean_inc_ref(v_a_3457_);
v___x_3467_ = lean_apply_10(v_k_3456_, v_x_3453_, v_F_3454_, v_val_3455_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_, lean_box(0));
return v___x_3467_;
}
else
{
lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; uint8_t v___x_3474_; 
v___x_3468_ = lean_unsigned_to_nat(3u);
v___x_3469_ = l_Lean_Expr_getAppNumArgs(v_val_3455_);
v___x_3470_ = lean_nat_sub(v___x_3469_, v___x_3468_);
v___x_3471_ = lean_unsigned_to_nat(1u);
v___x_3472_ = lean_nat_sub(v___x_3470_, v___x_3471_);
lean_dec(v___x_3470_);
v___x_3473_ = l_Lean_Expr_getRevArg_x21(v_val_3455_, v___x_3472_);
v___x_3474_ = lean_expr_eqv(v___x_3473_, v_x_3453_);
lean_dec_ref(v___x_3473_);
if (v___x_3474_ == 0)
{
lean_object* v___x_3475_; 
lean_dec(v___x_3469_);
lean_inc(v_a_3462_);
lean_inc_ref(v_a_3461_);
lean_inc(v_a_3460_);
lean_inc_ref(v_a_3459_);
lean_inc(v_a_3458_);
lean_inc_ref(v_a_3457_);
v___x_3475_ = lean_apply_10(v_k_3456_, v_x_3453_, v_F_3454_, v_val_3455_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_, lean_box(0));
return v___x_3475_;
}
else
{
lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; uint8_t v___x_3480_; 
v___x_3476_ = lean_unsigned_to_nat(4u);
v___x_3477_ = lean_nat_sub(v___x_3469_, v___x_3476_);
v___x_3478_ = lean_nat_sub(v___x_3477_, v___x_3471_);
lean_dec(v___x_3477_);
v___x_3479_ = l_Lean_Expr_getRevArg_x21(v_val_3455_, v___x_3478_);
v___x_3480_ = l_Lean_Expr_isLambda(v___x_3479_);
lean_dec_ref(v___x_3479_);
if (v___x_3480_ == 0)
{
lean_object* v___x_3481_; 
lean_dec(v___x_3469_);
lean_inc(v_a_3462_);
lean_inc_ref(v_a_3461_);
lean_inc(v_a_3460_);
lean_inc_ref(v_a_3459_);
lean_inc(v_a_3458_);
lean_inc_ref(v_a_3457_);
v___x_3481_ = lean_apply_10(v_k_3456_, v_x_3453_, v_F_3454_, v_val_3455_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_, lean_box(0));
return v___x_3481_;
}
else
{
lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; uint8_t v___x_3486_; 
v___x_3482_ = lean_unsigned_to_nat(5u);
v___x_3483_ = lean_nat_sub(v___x_3469_, v___x_3482_);
v___x_3484_ = lean_nat_sub(v___x_3483_, v___x_3471_);
lean_dec(v___x_3483_);
v___x_3485_ = l_Lean_Expr_getRevArg_x21(v_val_3455_, v___x_3484_);
v___x_3486_ = l_Lean_Expr_isLambda(v___x_3485_);
lean_dec_ref(v___x_3485_);
if (v___x_3486_ == 0)
{
lean_object* v___x_3487_; 
lean_dec(v___x_3469_);
lean_inc(v_a_3462_);
lean_inc_ref(v_a_3461_);
lean_inc(v_a_3460_);
lean_inc_ref(v_a_3459_);
lean_inc(v_a_3458_);
lean_inc_ref(v_a_3457_);
v___x_3487_ = lean_apply_10(v_k_3456_, v_x_3453_, v_F_3454_, v_val_3455_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_, lean_box(0));
return v___x_3487_;
}
else
{
lean_object* v___x_3488_; lean_object* v___x_3489_; 
v___x_3488_ = l_Lean_Expr_fvarId_x21(v_F_3454_);
v___x_3489_ = l_Lean_FVarId_getDecl___redArg(v___x_3488_, v_a_3459_, v_a_3461_, v_a_3462_);
if (lean_obj_tag(v___x_3489_) == 0)
{
lean_object* v_a_3490_; lean_object* v_dummy_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v_args_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___f_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; uint8_t v___x_3500_; lean_object* v___x_3501_; 
v_a_3490_ = lean_ctor_get(v___x_3489_, 0);
lean_inc_n(v_a_3490_, 2);
lean_dec_ref_known(v___x_3489_, 1);
v_dummy_3491_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_3469_);
v___x_3492_ = lean_mk_array(v___x_3469_, v_dummy_3491_);
v___x_3493_ = lean_nat_sub(v___x_3469_, v___x_3471_);
lean_dec(v___x_3469_);
v_args_3494_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_3455_, v___x_3492_, v___x_3493_);
v___x_3495_ = lean_unsigned_to_nat(0u);
v___x_3496_ = lean_box(v___x_3480_);
lean_inc_ref(v_x_3453_);
v___f_3497_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed), 14, 5);
lean_closure_set(v___f_3497_, 0, v_a_3490_);
lean_closure_set(v___f_3497_, 1, v___x_3464_);
lean_closure_set(v___f_3497_, 2, v___x_3495_);
lean_closure_set(v___f_3497_, 3, v_x_3453_);
lean_closure_set(v___f_3497_, 4, v___x_3496_);
v___x_3498_ = lean_unsigned_to_nat(2u);
v___x_3499_ = lean_array_get(v___x_3464_, v_args_3494_, v___x_3498_);
v___x_3500_ = 0;
v___x_3501_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_3499_, v___f_3497_, v___x_3500_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_a_3502_; lean_object* v_fst_3503_; lean_object* v_snd_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3563_; 
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_a_3502_);
lean_dec_ref_known(v___x_3501_, 1);
v_fst_3503_ = lean_ctor_get(v_a_3502_, 0);
v_snd_3504_ = lean_ctor_get(v_a_3502_, 1);
v_isSharedCheck_3563_ = !lean_is_exclusive(v_a_3502_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3506_ = v_a_3502_;
v_isShared_3507_ = v_isSharedCheck_3563_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_snd_3504_);
lean_inc(v_fst_3503_);
lean_dec(v_a_3502_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3563_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v_00_u03b1_3508_; lean_object* v_00_u03b2_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; 
v_00_u03b1_3508_ = lean_array_get(v___x_3464_, v_args_3494_, v___x_3495_);
v_00_u03b2_3509_ = lean_array_get(v___x_3464_, v_args_3494_, v___x_3471_);
v___x_3510_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__2));
v___x_3511_ = lean_array_get(v___x_3464_, v_args_3494_, v___x_3476_);
lean_inc_ref(v_x_3453_);
lean_inc(v_a_3490_);
lean_inc_ref(v_k_3456_);
lean_inc(v_00_u03b2_3509_);
lean_inc(v_00_u03b1_3508_);
v___x_3512_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3464_, v___x_3495_, v_00_u03b1_3508_, v_00_u03b2_3509_, v___x_3468_, v_k_3456_, v___x_3498_, v___x_3500_, v___x_3480_, v_a_3490_, v_x_3453_, v___x_3471_, v___x_3510_, v___x_3511_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_);
if (lean_obj_tag(v___x_3512_) == 0)
{
lean_object* v_a_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; 
v_a_3513_ = lean_ctor_get(v___x_3512_, 0);
lean_inc(v_a_3513_);
lean_dec_ref_known(v___x_3512_, 1);
v___x_3514_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__4));
v___x_3515_ = lean_array_get(v___x_3464_, v_args_3494_, v___x_3482_);
lean_dec_ref(v_args_3494_);
lean_inc_ref(v_x_3453_);
lean_inc(v_00_u03b2_3509_);
lean_inc(v_00_u03b1_3508_);
v___x_3516_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3464_, v___x_3495_, v_00_u03b1_3508_, v_00_u03b2_3509_, v___x_3468_, v_k_3456_, v___x_3498_, v___x_3500_, v___x_3480_, v_a_3490_, v_x_3453_, v___x_3471_, v___x_3514_, v___x_3515_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_);
if (lean_obj_tag(v___x_3516_) == 0)
{
lean_object* v_a_3517_; lean_object* v___x_3518_; 
v_a_3517_ = lean_ctor_get(v___x_3516_, 0);
lean_inc(v_a_3517_);
lean_dec_ref_known(v___x_3516_, 1);
lean_inc(v_00_u03b1_3508_);
v___x_3518_ = l_Lean_Meta_getLevel(v_00_u03b1_3508_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_);
if (lean_obj_tag(v___x_3518_) == 0)
{
lean_object* v_a_3519_; lean_object* v___x_3520_; 
v_a_3519_ = lean_ctor_get(v___x_3518_, 0);
lean_inc(v_a_3519_);
lean_dec_ref_known(v___x_3518_, 1);
lean_inc(v_00_u03b2_3509_);
v___x_3520_ = l_Lean_Meta_getLevel(v_00_u03b2_3509_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_object* v_a_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3546_; 
v_a_3521_ = lean_ctor_get(v___x_3520_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3520_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3523_ = v___x_3520_;
v_isShared_3524_ = v_isSharedCheck_3546_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_a_3521_);
lean_dec(v___x_3520_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3546_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3528_; 
v___x_3525_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6));
v___x_3526_ = lean_box(0);
if (v_isShared_3507_ == 0)
{
lean_ctor_set_tag(v___x_3506_, 1);
lean_ctor_set(v___x_3506_, 1, v___x_3526_);
lean_ctor_set(v___x_3506_, 0, v_a_3521_);
v___x_3528_ = v___x_3506_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_a_3521_);
lean_ctor_set(v_reuseFailAlloc_3545_, 1, v___x_3526_);
v___x_3528_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3543_; 
v___x_3529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3529_, 0, v_a_3519_);
lean_ctor_set(v___x_3529_, 1, v___x_3528_);
v___x_3530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3530_, 0, v_snd_3504_);
lean_ctor_set(v___x_3530_, 1, v___x_3529_);
v___x_3531_ = l_Lean_mkConst(v___x_3525_, v___x_3530_);
v___x_3532_ = lean_unsigned_to_nat(7u);
v___x_3533_ = lean_mk_empty_array_with_capacity(v___x_3532_);
v___x_3534_ = lean_array_push(v___x_3533_, v_00_u03b1_3508_);
v___x_3535_ = lean_array_push(v___x_3534_, v_00_u03b2_3509_);
v___x_3536_ = lean_array_push(v___x_3535_, v_fst_3503_);
v___x_3537_ = lean_array_push(v___x_3536_, v_x_3453_);
v___x_3538_ = lean_array_push(v___x_3537_, v_a_3513_);
v___x_3539_ = lean_array_push(v___x_3538_, v_a_3517_);
v___x_3540_ = lean_array_push(v___x_3539_, v_F_3454_);
v___x_3541_ = l_Lean_mkAppN(v___x_3531_, v___x_3540_);
lean_dec_ref(v___x_3540_);
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 0, v___x_3541_);
v___x_3543_ = v___x_3523_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v___x_3541_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
return v___x_3543_;
}
}
}
}
else
{
lean_object* v_a_3547_; lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3554_; 
lean_dec(v_a_3519_);
lean_dec(v_a_3517_);
lean_dec(v_a_3513_);
lean_dec(v_00_u03b2_3509_);
lean_dec(v_00_u03b1_3508_);
lean_del_object(v___x_3506_);
lean_dec(v_snd_3504_);
lean_dec(v_fst_3503_);
lean_dec_ref(v_F_3454_);
lean_dec_ref(v_x_3453_);
v_a_3547_ = lean_ctor_get(v___x_3520_, 0);
v_isSharedCheck_3554_ = !lean_is_exclusive(v___x_3520_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3549_ = v___x_3520_;
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
else
{
lean_inc(v_a_3547_);
lean_dec(v___x_3520_);
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
lean_object* v_a_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3562_; 
lean_dec(v_a_3517_);
lean_dec(v_a_3513_);
lean_dec(v_00_u03b2_3509_);
lean_dec(v_00_u03b1_3508_);
lean_del_object(v___x_3506_);
lean_dec(v_snd_3504_);
lean_dec(v_fst_3503_);
lean_dec_ref(v_F_3454_);
lean_dec_ref(v_x_3453_);
v_a_3555_ = lean_ctor_get(v___x_3518_, 0);
v_isSharedCheck_3562_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3562_ == 0)
{
v___x_3557_ = v___x_3518_;
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_a_3555_);
lean_dec(v___x_3518_);
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
else
{
lean_dec(v_a_3513_);
lean_dec(v_00_u03b2_3509_);
lean_dec(v_00_u03b1_3508_);
lean_del_object(v___x_3506_);
lean_dec(v_snd_3504_);
lean_dec(v_fst_3503_);
lean_dec_ref(v_F_3454_);
lean_dec_ref(v_x_3453_);
return v___x_3516_;
}
}
else
{
lean_dec(v_00_u03b2_3509_);
lean_dec(v_00_u03b1_3508_);
lean_del_object(v___x_3506_);
lean_dec(v_snd_3504_);
lean_dec(v_fst_3503_);
lean_dec_ref(v_args_3494_);
lean_dec(v_a_3490_);
lean_dec_ref(v_k_3456_);
lean_dec_ref(v_F_3454_);
lean_dec_ref(v_x_3453_);
return v___x_3512_;
}
}
}
else
{
lean_object* v_a_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3571_; 
lean_dec_ref(v_args_3494_);
lean_dec(v_a_3490_);
lean_dec_ref(v_k_3456_);
lean_dec_ref(v_F_3454_);
lean_dec_ref(v_x_3453_);
v_a_3564_ = lean_ctor_get(v___x_3501_, 0);
v_isSharedCheck_3571_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3571_ == 0)
{
v___x_3566_ = v___x_3501_;
v_isShared_3567_ = v_isSharedCheck_3571_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_a_3564_);
lean_dec(v___x_3501_);
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
else
{
lean_object* v_a_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3579_; 
lean_dec(v___x_3469_);
lean_dec_ref(v_k_3456_);
lean_dec_ref(v_val_3455_);
lean_dec_ref(v_F_3454_);
lean_dec_ref(v_x_3453_);
v_a_3572_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3579_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3574_ = v___x_3489_;
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_a_3572_);
lean_dec(v___x_3489_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3577_; 
if (v_isShared_3575_ == 0)
{
v___x_3577_ = v___x_3574_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v_a_3572_);
v___x_3577_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
return v___x_3577_;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1(lean_object* v___x_3584_, lean_object* v_body_3585_, lean_object* v_k_3586_, lean_object* v___x_3587_, uint8_t v___x_3588_, uint8_t v___x_3589_, lean_object* v_FNew_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_){
_start:
{
lean_object* v___x_3598_; 
lean_inc_ref(v_FNew_3590_);
lean_inc_ref(v___x_3584_);
v___x_3598_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v___x_3584_, v_FNew_3590_, v_body_3585_, v_k_3586_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_object* v_a_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; uint8_t v___x_3603_; lean_object* v___x_3604_; 
v_a_3599_ = lean_ctor_get(v___x_3598_, 0);
lean_inc(v_a_3599_);
lean_dec_ref_known(v___x_3598_, 1);
v___x_3600_ = lean_mk_empty_array_with_capacity(v___x_3587_);
v___x_3601_ = lean_array_push(v___x_3600_, v___x_3584_);
v___x_3602_ = lean_array_push(v___x_3601_, v_FNew_3590_);
v___x_3603_ = 1;
v___x_3604_ = l_Lean_Meta_mkLambdaFVars(v___x_3602_, v_a_3599_, v___x_3588_, v___x_3589_, v___x_3588_, v___x_3589_, v___x_3603_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_);
lean_dec_ref(v___x_3602_);
return v___x_3604_;
}
else
{
lean_dec_ref(v_FNew_3590_);
lean_dec_ref(v___x_3584_);
return v___x_3598_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1___boxed(lean_object* v___x_3605_, lean_object* v_body_3606_, lean_object* v_k_3607_, lean_object* v___x_3608_, lean_object* v___x_3609_, lean_object* v___x_3610_, lean_object* v_FNew_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_){
_start:
{
uint8_t v___x_6490__boxed_3619_; uint8_t v___x_6491__boxed_3620_; lean_object* v_res_3621_; 
v___x_6490__boxed_3619_ = lean_unbox(v___x_3609_);
v___x_6491__boxed_3620_ = lean_unbox(v___x_3610_);
v_res_3621_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1(v___x_3605_, v_body_3606_, v_k_3607_, v___x_3608_, v___x_6490__boxed_3619_, v___x_6491__boxed_3620_, v_FNew_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
lean_dec(v___y_3617_);
lean_dec_ref(v___y_3616_);
lean_dec(v___y_3615_);
lean_dec_ref(v___y_3614_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec(v___x_3608_);
return v_res_3621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2(lean_object* v___x_3622_, lean_object* v___x_3623_, lean_object* v_00_u03b1_3624_, lean_object* v_00_u03b2_3625_, lean_object* v___x_3626_, lean_object* v_ctorName_3627_, lean_object* v_k_3628_, lean_object* v___x_3629_, uint8_t v___x_3630_, uint8_t v___x_3631_, lean_object* v_a_3632_, lean_object* v_x_3633_, lean_object* v_xs_3634_, lean_object* v_body_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_){
_start:
{
lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; 
v___x_3643_ = lean_array_get_borrowed(v___x_3622_, v_xs_3634_, v___x_3623_);
v___x_3644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3644_, 0, v_00_u03b1_3624_);
v___x_3645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3645_, 0, v_00_u03b2_3625_);
lean_inc(v___x_3643_);
v___x_3646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3646_, 0, v___x_3643_);
v___x_3647_ = lean_mk_empty_array_with_capacity(v___x_3626_);
v___x_3648_ = lean_array_push(v___x_3647_, v___x_3644_);
v___x_3649_ = lean_array_push(v___x_3648_, v___x_3645_);
v___x_3650_ = lean_array_push(v___x_3649_, v___x_3646_);
v___x_3651_ = l_Lean_Meta_mkAppOptM(v_ctorName_3627_, v___x_3650_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_);
if (lean_obj_tag(v___x_3651_) == 0)
{
lean_object* v_a_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___f_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; 
v_a_3652_ = lean_ctor_get(v___x_3651_, 0);
lean_inc(v_a_3652_);
lean_dec_ref_known(v___x_3651_, 1);
v___x_3653_ = lean_box(v___x_3630_);
v___x_3654_ = lean_box(v___x_3631_);
lean_inc(v___x_3643_);
v___f_3655_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1___boxed), 14, 6);
lean_closure_set(v___f_3655_, 0, v___x_3643_);
lean_closure_set(v___f_3655_, 1, v_body_3635_);
lean_closure_set(v___f_3655_, 2, v_k_3628_);
lean_closure_set(v___f_3655_, 3, v___x_3629_);
lean_closure_set(v___f_3655_, 4, v___x_3653_);
lean_closure_set(v___f_3655_, 5, v___x_3654_);
v___x_3656_ = l_Lean_LocalDecl_type(v_a_3632_);
v___x_3657_ = l_Lean_Expr_replaceFVar(v___x_3656_, v_x_3633_, v_a_3652_);
lean_dec(v_a_3652_);
lean_dec_ref(v___x_3656_);
v___x_3658_ = l_Lean_LocalDecl_userName(v_a_3632_);
v___x_3659_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v___x_3658_, v___x_3657_, v___f_3655_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_);
return v___x_3659_;
}
else
{
lean_dec_ref(v_body_3635_);
lean_dec_ref(v_x_3633_);
lean_dec(v___x_3629_);
lean_dec_ref(v_k_3628_);
return v___x_3651_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2___boxed(lean_object** _args){
lean_object* v___x_3660_ = _args[0];
lean_object* v___x_3661_ = _args[1];
lean_object* v_00_u03b1_3662_ = _args[2];
lean_object* v_00_u03b2_3663_ = _args[3];
lean_object* v___x_3664_ = _args[4];
lean_object* v_ctorName_3665_ = _args[5];
lean_object* v_k_3666_ = _args[6];
lean_object* v___x_3667_ = _args[7];
lean_object* v___x_3668_ = _args[8];
lean_object* v___x_3669_ = _args[9];
lean_object* v_a_3670_ = _args[10];
lean_object* v_x_3671_ = _args[11];
lean_object* v_xs_3672_ = _args[12];
lean_object* v_body_3673_ = _args[13];
lean_object* v___y_3674_ = _args[14];
lean_object* v___y_3675_ = _args[15];
lean_object* v___y_3676_ = _args[16];
lean_object* v___y_3677_ = _args[17];
lean_object* v___y_3678_ = _args[18];
lean_object* v___y_3679_ = _args[19];
lean_object* v___y_3680_ = _args[20];
_start:
{
uint8_t v___x_6511__boxed_3681_; uint8_t v___x_6512__boxed_3682_; lean_object* v_res_3683_; 
v___x_6511__boxed_3681_ = lean_unbox(v___x_3668_);
v___x_6512__boxed_3682_ = lean_unbox(v___x_3669_);
v_res_3683_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2(v___x_3660_, v___x_3661_, v_00_u03b1_3662_, v_00_u03b2_3663_, v___x_3664_, v_ctorName_3665_, v_k_3666_, v___x_3667_, v___x_6511__boxed_3681_, v___x_6512__boxed_3682_, v_a_3670_, v_x_3671_, v_xs_3672_, v_body_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_);
lean_dec(v___y_3679_);
lean_dec_ref(v___y_3678_);
lean_dec(v___y_3677_);
lean_dec_ref(v___y_3676_);
lean_dec(v___y_3675_);
lean_dec_ref(v___y_3674_);
lean_dec_ref(v_xs_3672_);
lean_dec_ref(v_a_3670_);
lean_dec(v___x_3664_);
lean_dec(v___x_3661_);
lean_dec_ref(v___x_3660_);
return v_res_3683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(lean_object* v___x_3684_, lean_object* v___x_3685_, lean_object* v_00_u03b1_3686_, lean_object* v_00_u03b2_3687_, lean_object* v___x_3688_, lean_object* v_k_3689_, lean_object* v___x_3690_, uint8_t v___x_3691_, uint8_t v___x_3692_, lean_object* v_a_3693_, lean_object* v_x_3694_, lean_object* v___x_3695_, lean_object* v_ctorName_3696_, lean_object* v_minor_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_){
_start:
{
lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___f_3707_; lean_object* v___x_3708_; 
v___x_3705_ = lean_box(v___x_3691_);
v___x_3706_ = lean_box(v___x_3692_);
v___f_3707_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2___boxed), 21, 12);
lean_closure_set(v___f_3707_, 0, v___x_3684_);
lean_closure_set(v___f_3707_, 1, v___x_3685_);
lean_closure_set(v___f_3707_, 2, v_00_u03b1_3686_);
lean_closure_set(v___f_3707_, 3, v_00_u03b2_3687_);
lean_closure_set(v___f_3707_, 4, v___x_3688_);
lean_closure_set(v___f_3707_, 5, v_ctorName_3696_);
lean_closure_set(v___f_3707_, 6, v_k_3689_);
lean_closure_set(v___f_3707_, 7, v___x_3690_);
lean_closure_set(v___f_3707_, 8, v___x_3705_);
lean_closure_set(v___f_3707_, 9, v___x_3706_);
lean_closure_set(v___f_3707_, 10, v_a_3693_);
lean_closure_set(v___f_3707_, 11, v_x_3694_);
v___x_3708_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_minor_3697_, v___x_3695_, v___f_3707_, v___x_3691_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_);
return v___x_3708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3___boxed(lean_object** _args){
lean_object* v___x_3709_ = _args[0];
lean_object* v___x_3710_ = _args[1];
lean_object* v_00_u03b1_3711_ = _args[2];
lean_object* v_00_u03b2_3712_ = _args[3];
lean_object* v___x_3713_ = _args[4];
lean_object* v_k_3714_ = _args[5];
lean_object* v___x_3715_ = _args[6];
lean_object* v___x_3716_ = _args[7];
lean_object* v___x_3717_ = _args[8];
lean_object* v_a_3718_ = _args[9];
lean_object* v_x_3719_ = _args[10];
lean_object* v___x_3720_ = _args[11];
lean_object* v_ctorName_3721_ = _args[12];
lean_object* v_minor_3722_ = _args[13];
lean_object* v___y_3723_ = _args[14];
lean_object* v___y_3724_ = _args[15];
lean_object* v___y_3725_ = _args[16];
lean_object* v___y_3726_ = _args[17];
lean_object* v___y_3727_ = _args[18];
lean_object* v___y_3728_ = _args[19];
lean_object* v___y_3729_ = _args[20];
_start:
{
uint8_t v___x_6475__boxed_3730_; uint8_t v___x_6476__boxed_3731_; lean_object* v_res_3732_; 
v___x_6475__boxed_3730_ = lean_unbox(v___x_3716_);
v___x_6476__boxed_3731_ = lean_unbox(v___x_3717_);
v_res_3732_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3709_, v___x_3710_, v_00_u03b1_3711_, v_00_u03b2_3712_, v___x_3713_, v_k_3714_, v___x_3715_, v___x_6475__boxed_3730_, v___x_6476__boxed_3731_, v_a_3718_, v_x_3719_, v___x_3720_, v_ctorName_3721_, v_minor_3722_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_);
lean_dec(v___y_3728_);
lean_dec_ref(v___y_3727_);
lean_dec(v___y_3726_);
lean_dec_ref(v___y_3725_);
lean_dec(v___y_3724_);
lean_dec_ref(v___y_3723_);
return v_res_3732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___boxed(lean_object* v_x_3733_, lean_object* v_F_3734_, lean_object* v_val_3735_, lean_object* v_k_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_){
_start:
{
lean_object* v_res_3744_; 
v_res_3744_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v_x_3733_, v_F_3734_, v_val_3735_, v_k_3736_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_, v_a_3741_, v_a_3742_);
lean_dec(v_a_3742_);
lean_dec_ref(v_a_3741_);
lean_dec(v_a_3740_);
lean_dec_ref(v_a_3739_);
lean_dec(v_a_3738_);
lean_dec_ref(v_a_3737_);
return v_res_3744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1(lean_object* v_00_u03b1_3745_, lean_object* v_name_3746_, uint8_t v_bi_3747_, lean_object* v_type_3748_, lean_object* v_k_3749_, uint8_t v_kind_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_){
_start:
{
lean_object* v___x_3758_; 
v___x_3758_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(v_name_3746_, v_bi_3747_, v_type_3748_, v_k_3749_, v_kind_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
return v___x_3758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___boxed(lean_object* v_00_u03b1_3759_, lean_object* v_name_3760_, lean_object* v_bi_3761_, lean_object* v_type_3762_, lean_object* v_k_3763_, lean_object* v_kind_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_){
_start:
{
uint8_t v_bi_boxed_3772_; uint8_t v_kind_boxed_3773_; lean_object* v_res_3774_; 
v_bi_boxed_3772_ = lean_unbox(v_bi_3761_);
v_kind_boxed_3773_ = lean_unbox(v_kind_3764_);
v_res_3774_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1(v_00_u03b1_3759_, v_name_3760_, v_bi_boxed_3772_, v_type_3762_, v_k_3763_, v_kind_boxed_3773_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_);
lean_dec(v___y_3770_);
lean_dec_ref(v___y_3769_);
lean_dec(v___y_3768_);
lean_dec_ref(v___y_3767_);
lean_dec(v___y_3766_);
lean_dec_ref(v___y_3765_);
return v_res_3774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1(lean_object* v_00_u03b1_3775_, lean_object* v_name_3776_, lean_object* v_type_3777_, lean_object* v_k_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_){
_start:
{
lean_object* v___x_3786_; 
v___x_3786_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_name_3776_, v_type_3777_, v_k_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_);
return v___x_3786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___boxed(lean_object* v_00_u03b1_3787_, lean_object* v_name_3788_, lean_object* v_type_3789_, lean_object* v_k_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_){
_start:
{
lean_object* v_res_3798_; 
v_res_3798_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1(v_00_u03b1_3787_, v_name_3788_, v_type_3789_, v_k_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_);
lean_dec(v___y_3796_);
lean_dec_ref(v___y_3795_);
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3793_);
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3791_);
return v_res_3798_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3799_; 
v___x_3799_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return v___x_3799_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(lean_object* v_msg_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_){
_start:
{
lean_object* v___x_3808_; lean_object* v___x_3331__overap_3809_; lean_object* v___x_3810_; 
v___x_3808_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0, &l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0);
v___x_3331__overap_3809_ = lean_panic_fn_borrowed(v___x_3808_, v_msg_3800_);
lean_inc(v___y_3806_);
lean_inc_ref(v___y_3805_);
lean_inc(v___y_3804_);
lean_inc_ref(v___y_3803_);
lean_inc(v___y_3802_);
lean_inc_ref(v___y_3801_);
v___x_3810_ = lean_apply_7(v___x_3331__overap_3809_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, lean_box(0));
return v___x_3810_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___boxed(lean_object* v_msg_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_){
_start:
{
lean_object* v_res_3819_; 
v_res_3819_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(v_msg_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_);
lean_dec(v___y_3817_);
lean_dec_ref(v___y_3816_);
lean_dec(v___y_3815_);
lean_dec_ref(v___y_3814_);
lean_dec(v___y_3813_);
lean_dec_ref(v___y_3812_);
return v_res_3819_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3(void){
_start:
{
lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; 
v___x_3823_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__2));
v___x_3824_ = lean_unsigned_to_nat(49u);
v___x_3825_ = lean_unsigned_to_nat(186u);
v___x_3826_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__1));
v___x_3827_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__0));
v___x_3828_ = l_mkPanicMessageWithDecl(v___x_3827_, v___x_3826_, v___x_3825_, v___x_3824_, v___x_3823_);
return v___x_3828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1___boxed(lean_object* v___x_3834_, lean_object* v_a_3835_, lean_object* v_k_3836_, lean_object* v___x_3837_, lean_object* v___x_3838_, lean_object* v___x_3839_, lean_object* v___x_3840_, lean_object* v___x_3841_, lean_object* v_FNew_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_){
_start:
{
uint8_t v___x_3499__boxed_3850_; uint8_t v___x_3500__boxed_3851_; uint8_t v___x_3501__boxed_3852_; lean_object* v_res_3853_; 
v___x_3499__boxed_3850_ = lean_unbox(v___x_3839_);
v___x_3500__boxed_3851_ = lean_unbox(v___x_3840_);
v___x_3501__boxed_3852_ = lean_unbox(v___x_3841_);
v_res_3853_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1(v___x_3834_, v_a_3835_, v_k_3836_, v___x_3837_, v___x_3838_, v___x_3499__boxed_3850_, v___x_3500__boxed_3851_, v___x_3501__boxed_3852_, v_FNew_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
lean_dec(v___y_3848_);
lean_dec_ref(v___y_3847_);
lean_dec(v___y_3846_);
lean_dec_ref(v___y_3845_);
lean_dec(v___y_3844_);
lean_dec_ref(v___y_3843_);
lean_dec(v___x_3837_);
return v_res_3853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0(lean_object* v___x_3854_, lean_object* v___x_3855_, lean_object* v___x_3856_, lean_object* v___x_3857_, uint8_t v___x_3858_, uint8_t v___x_3859_, lean_object* v_00_u03b1_3860_, lean_object* v_00_u03b2_3861_, lean_object* v___x_3862_, lean_object* v_k_3863_, lean_object* v___x_3864_, lean_object* v_a_3865_, lean_object* v_x_3866_, lean_object* v_xs_3867_, lean_object* v_body_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_){
_start:
{
lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; uint8_t v___x_3881_; lean_object* v___x_3882_; 
v___x_3876_ = lean_array_get(v___x_3854_, v_xs_3867_, v___x_3855_);
v___x_3877_ = lean_array_get(v___x_3854_, v_xs_3867_, v___x_3856_);
v___x_3878_ = lean_array_get_size(v_xs_3867_);
v___x_3879_ = l_Array_toSubarray___redArg(v_xs_3867_, v___x_3857_, v___x_3878_);
v___x_3880_ = l_Subarray_copy___redArg(v___x_3879_);
v___x_3881_ = 1;
v___x_3882_ = l_Lean_Meta_mkLambdaFVars(v___x_3880_, v_body_3868_, v___x_3858_, v___x_3859_, v___x_3858_, v___x_3859_, v___x_3881_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
lean_dec_ref(v___x_3880_);
if (lean_obj_tag(v___x_3882_) == 0)
{
lean_object* v_a_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3909_; 
v_a_3883_ = lean_ctor_get(v___x_3882_, 0);
v_isSharedCheck_3909_ = !lean_is_exclusive(v___x_3882_);
if (v_isSharedCheck_3909_ == 0)
{
v___x_3885_ = v___x_3882_;
v_isShared_3886_ = v_isSharedCheck_3909_;
goto v_resetjp_3884_;
}
else
{
lean_inc(v_a_3883_);
lean_dec(v___x_3882_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3909_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v___x_3887_; lean_object* v___x_3889_; 
v___x_3887_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__2));
if (v_isShared_3886_ == 0)
{
lean_ctor_set_tag(v___x_3885_, 1);
lean_ctor_set(v___x_3885_, 0, v_00_u03b1_3860_);
v___x_3889_ = v___x_3885_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v_00_u03b1_3860_);
v___x_3889_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; 
v___x_3890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3890_, 0, v_00_u03b2_3861_);
lean_inc(v___x_3876_);
v___x_3891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3876_);
lean_inc(v___x_3877_);
v___x_3892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3892_, 0, v___x_3877_);
v___x_3893_ = lean_mk_empty_array_with_capacity(v___x_3862_);
v___x_3894_ = lean_array_push(v___x_3893_, v___x_3889_);
v___x_3895_ = lean_array_push(v___x_3894_, v___x_3890_);
v___x_3896_ = lean_array_push(v___x_3895_, v___x_3891_);
v___x_3897_ = lean_array_push(v___x_3896_, v___x_3892_);
v___x_3898_ = l_Lean_Meta_mkAppOptM(v___x_3887_, v___x_3897_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
if (lean_obj_tag(v___x_3898_) == 0)
{
lean_object* v_a_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___f_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; 
v_a_3899_ = lean_ctor_get(v___x_3898_, 0);
lean_inc(v_a_3899_);
lean_dec_ref_known(v___x_3898_, 1);
v___x_3900_ = lean_box(v___x_3858_);
v___x_3901_ = lean_box(v___x_3859_);
v___x_3902_ = lean_box(v___x_3881_);
v___f_3903_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1___boxed), 16, 8);
lean_closure_set(v___f_3903_, 0, v___x_3877_);
lean_closure_set(v___f_3903_, 1, v_a_3883_);
lean_closure_set(v___f_3903_, 2, v_k_3863_);
lean_closure_set(v___f_3903_, 3, v___x_3864_);
lean_closure_set(v___f_3903_, 4, v___x_3876_);
lean_closure_set(v___f_3903_, 5, v___x_3900_);
lean_closure_set(v___f_3903_, 6, v___x_3901_);
lean_closure_set(v___f_3903_, 7, v___x_3902_);
v___x_3904_ = l_Lean_LocalDecl_type(v_a_3865_);
v___x_3905_ = l_Lean_Expr_replaceFVar(v___x_3904_, v_x_3866_, v_a_3899_);
lean_dec(v_a_3899_);
lean_dec_ref(v___x_3904_);
v___x_3906_ = l_Lean_LocalDecl_userName(v_a_3865_);
v___x_3907_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v___x_3906_, v___x_3905_, v___f_3903_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
return v___x_3907_;
}
else
{
lean_dec(v_a_3883_);
lean_dec(v___x_3877_);
lean_dec(v___x_3876_);
lean_dec_ref(v_x_3866_);
lean_dec(v___x_3864_);
lean_dec_ref(v_k_3863_);
return v___x_3898_;
}
}
}
}
else
{
lean_dec(v___x_3877_);
lean_dec(v___x_3876_);
lean_dec_ref(v_x_3866_);
lean_dec(v___x_3864_);
lean_dec_ref(v_k_3863_);
lean_dec_ref(v_00_u03b2_3861_);
lean_dec_ref(v_00_u03b1_3860_);
return v___x_3882_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___boxed(lean_object** _args){
lean_object* v___x_3910_ = _args[0];
lean_object* v___x_3911_ = _args[1];
lean_object* v___x_3912_ = _args[2];
lean_object* v___x_3913_ = _args[3];
lean_object* v___x_3914_ = _args[4];
lean_object* v___x_3915_ = _args[5];
lean_object* v_00_u03b1_3916_ = _args[6];
lean_object* v_00_u03b2_3917_ = _args[7];
lean_object* v___x_3918_ = _args[8];
lean_object* v_k_3919_ = _args[9];
lean_object* v___x_3920_ = _args[10];
lean_object* v_a_3921_ = _args[11];
lean_object* v_x_3922_ = _args[12];
lean_object* v_xs_3923_ = _args[13];
lean_object* v_body_3924_ = _args[14];
lean_object* v___y_3925_ = _args[15];
lean_object* v___y_3926_ = _args[16];
lean_object* v___y_3927_ = _args[17];
lean_object* v___y_3928_ = _args[18];
lean_object* v___y_3929_ = _args[19];
lean_object* v___y_3930_ = _args[20];
lean_object* v___y_3931_ = _args[21];
_start:
{
uint8_t v___x_3526__boxed_3932_; uint8_t v___x_3527__boxed_3933_; lean_object* v_res_3934_; 
v___x_3526__boxed_3932_ = lean_unbox(v___x_3914_);
v___x_3527__boxed_3933_ = lean_unbox(v___x_3915_);
v_res_3934_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0(v___x_3910_, v___x_3911_, v___x_3912_, v___x_3913_, v___x_3526__boxed_3932_, v___x_3527__boxed_3933_, v_00_u03b1_3916_, v_00_u03b2_3917_, v___x_3918_, v_k_3919_, v___x_3920_, v_a_3921_, v_x_3922_, v_xs_3923_, v_body_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_);
lean_dec(v___y_3930_);
lean_dec_ref(v___y_3929_);
lean_dec(v___y_3928_);
lean_dec_ref(v___y_3927_);
lean_dec(v___y_3926_);
lean_dec_ref(v___y_3925_);
lean_dec_ref(v_a_3921_);
lean_dec(v___x_3918_);
lean_dec(v___x_3912_);
lean_dec(v___x_3911_);
lean_dec_ref(v___x_3910_);
return v_res_3934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(lean_object* v_x_3938_, lean_object* v_F_3939_, lean_object* v_val_3940_, lean_object* v_k_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_){
_start:
{
lean_object* v___y_3950_; lean_object* v___y_3951_; lean_object* v___y_3952_; lean_object* v___y_3953_; lean_object* v___y_3954_; lean_object* v___y_3955_; lean_object* v___x_3958_; uint8_t v___y_3960_; uint8_t v___x_4051_; 
v___x_3958_ = l_Lean_instInhabitedExpr;
v___x_4051_ = l_Lean_Expr_isFVar(v_x_3938_);
if (v___x_4051_ == 0)
{
v___y_3960_ = v___x_4051_;
goto v___jp_3959_;
}
else
{
lean_object* v___x_4052_; lean_object* v___x_4053_; uint8_t v___x_4054_; 
v___x_4052_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4));
v___x_4053_ = lean_unsigned_to_nat(5u);
v___x_4054_ = l_Lean_Expr_isAppOfArity(v_val_3940_, v___x_4052_, v___x_4053_);
v___y_3960_ = v___x_4054_;
goto v___jp_3959_;
}
v___jp_3949_:
{
lean_object* v___x_3956_; lean_object* v___x_3957_; 
v___x_3956_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3);
v___x_3957_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(v___x_3956_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
return v___x_3957_;
}
v___jp_3959_:
{
if (v___y_3960_ == 0)
{
lean_object* v___x_3961_; 
lean_dec_ref(v_x_3938_);
lean_inc(v_a_3947_);
lean_inc_ref(v_a_3946_);
lean_inc(v_a_3945_);
lean_inc_ref(v_a_3944_);
lean_inc(v_a_3943_);
lean_inc_ref(v_a_3942_);
v___x_3961_ = lean_apply_9(v_k_3941_, v_F_3939_, v_val_3940_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, lean_box(0));
return v___x_3961_;
}
else
{
lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; uint8_t v___x_3968_; 
v___x_3962_ = lean_unsigned_to_nat(3u);
v___x_3963_ = l_Lean_Expr_getAppNumArgs(v_val_3940_);
v___x_3964_ = lean_nat_sub(v___x_3963_, v___x_3962_);
v___x_3965_ = lean_unsigned_to_nat(1u);
v___x_3966_ = lean_nat_sub(v___x_3964_, v___x_3965_);
lean_dec(v___x_3964_);
v___x_3967_ = l_Lean_Expr_getRevArg_x21(v_val_3940_, v___x_3966_);
v___x_3968_ = lean_expr_eqv(v___x_3967_, v_x_3938_);
lean_dec_ref(v___x_3967_);
if (v___x_3968_ == 0)
{
lean_object* v___x_3969_; 
lean_dec(v___x_3963_);
lean_dec_ref(v_x_3938_);
lean_inc(v_a_3947_);
lean_inc_ref(v_a_3946_);
lean_inc(v_a_3945_);
lean_inc_ref(v_a_3944_);
lean_inc(v_a_3943_);
lean_inc_ref(v_a_3942_);
v___x_3969_ = lean_apply_9(v_k_3941_, v_F_3939_, v_val_3940_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, lean_box(0));
return v___x_3969_;
}
else
{
lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; uint8_t v___x_3974_; 
v___x_3970_ = lean_unsigned_to_nat(4u);
v___x_3971_ = lean_nat_sub(v___x_3963_, v___x_3970_);
v___x_3972_ = lean_nat_sub(v___x_3971_, v___x_3965_);
lean_dec(v___x_3971_);
v___x_3973_ = l_Lean_Expr_getRevArg_x21(v_val_3940_, v___x_3972_);
v___x_3974_ = l_Lean_Expr_isLambda(v___x_3973_);
if (v___x_3974_ == 0)
{
lean_object* v___x_3975_; 
lean_dec_ref(v___x_3973_);
lean_dec(v___x_3963_);
lean_dec_ref(v_x_3938_);
lean_inc(v_a_3947_);
lean_inc_ref(v_a_3946_);
lean_inc(v_a_3945_);
lean_inc_ref(v_a_3944_);
lean_inc(v_a_3943_);
lean_inc_ref(v_a_3942_);
v___x_3975_ = lean_apply_9(v_k_3941_, v_F_3939_, v_val_3940_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, lean_box(0));
return v___x_3975_;
}
else
{
lean_object* v___x_3976_; uint8_t v___x_3977_; 
v___x_3976_ = l_Lean_Expr_bindingBody_x21(v___x_3973_);
lean_dec_ref(v___x_3973_);
v___x_3977_ = l_Lean_Expr_isLambda(v___x_3976_);
lean_dec_ref(v___x_3976_);
if (v___x_3977_ == 0)
{
lean_object* v___x_3978_; 
lean_dec(v___x_3963_);
lean_dec_ref(v_x_3938_);
lean_inc(v_a_3947_);
lean_inc_ref(v_a_3946_);
lean_inc(v_a_3945_);
lean_inc_ref(v_a_3944_);
lean_inc(v_a_3943_);
lean_inc_ref(v_a_3942_);
v___x_3978_ = lean_apply_9(v_k_3941_, v_F_3939_, v_val_3940_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, lean_box(0));
return v___x_3978_;
}
else
{
lean_object* v___x_3979_; lean_object* v___x_3980_; 
v___x_3979_ = l_Lean_Expr_getAppFn(v_val_3940_);
v___x_3980_ = l_Lean_Expr_constLevels_x21(v___x_3979_);
lean_dec_ref(v___x_3979_);
if (lean_obj_tag(v___x_3980_) == 1)
{
lean_object* v_tail_3981_; 
v_tail_3981_ = lean_ctor_get(v___x_3980_, 1);
lean_inc(v_tail_3981_);
lean_dec_ref_known(v___x_3980_, 2);
if (lean_obj_tag(v_tail_3981_) == 1)
{
lean_object* v_tail_3982_; 
v_tail_3982_ = lean_ctor_get(v_tail_3981_, 1);
lean_inc(v_tail_3982_);
if (lean_obj_tag(v_tail_3982_) == 1)
{
lean_object* v_tail_3983_; lean_object* v___x_3985_; uint8_t v_isShared_3986_; uint8_t v_isSharedCheck_4049_; 
v_tail_3983_ = lean_ctor_get(v_tail_3982_, 1);
v_isSharedCheck_4049_ = !lean_is_exclusive(v_tail_3982_);
if (v_isSharedCheck_4049_ == 0)
{
lean_object* v_unused_4050_; 
v_unused_4050_ = lean_ctor_get(v_tail_3982_, 0);
lean_dec(v_unused_4050_);
v___x_3985_ = v_tail_3982_;
v_isShared_3986_ = v_isSharedCheck_4049_;
goto v_resetjp_3984_;
}
else
{
lean_inc(v_tail_3983_);
lean_dec(v_tail_3982_);
v___x_3985_ = lean_box(0);
v_isShared_3986_ = v_isSharedCheck_4049_;
goto v_resetjp_3984_;
}
v_resetjp_3984_:
{
if (lean_obj_tag(v_tail_3983_) == 0)
{
lean_object* v___x_3987_; lean_object* v___x_3988_; 
v___x_3987_ = l_Lean_Expr_fvarId_x21(v_F_3939_);
v___x_3988_ = l_Lean_FVarId_getDecl___redArg(v___x_3987_, v_a_3944_, v_a_3946_, v_a_3947_);
if (lean_obj_tag(v___x_3988_) == 0)
{
lean_object* v_a_3989_; lean_object* v_dummy_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v_args_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___f_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; uint8_t v___x_3999_; lean_object* v___x_4000_; 
v_a_3989_ = lean_ctor_get(v___x_3988_, 0);
lean_inc_n(v_a_3989_, 2);
lean_dec_ref_known(v___x_3988_, 1);
v_dummy_3990_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_3963_);
v___x_3991_ = lean_mk_array(v___x_3963_, v_dummy_3990_);
v___x_3992_ = lean_nat_sub(v___x_3963_, v___x_3965_);
lean_dec(v___x_3963_);
v_args_3993_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_3940_, v___x_3991_, v___x_3992_);
v___x_3994_ = lean_unsigned_to_nat(0u);
v___x_3995_ = lean_box(v___x_3974_);
lean_inc_ref(v_x_3938_);
v___f_3996_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed), 14, 5);
lean_closure_set(v___f_3996_, 0, v_a_3989_);
lean_closure_set(v___f_3996_, 1, v___x_3958_);
lean_closure_set(v___f_3996_, 2, v___x_3994_);
lean_closure_set(v___f_3996_, 3, v_x_3938_);
lean_closure_set(v___f_3996_, 4, v___x_3995_);
v___x_3997_ = lean_unsigned_to_nat(2u);
v___x_3998_ = lean_array_get(v___x_3958_, v_args_3993_, v___x_3997_);
v___x_3999_ = 0;
v___x_4000_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_3998_, v___f_3996_, v___x_3999_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_);
if (lean_obj_tag(v___x_4000_) == 0)
{
lean_object* v_a_4001_; lean_object* v_fst_4002_; lean_object* v_snd_4003_; lean_object* v_00_u03b1_4004_; lean_object* v_00_u03b2_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___f_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; 
v_a_4001_ = lean_ctor_get(v___x_4000_, 0);
lean_inc(v_a_4001_);
lean_dec_ref_known(v___x_4000_, 1);
v_fst_4002_ = lean_ctor_get(v_a_4001_, 0);
lean_inc(v_fst_4002_);
v_snd_4003_ = lean_ctor_get(v_a_4001_, 1);
lean_inc(v_snd_4003_);
lean_dec(v_a_4001_);
v_00_u03b1_4004_ = lean_array_get(v___x_3958_, v_args_3993_, v___x_3994_);
v_00_u03b2_4005_ = lean_array_get(v___x_3958_, v_args_3993_, v___x_3965_);
v___x_4006_ = lean_box(v___x_3999_);
v___x_4007_ = lean_box(v___x_3974_);
lean_inc_ref(v_x_3938_);
lean_inc(v_00_u03b2_4005_);
lean_inc(v_00_u03b1_4004_);
v___f_4008_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___boxed), 22, 13);
lean_closure_set(v___f_4008_, 0, v___x_3958_);
lean_closure_set(v___f_4008_, 1, v___x_3994_);
lean_closure_set(v___f_4008_, 2, v___x_3965_);
lean_closure_set(v___f_4008_, 3, v___x_3997_);
lean_closure_set(v___f_4008_, 4, v___x_4006_);
lean_closure_set(v___f_4008_, 5, v___x_4007_);
lean_closure_set(v___f_4008_, 6, v_00_u03b1_4004_);
lean_closure_set(v___f_4008_, 7, v_00_u03b2_4005_);
lean_closure_set(v___f_4008_, 8, v___x_3970_);
lean_closure_set(v___f_4008_, 9, v_k_3941_);
lean_closure_set(v___f_4008_, 10, v___x_3962_);
lean_closure_set(v___f_4008_, 11, v_a_3989_);
lean_closure_set(v___f_4008_, 12, v_x_3938_);
v___x_4009_ = lean_array_get(v___x_3958_, v_args_3993_, v___x_3970_);
lean_dec_ref(v_args_3993_);
v___x_4010_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_4009_, v___f_4008_, v___x_3999_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_);
if (lean_obj_tag(v___x_4010_) == 0)
{
lean_object* v_a_4011_; lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4032_; 
v_a_4011_ = lean_ctor_get(v___x_4010_, 0);
v_isSharedCheck_4032_ = !lean_is_exclusive(v___x_4010_);
if (v_isSharedCheck_4032_ == 0)
{
v___x_4013_ = v___x_4010_;
v_isShared_4014_ = v_isSharedCheck_4032_;
goto v_resetjp_4012_;
}
else
{
lean_inc(v_a_4011_);
lean_dec(v___x_4010_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4032_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
lean_object* v___x_4015_; lean_object* v___x_4017_; 
v___x_4015_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4));
if (v_isShared_3986_ == 0)
{
lean_ctor_set(v___x_3985_, 1, v_tail_3981_);
lean_ctor_set(v___x_3985_, 0, v_snd_4003_);
v___x_4017_ = v___x_3985_;
goto v_reusejp_4016_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v_snd_4003_);
lean_ctor_set(v_reuseFailAlloc_4031_, 1, v_tail_3981_);
v___x_4017_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4016_;
}
v_reusejp_4016_:
{
lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4029_; 
v___x_4018_ = l_Lean_mkConst(v___x_4015_, v___x_4017_);
v___x_4019_ = lean_unsigned_to_nat(6u);
v___x_4020_ = lean_mk_empty_array_with_capacity(v___x_4019_);
v___x_4021_ = lean_array_push(v___x_4020_, v_00_u03b1_4004_);
v___x_4022_ = lean_array_push(v___x_4021_, v_00_u03b2_4005_);
v___x_4023_ = lean_array_push(v___x_4022_, v_fst_4002_);
v___x_4024_ = lean_array_push(v___x_4023_, v_x_3938_);
v___x_4025_ = lean_array_push(v___x_4024_, v_a_4011_);
v___x_4026_ = lean_array_push(v___x_4025_, v_F_3939_);
v___x_4027_ = l_Lean_mkAppN(v___x_4018_, v___x_4026_);
lean_dec_ref(v___x_4026_);
if (v_isShared_4014_ == 0)
{
lean_ctor_set(v___x_4013_, 0, v___x_4027_);
v___x_4029_ = v___x_4013_;
goto v_reusejp_4028_;
}
else
{
lean_object* v_reuseFailAlloc_4030_; 
v_reuseFailAlloc_4030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4030_, 0, v___x_4027_);
v___x_4029_ = v_reuseFailAlloc_4030_;
goto v_reusejp_4028_;
}
v_reusejp_4028_:
{
return v___x_4029_;
}
}
}
}
else
{
lean_dec(v_00_u03b2_4005_);
lean_dec(v_00_u03b1_4004_);
lean_dec(v_snd_4003_);
lean_dec(v_fst_4002_);
lean_del_object(v___x_3985_);
lean_dec_ref_known(v_tail_3981_, 2);
lean_dec_ref(v_F_3939_);
lean_dec_ref(v_x_3938_);
return v___x_4010_;
}
}
else
{
lean_object* v_a_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4040_; 
lean_dec_ref(v_args_3993_);
lean_dec(v_a_3989_);
lean_del_object(v___x_3985_);
lean_dec_ref_known(v_tail_3981_, 2);
lean_dec_ref(v_k_3941_);
lean_dec_ref(v_F_3939_);
lean_dec_ref(v_x_3938_);
v_a_4033_ = lean_ctor_get(v___x_4000_, 0);
v_isSharedCheck_4040_ = !lean_is_exclusive(v___x_4000_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_4035_ = v___x_4000_;
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_a_4033_);
lean_dec(v___x_4000_);
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
lean_object* v_a_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4048_; 
lean_del_object(v___x_3985_);
lean_dec_ref_known(v_tail_3981_, 2);
lean_dec(v___x_3963_);
lean_dec_ref(v_k_3941_);
lean_dec_ref(v_val_3940_);
lean_dec_ref(v_F_3939_);
lean_dec_ref(v_x_3938_);
v_a_4041_ = lean_ctor_get(v___x_3988_, 0);
v_isSharedCheck_4048_ = !lean_is_exclusive(v___x_3988_);
if (v_isSharedCheck_4048_ == 0)
{
v___x_4043_ = v___x_3988_;
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_a_4041_);
lean_dec(v___x_3988_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v___x_4046_; 
if (v_isShared_4044_ == 0)
{
v___x_4046_ = v___x_4043_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v_a_4041_);
v___x_4046_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
return v___x_4046_;
}
}
}
}
else
{
lean_del_object(v___x_3985_);
lean_dec(v_tail_3983_);
lean_dec_ref_known(v_tail_3981_, 2);
lean_dec(v___x_3963_);
lean_dec_ref(v_k_3941_);
lean_dec_ref(v_val_3940_);
lean_dec_ref(v_F_3939_);
lean_dec_ref(v_x_3938_);
v___y_3950_ = v_a_3942_;
v___y_3951_ = v_a_3943_;
v___y_3952_ = v_a_3944_;
v___y_3953_ = v_a_3945_;
v___y_3954_ = v_a_3946_;
v___y_3955_ = v_a_3947_;
goto v___jp_3949_;
}
}
}
else
{
lean_dec(v_tail_3982_);
lean_dec_ref_known(v_tail_3981_, 2);
lean_dec(v___x_3963_);
lean_dec_ref(v_k_3941_);
lean_dec_ref(v_val_3940_);
lean_dec_ref(v_F_3939_);
lean_dec_ref(v_x_3938_);
v___y_3950_ = v_a_3942_;
v___y_3951_ = v_a_3943_;
v___y_3952_ = v_a_3944_;
v___y_3953_ = v_a_3945_;
v___y_3954_ = v_a_3946_;
v___y_3955_ = v_a_3947_;
goto v___jp_3949_;
}
}
else
{
lean_dec(v_tail_3981_);
lean_dec(v___x_3963_);
lean_dec_ref(v_k_3941_);
lean_dec_ref(v_val_3940_);
lean_dec_ref(v_F_3939_);
lean_dec_ref(v_x_3938_);
v___y_3950_ = v_a_3942_;
v___y_3951_ = v_a_3943_;
v___y_3952_ = v_a_3944_;
v___y_3953_ = v_a_3945_;
v___y_3954_ = v_a_3946_;
v___y_3955_ = v_a_3947_;
goto v___jp_3949_;
}
}
else
{
lean_dec(v___x_3980_);
lean_dec(v___x_3963_);
lean_dec_ref(v_k_3941_);
lean_dec_ref(v_val_3940_);
lean_dec_ref(v_F_3939_);
lean_dec_ref(v_x_3938_);
v___y_3950_ = v_a_3942_;
v___y_3951_ = v_a_3943_;
v___y_3952_ = v_a_3944_;
v___y_3953_ = v_a_3945_;
v___y_3954_ = v_a_3946_;
v___y_3955_ = v_a_3947_;
goto v___jp_3949_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1(lean_object* v___x_4055_, lean_object* v_a_4056_, lean_object* v_k_4057_, lean_object* v___x_4058_, lean_object* v___x_4059_, uint8_t v___x_4060_, uint8_t v___x_4061_, uint8_t v___x_4062_, lean_object* v_FNew_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_){
_start:
{
lean_object* v___x_4071_; 
lean_inc_ref(v_FNew_4063_);
lean_inc_ref(v___x_4055_);
v___x_4071_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v___x_4055_, v_FNew_4063_, v_a_4056_, v_k_4057_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_);
if (lean_obj_tag(v___x_4071_) == 0)
{
lean_object* v_a_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; 
v_a_4072_ = lean_ctor_get(v___x_4071_, 0);
lean_inc(v_a_4072_);
lean_dec_ref_known(v___x_4071_, 1);
v___x_4073_ = lean_mk_empty_array_with_capacity(v___x_4058_);
v___x_4074_ = lean_array_push(v___x_4073_, v___x_4059_);
v___x_4075_ = lean_array_push(v___x_4074_, v___x_4055_);
v___x_4076_ = lean_array_push(v___x_4075_, v_FNew_4063_);
v___x_4077_ = l_Lean_Meta_mkLambdaFVars(v___x_4076_, v_a_4072_, v___x_4060_, v___x_4061_, v___x_4060_, v___x_4061_, v___x_4062_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_);
lean_dec_ref(v___x_4076_);
return v___x_4077_;
}
else
{
lean_dec_ref(v_FNew_4063_);
lean_dec_ref(v___x_4059_);
lean_dec_ref(v___x_4055_);
return v___x_4071_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___boxed(lean_object* v_x_4078_, lean_object* v_F_4079_, lean_object* v_val_4080_, lean_object* v_k_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_, lean_object* v_a_4084_, lean_object* v_a_4085_, lean_object* v_a_4086_, lean_object* v_a_4087_, lean_object* v_a_4088_){
_start:
{
lean_object* v_res_4089_; 
v_res_4089_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v_x_4078_, v_F_4079_, v_val_4080_, v_k_4081_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_, v_a_4086_, v_a_4087_);
lean_dec(v_a_4087_);
lean_dec_ref(v_a_4086_);
lean_dec(v_a_4085_);
lean_dec_ref(v_a_4084_);
lean_dec(v_a_4083_);
lean_dec_ref(v_a_4082_);
return v_res_4089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0(lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_){
_start:
{
lean_object* v___x_4103_; 
v___x_4103_ = l_Lean_Elab_WF_applyCleanWfTactic(v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_);
if (lean_obj_tag(v___x_4103_) == 0)
{
lean_object* v_ref_4104_; uint8_t v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; 
lean_dec_ref_known(v___x_4103_, 1);
v_ref_4104_ = lean_ctor_get(v___y_4100_, 2);
v___x_4105_ = 0;
v___x_4106_ = l_Lean_SourceInfo_fromRef(v_ref_4104_, v___x_4105_);
v___x_4107_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__1));
v___x_4108_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__2));
lean_inc(v___x_4106_);
v___x_4109_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4109_, 0, v___x_4106_);
lean_ctor_set(v___x_4109_, 1, v___x_4108_);
v___x_4110_ = l_Lean_Syntax_node1(v___x_4106_, v___x_4107_, v___x_4109_);
v___x_4111_ = l_Lean_Elab_Tactic_evalTactic(v___x_4110_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_);
return v___x_4111_;
}
else
{
return v___x_4103_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___boxed(lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_){
_start:
{
lean_object* v_res_4121_; 
v_res_4121_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0(v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_);
lean_dec(v___y_4119_);
lean_dec_ref(v___y_4118_);
lean_dec(v___y_4117_);
lean_dec_ref(v___y_4116_);
lean_dec(v___y_4115_);
lean_dec_ref(v___y_4114_);
lean_dec(v___y_4113_);
lean_dec_ref(v___y_4112_);
return v_res_4121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(lean_object* v_mvarId_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_){
_start:
{
lean_object* v___f_4131_; lean_object* v___x_4132_; 
v___f_4131_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___closed__0));
v___x_4132_ = l_Lean_Elab_Tactic_run(v_mvarId_4123_, v___f_4131_, v_a_4124_, v_a_4125_, v_a_4126_, v_a_4127_, v_a_4128_, v_a_4129_);
if (lean_obj_tag(v___x_4132_) == 0)
{
lean_object* v_a_4133_; lean_object* v___x_4135_; uint8_t v_isShared_4136_; uint8_t v_isSharedCheck_4143_; 
v_a_4133_ = lean_ctor_get(v___x_4132_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v___x_4132_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4135_ = v___x_4132_;
v_isShared_4136_ = v_isSharedCheck_4143_;
goto v_resetjp_4134_;
}
else
{
lean_inc(v_a_4133_);
lean_dec(v___x_4132_);
v___x_4135_ = lean_box(0);
v_isShared_4136_ = v_isSharedCheck_4143_;
goto v_resetjp_4134_;
}
v_resetjp_4134_:
{
uint8_t v___x_4137_; 
v___x_4137_ = l_List_isEmpty___redArg(v_a_4133_);
if (v___x_4137_ == 0)
{
lean_object* v___x_4138_; 
lean_del_object(v___x_4135_);
v___x_4138_ = l_Lean_Elab_Term_reportUnsolvedGoals(v_a_4133_, v_a_4126_, v_a_4127_, v_a_4128_, v_a_4129_);
return v___x_4138_;
}
else
{
lean_object* v___x_4139_; lean_object* v___x_4141_; 
lean_dec(v_a_4133_);
v___x_4139_ = lean_box(0);
if (v_isShared_4136_ == 0)
{
lean_ctor_set(v___x_4135_, 0, v___x_4139_);
v___x_4141_ = v___x_4135_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v___x_4139_);
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
else
{
lean_object* v_a_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4151_; 
v_a_4144_ = lean_ctor_get(v___x_4132_, 0);
v_isSharedCheck_4151_ = !lean_is_exclusive(v___x_4132_);
if (v_isSharedCheck_4151_ == 0)
{
v___x_4146_ = v___x_4132_;
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_a_4144_);
lean_dec(v___x_4132_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
lean_object* v___x_4149_; 
if (v_isShared_4147_ == 0)
{
v___x_4149_ = v___x_4146_;
goto v_reusejp_4148_;
}
else
{
lean_object* v_reuseFailAlloc_4150_; 
v_reuseFailAlloc_4150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4150_, 0, v_a_4144_);
v___x_4149_ = v_reuseFailAlloc_4150_;
goto v_reusejp_4148_;
}
v_reusejp_4148_:
{
return v___x_4149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___boxed(lean_object* v_mvarId_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_){
_start:
{
lean_object* v_res_4160_; 
v_res_4160_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(v_mvarId_4152_, v_a_4153_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_);
lean_dec(v_a_4158_);
lean_dec_ref(v_a_4157_);
lean_dec(v_a_4156_);
lean_dec_ref(v_a_4155_);
lean_dec(v_a_4154_);
lean_dec_ref(v_a_4153_);
return v_res_4160_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(lean_object* v_x_4161_, lean_object* v_x_4162_, lean_object* v_x_4163_, lean_object* v_x_4164_){
_start:
{
lean_object* v_ks_4165_; lean_object* v_vs_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4190_; 
v_ks_4165_ = lean_ctor_get(v_x_4161_, 0);
v_vs_4166_ = lean_ctor_get(v_x_4161_, 1);
v_isSharedCheck_4190_ = !lean_is_exclusive(v_x_4161_);
if (v_isSharedCheck_4190_ == 0)
{
v___x_4168_ = v_x_4161_;
v_isShared_4169_ = v_isSharedCheck_4190_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_vs_4166_);
lean_inc(v_ks_4165_);
lean_dec(v_x_4161_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4190_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
lean_object* v___x_4170_; uint8_t v___x_4171_; 
v___x_4170_ = lean_array_get_size(v_ks_4165_);
v___x_4171_ = lean_nat_dec_lt(v_x_4162_, v___x_4170_);
if (v___x_4171_ == 0)
{
lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4175_; 
lean_dec(v_x_4162_);
v___x_4172_ = lean_array_push(v_ks_4165_, v_x_4163_);
v___x_4173_ = lean_array_push(v_vs_4166_, v_x_4164_);
if (v_isShared_4169_ == 0)
{
lean_ctor_set(v___x_4168_, 1, v___x_4173_);
lean_ctor_set(v___x_4168_, 0, v___x_4172_);
v___x_4175_ = v___x_4168_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v___x_4172_);
lean_ctor_set(v_reuseFailAlloc_4176_, 1, v___x_4173_);
v___x_4175_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
return v___x_4175_;
}
}
else
{
lean_object* v_k_x27_4177_; uint8_t v___x_4178_; 
v_k_x27_4177_ = lean_array_fget_borrowed(v_ks_4165_, v_x_4162_);
v___x_4178_ = l_Lean_instBEqMVarId_beq(v_x_4163_, v_k_x27_4177_);
if (v___x_4178_ == 0)
{
lean_object* v___x_4180_; 
if (v_isShared_4169_ == 0)
{
v___x_4180_ = v___x_4168_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4184_; 
v_reuseFailAlloc_4184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4184_, 0, v_ks_4165_);
lean_ctor_set(v_reuseFailAlloc_4184_, 1, v_vs_4166_);
v___x_4180_ = v_reuseFailAlloc_4184_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
lean_object* v___x_4181_; lean_object* v___x_4182_; 
v___x_4181_ = lean_unsigned_to_nat(1u);
v___x_4182_ = lean_nat_add(v_x_4162_, v___x_4181_);
lean_dec(v_x_4162_);
v_x_4161_ = v___x_4180_;
v_x_4162_ = v___x_4182_;
goto _start;
}
}
else
{
lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4188_; 
v___x_4185_ = lean_array_fset(v_ks_4165_, v_x_4162_, v_x_4163_);
v___x_4186_ = lean_array_fset(v_vs_4166_, v_x_4162_, v_x_4164_);
lean_dec(v_x_4162_);
if (v_isShared_4169_ == 0)
{
lean_ctor_set(v___x_4168_, 1, v___x_4186_);
lean_ctor_set(v___x_4168_, 0, v___x_4185_);
v___x_4188_ = v___x_4168_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v___x_4185_);
lean_ctor_set(v_reuseFailAlloc_4189_, 1, v___x_4186_);
v___x_4188_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
return v___x_4188_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_4191_, lean_object* v_k_4192_, lean_object* v_v_4193_){
_start:
{
lean_object* v___x_4194_; lean_object* v___x_4195_; 
v___x_4194_ = lean_unsigned_to_nat(0u);
v___x_4195_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_n_4191_, v___x_4194_, v_k_4192_, v_v_4193_);
return v___x_4195_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4196_; 
v___x_4196_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4196_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(lean_object* v_x_4197_, size_t v_x_4198_, size_t v_x_4199_, lean_object* v_x_4200_, lean_object* v_x_4201_){
_start:
{
if (lean_obj_tag(v_x_4197_) == 0)
{
lean_object* v_es_4202_; size_t v___x_4203_; size_t v___x_4204_; lean_object* v_j_4205_; lean_object* v___x_4206_; uint8_t v___x_4207_; 
v_es_4202_ = lean_ctor_get(v_x_4197_, 0);
v___x_4203_ = ((size_t)31ULL);
v___x_4204_ = lean_usize_land(v_x_4198_, v___x_4203_);
v_j_4205_ = lean_usize_to_nat(v___x_4204_);
v___x_4206_ = lean_array_get_size(v_es_4202_);
v___x_4207_ = lean_nat_dec_lt(v_j_4205_, v___x_4206_);
if (v___x_4207_ == 0)
{
lean_dec(v_j_4205_);
lean_dec(v_x_4201_);
lean_dec(v_x_4200_);
return v_x_4197_;
}
else
{
lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4246_; 
lean_inc_ref(v_es_4202_);
v_isSharedCheck_4246_ = !lean_is_exclusive(v_x_4197_);
if (v_isSharedCheck_4246_ == 0)
{
lean_object* v_unused_4247_; 
v_unused_4247_ = lean_ctor_get(v_x_4197_, 0);
lean_dec(v_unused_4247_);
v___x_4209_ = v_x_4197_;
v_isShared_4210_ = v_isSharedCheck_4246_;
goto v_resetjp_4208_;
}
else
{
lean_dec(v_x_4197_);
v___x_4209_ = lean_box(0);
v_isShared_4210_ = v_isSharedCheck_4246_;
goto v_resetjp_4208_;
}
v_resetjp_4208_:
{
lean_object* v_v_4211_; lean_object* v___x_4212_; lean_object* v_xs_x27_4213_; lean_object* v___y_4215_; 
v_v_4211_ = lean_array_fget(v_es_4202_, v_j_4205_);
v___x_4212_ = lean_box(0);
v_xs_x27_4213_ = lean_array_fset(v_es_4202_, v_j_4205_, v___x_4212_);
switch(lean_obj_tag(v_v_4211_))
{
case 0:
{
lean_object* v_key_4220_; lean_object* v_val_4221_; lean_object* v___x_4223_; uint8_t v_isShared_4224_; uint8_t v_isSharedCheck_4231_; 
v_key_4220_ = lean_ctor_get(v_v_4211_, 0);
v_val_4221_ = lean_ctor_get(v_v_4211_, 1);
v_isSharedCheck_4231_ = !lean_is_exclusive(v_v_4211_);
if (v_isSharedCheck_4231_ == 0)
{
v___x_4223_ = v_v_4211_;
v_isShared_4224_ = v_isSharedCheck_4231_;
goto v_resetjp_4222_;
}
else
{
lean_inc(v_val_4221_);
lean_inc(v_key_4220_);
lean_dec(v_v_4211_);
v___x_4223_ = lean_box(0);
v_isShared_4224_ = v_isSharedCheck_4231_;
goto v_resetjp_4222_;
}
v_resetjp_4222_:
{
uint8_t v___x_4225_; 
v___x_4225_ = l_Lean_instBEqMVarId_beq(v_x_4200_, v_key_4220_);
if (v___x_4225_ == 0)
{
lean_object* v___x_4226_; lean_object* v___x_4227_; 
lean_del_object(v___x_4223_);
v___x_4226_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4220_, v_val_4221_, v_x_4200_, v_x_4201_);
v___x_4227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4227_, 0, v___x_4226_);
v___y_4215_ = v___x_4227_;
goto v___jp_4214_;
}
else
{
lean_object* v___x_4229_; 
lean_dec(v_val_4221_);
lean_dec(v_key_4220_);
if (v_isShared_4224_ == 0)
{
lean_ctor_set(v___x_4223_, 1, v_x_4201_);
lean_ctor_set(v___x_4223_, 0, v_x_4200_);
v___x_4229_ = v___x_4223_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v_x_4200_);
lean_ctor_set(v_reuseFailAlloc_4230_, 1, v_x_4201_);
v___x_4229_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
v___y_4215_ = v___x_4229_;
goto v___jp_4214_;
}
}
}
}
case 1:
{
lean_object* v_node_4232_; lean_object* v___x_4234_; uint8_t v_isShared_4235_; uint8_t v_isSharedCheck_4244_; 
v_node_4232_ = lean_ctor_get(v_v_4211_, 0);
v_isSharedCheck_4244_ = !lean_is_exclusive(v_v_4211_);
if (v_isSharedCheck_4244_ == 0)
{
v___x_4234_ = v_v_4211_;
v_isShared_4235_ = v_isSharedCheck_4244_;
goto v_resetjp_4233_;
}
else
{
lean_inc(v_node_4232_);
lean_dec(v_v_4211_);
v___x_4234_ = lean_box(0);
v_isShared_4235_ = v_isSharedCheck_4244_;
goto v_resetjp_4233_;
}
v_resetjp_4233_:
{
size_t v___x_4236_; size_t v___x_4237_; size_t v___x_4238_; size_t v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4242_; 
v___x_4236_ = ((size_t)5ULL);
v___x_4237_ = lean_usize_shift_right(v_x_4198_, v___x_4236_);
v___x_4238_ = ((size_t)1ULL);
v___x_4239_ = lean_usize_add(v_x_4199_, v___x_4238_);
v___x_4240_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_node_4232_, v___x_4237_, v___x_4239_, v_x_4200_, v_x_4201_);
if (v_isShared_4235_ == 0)
{
lean_ctor_set(v___x_4234_, 0, v___x_4240_);
v___x_4242_ = v___x_4234_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4243_; 
v_reuseFailAlloc_4243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4243_, 0, v___x_4240_);
v___x_4242_ = v_reuseFailAlloc_4243_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
v___y_4215_ = v___x_4242_;
goto v___jp_4214_;
}
}
}
default: 
{
lean_object* v___x_4245_; 
v___x_4245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4245_, 0, v_x_4200_);
lean_ctor_set(v___x_4245_, 1, v_x_4201_);
v___y_4215_ = v___x_4245_;
goto v___jp_4214_;
}
}
v___jp_4214_:
{
lean_object* v___x_4216_; lean_object* v___x_4218_; 
v___x_4216_ = lean_array_fset(v_xs_x27_4213_, v_j_4205_, v___y_4215_);
lean_dec(v_j_4205_);
if (v_isShared_4210_ == 0)
{
lean_ctor_set(v___x_4209_, 0, v___x_4216_);
v___x_4218_ = v___x_4209_;
goto v_reusejp_4217_;
}
else
{
lean_object* v_reuseFailAlloc_4219_; 
v_reuseFailAlloc_4219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4219_, 0, v___x_4216_);
v___x_4218_ = v_reuseFailAlloc_4219_;
goto v_reusejp_4217_;
}
v_reusejp_4217_:
{
return v___x_4218_;
}
}
}
}
}
else
{
lean_object* v_ks_4248_; lean_object* v_vs_4249_; lean_object* v___x_4251_; uint8_t v_isShared_4252_; uint8_t v_isSharedCheck_4267_; 
v_ks_4248_ = lean_ctor_get(v_x_4197_, 0);
v_vs_4249_ = lean_ctor_get(v_x_4197_, 1);
v_isSharedCheck_4267_ = !lean_is_exclusive(v_x_4197_);
if (v_isSharedCheck_4267_ == 0)
{
v___x_4251_ = v_x_4197_;
v_isShared_4252_ = v_isSharedCheck_4267_;
goto v_resetjp_4250_;
}
else
{
lean_inc(v_vs_4249_);
lean_inc(v_ks_4248_);
lean_dec(v_x_4197_);
v___x_4251_ = lean_box(0);
v_isShared_4252_ = v_isSharedCheck_4267_;
goto v_resetjp_4250_;
}
v_resetjp_4250_:
{
lean_object* v___x_4254_; 
if (v_isShared_4252_ == 0)
{
v___x_4254_ = v___x_4251_;
goto v_reusejp_4253_;
}
else
{
lean_object* v_reuseFailAlloc_4266_; 
v_reuseFailAlloc_4266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4266_, 0, v_ks_4248_);
lean_ctor_set(v_reuseFailAlloc_4266_, 1, v_vs_4249_);
v___x_4254_ = v_reuseFailAlloc_4266_;
goto v_reusejp_4253_;
}
v_reusejp_4253_:
{
lean_object* v_newNode_4255_; size_t v___x_4256_; uint8_t v___x_4257_; 
v_newNode_4255_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(v___x_4254_, v_x_4200_, v_x_4201_);
v___x_4256_ = ((size_t)7ULL);
v___x_4257_ = lean_usize_dec_le(v___x_4256_, v_x_4199_);
if (v___x_4257_ == 0)
{
lean_object* v___x_4258_; lean_object* v___x_4259_; uint8_t v___x_4260_; 
v___x_4258_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4255_);
v___x_4259_ = lean_unsigned_to_nat(4u);
v___x_4260_ = lean_nat_dec_lt(v___x_4258_, v___x_4259_);
lean_dec(v___x_4258_);
if (v___x_4260_ == 0)
{
lean_object* v_ks_4261_; lean_object* v_vs_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; 
v_ks_4261_ = lean_ctor_get(v_newNode_4255_, 0);
lean_inc_ref(v_ks_4261_);
v_vs_4262_ = lean_ctor_get(v_newNode_4255_, 1);
lean_inc_ref(v_vs_4262_);
lean_dec_ref(v_newNode_4255_);
v___x_4263_ = lean_unsigned_to_nat(0u);
v___x_4264_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_4265_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_x_4199_, v_ks_4261_, v_vs_4262_, v___x_4263_, v___x_4264_);
lean_dec_ref(v_vs_4262_);
lean_dec_ref(v_ks_4261_);
return v___x_4265_;
}
else
{
return v_newNode_4255_;
}
}
else
{
return v_newNode_4255_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_4268_, lean_object* v_keys_4269_, lean_object* v_vals_4270_, lean_object* v_i_4271_, lean_object* v_entries_4272_){
_start:
{
lean_object* v___x_4273_; uint8_t v___x_4274_; 
v___x_4273_ = lean_array_get_size(v_keys_4269_);
v___x_4274_ = lean_nat_dec_lt(v_i_4271_, v___x_4273_);
if (v___x_4274_ == 0)
{
lean_dec(v_i_4271_);
return v_entries_4272_;
}
else
{
lean_object* v_k_4275_; lean_object* v_v_4276_; uint64_t v___x_4277_; size_t v_h_4278_; size_t v___x_4279_; lean_object* v___x_4280_; size_t v___x_4281_; size_t v___x_4282_; size_t v___x_4283_; size_t v_h_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; 
v_k_4275_ = lean_array_fget_borrowed(v_keys_4269_, v_i_4271_);
v_v_4276_ = lean_array_fget_borrowed(v_vals_4270_, v_i_4271_);
v___x_4277_ = l_Lean_instHashableMVarId_hash(v_k_4275_);
v_h_4278_ = lean_uint64_to_usize(v___x_4277_);
v___x_4279_ = ((size_t)5ULL);
v___x_4280_ = lean_unsigned_to_nat(1u);
v___x_4281_ = ((size_t)1ULL);
v___x_4282_ = lean_usize_sub(v_depth_4268_, v___x_4281_);
v___x_4283_ = lean_usize_mul(v___x_4279_, v___x_4282_);
v_h_4284_ = lean_usize_shift_right(v_h_4278_, v___x_4283_);
v___x_4285_ = lean_nat_add(v_i_4271_, v___x_4280_);
lean_dec(v_i_4271_);
lean_inc(v_v_4276_);
lean_inc(v_k_4275_);
v___x_4286_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_entries_4272_, v_h_4284_, v_depth_4268_, v_k_4275_, v_v_4276_);
v_i_4271_ = v___x_4285_;
v_entries_4272_ = v___x_4286_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_4288_, lean_object* v_keys_4289_, lean_object* v_vals_4290_, lean_object* v_i_4291_, lean_object* v_entries_4292_){
_start:
{
size_t v_depth_boxed_4293_; lean_object* v_res_4294_; 
v_depth_boxed_4293_ = lean_unbox_usize(v_depth_4288_);
lean_dec(v_depth_4288_);
v_res_4294_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_4293_, v_keys_4289_, v_vals_4290_, v_i_4291_, v_entries_4292_);
lean_dec_ref(v_vals_4290_);
lean_dec_ref(v_keys_4289_);
return v_res_4294_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_4295_, lean_object* v_x_4296_, lean_object* v_x_4297_, lean_object* v_x_4298_, lean_object* v_x_4299_){
_start:
{
size_t v_x_3982__boxed_4300_; size_t v_x_3983__boxed_4301_; lean_object* v_res_4302_; 
v_x_3982__boxed_4300_ = lean_unbox_usize(v_x_4296_);
lean_dec(v_x_4296_);
v_x_3983__boxed_4301_ = lean_unbox_usize(v_x_4297_);
lean_dec(v_x_4297_);
v_res_4302_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4295_, v_x_3982__boxed_4300_, v_x_3983__boxed_4301_, v_x_4298_, v_x_4299_);
return v_res_4302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(lean_object* v_x_4303_, lean_object* v_x_4304_, lean_object* v_x_4305_){
_start:
{
uint64_t v___x_4306_; size_t v___x_4307_; size_t v___x_4308_; lean_object* v___x_4309_; 
v___x_4306_ = l_Lean_instHashableMVarId_hash(v_x_4304_);
v___x_4307_ = lean_uint64_to_usize(v___x_4306_);
v___x_4308_ = ((size_t)1ULL);
v___x_4309_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4303_, v___x_4307_, v___x_4308_, v_x_4304_, v_x_4305_);
return v___x_4309_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(lean_object* v_mvarId_4310_, lean_object* v_val_4311_, lean_object* v___y_4312_){
_start:
{
lean_object* v___x_4314_; lean_object* v_mctx_4315_; lean_object* v_cache_4316_; lean_object* v_zetaDeltaFVarIds_4317_; lean_object* v_postponed_4318_; lean_object* v_diag_4319_; lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4348_; 
v___x_4314_ = lean_st_ref_take(v___y_4312_);
v_mctx_4315_ = lean_ctor_get(v___x_4314_, 0);
v_cache_4316_ = lean_ctor_get(v___x_4314_, 1);
v_zetaDeltaFVarIds_4317_ = lean_ctor_get(v___x_4314_, 2);
v_postponed_4318_ = lean_ctor_get(v___x_4314_, 3);
v_diag_4319_ = lean_ctor_get(v___x_4314_, 4);
v_isSharedCheck_4348_ = !lean_is_exclusive(v___x_4314_);
if (v_isSharedCheck_4348_ == 0)
{
v___x_4321_ = v___x_4314_;
v_isShared_4322_ = v_isSharedCheck_4348_;
goto v_resetjp_4320_;
}
else
{
lean_inc(v_diag_4319_);
lean_inc(v_postponed_4318_);
lean_inc(v_zetaDeltaFVarIds_4317_);
lean_inc(v_cache_4316_);
lean_inc(v_mctx_4315_);
lean_dec(v___x_4314_);
v___x_4321_ = lean_box(0);
v_isShared_4322_ = v_isSharedCheck_4348_;
goto v_resetjp_4320_;
}
v_resetjp_4320_:
{
lean_object* v_depth_4323_; lean_object* v_levelAssignDepth_4324_; lean_object* v_lmvarCounter_4325_; lean_object* v_mvarCounter_4326_; lean_object* v_lDecls_4327_; lean_object* v_decls_4328_; lean_object* v_userNames_4329_; lean_object* v_lAssignment_4330_; lean_object* v_eAssignment_4331_; lean_object* v_dAssignment_4332_; lean_object* v_instanceTypedMVars_4333_; lean_object* v___x_4335_; uint8_t v_isShared_4336_; uint8_t v_isSharedCheck_4347_; 
v_depth_4323_ = lean_ctor_get(v_mctx_4315_, 0);
v_levelAssignDepth_4324_ = lean_ctor_get(v_mctx_4315_, 1);
v_lmvarCounter_4325_ = lean_ctor_get(v_mctx_4315_, 2);
v_mvarCounter_4326_ = lean_ctor_get(v_mctx_4315_, 3);
v_lDecls_4327_ = lean_ctor_get(v_mctx_4315_, 4);
v_decls_4328_ = lean_ctor_get(v_mctx_4315_, 5);
v_userNames_4329_ = lean_ctor_get(v_mctx_4315_, 6);
v_lAssignment_4330_ = lean_ctor_get(v_mctx_4315_, 7);
v_eAssignment_4331_ = lean_ctor_get(v_mctx_4315_, 8);
v_dAssignment_4332_ = lean_ctor_get(v_mctx_4315_, 9);
v_instanceTypedMVars_4333_ = lean_ctor_get(v_mctx_4315_, 10);
v_isSharedCheck_4347_ = !lean_is_exclusive(v_mctx_4315_);
if (v_isSharedCheck_4347_ == 0)
{
v___x_4335_ = v_mctx_4315_;
v_isShared_4336_ = v_isSharedCheck_4347_;
goto v_resetjp_4334_;
}
else
{
lean_inc(v_instanceTypedMVars_4333_);
lean_inc(v_dAssignment_4332_);
lean_inc(v_eAssignment_4331_);
lean_inc(v_lAssignment_4330_);
lean_inc(v_userNames_4329_);
lean_inc(v_decls_4328_);
lean_inc(v_lDecls_4327_);
lean_inc(v_mvarCounter_4326_);
lean_inc(v_lmvarCounter_4325_);
lean_inc(v_levelAssignDepth_4324_);
lean_inc(v_depth_4323_);
lean_dec(v_mctx_4315_);
v___x_4335_ = lean_box(0);
v_isShared_4336_ = v_isSharedCheck_4347_;
goto v_resetjp_4334_;
}
v_resetjp_4334_:
{
lean_object* v___x_4337_; lean_object* v___x_4339_; 
v___x_4337_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(v_eAssignment_4331_, v_mvarId_4310_, v_val_4311_);
if (v_isShared_4336_ == 0)
{
lean_ctor_set(v___x_4335_, 8, v___x_4337_);
v___x_4339_ = v___x_4335_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4346_; 
v_reuseFailAlloc_4346_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_4346_, 0, v_depth_4323_);
lean_ctor_set(v_reuseFailAlloc_4346_, 1, v_levelAssignDepth_4324_);
lean_ctor_set(v_reuseFailAlloc_4346_, 2, v_lmvarCounter_4325_);
lean_ctor_set(v_reuseFailAlloc_4346_, 3, v_mvarCounter_4326_);
lean_ctor_set(v_reuseFailAlloc_4346_, 4, v_lDecls_4327_);
lean_ctor_set(v_reuseFailAlloc_4346_, 5, v_decls_4328_);
lean_ctor_set(v_reuseFailAlloc_4346_, 6, v_userNames_4329_);
lean_ctor_set(v_reuseFailAlloc_4346_, 7, v_lAssignment_4330_);
lean_ctor_set(v_reuseFailAlloc_4346_, 8, v___x_4337_);
lean_ctor_set(v_reuseFailAlloc_4346_, 9, v_dAssignment_4332_);
lean_ctor_set(v_reuseFailAlloc_4346_, 10, v_instanceTypedMVars_4333_);
v___x_4339_ = v_reuseFailAlloc_4346_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
lean_object* v___x_4341_; 
if (v_isShared_4322_ == 0)
{
lean_ctor_set(v___x_4321_, 0, v___x_4339_);
v___x_4341_ = v___x_4321_;
goto v_reusejp_4340_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v___x_4339_);
lean_ctor_set(v_reuseFailAlloc_4345_, 1, v_cache_4316_);
lean_ctor_set(v_reuseFailAlloc_4345_, 2, v_zetaDeltaFVarIds_4317_);
lean_ctor_set(v_reuseFailAlloc_4345_, 3, v_postponed_4318_);
lean_ctor_set(v_reuseFailAlloc_4345_, 4, v_diag_4319_);
v___x_4341_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4340_;
}
v_reusejp_4340_:
{
lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; 
v___x_4342_ = lean_st_ref_put(v___y_4312_, v___x_4341_);
v___x_4343_ = lean_box(0);
v___x_4344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4344_, 0, v___x_4343_);
return v___x_4344_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg___boxed(lean_object* v_mvarId_4349_, lean_object* v_val_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_){
_start:
{
lean_object* v_res_4353_; 
v_res_4353_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mvarId_4349_, v_val_4350_, v___y_4351_);
lean_dec(v___y_4351_);
return v_res_4353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___lam__0(lean_object* v_mv_u2081_4358_, lean_object* v_mv_u2082_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_){
_start:
{
lean_object* v___x_4368_; 
lean_inc(v_mv_u2081_4358_);
v___x_4368_ = l_Lean_MVarId_getDecl(v_mv_u2081_4358_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_);
if (lean_obj_tag(v___x_4368_) == 0)
{
lean_object* v_a_4369_; lean_object* v___x_4370_; 
v_a_4369_ = lean_ctor_get(v___x_4368_, 0);
lean_inc(v_a_4369_);
lean_dec_ref_known(v___x_4368_, 1);
lean_inc(v_mv_u2082_4359_);
v___x_4370_ = l_Lean_MVarId_getDecl(v_mv_u2082_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_);
if (lean_obj_tag(v___x_4370_) == 0)
{
lean_object* v_a_4371_; lean_object* v_lctx_4372_; lean_object* v_type_4373_; lean_object* v_lctx_4374_; lean_object* v_type_4375_; uint8_t v___x_4376_; 
v_a_4371_ = lean_ctor_get(v___x_4370_, 0);
lean_inc(v_a_4371_);
lean_dec_ref_known(v___x_4370_, 1);
v_lctx_4372_ = lean_ctor_get(v_a_4369_, 1);
lean_inc_ref(v_lctx_4372_);
v_type_4373_ = lean_ctor_get(v_a_4369_, 2);
lean_inc_ref(v_type_4373_);
lean_dec(v_a_4369_);
v_lctx_4374_ = lean_ctor_get(v_a_4371_, 1);
lean_inc_ref(v_lctx_4374_);
v_type_4375_ = lean_ctor_get(v_a_4371_, 2);
lean_inc_ref(v_type_4375_);
lean_dec(v_a_4371_);
v___x_4376_ = lean_expr_eqv(v_type_4373_, v_type_4375_);
lean_dec_ref(v_type_4375_);
lean_dec_ref(v_type_4373_);
if (v___x_4376_ == 0)
{
lean_dec_ref(v_lctx_4374_);
lean_dec_ref(v_lctx_4372_);
lean_dec(v_mv_u2082_4359_);
lean_dec(v_mv_u2081_4358_);
goto v___jp_4365_;
}
else
{
lean_object* v___x_4377_; uint8_t v___x_4378_; 
v___x_4377_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
v___x_4378_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_4372_, v_lctx_4374_, v___x_4377_);
if (v___x_4378_ == 0)
{
uint8_t v___x_4379_; 
v___x_4379_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_4374_, v_lctx_4372_, v___x_4377_);
lean_dec_ref(v_lctx_4372_);
lean_dec_ref(v_lctx_4374_);
if (v___x_4379_ == 0)
{
lean_dec(v_mv_u2082_4359_);
lean_dec(v_mv_u2081_4358_);
goto v___jp_4365_;
}
else
{
lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4383_; uint8_t v_isShared_4384_; uint8_t v_isSharedCheck_4391_; 
v___x_4380_ = l_Lean_Expr_mvar___override(v_mv_u2082_4359_);
v___x_4381_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mv_u2081_4358_, v___x_4380_, v___y_4361_);
v_isSharedCheck_4391_ = !lean_is_exclusive(v___x_4381_);
if (v_isSharedCheck_4391_ == 0)
{
lean_object* v_unused_4392_; 
v_unused_4392_ = lean_ctor_get(v___x_4381_, 0);
lean_dec(v_unused_4392_);
v___x_4383_ = v___x_4381_;
v_isShared_4384_ = v_isSharedCheck_4391_;
goto v_resetjp_4382_;
}
else
{
lean_dec(v___x_4381_);
v___x_4383_ = lean_box(0);
v_isShared_4384_ = v_isSharedCheck_4391_;
goto v_resetjp_4382_;
}
v_resetjp_4382_:
{
lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4389_; 
v___x_4385_ = lean_box(v___x_4378_);
v___x_4386_ = lean_box(v___x_4376_);
v___x_4387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4387_, 0, v___x_4385_);
lean_ctor_set(v___x_4387_, 1, v___x_4386_);
if (v_isShared_4384_ == 0)
{
lean_ctor_set(v___x_4383_, 0, v___x_4387_);
v___x_4389_ = v___x_4383_;
goto v_reusejp_4388_;
}
else
{
lean_object* v_reuseFailAlloc_4390_; 
v_reuseFailAlloc_4390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4390_, 0, v___x_4387_);
v___x_4389_ = v_reuseFailAlloc_4390_;
goto v_reusejp_4388_;
}
v_reusejp_4388_:
{
return v___x_4389_;
}
}
}
}
else
{
lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4396_; uint8_t v_isShared_4397_; uint8_t v_isSharedCheck_4405_; 
lean_dec_ref(v_lctx_4374_);
lean_dec_ref(v_lctx_4372_);
v___x_4393_ = l_Lean_Expr_mvar___override(v_mv_u2081_4358_);
v___x_4394_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mv_u2082_4359_, v___x_4393_, v___y_4361_);
v_isSharedCheck_4405_ = !lean_is_exclusive(v___x_4394_);
if (v_isSharedCheck_4405_ == 0)
{
lean_object* v_unused_4406_; 
v_unused_4406_ = lean_ctor_get(v___x_4394_, 0);
lean_dec(v_unused_4406_);
v___x_4396_ = v___x_4394_;
v_isShared_4397_ = v_isSharedCheck_4405_;
goto v_resetjp_4395_;
}
else
{
lean_dec(v___x_4394_);
v___x_4396_ = lean_box(0);
v_isShared_4397_ = v_isSharedCheck_4405_;
goto v_resetjp_4395_;
}
v_resetjp_4395_:
{
uint8_t v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4403_; 
v___x_4398_ = 0;
v___x_4399_ = lean_box(v___x_4376_);
v___x_4400_ = lean_box(v___x_4398_);
v___x_4401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4401_, 0, v___x_4399_);
lean_ctor_set(v___x_4401_, 1, v___x_4400_);
if (v_isShared_4397_ == 0)
{
lean_ctor_set(v___x_4396_, 0, v___x_4401_);
v___x_4403_ = v___x_4396_;
goto v_reusejp_4402_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4404_, 0, v___x_4401_);
v___x_4403_ = v_reuseFailAlloc_4404_;
goto v_reusejp_4402_;
}
v_reusejp_4402_:
{
return v___x_4403_;
}
}
}
}
}
else
{
lean_object* v_a_4407_; lean_object* v___x_4409_; uint8_t v_isShared_4410_; uint8_t v_isSharedCheck_4414_; 
lean_dec(v_a_4369_);
lean_dec(v_mv_u2082_4359_);
lean_dec(v_mv_u2081_4358_);
v_a_4407_ = lean_ctor_get(v___x_4370_, 0);
v_isSharedCheck_4414_ = !lean_is_exclusive(v___x_4370_);
if (v_isSharedCheck_4414_ == 0)
{
v___x_4409_ = v___x_4370_;
v_isShared_4410_ = v_isSharedCheck_4414_;
goto v_resetjp_4408_;
}
else
{
lean_inc(v_a_4407_);
lean_dec(v___x_4370_);
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
}
else
{
lean_object* v_a_4415_; lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4422_; 
lean_dec(v_mv_u2082_4359_);
lean_dec(v_mv_u2081_4358_);
v_a_4415_ = lean_ctor_get(v___x_4368_, 0);
v_isSharedCheck_4422_ = !lean_is_exclusive(v___x_4368_);
if (v_isSharedCheck_4422_ == 0)
{
v___x_4417_ = v___x_4368_;
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
else
{
lean_inc(v_a_4415_);
lean_dec(v___x_4368_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
lean_object* v___x_4420_; 
if (v_isShared_4418_ == 0)
{
v___x_4420_ = v___x_4417_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4421_; 
v_reuseFailAlloc_4421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4421_, 0, v_a_4415_);
v___x_4420_ = v_reuseFailAlloc_4421_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
return v___x_4420_;
}
}
}
v___jp_4365_:
{
lean_object* v___x_4366_; lean_object* v___x_4367_; 
v___x_4366_ = ((lean_object*)(l_Lean_Elab_WF_assignSubsumed___lam__0___closed__0));
v___x_4367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4367_, 0, v___x_4366_);
return v___x_4367_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___lam__0___boxed(lean_object* v_mv_u2081_4423_, lean_object* v_mv_u2082_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_){
_start:
{
lean_object* v_res_4430_; 
v_res_4430_ = l_Lean_Elab_WF_assignSubsumed___lam__0(v_mv_u2081_4423_, v_mv_u2082_4424_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_);
lean_dec(v___y_4428_);
lean_dec_ref(v___y_4427_);
lean_dec(v___y_4426_);
lean_dec_ref(v___y_4425_);
return v_res_4430_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1(lean_object* v___x_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_){
_start:
{
lean_object* v___x_4437_; 
v___x_4437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4437_, 0, v___x_4431_);
return v___x_4437_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1___boxed(lean_object* v___x_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_){
_start:
{
lean_object* v_res_4444_; 
v_res_4444_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1(v___x_4438_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
lean_dec(v___y_4442_);
lean_dec_ref(v___y_4441_);
lean_dec(v___y_4440_);
lean_dec_ref(v___y_4439_);
return v_res_4444_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0(lean_object* v_f_4445_, lean_object* v___x_4446_, lean_object* v___x_4447_, lean_object* v___x_4448_, lean_object* v_a_4449_, uint8_t v___x_4450_, lean_object* v_snd_4451_, lean_object* v_fst_4452_, lean_object* v_next_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_){
_start:
{
lean_object* v___x_4459_; 
v___x_4459_ = lean_apply_7(v_f_4445_, v___x_4446_, v___x_4447_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_, lean_box(0));
if (lean_obj_tag(v___x_4459_) == 0)
{
lean_object* v_a_4460_; lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4495_; 
v_a_4460_ = lean_ctor_get(v___x_4459_, 0);
v_isSharedCheck_4495_ = !lean_is_exclusive(v___x_4459_);
if (v_isSharedCheck_4495_ == 0)
{
v___x_4462_ = v___x_4459_;
v_isShared_4463_ = v_isSharedCheck_4495_;
goto v_resetjp_4461_;
}
else
{
lean_inc(v_a_4460_);
lean_dec(v___x_4459_);
v___x_4462_ = lean_box(0);
v_isShared_4463_ = v_isSharedCheck_4495_;
goto v_resetjp_4461_;
}
v_resetjp_4461_:
{
lean_object* v_fst_4464_; lean_object* v_snd_4465_; lean_object* v___x_4467_; uint8_t v_isShared_4468_; uint8_t v_isSharedCheck_4494_; 
v_fst_4464_ = lean_ctor_get(v_a_4460_, 0);
v_snd_4465_ = lean_ctor_get(v_a_4460_, 1);
v_isSharedCheck_4494_ = !lean_is_exclusive(v_a_4460_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_4467_ = v_a_4460_;
v_isShared_4468_ = v_isSharedCheck_4494_;
goto v_resetjp_4466_;
}
else
{
lean_inc(v_snd_4465_);
lean_inc(v_fst_4464_);
lean_dec(v_a_4460_);
v___x_4467_ = lean_box(0);
v_isShared_4468_ = v_isSharedCheck_4494_;
goto v_resetjp_4466_;
}
v_resetjp_4466_:
{
lean_object* v_removed_4470_; lean_object* v_numRemoved_4471_; uint8_t v___x_4490_; 
v___x_4490_ = lean_unbox(v_fst_4464_);
lean_dec(v_fst_4464_);
if (v___x_4490_ == 0)
{
lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; 
v___x_4491_ = lean_nat_add(v_snd_4451_, v___x_4448_);
lean_dec(v_snd_4451_);
v___x_4492_ = lean_box(v___x_4450_);
v___x_4493_ = lean_array_set(v_fst_4452_, v_next_4453_, v___x_4492_);
v_removed_4470_ = v___x_4493_;
v_numRemoved_4471_ = v___x_4491_;
goto v___jp_4469_;
}
else
{
v_removed_4470_ = v_fst_4452_;
v_numRemoved_4471_ = v_snd_4451_;
goto v___jp_4469_;
}
v___jp_4469_:
{
uint8_t v___x_4472_; 
v___x_4472_ = lean_unbox(v_snd_4465_);
lean_dec(v_snd_4465_);
if (v___x_4472_ == 0)
{
lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4477_; 
v___x_4473_ = lean_nat_add(v_numRemoved_4471_, v___x_4448_);
lean_dec(v_numRemoved_4471_);
v___x_4474_ = lean_box(v___x_4450_);
v___x_4475_ = lean_array_set(v_removed_4470_, v_a_4449_, v___x_4474_);
if (v_isShared_4468_ == 0)
{
lean_ctor_set(v___x_4467_, 1, v___x_4473_);
lean_ctor_set(v___x_4467_, 0, v___x_4475_);
v___x_4477_ = v___x_4467_;
goto v_reusejp_4476_;
}
else
{
lean_object* v_reuseFailAlloc_4482_; 
v_reuseFailAlloc_4482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4482_, 0, v___x_4475_);
lean_ctor_set(v_reuseFailAlloc_4482_, 1, v___x_4473_);
v___x_4477_ = v_reuseFailAlloc_4482_;
goto v_reusejp_4476_;
}
v_reusejp_4476_:
{
lean_object* v___x_4478_; lean_object* v___x_4480_; 
v___x_4478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4478_, 0, v___x_4477_);
if (v_isShared_4463_ == 0)
{
lean_ctor_set(v___x_4462_, 0, v___x_4478_);
v___x_4480_ = v___x_4462_;
goto v_reusejp_4479_;
}
else
{
lean_object* v_reuseFailAlloc_4481_; 
v_reuseFailAlloc_4481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4481_, 0, v___x_4478_);
v___x_4480_ = v_reuseFailAlloc_4481_;
goto v_reusejp_4479_;
}
v_reusejp_4479_:
{
return v___x_4480_;
}
}
}
else
{
lean_object* v___x_4484_; 
if (v_isShared_4468_ == 0)
{
lean_ctor_set(v___x_4467_, 1, v_numRemoved_4471_);
lean_ctor_set(v___x_4467_, 0, v_removed_4470_);
v___x_4484_ = v___x_4467_;
goto v_reusejp_4483_;
}
else
{
lean_object* v_reuseFailAlloc_4489_; 
v_reuseFailAlloc_4489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4489_, 0, v_removed_4470_);
lean_ctor_set(v_reuseFailAlloc_4489_, 1, v_numRemoved_4471_);
v___x_4484_ = v_reuseFailAlloc_4489_;
goto v_reusejp_4483_;
}
v_reusejp_4483_:
{
lean_object* v___x_4485_; lean_object* v___x_4487_; 
v___x_4485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4485_, 0, v___x_4484_);
if (v_isShared_4463_ == 0)
{
lean_ctor_set(v___x_4462_, 0, v___x_4485_);
v___x_4487_ = v___x_4462_;
goto v_reusejp_4486_;
}
else
{
lean_object* v_reuseFailAlloc_4488_; 
v_reuseFailAlloc_4488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4488_, 0, v___x_4485_);
v___x_4487_ = v_reuseFailAlloc_4488_;
goto v_reusejp_4486_;
}
v_reusejp_4486_:
{
return v___x_4487_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4496_; lean_object* v___x_4498_; uint8_t v_isShared_4499_; uint8_t v_isSharedCheck_4503_; 
lean_dec(v_fst_4452_);
lean_dec(v_snd_4451_);
v_a_4496_ = lean_ctor_get(v___x_4459_, 0);
v_isSharedCheck_4503_ = !lean_is_exclusive(v___x_4459_);
if (v_isSharedCheck_4503_ == 0)
{
v___x_4498_ = v___x_4459_;
v_isShared_4499_ = v_isSharedCheck_4503_;
goto v_resetjp_4497_;
}
else
{
lean_inc(v_a_4496_);
lean_dec(v___x_4459_);
v___x_4498_ = lean_box(0);
v_isShared_4499_ = v_isSharedCheck_4503_;
goto v_resetjp_4497_;
}
v_resetjp_4497_:
{
lean_object* v___x_4501_; 
if (v_isShared_4499_ == 0)
{
v___x_4501_ = v___x_4498_;
goto v_reusejp_4500_;
}
else
{
lean_object* v_reuseFailAlloc_4502_; 
v_reuseFailAlloc_4502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4502_, 0, v_a_4496_);
v___x_4501_ = v_reuseFailAlloc_4502_;
goto v_reusejp_4500_;
}
v_reusejp_4500_:
{
return v___x_4501_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_f_4504_, lean_object* v___x_4505_, lean_object* v___x_4506_, lean_object* v___x_4507_, lean_object* v_a_4508_, lean_object* v___x_4509_, lean_object* v_snd_4510_, lean_object* v_fst_4511_, lean_object* v_next_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_){
_start:
{
uint8_t v___x_4355__boxed_4518_; lean_object* v_res_4519_; 
v___x_4355__boxed_4518_ = lean_unbox(v___x_4509_);
v_res_4519_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0(v_f_4504_, v___x_4505_, v___x_4506_, v___x_4507_, v_a_4508_, v___x_4355__boxed_4518_, v_snd_4510_, v_fst_4511_, v_next_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_);
lean_dec(v_next_4512_);
lean_dec(v_a_4508_);
lean_dec(v___x_4507_);
return v_res_4519_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(lean_object* v_upperBound_4520_, lean_object* v_a_4521_, lean_object* v_next_4522_, lean_object* v_f_4523_, lean_object* v_a_4524_, lean_object* v_b_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_){
_start:
{
uint8_t v___x_4531_; 
v___x_4531_ = lean_nat_dec_lt(v_a_4524_, v_upperBound_4520_);
if (v___x_4531_ == 0)
{
lean_object* v___x_4532_; 
lean_dec(v_a_4524_);
lean_dec_ref(v_f_4523_);
lean_dec(v_next_4522_);
v___x_4532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4532_, 0, v_b_4525_);
return v___x_4532_;
}
else
{
lean_object* v_fst_4533_; lean_object* v_snd_4534_; lean_object* v___x_4536_; uint8_t v_isShared_4537_; uint8_t v_isSharedCheck_4581_; 
v_fst_4533_ = lean_ctor_get(v_b_4525_, 0);
v_snd_4534_ = lean_ctor_get(v_b_4525_, 1);
v_isSharedCheck_4581_ = !lean_is_exclusive(v_b_4525_);
if (v_isSharedCheck_4581_ == 0)
{
v___x_4536_ = v_b_4525_;
v_isShared_4537_ = v_isSharedCheck_4581_;
goto v_resetjp_4535_;
}
else
{
lean_inc(v_snd_4534_);
lean_inc(v_fst_4533_);
lean_dec(v_b_4525_);
v___x_4536_ = lean_box(0);
v_isShared_4537_ = v_isSharedCheck_4581_;
goto v_resetjp_4535_;
}
v_resetjp_4535_:
{
lean_object* v___x_4538_; lean_object* v___y_4540_; uint8_t v___y_4563_; uint8_t v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; uint8_t v___x_4576_; 
v___x_4538_ = lean_unsigned_to_nat(1u);
v___x_4573_ = 0;
v___x_4574_ = lean_box(v___x_4573_);
v___x_4575_ = lean_array_get(v___x_4574_, v_fst_4533_, v_next_4522_);
lean_dec(v___x_4574_);
v___x_4576_ = lean_unbox(v___x_4575_);
if (v___x_4576_ == 0)
{
lean_object* v___x_4577_; lean_object* v___x_4578_; uint8_t v___x_4579_; 
lean_dec(v___x_4575_);
v___x_4577_ = lean_box(v___x_4573_);
v___x_4578_ = lean_array_get(v___x_4577_, v_fst_4533_, v_a_4524_);
lean_dec(v___x_4577_);
v___x_4579_ = lean_unbox(v___x_4578_);
lean_dec(v___x_4578_);
v___y_4563_ = v___x_4579_;
goto v___jp_4562_;
}
else
{
uint8_t v___x_4580_; 
v___x_4580_ = lean_unbox(v___x_4575_);
lean_dec(v___x_4575_);
v___y_4563_ = v___x_4580_;
goto v___jp_4562_;
}
v___jp_4539_:
{
lean_object* v___x_4541_; 
lean_inc(v___y_4529_);
lean_inc_ref(v___y_4528_);
lean_inc(v___y_4527_);
lean_inc_ref(v___y_4526_);
v___x_4541_ = lean_apply_5(v___y_4540_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_, lean_box(0));
if (lean_obj_tag(v___x_4541_) == 0)
{
lean_object* v_a_4542_; lean_object* v___x_4544_; uint8_t v_isShared_4545_; uint8_t v_isSharedCheck_4553_; 
v_a_4542_ = lean_ctor_get(v___x_4541_, 0);
v_isSharedCheck_4553_ = !lean_is_exclusive(v___x_4541_);
if (v_isSharedCheck_4553_ == 0)
{
v___x_4544_ = v___x_4541_;
v_isShared_4545_ = v_isSharedCheck_4553_;
goto v_resetjp_4543_;
}
else
{
lean_inc(v_a_4542_);
lean_dec(v___x_4541_);
v___x_4544_ = lean_box(0);
v_isShared_4545_ = v_isSharedCheck_4553_;
goto v_resetjp_4543_;
}
v_resetjp_4543_:
{
if (lean_obj_tag(v_a_4542_) == 0)
{
lean_object* v_a_4546_; lean_object* v___x_4548_; 
lean_dec(v_a_4524_);
lean_dec_ref(v_f_4523_);
lean_dec(v_next_4522_);
v_a_4546_ = lean_ctor_get(v_a_4542_, 0);
lean_inc(v_a_4546_);
lean_dec_ref_known(v_a_4542_, 1);
if (v_isShared_4545_ == 0)
{
lean_ctor_set(v___x_4544_, 0, v_a_4546_);
v___x_4548_ = v___x_4544_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v_a_4546_);
v___x_4548_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
return v___x_4548_;
}
}
else
{
lean_object* v_a_4550_; lean_object* v___x_4551_; 
lean_del_object(v___x_4544_);
v_a_4550_ = lean_ctor_get(v_a_4542_, 0);
lean_inc(v_a_4550_);
lean_dec_ref_known(v_a_4542_, 1);
v___x_4551_ = lean_nat_add(v_a_4524_, v___x_4538_);
lean_dec(v_a_4524_);
v_a_4524_ = v___x_4551_;
v_b_4525_ = v_a_4550_;
goto _start;
}
}
}
else
{
lean_object* v_a_4554_; lean_object* v___x_4556_; uint8_t v_isShared_4557_; uint8_t v_isSharedCheck_4561_; 
lean_dec(v_a_4524_);
lean_dec_ref(v_f_4523_);
lean_dec(v_next_4522_);
v_a_4554_ = lean_ctor_get(v___x_4541_, 0);
v_isSharedCheck_4561_ = !lean_is_exclusive(v___x_4541_);
if (v_isSharedCheck_4561_ == 0)
{
v___x_4556_ = v___x_4541_;
v_isShared_4557_ = v_isSharedCheck_4561_;
goto v_resetjp_4555_;
}
else
{
lean_inc(v_a_4554_);
lean_dec(v___x_4541_);
v___x_4556_ = lean_box(0);
v_isShared_4557_ = v_isSharedCheck_4561_;
goto v_resetjp_4555_;
}
v_resetjp_4555_:
{
lean_object* v___x_4559_; 
if (v_isShared_4557_ == 0)
{
v___x_4559_ = v___x_4556_;
goto v_reusejp_4558_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v_a_4554_);
v___x_4559_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4558_;
}
v_reusejp_4558_:
{
return v___x_4559_;
}
}
}
}
v___jp_4562_:
{
if (v___y_4563_ == 0)
{
lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___f_4567_; 
lean_del_object(v___x_4536_);
v___x_4564_ = lean_array_fget_borrowed(v_a_4521_, v_next_4522_);
v___x_4565_ = lean_array_fget_borrowed(v_a_4521_, v_a_4524_);
v___x_4566_ = lean_box(v___x_4531_);
lean_inc(v_next_4522_);
lean_inc(v_a_4524_);
lean_inc(v___x_4565_);
lean_inc(v___x_4564_);
lean_inc_ref(v_f_4523_);
v___f_4567_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4567_, 0, v_f_4523_);
lean_closure_set(v___f_4567_, 1, v___x_4564_);
lean_closure_set(v___f_4567_, 2, v___x_4565_);
lean_closure_set(v___f_4567_, 3, v___x_4538_);
lean_closure_set(v___f_4567_, 4, v_a_4524_);
lean_closure_set(v___f_4567_, 5, v___x_4566_);
lean_closure_set(v___f_4567_, 6, v_snd_4534_);
lean_closure_set(v___f_4567_, 7, v_fst_4533_);
lean_closure_set(v___f_4567_, 8, v_next_4522_);
v___y_4540_ = v___f_4567_;
goto v___jp_4539_;
}
else
{
lean_object* v___x_4569_; 
if (v_isShared_4537_ == 0)
{
v___x_4569_ = v___x_4536_;
goto v_reusejp_4568_;
}
else
{
lean_object* v_reuseFailAlloc_4572_; 
v_reuseFailAlloc_4572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4572_, 0, v_fst_4533_);
lean_ctor_set(v_reuseFailAlloc_4572_, 1, v_snd_4534_);
v___x_4569_ = v_reuseFailAlloc_4572_;
goto v_reusejp_4568_;
}
v_reusejp_4568_:
{
lean_object* v___x_4570_; lean_object* v___f_4571_; 
v___x_4570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4570_, 0, v___x_4569_);
v___f_4571_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1___boxed), 6, 1);
lean_closure_set(v___f_4571_, 0, v___x_4570_);
v___y_4540_ = v___f_4571_;
goto v___jp_4539_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___boxed(lean_object* v_upperBound_4582_, lean_object* v_a_4583_, lean_object* v_next_4584_, lean_object* v_f_4585_, lean_object* v_a_4586_, lean_object* v_b_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_){
_start:
{
lean_object* v_res_4593_; 
v_res_4593_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v_upperBound_4582_, v_a_4583_, v_next_4584_, v_f_4585_, v_a_4586_, v_b_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_);
lean_dec(v___y_4591_);
lean_dec_ref(v___y_4590_);
lean_dec(v___y_4589_);
lean_dec_ref(v___y_4588_);
lean_dec_ref(v_a_4583_);
lean_dec(v_upperBound_4582_);
return v_res_4593_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(lean_object* v_upperBound_4594_, lean_object* v___x_4595_, lean_object* v_a_4596_, lean_object* v_f_4597_, lean_object* v_a_4598_, lean_object* v_b_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_){
_start:
{
uint8_t v___x_4605_; 
v___x_4605_ = lean_nat_dec_lt(v_a_4598_, v_upperBound_4594_);
if (v___x_4605_ == 0)
{
lean_object* v___x_4606_; 
lean_dec(v_a_4598_);
lean_dec_ref(v_f_4597_);
v___x_4606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4606_, 0, v_b_4599_);
return v___x_4606_;
}
else
{
lean_object* v_fst_4607_; lean_object* v_snd_4608_; lean_object* v___x_4610_; uint8_t v_isShared_4611_; uint8_t v_isSharedCheck_4629_; 
v_fst_4607_ = lean_ctor_get(v_b_4599_, 0);
v_snd_4608_ = lean_ctor_get(v_b_4599_, 1);
v_isSharedCheck_4629_ = !lean_is_exclusive(v_b_4599_);
if (v_isSharedCheck_4629_ == 0)
{
v___x_4610_ = v_b_4599_;
v_isShared_4611_ = v_isSharedCheck_4629_;
goto v_resetjp_4609_;
}
else
{
lean_inc(v_snd_4608_);
lean_inc(v_fst_4607_);
lean_dec(v_b_4599_);
v___x_4610_ = lean_box(0);
v_isShared_4611_ = v_isSharedCheck_4629_;
goto v_resetjp_4609_;
}
v_resetjp_4609_:
{
lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4615_; 
v___x_4612_ = lean_unsigned_to_nat(1u);
v___x_4613_ = lean_nat_add(v_a_4598_, v___x_4612_);
if (v_isShared_4611_ == 0)
{
v___x_4615_ = v___x_4610_;
goto v_reusejp_4614_;
}
else
{
lean_object* v_reuseFailAlloc_4628_; 
v_reuseFailAlloc_4628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4628_, 0, v_fst_4607_);
lean_ctor_set(v_reuseFailAlloc_4628_, 1, v_snd_4608_);
v___x_4615_ = v_reuseFailAlloc_4628_;
goto v_reusejp_4614_;
}
v_reusejp_4614_:
{
lean_object* v___x_4616_; 
lean_inc(v___x_4613_);
lean_inc_ref(v_f_4597_);
v___x_4616_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v___x_4595_, v_a_4596_, v_a_4598_, v_f_4597_, v___x_4613_, v___x_4615_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_);
if (lean_obj_tag(v___x_4616_) == 0)
{
lean_object* v_a_4617_; lean_object* v_fst_4618_; lean_object* v_snd_4619_; lean_object* v___x_4621_; uint8_t v_isShared_4622_; uint8_t v_isSharedCheck_4627_; 
v_a_4617_ = lean_ctor_get(v___x_4616_, 0);
lean_inc(v_a_4617_);
lean_dec_ref_known(v___x_4616_, 1);
v_fst_4618_ = lean_ctor_get(v_a_4617_, 0);
v_snd_4619_ = lean_ctor_get(v_a_4617_, 1);
v_isSharedCheck_4627_ = !lean_is_exclusive(v_a_4617_);
if (v_isSharedCheck_4627_ == 0)
{
v___x_4621_ = v_a_4617_;
v_isShared_4622_ = v_isSharedCheck_4627_;
goto v_resetjp_4620_;
}
else
{
lean_inc(v_snd_4619_);
lean_inc(v_fst_4618_);
lean_dec(v_a_4617_);
v___x_4621_ = lean_box(0);
v_isShared_4622_ = v_isSharedCheck_4627_;
goto v_resetjp_4620_;
}
v_resetjp_4620_:
{
lean_object* v___x_4624_; 
if (v_isShared_4622_ == 0)
{
v___x_4624_ = v___x_4621_;
goto v_reusejp_4623_;
}
else
{
lean_object* v_reuseFailAlloc_4626_; 
v_reuseFailAlloc_4626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4626_, 0, v_fst_4618_);
lean_ctor_set(v_reuseFailAlloc_4626_, 1, v_snd_4619_);
v___x_4624_ = v_reuseFailAlloc_4626_;
goto v_reusejp_4623_;
}
v_reusejp_4623_:
{
v_a_4598_ = v___x_4613_;
v_b_4599_ = v___x_4624_;
goto _start;
}
}
}
else
{
lean_dec(v___x_4613_);
lean_dec_ref(v_f_4597_);
return v___x_4616_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_4630_, lean_object* v___x_4631_, lean_object* v_a_4632_, lean_object* v_f_4633_, lean_object* v_a_4634_, lean_object* v_b_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_){
_start:
{
lean_object* v_res_4641_; 
v_res_4641_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v_upperBound_4630_, v___x_4631_, v_a_4632_, v_f_4633_, v_a_4634_, v_b_4635_, v___y_4636_, v___y_4637_, v___y_4638_, v___y_4639_);
lean_dec(v___y_4639_);
lean_dec_ref(v___y_4638_);
lean_dec(v___y_4637_);
lean_dec_ref(v___y_4636_);
lean_dec_ref(v_a_4632_);
lean_dec(v___x_4631_);
lean_dec(v_upperBound_4630_);
return v_res_4641_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0(lean_object* v___x_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_){
_start:
{
lean_object* v___x_4648_; 
v___x_4648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4648_, 0, v___x_4642_);
return v___x_4648_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed(lean_object* v___x_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_){
_start:
{
lean_object* v_res_4655_; 
v_res_4655_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0(v___x_4649_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_);
lean_dec(v___y_4653_);
lean_dec_ref(v___y_4652_);
lean_dec(v___y_4651_);
lean_dec_ref(v___y_4650_);
return v_res_4655_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(lean_object* v_upperBound_4656_, lean_object* v_removed_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_b_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_){
_start:
{
lean_object* v___y_4667_; uint8_t v___x_4690_; 
v___x_4690_ = lean_nat_dec_lt(v_a_4659_, v_upperBound_4656_);
if (v___x_4690_ == 0)
{
lean_object* v___x_4691_; 
lean_dec(v_a_4659_);
v___x_4691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4691_, 0, v_b_4660_);
return v___x_4691_;
}
else
{
uint8_t v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; uint8_t v___x_4695_; 
v___x_4692_ = 0;
v___x_4693_ = lean_box(v___x_4692_);
v___x_4694_ = lean_array_get(v___x_4693_, v_removed_4657_, v_a_4659_);
lean_dec(v___x_4693_);
v___x_4695_ = lean_unbox(v___x_4694_);
lean_dec(v___x_4694_);
if (v___x_4695_ == 0)
{
lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___f_4699_; 
v___x_4696_ = lean_array_fget_borrowed(v_a_4658_, v_a_4659_);
lean_inc(v___x_4696_);
v___x_4697_ = lean_array_push(v_b_4660_, v___x_4696_);
v___x_4698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4698_, 0, v___x_4697_);
v___f_4699_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4699_, 0, v___x_4698_);
v___y_4667_ = v___f_4699_;
goto v___jp_4666_;
}
else
{
lean_object* v___x_4700_; lean_object* v___f_4701_; 
v___x_4700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4700_, 0, v_b_4660_);
v___f_4701_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4701_, 0, v___x_4700_);
v___y_4667_ = v___f_4701_;
goto v___jp_4666_;
}
}
v___jp_4666_:
{
lean_object* v___x_4668_; 
lean_inc(v___y_4664_);
lean_inc_ref(v___y_4663_);
lean_inc(v___y_4662_);
lean_inc_ref(v___y_4661_);
v___x_4668_ = lean_apply_5(v___y_4667_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_, lean_box(0));
if (lean_obj_tag(v___x_4668_) == 0)
{
lean_object* v_a_4669_; lean_object* v___x_4671_; uint8_t v_isShared_4672_; uint8_t v_isSharedCheck_4681_; 
v_a_4669_ = lean_ctor_get(v___x_4668_, 0);
v_isSharedCheck_4681_ = !lean_is_exclusive(v___x_4668_);
if (v_isSharedCheck_4681_ == 0)
{
v___x_4671_ = v___x_4668_;
v_isShared_4672_ = v_isSharedCheck_4681_;
goto v_resetjp_4670_;
}
else
{
lean_inc(v_a_4669_);
lean_dec(v___x_4668_);
v___x_4671_ = lean_box(0);
v_isShared_4672_ = v_isSharedCheck_4681_;
goto v_resetjp_4670_;
}
v_resetjp_4670_:
{
if (lean_obj_tag(v_a_4669_) == 0)
{
lean_object* v_a_4673_; lean_object* v___x_4675_; 
lean_dec(v_a_4659_);
v_a_4673_ = lean_ctor_get(v_a_4669_, 0);
lean_inc(v_a_4673_);
lean_dec_ref_known(v_a_4669_, 1);
if (v_isShared_4672_ == 0)
{
lean_ctor_set(v___x_4671_, 0, v_a_4673_);
v___x_4675_ = v___x_4671_;
goto v_reusejp_4674_;
}
else
{
lean_object* v_reuseFailAlloc_4676_; 
v_reuseFailAlloc_4676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4676_, 0, v_a_4673_);
v___x_4675_ = v_reuseFailAlloc_4676_;
goto v_reusejp_4674_;
}
v_reusejp_4674_:
{
return v___x_4675_;
}
}
else
{
lean_object* v_a_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; 
lean_del_object(v___x_4671_);
v_a_4677_ = lean_ctor_get(v_a_4669_, 0);
lean_inc(v_a_4677_);
lean_dec_ref_known(v_a_4669_, 1);
v___x_4678_ = lean_unsigned_to_nat(1u);
v___x_4679_ = lean_nat_add(v_a_4659_, v___x_4678_);
lean_dec(v_a_4659_);
v_a_4659_ = v___x_4679_;
v_b_4660_ = v_a_4677_;
goto _start;
}
}
}
else
{
lean_object* v_a_4682_; lean_object* v___x_4684_; uint8_t v_isShared_4685_; uint8_t v_isSharedCheck_4689_; 
lean_dec(v_a_4659_);
v_a_4682_ = lean_ctor_get(v___x_4668_, 0);
v_isSharedCheck_4689_ = !lean_is_exclusive(v___x_4668_);
if (v_isSharedCheck_4689_ == 0)
{
v___x_4684_ = v___x_4668_;
v_isShared_4685_ = v_isSharedCheck_4689_;
goto v_resetjp_4683_;
}
else
{
lean_inc(v_a_4682_);
lean_dec(v___x_4668_);
v___x_4684_ = lean_box(0);
v_isShared_4685_ = v_isSharedCheck_4689_;
goto v_resetjp_4683_;
}
v_resetjp_4683_:
{
lean_object* v___x_4687_; 
if (v_isShared_4685_ == 0)
{
v___x_4687_ = v___x_4684_;
goto v_reusejp_4686_;
}
else
{
lean_object* v_reuseFailAlloc_4688_; 
v_reuseFailAlloc_4688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4688_, 0, v_a_4682_);
v___x_4687_ = v_reuseFailAlloc_4688_;
goto v_reusejp_4686_;
}
v_reusejp_4686_:
{
return v___x_4687_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___boxed(lean_object* v_upperBound_4702_, lean_object* v_removed_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_, lean_object* v_b_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_){
_start:
{
lean_object* v_res_4712_; 
v_res_4712_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v_upperBound_4702_, v_removed_4703_, v_a_4704_, v_a_4705_, v_b_4706_, v___y_4707_, v___y_4708_, v___y_4709_, v___y_4710_);
lean_dec(v___y_4710_);
lean_dec_ref(v___y_4709_);
lean_dec(v___y_4708_);
lean_dec_ref(v___y_4707_);
lean_dec_ref(v_a_4704_);
lean_dec_ref(v_removed_4703_);
lean_dec(v_upperBound_4702_);
return v_res_4712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(lean_object* v_a_4713_, lean_object* v_f_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_){
_start:
{
lean_object* v___x_4720_; uint8_t v___x_4721_; lean_object* v___x_4722_; lean_object* v_removed_4723_; lean_object* v_numRemoved_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; 
v___x_4720_ = lean_array_get_size(v_a_4713_);
v___x_4721_ = 0;
v___x_4722_ = lean_box(v___x_4721_);
v_removed_4723_ = lean_mk_array(v___x_4720_, v___x_4722_);
v_numRemoved_4724_ = lean_unsigned_to_nat(0u);
v___x_4725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4725_, 0, v_removed_4723_);
lean_ctor_set(v___x_4725_, 1, v_numRemoved_4724_);
v___x_4726_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v___x_4720_, v___x_4720_, v_a_4713_, v_f_4714_, v_numRemoved_4724_, v___x_4725_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_);
if (lean_obj_tag(v___x_4726_) == 0)
{
lean_object* v_a_4727_; lean_object* v_fst_4728_; lean_object* v_snd_4729_; lean_object* v_a_x27_4730_; lean_object* v___x_4731_; 
v_a_4727_ = lean_ctor_get(v___x_4726_, 0);
lean_inc(v_a_4727_);
lean_dec_ref_known(v___x_4726_, 1);
v_fst_4728_ = lean_ctor_get(v_a_4727_, 0);
lean_inc(v_fst_4728_);
v_snd_4729_ = lean_ctor_get(v_a_4727_, 1);
lean_inc(v_snd_4729_);
lean_dec(v_a_4727_);
v_a_x27_4730_ = lean_mk_empty_array_with_capacity(v_snd_4729_);
lean_dec(v_snd_4729_);
v___x_4731_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v___x_4720_, v_fst_4728_, v_a_4713_, v_numRemoved_4724_, v_a_x27_4730_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_);
lean_dec(v_fst_4728_);
return v___x_4731_;
}
else
{
lean_object* v_a_4732_; lean_object* v___x_4734_; uint8_t v_isShared_4735_; uint8_t v_isSharedCheck_4739_; 
v_a_4732_ = lean_ctor_get(v___x_4726_, 0);
v_isSharedCheck_4739_ = !lean_is_exclusive(v___x_4726_);
if (v_isSharedCheck_4739_ == 0)
{
v___x_4734_ = v___x_4726_;
v_isShared_4735_ = v_isSharedCheck_4739_;
goto v_resetjp_4733_;
}
else
{
lean_inc(v_a_4732_);
lean_dec(v___x_4726_);
v___x_4734_ = lean_box(0);
v_isShared_4735_ = v_isSharedCheck_4739_;
goto v_resetjp_4733_;
}
v_resetjp_4733_:
{
lean_object* v___x_4737_; 
if (v_isShared_4735_ == 0)
{
v___x_4737_ = v___x_4734_;
goto v_reusejp_4736_;
}
else
{
lean_object* v_reuseFailAlloc_4738_; 
v_reuseFailAlloc_4738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4738_, 0, v_a_4732_);
v___x_4737_ = v_reuseFailAlloc_4738_;
goto v_reusejp_4736_;
}
v_reusejp_4736_:
{
return v___x_4737_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg___boxed(lean_object* v_a_4740_, lean_object* v_f_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_){
_start:
{
lean_object* v_res_4747_; 
v_res_4747_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_a_4740_, v_f_4741_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_);
lean_dec(v___y_4745_);
lean_dec_ref(v___y_4744_);
lean_dec(v___y_4743_);
lean_dec_ref(v___y_4742_);
lean_dec_ref(v_a_4740_);
return v_res_4747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed(lean_object* v_mvars_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_){
_start:
{
lean_object* v___f_4755_; lean_object* v___x_4756_; 
v___f_4755_ = ((lean_object*)(l_Lean_Elab_WF_assignSubsumed___closed__0));
v___x_4756_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_mvars_4749_, v___f_4755_, v_a_4750_, v_a_4751_, v_a_4752_, v_a_4753_);
return v___x_4756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___boxed(lean_object* v_mvars_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_){
_start:
{
lean_object* v_res_4763_; 
v_res_4763_ = l_Lean_Elab_WF_assignSubsumed(v_mvars_4757_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_);
lean_dec(v_a_4761_);
lean_dec_ref(v_a_4760_);
lean_dec(v_a_4759_);
lean_dec_ref(v_a_4758_);
lean_dec_ref(v_mvars_4757_);
return v_res_4763_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0(lean_object* v_mvarId_4764_, lean_object* v_val_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_, lean_object* v___y_4768_, lean_object* v___y_4769_){
_start:
{
lean_object* v___x_4771_; 
v___x_4771_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mvarId_4764_, v_val_4765_, v___y_4767_);
return v___x_4771_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___boxed(lean_object* v_mvarId_4772_, lean_object* v_val_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_){
_start:
{
lean_object* v_res_4779_; 
v_res_4779_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0(v_mvarId_4772_, v_val_4773_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_);
lean_dec(v___y_4777_);
lean_dec_ref(v___y_4776_);
lean_dec(v___y_4775_);
lean_dec_ref(v___y_4774_);
return v_res_4779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1(lean_object* v_00_u03b1_4780_, lean_object* v_a_4781_, lean_object* v_f_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_){
_start:
{
lean_object* v___x_4788_; 
v___x_4788_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_a_4781_, v_f_4782_, v___y_4783_, v___y_4784_, v___y_4785_, v___y_4786_);
return v___x_4788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___boxed(lean_object* v_00_u03b1_4789_, lean_object* v_a_4790_, lean_object* v_f_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_){
_start:
{
lean_object* v_res_4797_; 
v_res_4797_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1(v_00_u03b1_4789_, v_a_4790_, v_f_4791_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_);
lean_dec(v___y_4795_);
lean_dec_ref(v___y_4794_);
lean_dec(v___y_4793_);
lean_dec_ref(v___y_4792_);
lean_dec_ref(v_a_4790_);
return v_res_4797_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0(lean_object* v_00_u03b2_4798_, lean_object* v_x_4799_, lean_object* v_x_4800_, lean_object* v_x_4801_){
_start:
{
lean_object* v___x_4802_; 
v___x_4802_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(v_x_4799_, v_x_4800_, v_x_4801_);
return v___x_4802_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2(lean_object* v_upperBound_4803_, lean_object* v_00_u03b1_4804_, lean_object* v_a_4805_, lean_object* v_next_4806_, lean_object* v_f_4807_, lean_object* v_inst_4808_, lean_object* v_R_4809_, lean_object* v_a_4810_, lean_object* v_b_4811_, lean_object* v_c_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_, lean_object* v___y_4816_){
_start:
{
lean_object* v___x_4818_; 
v___x_4818_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v_upperBound_4803_, v_a_4805_, v_next_4806_, v_f_4807_, v_a_4810_, v_b_4811_, v___y_4813_, v___y_4814_, v___y_4815_, v___y_4816_);
return v___x_4818_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___boxed(lean_object* v_upperBound_4819_, lean_object* v_00_u03b1_4820_, lean_object* v_a_4821_, lean_object* v_next_4822_, lean_object* v_f_4823_, lean_object* v_inst_4824_, lean_object* v_R_4825_, lean_object* v_a_4826_, lean_object* v_b_4827_, lean_object* v_c_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_){
_start:
{
lean_object* v_res_4834_; 
v_res_4834_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2(v_upperBound_4819_, v_00_u03b1_4820_, v_a_4821_, v_next_4822_, v_f_4823_, v_inst_4824_, v_R_4825_, v_a_4826_, v_b_4827_, v_c_4828_, v___y_4829_, v___y_4830_, v___y_4831_, v___y_4832_);
lean_dec(v___y_4832_);
lean_dec_ref(v___y_4831_);
lean_dec(v___y_4830_);
lean_dec_ref(v___y_4829_);
lean_dec_ref(v_a_4821_);
lean_dec(v_upperBound_4819_);
return v_res_4834_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3(lean_object* v_00_u03b1_4835_, lean_object* v_upperBound_4836_, lean_object* v_removed_4837_, lean_object* v_a_4838_, lean_object* v_inst_4839_, lean_object* v_R_4840_, lean_object* v_a_4841_, lean_object* v_b_4842_, lean_object* v_c_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_){
_start:
{
lean_object* v___x_4849_; 
v___x_4849_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v_upperBound_4836_, v_removed_4837_, v_a_4838_, v_a_4841_, v_b_4842_, v___y_4844_, v___y_4845_, v___y_4846_, v___y_4847_);
return v___x_4849_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___boxed(lean_object* v_00_u03b1_4850_, lean_object* v_upperBound_4851_, lean_object* v_removed_4852_, lean_object* v_a_4853_, lean_object* v_inst_4854_, lean_object* v_R_4855_, lean_object* v_a_4856_, lean_object* v_b_4857_, lean_object* v_c_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_){
_start:
{
lean_object* v_res_4864_; 
v_res_4864_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3(v_00_u03b1_4850_, v_upperBound_4851_, v_removed_4852_, v_a_4853_, v_inst_4854_, v_R_4855_, v_a_4856_, v_b_4857_, v_c_4858_, v___y_4859_, v___y_4860_, v___y_4861_, v___y_4862_);
lean_dec(v___y_4862_);
lean_dec_ref(v___y_4861_);
lean_dec(v___y_4860_);
lean_dec_ref(v___y_4859_);
lean_dec_ref(v_a_4853_);
lean_dec_ref(v_removed_4852_);
lean_dec(v_upperBound_4851_);
return v_res_4864_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4(lean_object* v_upperBound_4865_, lean_object* v___x_4866_, lean_object* v_00_u03b1_4867_, lean_object* v_a_4868_, lean_object* v_f_4869_, lean_object* v_inst_4870_, lean_object* v_R_4871_, lean_object* v_a_4872_, lean_object* v_b_4873_, lean_object* v_c_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_, lean_object* v___y_4878_){
_start:
{
lean_object* v___x_4880_; 
v___x_4880_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v_upperBound_4865_, v___x_4866_, v_a_4868_, v_f_4869_, v_a_4872_, v_b_4873_, v___y_4875_, v___y_4876_, v___y_4877_, v___y_4878_);
return v___x_4880_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___boxed(lean_object* v_upperBound_4881_, lean_object* v___x_4882_, lean_object* v_00_u03b1_4883_, lean_object* v_a_4884_, lean_object* v_f_4885_, lean_object* v_inst_4886_, lean_object* v_R_4887_, lean_object* v_a_4888_, lean_object* v_b_4889_, lean_object* v_c_4890_, lean_object* v___y_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_){
_start:
{
lean_object* v_res_4896_; 
v_res_4896_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4(v_upperBound_4881_, v___x_4882_, v_00_u03b1_4883_, v_a_4884_, v_f_4885_, v_inst_4886_, v_R_4887_, v_a_4888_, v_b_4889_, v_c_4890_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
lean_dec(v___y_4894_);
lean_dec_ref(v___y_4893_);
lean_dec(v___y_4892_);
lean_dec_ref(v___y_4891_);
lean_dec_ref(v_a_4884_);
lean_dec(v___x_4882_);
lean_dec(v_upperBound_4881_);
return v_res_4896_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4897_, lean_object* v_x_4898_, size_t v_x_4899_, size_t v_x_4900_, lean_object* v_x_4901_, lean_object* v_x_4902_){
_start:
{
lean_object* v___x_4903_; 
v___x_4903_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4898_, v_x_4899_, v_x_4900_, v_x_4901_, v_x_4902_);
return v___x_4903_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4904_, lean_object* v_x_4905_, lean_object* v_x_4906_, lean_object* v_x_4907_, lean_object* v_x_4908_, lean_object* v_x_4909_){
_start:
{
size_t v_x_4925__boxed_4910_; size_t v_x_4926__boxed_4911_; lean_object* v_res_4912_; 
v_x_4925__boxed_4910_ = lean_unbox_usize(v_x_4906_);
lean_dec(v_x_4906_);
v_x_4926__boxed_4911_ = lean_unbox_usize(v_x_4907_);
lean_dec(v_x_4907_);
v_res_4912_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1(v_00_u03b2_4904_, v_x_4905_, v_x_4925__boxed_4910_, v_x_4926__boxed_4911_, v_x_4908_, v_x_4909_);
return v_res_4912_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_4913_, lean_object* v_n_4914_, lean_object* v_k_4915_, lean_object* v_v_4916_){
_start:
{
lean_object* v___x_4917_; 
v___x_4917_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(v_n_4914_, v_k_4915_, v_v_4916_);
return v___x_4917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_4918_, size_t v_depth_4919_, lean_object* v_keys_4920_, lean_object* v_vals_4921_, lean_object* v_heq_4922_, lean_object* v_i_4923_, lean_object* v_entries_4924_){
_start:
{
lean_object* v___x_4925_; 
v___x_4925_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_4919_, v_keys_4920_, v_vals_4921_, v_i_4923_, v_entries_4924_);
return v___x_4925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_4926_, lean_object* v_depth_4927_, lean_object* v_keys_4928_, lean_object* v_vals_4929_, lean_object* v_heq_4930_, lean_object* v_i_4931_, lean_object* v_entries_4932_){
_start:
{
size_t v_depth_boxed_4933_; lean_object* v_res_4934_; 
v_depth_boxed_4933_ = lean_unbox_usize(v_depth_4927_);
lean_dec(v_depth_4927_);
v_res_4934_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_4926_, v_depth_boxed_4933_, v_keys_4928_, v_vals_4929_, v_heq_4930_, v_i_4931_, v_entries_4932_);
lean_dec_ref(v_vals_4929_);
lean_dec_ref(v_keys_4928_);
return v_res_4934_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_4935_, lean_object* v_x_4936_, lean_object* v_x_4937_, lean_object* v_x_4938_, lean_object* v_x_4939_){
_start:
{
lean_object* v___x_4940_; 
v___x_4940_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_x_4936_, v_x_4937_, v_x_4938_, v_x_4939_);
return v___x_4940_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4942_; lean_object* v___x_4943_; 
v___x_4942_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__0));
v___x_4943_ = l_Lean_stringToMessageData(v___x_4942_);
return v___x_4943_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4945_; lean_object* v___x_4946_; 
v___x_4945_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__2));
v___x_4946_ = l_Lean_stringToMessageData(v___x_4945_);
return v___x_4946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(lean_object* v_argsPacker_4947_, lean_object* v_as_4948_, size_t v_sz_4949_, size_t v_i_4950_, lean_object* v_b_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_){
_start:
{
lean_object* v_a_4958_; uint8_t v___x_4962_; 
v___x_4962_ = lean_usize_dec_lt(v_i_4950_, v_sz_4949_);
if (v___x_4962_ == 0)
{
lean_object* v___x_4963_; 
v___x_4963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4963_, 0, v_b_4951_);
return v___x_4963_;
}
else
{
lean_object* v_a_4964_; lean_object* v___x_4965_; 
v_a_4964_ = lean_array_uget_borrowed(v_as_4948_, v_i_4950_);
lean_inc(v_a_4964_);
v___x_4965_ = l_Lean_MVarId_getType(v_a_4964_, v___y_4952_, v___y_4953_, v___y_4954_, v___y_4955_);
if (lean_obj_tag(v___x_4965_) == 0)
{
lean_object* v_a_4966_; lean_object* v___y_4968_; lean_object* v___y_4969_; lean_object* v___y_4970_; lean_object* v___y_4971_; 
v_a_4966_ = lean_ctor_get(v___x_4965_, 0);
lean_inc(v_a_4966_);
lean_dec_ref_known(v___x_4965_, 1);
if (lean_obj_tag(v_a_4966_) == 10)
{
lean_object* v_expr_4984_; 
v_expr_4984_ = lean_ctor_get(v_a_4966_, 1);
if (lean_obj_tag(v_expr_4984_) == 5)
{
lean_object* v_arg_4985_; lean_object* v___x_4986_; 
lean_inc_ref(v_expr_4984_);
lean_dec_ref_known(v_a_4966_, 2);
v_arg_4985_ = lean_ctor_get(v_expr_4984_, 1);
lean_inc_ref_n(v_arg_4985_, 2);
lean_dec_ref_known(v_expr_4984_, 2);
v___x_4986_ = l_Lean_Meta_ArgsPacker_unpack(v_argsPacker_4947_, v_arg_4985_);
if (lean_obj_tag(v___x_4986_) == 1)
{
lean_object* v_val_4987_; lean_object* v_fst_4988_; lean_object* v___x_4989_; uint8_t v___x_4990_; 
lean_dec_ref(v_arg_4985_);
v_val_4987_ = lean_ctor_get(v___x_4986_, 0);
lean_inc(v_val_4987_);
lean_dec_ref_known(v___x_4986_, 1);
v_fst_4988_ = lean_ctor_get(v_val_4987_, 0);
lean_inc(v_fst_4988_);
lean_dec(v_val_4987_);
v___x_4989_ = lean_array_get_size(v_b_4951_);
v___x_4990_ = lean_nat_dec_lt(v_fst_4988_, v___x_4989_);
if (v___x_4990_ == 0)
{
lean_dec(v_fst_4988_);
v_a_4958_ = v_b_4951_;
goto v___jp_4957_;
}
else
{
lean_object* v_v_4991_; lean_object* v___x_4992_; lean_object* v_xs_x27_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; 
v_v_4991_ = lean_array_fget(v_b_4951_, v_fst_4988_);
v___x_4992_ = lean_box(0);
v_xs_x27_4993_ = lean_array_fset(v_b_4951_, v_fst_4988_, v___x_4992_);
lean_inc(v_a_4964_);
v___x_4994_ = lean_array_push(v_v_4991_, v_a_4964_);
v___x_4995_ = lean_array_fset(v_xs_x27_4993_, v_fst_4988_, v___x_4994_);
lean_dec(v_fst_4988_);
v_a_4958_ = v___x_4995_;
goto v___jp_4957_;
}
}
else
{
lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; 
lean_dec(v___x_4986_);
v___x_4996_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3);
v___x_4997_ = l_Lean_indentExpr(v_arg_4985_);
v___x_4998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4998_, 0, v___x_4996_);
lean_ctor_set(v___x_4998_, 1, v___x_4997_);
v___x_4999_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v___x_4998_, v___y_4952_, v___y_4953_, v___y_4954_, v___y_4955_);
if (lean_obj_tag(v___x_4999_) == 0)
{
lean_dec_ref_known(v___x_4999_, 1);
v_a_4958_ = v_b_4951_;
goto v___jp_4957_;
}
else
{
lean_object* v_a_5000_; lean_object* v___x_5002_; uint8_t v_isShared_5003_; uint8_t v_isSharedCheck_5007_; 
lean_dec_ref(v_b_4951_);
v_a_5000_ = lean_ctor_get(v___x_4999_, 0);
v_isSharedCheck_5007_ = !lean_is_exclusive(v___x_4999_);
if (v_isSharedCheck_5007_ == 0)
{
v___x_5002_ = v___x_4999_;
v_isShared_5003_ = v_isSharedCheck_5007_;
goto v_resetjp_5001_;
}
else
{
lean_inc(v_a_5000_);
lean_dec(v___x_4999_);
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
}
else
{
v___y_4968_ = v___y_4952_;
v___y_4969_ = v___y_4953_;
v___y_4970_ = v___y_4954_;
v___y_4971_ = v___y_4955_;
goto v___jp_4967_;
}
}
else
{
v___y_4968_ = v___y_4952_;
v___y_4969_ = v___y_4953_;
v___y_4970_ = v___y_4954_;
v___y_4971_ = v___y_4955_;
goto v___jp_4967_;
}
v___jp_4967_:
{
lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; 
v___x_4972_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1);
v___x_4973_ = l_Lean_indentExpr(v_a_4966_);
v___x_4974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4974_, 0, v___x_4972_);
lean_ctor_set(v___x_4974_, 1, v___x_4973_);
v___x_4975_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v___x_4974_, v___y_4968_, v___y_4969_, v___y_4970_, v___y_4971_);
if (lean_obj_tag(v___x_4975_) == 0)
{
lean_dec_ref_known(v___x_4975_, 1);
v_a_4958_ = v_b_4951_;
goto v___jp_4957_;
}
else
{
lean_object* v_a_4976_; lean_object* v___x_4978_; uint8_t v_isShared_4979_; uint8_t v_isSharedCheck_4983_; 
lean_dec_ref(v_b_4951_);
v_a_4976_ = lean_ctor_get(v___x_4975_, 0);
v_isSharedCheck_4983_ = !lean_is_exclusive(v___x_4975_);
if (v_isSharedCheck_4983_ == 0)
{
v___x_4978_ = v___x_4975_;
v_isShared_4979_ = v_isSharedCheck_4983_;
goto v_resetjp_4977_;
}
else
{
lean_inc(v_a_4976_);
lean_dec(v___x_4975_);
v___x_4978_ = lean_box(0);
v_isShared_4979_ = v_isSharedCheck_4983_;
goto v_resetjp_4977_;
}
v_resetjp_4977_:
{
lean_object* v___x_4981_; 
if (v_isShared_4979_ == 0)
{
v___x_4981_ = v___x_4978_;
goto v_reusejp_4980_;
}
else
{
lean_object* v_reuseFailAlloc_4982_; 
v_reuseFailAlloc_4982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4982_, 0, v_a_4976_);
v___x_4981_ = v_reuseFailAlloc_4982_;
goto v_reusejp_4980_;
}
v_reusejp_4980_:
{
return v___x_4981_;
}
}
}
}
}
else
{
lean_object* v_a_5008_; lean_object* v___x_5010_; uint8_t v_isShared_5011_; uint8_t v_isSharedCheck_5015_; 
lean_dec_ref(v_b_4951_);
v_a_5008_ = lean_ctor_get(v___x_4965_, 0);
v_isSharedCheck_5015_ = !lean_is_exclusive(v___x_4965_);
if (v_isSharedCheck_5015_ == 0)
{
v___x_5010_ = v___x_4965_;
v_isShared_5011_ = v_isSharedCheck_5015_;
goto v_resetjp_5009_;
}
else
{
lean_inc(v_a_5008_);
lean_dec(v___x_4965_);
v___x_5010_ = lean_box(0);
v_isShared_5011_ = v_isSharedCheck_5015_;
goto v_resetjp_5009_;
}
v_resetjp_5009_:
{
lean_object* v___x_5013_; 
if (v_isShared_5011_ == 0)
{
v___x_5013_ = v___x_5010_;
goto v_reusejp_5012_;
}
else
{
lean_object* v_reuseFailAlloc_5014_; 
v_reuseFailAlloc_5014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5014_, 0, v_a_5008_);
v___x_5013_ = v_reuseFailAlloc_5014_;
goto v_reusejp_5012_;
}
v_reusejp_5012_:
{
return v___x_5013_;
}
}
}
}
v___jp_4957_:
{
size_t v___x_4959_; size_t v___x_4960_; 
v___x_4959_ = ((size_t)1ULL);
v___x_4960_ = lean_usize_add(v_i_4950_, v___x_4959_);
v_i_4950_ = v___x_4960_;
v_b_4951_ = v_a_4958_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___boxed(lean_object* v_argsPacker_5016_, lean_object* v_as_5017_, lean_object* v_sz_5018_, lean_object* v_i_5019_, lean_object* v_b_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_){
_start:
{
size_t v_sz_boxed_5026_; size_t v_i_boxed_5027_; lean_object* v_res_5028_; 
v_sz_boxed_5026_ = lean_unbox_usize(v_sz_5018_);
lean_dec(v_sz_5018_);
v_i_boxed_5027_ = lean_unbox_usize(v_i_5019_);
lean_dec(v_i_5019_);
v_res_5028_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(v_argsPacker_5016_, v_as_5017_, v_sz_boxed_5026_, v_i_boxed_5027_, v_b_5020_, v___y_5021_, v___y_5022_, v___y_5023_, v___y_5024_);
lean_dec(v___y_5024_);
lean_dec_ref(v___y_5023_);
lean_dec(v___y_5022_);
lean_dec_ref(v___y_5021_);
lean_dec_ref(v_as_5017_);
lean_dec_ref(v_argsPacker_5016_);
return v_res_5028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_groupGoalsByFunction(lean_object* v_argsPacker_5029_, lean_object* v_numFuncs_5030_, lean_object* v_goals_5031_, lean_object* v_a_5032_, lean_object* v_a_5033_, lean_object* v_a_5034_, lean_object* v_a_5035_){
_start:
{
lean_object* v___x_5037_; lean_object* v_r_5038_; size_t v_sz_5039_; size_t v___x_5040_; lean_object* v___x_5041_; 
v___x_5037_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg___closed__0));
v_r_5038_ = lean_mk_array(v_numFuncs_5030_, v___x_5037_);
v_sz_5039_ = lean_array_size(v_goals_5031_);
v___x_5040_ = ((size_t)0ULL);
v___x_5041_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(v_argsPacker_5029_, v_goals_5031_, v_sz_5039_, v___x_5040_, v_r_5038_, v_a_5032_, v_a_5033_, v_a_5034_, v_a_5035_);
return v___x_5041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_groupGoalsByFunction___boxed(lean_object* v_argsPacker_5042_, lean_object* v_numFuncs_5043_, lean_object* v_goals_5044_, lean_object* v_a_5045_, lean_object* v_a_5046_, lean_object* v_a_5047_, lean_object* v_a_5048_, lean_object* v_a_5049_){
_start:
{
lean_object* v_res_5050_; 
v_res_5050_ = l_Lean_Elab_WF_groupGoalsByFunction(v_argsPacker_5042_, v_numFuncs_5043_, v_goals_5044_, v_a_5045_, v_a_5046_, v_a_5047_, v_a_5048_);
lean_dec(v_a_5048_);
lean_dec_ref(v_a_5047_);
lean_dec(v_a_5046_);
lean_dec_ref(v_a_5045_);
lean_dec_ref(v_goals_5044_);
lean_dec_ref(v_argsPacker_5042_);
return v_res_5050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(lean_object* v_t_5051_, lean_object* v___y_5052_){
_start:
{
lean_object* v___x_5054_; lean_object* v_infoState_5055_; uint8_t v_enabled_5056_; 
v___x_5054_ = lean_st_ref_get(v___y_5052_);
v_infoState_5055_ = lean_ctor_get(v___x_5054_, 7);
lean_inc_ref(v_infoState_5055_);
lean_dec(v___x_5054_);
v_enabled_5056_ = lean_ctor_get_uint8(v_infoState_5055_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5055_);
if (v_enabled_5056_ == 0)
{
lean_object* v___x_5057_; lean_object* v___x_5058_; 
lean_dec_ref(v_t_5051_);
v___x_5057_ = lean_box(0);
v___x_5058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5058_, 0, v___x_5057_);
return v___x_5058_;
}
else
{
lean_object* v___x_5059_; lean_object* v_infoState_5060_; lean_object* v_env_5061_; lean_object* v_nextMacroScope_5062_; lean_object* v_ngen_5063_; lean_object* v_auxDeclNGen_5064_; lean_object* v_traceState_5065_; lean_object* v_cache_5066_; lean_object* v_messages_5067_; lean_object* v_snapshotTasks_5068_; lean_object* v___x_5070_; uint8_t v_isShared_5071_; uint8_t v_isSharedCheck_5090_; 
v___x_5059_ = lean_st_ref_take(v___y_5052_);
v_infoState_5060_ = lean_ctor_get(v___x_5059_, 7);
v_env_5061_ = lean_ctor_get(v___x_5059_, 0);
v_nextMacroScope_5062_ = lean_ctor_get(v___x_5059_, 1);
v_ngen_5063_ = lean_ctor_get(v___x_5059_, 2);
v_auxDeclNGen_5064_ = lean_ctor_get(v___x_5059_, 3);
v_traceState_5065_ = lean_ctor_get(v___x_5059_, 4);
v_cache_5066_ = lean_ctor_get(v___x_5059_, 5);
v_messages_5067_ = lean_ctor_get(v___x_5059_, 6);
v_snapshotTasks_5068_ = lean_ctor_get(v___x_5059_, 8);
v_isSharedCheck_5090_ = !lean_is_exclusive(v___x_5059_);
if (v_isSharedCheck_5090_ == 0)
{
v___x_5070_ = v___x_5059_;
v_isShared_5071_ = v_isSharedCheck_5090_;
goto v_resetjp_5069_;
}
else
{
lean_inc(v_snapshotTasks_5068_);
lean_inc(v_infoState_5060_);
lean_inc(v_messages_5067_);
lean_inc(v_cache_5066_);
lean_inc(v_traceState_5065_);
lean_inc(v_auxDeclNGen_5064_);
lean_inc(v_ngen_5063_);
lean_inc(v_nextMacroScope_5062_);
lean_inc(v_env_5061_);
lean_dec(v___x_5059_);
v___x_5070_ = lean_box(0);
v_isShared_5071_ = v_isSharedCheck_5090_;
goto v_resetjp_5069_;
}
v_resetjp_5069_:
{
uint8_t v_enabled_5072_; lean_object* v_assignment_5073_; lean_object* v_lazyAssignment_5074_; lean_object* v_trees_5075_; lean_object* v___x_5077_; uint8_t v_isShared_5078_; uint8_t v_isSharedCheck_5089_; 
v_enabled_5072_ = lean_ctor_get_uint8(v_infoState_5060_, sizeof(void*)*3);
v_assignment_5073_ = lean_ctor_get(v_infoState_5060_, 0);
v_lazyAssignment_5074_ = lean_ctor_get(v_infoState_5060_, 1);
v_trees_5075_ = lean_ctor_get(v_infoState_5060_, 2);
v_isSharedCheck_5089_ = !lean_is_exclusive(v_infoState_5060_);
if (v_isSharedCheck_5089_ == 0)
{
v___x_5077_ = v_infoState_5060_;
v_isShared_5078_ = v_isSharedCheck_5089_;
goto v_resetjp_5076_;
}
else
{
lean_inc(v_trees_5075_);
lean_inc(v_lazyAssignment_5074_);
lean_inc(v_assignment_5073_);
lean_dec(v_infoState_5060_);
v___x_5077_ = lean_box(0);
v_isShared_5078_ = v_isSharedCheck_5089_;
goto v_resetjp_5076_;
}
v_resetjp_5076_:
{
lean_object* v___x_5079_; lean_object* v___x_5081_; 
v___x_5079_ = l_Lean_PersistentArray_push___redArg(v_trees_5075_, v_t_5051_);
if (v_isShared_5078_ == 0)
{
lean_ctor_set(v___x_5077_, 2, v___x_5079_);
v___x_5081_ = v___x_5077_;
goto v_reusejp_5080_;
}
else
{
lean_object* v_reuseFailAlloc_5088_; 
v_reuseFailAlloc_5088_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5088_, 0, v_assignment_5073_);
lean_ctor_set(v_reuseFailAlloc_5088_, 1, v_lazyAssignment_5074_);
lean_ctor_set(v_reuseFailAlloc_5088_, 2, v___x_5079_);
lean_ctor_set_uint8(v_reuseFailAlloc_5088_, sizeof(void*)*3, v_enabled_5072_);
v___x_5081_ = v_reuseFailAlloc_5088_;
goto v_reusejp_5080_;
}
v_reusejp_5080_:
{
lean_object* v___x_5083_; 
if (v_isShared_5071_ == 0)
{
lean_ctor_set(v___x_5070_, 7, v___x_5081_);
v___x_5083_ = v___x_5070_;
goto v_reusejp_5082_;
}
else
{
lean_object* v_reuseFailAlloc_5087_; 
v_reuseFailAlloc_5087_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5087_, 0, v_env_5061_);
lean_ctor_set(v_reuseFailAlloc_5087_, 1, v_nextMacroScope_5062_);
lean_ctor_set(v_reuseFailAlloc_5087_, 2, v_ngen_5063_);
lean_ctor_set(v_reuseFailAlloc_5087_, 3, v_auxDeclNGen_5064_);
lean_ctor_set(v_reuseFailAlloc_5087_, 4, v_traceState_5065_);
lean_ctor_set(v_reuseFailAlloc_5087_, 5, v_cache_5066_);
lean_ctor_set(v_reuseFailAlloc_5087_, 6, v_messages_5067_);
lean_ctor_set(v_reuseFailAlloc_5087_, 7, v___x_5081_);
lean_ctor_set(v_reuseFailAlloc_5087_, 8, v_snapshotTasks_5068_);
v___x_5083_ = v_reuseFailAlloc_5087_;
goto v_reusejp_5082_;
}
v_reusejp_5082_:
{
lean_object* v___x_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; 
v___x_5084_ = lean_st_ref_put(v___y_5052_, v___x_5083_);
v___x_5085_ = lean_box(0);
v___x_5086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5086_, 0, v___x_5085_);
return v___x_5086_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg___boxed(lean_object* v_t_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_){
_start:
{
lean_object* v_res_5094_; 
v_res_5094_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v_t_5091_, v___y_5092_);
lean_dec(v___y_5092_);
return v_res_5094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0(lean_object* v_t_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_, lean_object* v___y_5101_){
_start:
{
lean_object* v___x_5103_; 
v___x_5103_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v_t_5095_, v___y_5101_);
return v___x_5103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___boxed(lean_object* v_t_5104_, lean_object* v___y_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_){
_start:
{
lean_object* v_res_5112_; 
v_res_5112_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0(v_t_5104_, v___y_5105_, v___y_5106_, v___y_5107_, v___y_5108_, v___y_5109_, v___y_5110_);
lean_dec(v___y_5110_);
lean_dec_ref(v___y_5109_);
lean_dec(v___y_5108_);
lean_dec_ref(v___y_5107_);
lean_dec(v___y_5106_);
lean_dec_ref(v___y_5105_);
return v_res_5112_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(lean_object* v_e_5113_, lean_object* v___y_5114_){
_start:
{
uint8_t v___x_5116_; 
v___x_5116_ = l_Lean_Expr_hasMVar(v_e_5113_);
if (v___x_5116_ == 0)
{
lean_object* v___x_5117_; 
v___x_5117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5117_, 0, v_e_5113_);
return v___x_5117_;
}
else
{
lean_object* v___x_5118_; lean_object* v_mctx_5119_; lean_object* v___x_5120_; lean_object* v_fst_5121_; lean_object* v_snd_5122_; lean_object* v___x_5123_; lean_object* v_cache_5124_; lean_object* v_zetaDeltaFVarIds_5125_; lean_object* v_postponed_5126_; lean_object* v_diag_5127_; lean_object* v___x_5129_; uint8_t v_isShared_5130_; uint8_t v_isSharedCheck_5136_; 
v___x_5118_ = lean_st_ref_get(v___y_5114_);
v_mctx_5119_ = lean_ctor_get(v___x_5118_, 0);
lean_inc_ref(v_mctx_5119_);
lean_dec(v___x_5118_);
v___x_5120_ = l_Lean_instantiateMVarsCore(v_mctx_5119_, v_e_5113_);
v_fst_5121_ = lean_ctor_get(v___x_5120_, 0);
lean_inc(v_fst_5121_);
v_snd_5122_ = lean_ctor_get(v___x_5120_, 1);
lean_inc(v_snd_5122_);
lean_dec_ref(v___x_5120_);
v___x_5123_ = lean_st_ref_take(v___y_5114_);
v_cache_5124_ = lean_ctor_get(v___x_5123_, 1);
v_zetaDeltaFVarIds_5125_ = lean_ctor_get(v___x_5123_, 2);
v_postponed_5126_ = lean_ctor_get(v___x_5123_, 3);
v_diag_5127_ = lean_ctor_get(v___x_5123_, 4);
v_isSharedCheck_5136_ = !lean_is_exclusive(v___x_5123_);
if (v_isSharedCheck_5136_ == 0)
{
lean_object* v_unused_5137_; 
v_unused_5137_ = lean_ctor_get(v___x_5123_, 0);
lean_dec(v_unused_5137_);
v___x_5129_ = v___x_5123_;
v_isShared_5130_ = v_isSharedCheck_5136_;
goto v_resetjp_5128_;
}
else
{
lean_inc(v_diag_5127_);
lean_inc(v_postponed_5126_);
lean_inc(v_zetaDeltaFVarIds_5125_);
lean_inc(v_cache_5124_);
lean_dec(v___x_5123_);
v___x_5129_ = lean_box(0);
v_isShared_5130_ = v_isSharedCheck_5136_;
goto v_resetjp_5128_;
}
v_resetjp_5128_:
{
lean_object* v___x_5132_; 
if (v_isShared_5130_ == 0)
{
lean_ctor_set(v___x_5129_, 0, v_snd_5122_);
v___x_5132_ = v___x_5129_;
goto v_reusejp_5131_;
}
else
{
lean_object* v_reuseFailAlloc_5135_; 
v_reuseFailAlloc_5135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5135_, 0, v_snd_5122_);
lean_ctor_set(v_reuseFailAlloc_5135_, 1, v_cache_5124_);
lean_ctor_set(v_reuseFailAlloc_5135_, 2, v_zetaDeltaFVarIds_5125_);
lean_ctor_set(v_reuseFailAlloc_5135_, 3, v_postponed_5126_);
lean_ctor_set(v_reuseFailAlloc_5135_, 4, v_diag_5127_);
v___x_5132_ = v_reuseFailAlloc_5135_;
goto v_reusejp_5131_;
}
v_reusejp_5131_:
{
lean_object* v___x_5133_; lean_object* v___x_5134_; 
v___x_5133_ = lean_st_ref_put(v___y_5114_, v___x_5132_);
v___x_5134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5134_, 0, v_fst_5121_);
return v___x_5134_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg___boxed(lean_object* v_e_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_){
_start:
{
lean_object* v_res_5141_; 
v_res_5141_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_e_5138_, v___y_5139_);
lean_dec(v___y_5139_);
return v_res_5141_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7(lean_object* v_e_5142_, lean_object* v___y_5143_, lean_object* v___y_5144_, lean_object* v___y_5145_, lean_object* v___y_5146_){
_start:
{
lean_object* v___x_5148_; 
v___x_5148_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_e_5142_, v___y_5144_);
return v___x_5148_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___boxed(lean_object* v_e_5149_, lean_object* v___y_5150_, lean_object* v___y_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_){
_start:
{
lean_object* v_res_5155_; 
v_res_5155_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7(v_e_5149_, v___y_5150_, v___y_5151_, v___y_5152_, v___y_5153_);
lean_dec(v___y_5153_);
lean_dec_ref(v___y_5152_);
lean_dec(v___y_5151_);
lean_dec_ref(v___y_5150_);
return v_res_5155_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(lean_object* v_as_5156_, size_t v_i_5157_, size_t v_stop_5158_, lean_object* v_b_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_, lean_object* v___y_5165_){
_start:
{
uint8_t v___x_5167_; 
v___x_5167_ = lean_usize_dec_eq(v_i_5157_, v_stop_5158_);
if (v___x_5167_ == 0)
{
lean_object* v___x_5168_; lean_object* v___x_5169_; lean_object* v___x_5170_; 
v___x_5168_ = lean_array_uget_borrowed(v_as_5156_, v_i_5157_);
lean_inc(v___x_5168_);
v___x_5169_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_5169_, 0, v___x_5168_);
v___x_5170_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v___x_5169_, v___y_5165_);
if (lean_obj_tag(v___x_5170_) == 0)
{
lean_object* v_a_5171_; size_t v___x_5172_; size_t v___x_5173_; 
v_a_5171_ = lean_ctor_get(v___x_5170_, 0);
lean_inc(v_a_5171_);
lean_dec_ref_known(v___x_5170_, 1);
v___x_5172_ = ((size_t)1ULL);
v___x_5173_ = lean_usize_add(v_i_5157_, v___x_5172_);
v_i_5157_ = v___x_5173_;
v_b_5159_ = v_a_5171_;
goto _start;
}
else
{
return v___x_5170_;
}
}
else
{
lean_object* v___x_5175_; 
v___x_5175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5175_, 0, v_b_5159_);
return v___x_5175_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4___boxed(lean_object* v_as_5176_, lean_object* v_i_5177_, lean_object* v_stop_5178_, lean_object* v_b_5179_, lean_object* v___y_5180_, lean_object* v___y_5181_, lean_object* v___y_5182_, lean_object* v___y_5183_, lean_object* v___y_5184_, lean_object* v___y_5185_, lean_object* v___y_5186_){
_start:
{
size_t v_i_boxed_5187_; size_t v_stop_boxed_5188_; lean_object* v_res_5189_; 
v_i_boxed_5187_ = lean_unbox_usize(v_i_5177_);
lean_dec(v_i_5177_);
v_stop_boxed_5188_ = lean_unbox_usize(v_stop_5178_);
lean_dec(v_stop_5178_);
v_res_5189_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v_as_5176_, v_i_boxed_5187_, v_stop_boxed_5188_, v_b_5179_, v___y_5180_, v___y_5181_, v___y_5182_, v___y_5183_, v___y_5184_, v___y_5185_);
lean_dec(v___y_5185_);
lean_dec_ref(v___y_5184_);
lean_dec(v___y_5183_);
lean_dec_ref(v___y_5182_);
lean_dec(v___y_5181_);
lean_dec_ref(v___y_5180_);
lean_dec_ref(v_as_5176_);
return v_res_5189_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; 
v___x_5190_ = lean_unsigned_to_nat(32u);
v___x_5191_ = lean_mk_empty_array_with_capacity(v___x_5190_);
v___x_5192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5192_, 0, v___x_5191_);
return v___x_5192_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; 
v___x_5193_ = ((size_t)5ULL);
v___x_5194_ = lean_unsigned_to_nat(0u);
v___x_5195_ = lean_unsigned_to_nat(32u);
v___x_5196_ = lean_mk_empty_array_with_capacity(v___x_5195_);
v___x_5197_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0);
v___x_5198_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5198_, 0, v___x_5197_);
lean_ctor_set(v___x_5198_, 1, v___x_5196_);
lean_ctor_set(v___x_5198_, 2, v___x_5194_);
lean_ctor_set(v___x_5198_, 3, v___x_5194_);
lean_ctor_set_usize(v___x_5198_, 4, v___x_5193_);
return v___x_5198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(lean_object* v___y_5199_){
_start:
{
lean_object* v___x_5201_; lean_object* v_infoState_5202_; lean_object* v_trees_5203_; lean_object* v___x_5204_; lean_object* v_infoState_5205_; lean_object* v_env_5206_; lean_object* v_nextMacroScope_5207_; lean_object* v_ngen_5208_; lean_object* v_auxDeclNGen_5209_; lean_object* v_traceState_5210_; lean_object* v_cache_5211_; lean_object* v_messages_5212_; lean_object* v_snapshotTasks_5213_; lean_object* v___x_5215_; uint8_t v_isShared_5216_; uint8_t v_isSharedCheck_5234_; 
v___x_5201_ = lean_st_ref_get(v___y_5199_);
v_infoState_5202_ = lean_ctor_get(v___x_5201_, 7);
lean_inc_ref(v_infoState_5202_);
lean_dec(v___x_5201_);
v_trees_5203_ = lean_ctor_get(v_infoState_5202_, 2);
lean_inc_ref(v_trees_5203_);
lean_dec_ref(v_infoState_5202_);
v___x_5204_ = lean_st_ref_take(v___y_5199_);
v_infoState_5205_ = lean_ctor_get(v___x_5204_, 7);
v_env_5206_ = lean_ctor_get(v___x_5204_, 0);
v_nextMacroScope_5207_ = lean_ctor_get(v___x_5204_, 1);
v_ngen_5208_ = lean_ctor_get(v___x_5204_, 2);
v_auxDeclNGen_5209_ = lean_ctor_get(v___x_5204_, 3);
v_traceState_5210_ = lean_ctor_get(v___x_5204_, 4);
v_cache_5211_ = lean_ctor_get(v___x_5204_, 5);
v_messages_5212_ = lean_ctor_get(v___x_5204_, 6);
v_snapshotTasks_5213_ = lean_ctor_get(v___x_5204_, 8);
v_isSharedCheck_5234_ = !lean_is_exclusive(v___x_5204_);
if (v_isSharedCheck_5234_ == 0)
{
v___x_5215_ = v___x_5204_;
v_isShared_5216_ = v_isSharedCheck_5234_;
goto v_resetjp_5214_;
}
else
{
lean_inc(v_snapshotTasks_5213_);
lean_inc(v_infoState_5205_);
lean_inc(v_messages_5212_);
lean_inc(v_cache_5211_);
lean_inc(v_traceState_5210_);
lean_inc(v_auxDeclNGen_5209_);
lean_inc(v_ngen_5208_);
lean_inc(v_nextMacroScope_5207_);
lean_inc(v_env_5206_);
lean_dec(v___x_5204_);
v___x_5215_ = lean_box(0);
v_isShared_5216_ = v_isSharedCheck_5234_;
goto v_resetjp_5214_;
}
v_resetjp_5214_:
{
uint8_t v_enabled_5217_; lean_object* v_assignment_5218_; lean_object* v_lazyAssignment_5219_; lean_object* v___x_5221_; uint8_t v_isShared_5222_; uint8_t v_isSharedCheck_5232_; 
v_enabled_5217_ = lean_ctor_get_uint8(v_infoState_5205_, sizeof(void*)*3);
v_assignment_5218_ = lean_ctor_get(v_infoState_5205_, 0);
v_lazyAssignment_5219_ = lean_ctor_get(v_infoState_5205_, 1);
v_isSharedCheck_5232_ = !lean_is_exclusive(v_infoState_5205_);
if (v_isSharedCheck_5232_ == 0)
{
lean_object* v_unused_5233_; 
v_unused_5233_ = lean_ctor_get(v_infoState_5205_, 2);
lean_dec(v_unused_5233_);
v___x_5221_ = v_infoState_5205_;
v_isShared_5222_ = v_isSharedCheck_5232_;
goto v_resetjp_5220_;
}
else
{
lean_inc(v_lazyAssignment_5219_);
lean_inc(v_assignment_5218_);
lean_dec(v_infoState_5205_);
v___x_5221_ = lean_box(0);
v_isShared_5222_ = v_isSharedCheck_5232_;
goto v_resetjp_5220_;
}
v_resetjp_5220_:
{
lean_object* v___x_5223_; lean_object* v___x_5225_; 
v___x_5223_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1);
if (v_isShared_5222_ == 0)
{
lean_ctor_set(v___x_5221_, 2, v___x_5223_);
v___x_5225_ = v___x_5221_;
goto v_reusejp_5224_;
}
else
{
lean_object* v_reuseFailAlloc_5231_; 
v_reuseFailAlloc_5231_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5231_, 0, v_assignment_5218_);
lean_ctor_set(v_reuseFailAlloc_5231_, 1, v_lazyAssignment_5219_);
lean_ctor_set(v_reuseFailAlloc_5231_, 2, v___x_5223_);
lean_ctor_set_uint8(v_reuseFailAlloc_5231_, sizeof(void*)*3, v_enabled_5217_);
v___x_5225_ = v_reuseFailAlloc_5231_;
goto v_reusejp_5224_;
}
v_reusejp_5224_:
{
lean_object* v___x_5227_; 
if (v_isShared_5216_ == 0)
{
lean_ctor_set(v___x_5215_, 7, v___x_5225_);
v___x_5227_ = v___x_5215_;
goto v_reusejp_5226_;
}
else
{
lean_object* v_reuseFailAlloc_5230_; 
v_reuseFailAlloc_5230_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5230_, 0, v_env_5206_);
lean_ctor_set(v_reuseFailAlloc_5230_, 1, v_nextMacroScope_5207_);
lean_ctor_set(v_reuseFailAlloc_5230_, 2, v_ngen_5208_);
lean_ctor_set(v_reuseFailAlloc_5230_, 3, v_auxDeclNGen_5209_);
lean_ctor_set(v_reuseFailAlloc_5230_, 4, v_traceState_5210_);
lean_ctor_set(v_reuseFailAlloc_5230_, 5, v_cache_5211_);
lean_ctor_set(v_reuseFailAlloc_5230_, 6, v_messages_5212_);
lean_ctor_set(v_reuseFailAlloc_5230_, 7, v___x_5225_);
lean_ctor_set(v_reuseFailAlloc_5230_, 8, v_snapshotTasks_5213_);
v___x_5227_ = v_reuseFailAlloc_5230_;
goto v_reusejp_5226_;
}
v_reusejp_5226_:
{
lean_object* v___x_5228_; lean_object* v___x_5229_; 
v___x_5228_ = lean_st_ref_put(v___y_5199_, v___x_5227_);
v___x_5229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5229_, 0, v_trees_5203_);
return v___x_5229_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___boxed(lean_object* v___y_5235_, lean_object* v___y_5236_){
_start:
{
lean_object* v_res_5237_; 
v_res_5237_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_5235_);
lean_dec(v___y_5235_);
return v_res_5237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(lean_object* v___y_5238_, lean_object* v_mkInfoTree_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_, lean_object* v_a_5247_, lean_object* v_a_x3f_5248_){
_start:
{
lean_object* v___x_5250_; lean_object* v_infoState_5251_; lean_object* v_trees_5252_; lean_object* v___x_5253_; 
v___x_5250_ = lean_st_ref_get(v___y_5238_);
v_infoState_5251_ = lean_ctor_get(v___x_5250_, 7);
lean_inc_ref(v_infoState_5251_);
lean_dec(v___x_5250_);
v_trees_5252_ = lean_ctor_get(v_infoState_5251_, 2);
lean_inc_ref(v_trees_5252_);
lean_dec_ref(v_infoState_5251_);
lean_inc(v___y_5238_);
lean_inc_ref(v___y_5246_);
lean_inc(v___y_5245_);
lean_inc_ref(v___y_5244_);
lean_inc(v___y_5243_);
lean_inc_ref(v___y_5242_);
lean_inc(v___y_5241_);
lean_inc_ref(v___y_5240_);
v___x_5253_ = lean_apply_10(v_mkInfoTree_5239_, v_trees_5252_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5238_, lean_box(0));
if (lean_obj_tag(v___x_5253_) == 0)
{
lean_object* v_a_5254_; lean_object* v___x_5256_; uint8_t v_isShared_5257_; uint8_t v_isSharedCheck_5292_; 
v_a_5254_ = lean_ctor_get(v___x_5253_, 0);
v_isSharedCheck_5292_ = !lean_is_exclusive(v___x_5253_);
if (v_isSharedCheck_5292_ == 0)
{
v___x_5256_ = v___x_5253_;
v_isShared_5257_ = v_isSharedCheck_5292_;
goto v_resetjp_5255_;
}
else
{
lean_inc(v_a_5254_);
lean_dec(v___x_5253_);
v___x_5256_ = lean_box(0);
v_isShared_5257_ = v_isSharedCheck_5292_;
goto v_resetjp_5255_;
}
v_resetjp_5255_:
{
lean_object* v___x_5258_; lean_object* v_infoState_5259_; lean_object* v_env_5260_; lean_object* v_nextMacroScope_5261_; lean_object* v_ngen_5262_; lean_object* v_auxDeclNGen_5263_; lean_object* v_traceState_5264_; lean_object* v_cache_5265_; lean_object* v_messages_5266_; lean_object* v_snapshotTasks_5267_; lean_object* v___x_5269_; uint8_t v_isShared_5270_; uint8_t v_isSharedCheck_5291_; 
v___x_5258_ = lean_st_ref_take(v___y_5238_);
v_infoState_5259_ = lean_ctor_get(v___x_5258_, 7);
v_env_5260_ = lean_ctor_get(v___x_5258_, 0);
v_nextMacroScope_5261_ = lean_ctor_get(v___x_5258_, 1);
v_ngen_5262_ = lean_ctor_get(v___x_5258_, 2);
v_auxDeclNGen_5263_ = lean_ctor_get(v___x_5258_, 3);
v_traceState_5264_ = lean_ctor_get(v___x_5258_, 4);
v_cache_5265_ = lean_ctor_get(v___x_5258_, 5);
v_messages_5266_ = lean_ctor_get(v___x_5258_, 6);
v_snapshotTasks_5267_ = lean_ctor_get(v___x_5258_, 8);
v_isSharedCheck_5291_ = !lean_is_exclusive(v___x_5258_);
if (v_isSharedCheck_5291_ == 0)
{
v___x_5269_ = v___x_5258_;
v_isShared_5270_ = v_isSharedCheck_5291_;
goto v_resetjp_5268_;
}
else
{
lean_inc(v_snapshotTasks_5267_);
lean_inc(v_infoState_5259_);
lean_inc(v_messages_5266_);
lean_inc(v_cache_5265_);
lean_inc(v_traceState_5264_);
lean_inc(v_auxDeclNGen_5263_);
lean_inc(v_ngen_5262_);
lean_inc(v_nextMacroScope_5261_);
lean_inc(v_env_5260_);
lean_dec(v___x_5258_);
v___x_5269_ = lean_box(0);
v_isShared_5270_ = v_isSharedCheck_5291_;
goto v_resetjp_5268_;
}
v_resetjp_5268_:
{
uint8_t v_enabled_5271_; lean_object* v_assignment_5272_; lean_object* v_lazyAssignment_5273_; lean_object* v___x_5275_; uint8_t v_isShared_5276_; uint8_t v_isSharedCheck_5289_; 
v_enabled_5271_ = lean_ctor_get_uint8(v_infoState_5259_, sizeof(void*)*3);
v_assignment_5272_ = lean_ctor_get(v_infoState_5259_, 0);
v_lazyAssignment_5273_ = lean_ctor_get(v_infoState_5259_, 1);
v_isSharedCheck_5289_ = !lean_is_exclusive(v_infoState_5259_);
if (v_isSharedCheck_5289_ == 0)
{
lean_object* v_unused_5290_; 
v_unused_5290_ = lean_ctor_get(v_infoState_5259_, 2);
lean_dec(v_unused_5290_);
v___x_5275_ = v_infoState_5259_;
v_isShared_5276_ = v_isSharedCheck_5289_;
goto v_resetjp_5274_;
}
else
{
lean_inc(v_lazyAssignment_5273_);
lean_inc(v_assignment_5272_);
lean_dec(v_infoState_5259_);
v___x_5275_ = lean_box(0);
v_isShared_5276_ = v_isSharedCheck_5289_;
goto v_resetjp_5274_;
}
v_resetjp_5274_:
{
lean_object* v___x_5277_; lean_object* v___x_5279_; 
v___x_5277_ = l_Lean_PersistentArray_push___redArg(v_a_5247_, v_a_5254_);
if (v_isShared_5276_ == 0)
{
lean_ctor_set(v___x_5275_, 2, v___x_5277_);
v___x_5279_ = v___x_5275_;
goto v_reusejp_5278_;
}
else
{
lean_object* v_reuseFailAlloc_5288_; 
v_reuseFailAlloc_5288_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5288_, 0, v_assignment_5272_);
lean_ctor_set(v_reuseFailAlloc_5288_, 1, v_lazyAssignment_5273_);
lean_ctor_set(v_reuseFailAlloc_5288_, 2, v___x_5277_);
lean_ctor_set_uint8(v_reuseFailAlloc_5288_, sizeof(void*)*3, v_enabled_5271_);
v___x_5279_ = v_reuseFailAlloc_5288_;
goto v_reusejp_5278_;
}
v_reusejp_5278_:
{
lean_object* v___x_5281_; 
if (v_isShared_5270_ == 0)
{
lean_ctor_set(v___x_5269_, 7, v___x_5279_);
v___x_5281_ = v___x_5269_;
goto v_reusejp_5280_;
}
else
{
lean_object* v_reuseFailAlloc_5287_; 
v_reuseFailAlloc_5287_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5287_, 0, v_env_5260_);
lean_ctor_set(v_reuseFailAlloc_5287_, 1, v_nextMacroScope_5261_);
lean_ctor_set(v_reuseFailAlloc_5287_, 2, v_ngen_5262_);
lean_ctor_set(v_reuseFailAlloc_5287_, 3, v_auxDeclNGen_5263_);
lean_ctor_set(v_reuseFailAlloc_5287_, 4, v_traceState_5264_);
lean_ctor_set(v_reuseFailAlloc_5287_, 5, v_cache_5265_);
lean_ctor_set(v_reuseFailAlloc_5287_, 6, v_messages_5266_);
lean_ctor_set(v_reuseFailAlloc_5287_, 7, v___x_5279_);
lean_ctor_set(v_reuseFailAlloc_5287_, 8, v_snapshotTasks_5267_);
v___x_5281_ = v_reuseFailAlloc_5287_;
goto v_reusejp_5280_;
}
v_reusejp_5280_:
{
lean_object* v___x_5282_; lean_object* v___x_5283_; lean_object* v___x_5285_; 
v___x_5282_ = lean_st_ref_put(v___y_5238_, v___x_5281_);
v___x_5283_ = lean_box(0);
if (v_isShared_5257_ == 0)
{
lean_ctor_set(v___x_5256_, 0, v___x_5283_);
v___x_5285_ = v___x_5256_;
goto v_reusejp_5284_;
}
else
{
lean_object* v_reuseFailAlloc_5286_; 
v_reuseFailAlloc_5286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5286_, 0, v___x_5283_);
v___x_5285_ = v_reuseFailAlloc_5286_;
goto v_reusejp_5284_;
}
v_reusejp_5284_:
{
return v___x_5285_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5293_; lean_object* v___x_5295_; uint8_t v_isShared_5296_; uint8_t v_isSharedCheck_5300_; 
lean_dec_ref(v_a_5247_);
v_a_5293_ = lean_ctor_get(v___x_5253_, 0);
v_isSharedCheck_5300_ = !lean_is_exclusive(v___x_5253_);
if (v_isSharedCheck_5300_ == 0)
{
v___x_5295_ = v___x_5253_;
v_isShared_5296_ = v_isSharedCheck_5300_;
goto v_resetjp_5294_;
}
else
{
lean_inc(v_a_5293_);
lean_dec(v___x_5253_);
v___x_5295_ = lean_box(0);
v_isShared_5296_ = v_isSharedCheck_5300_;
goto v_resetjp_5294_;
}
v_resetjp_5294_:
{
lean_object* v___x_5298_; 
if (v_isShared_5296_ == 0)
{
v___x_5298_ = v___x_5295_;
goto v_reusejp_5297_;
}
else
{
lean_object* v_reuseFailAlloc_5299_; 
v_reuseFailAlloc_5299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5299_, 0, v_a_5293_);
v___x_5298_ = v_reuseFailAlloc_5299_;
goto v_reusejp_5297_;
}
v_reusejp_5297_:
{
return v___x_5298_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0___boxed(lean_object* v___y_5301_, lean_object* v_mkInfoTree_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_, lean_object* v___y_5309_, lean_object* v_a_5310_, lean_object* v_a_x3f_5311_, lean_object* v___y_5312_){
_start:
{
lean_object* v_res_5313_; 
v_res_5313_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5301_, v_mkInfoTree_5302_, v___y_5303_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_, v___y_5308_, v___y_5309_, v_a_5310_, v_a_x3f_5311_);
lean_dec(v_a_x3f_5311_);
lean_dec_ref(v___y_5309_);
lean_dec(v___y_5308_);
lean_dec_ref(v___y_5307_);
lean_dec(v___y_5306_);
lean_dec_ref(v___y_5305_);
lean_dec(v___y_5304_);
lean_dec_ref(v___y_5303_);
lean_dec(v___y_5301_);
return v_res_5313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(lean_object* v_x_5314_, lean_object* v_mkInfoTree_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_){
_start:
{
lean_object* v___x_5325_; lean_object* v_infoState_5326_; uint8_t v_enabled_5327_; 
v___x_5325_ = lean_st_ref_get(v___y_5323_);
v_infoState_5326_ = lean_ctor_get(v___x_5325_, 7);
lean_inc_ref(v_infoState_5326_);
lean_dec(v___x_5325_);
v_enabled_5327_ = lean_ctor_get_uint8(v_infoState_5326_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5326_);
if (v_enabled_5327_ == 0)
{
lean_object* v___x_5328_; 
lean_dec_ref(v_mkInfoTree_5315_);
lean_inc(v___y_5323_);
lean_inc_ref(v___y_5322_);
lean_inc(v___y_5321_);
lean_inc_ref(v___y_5320_);
lean_inc(v___y_5319_);
lean_inc_ref(v___y_5318_);
lean_inc(v___y_5317_);
lean_inc_ref(v___y_5316_);
v___x_5328_ = lean_apply_9(v_x_5314_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_, v___y_5323_, lean_box(0));
return v___x_5328_;
}
else
{
lean_object* v___x_5329_; lean_object* v_a_5330_; lean_object* v_r_5331_; 
v___x_5329_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_5323_);
v_a_5330_ = lean_ctor_get(v___x_5329_, 0);
lean_inc(v_a_5330_);
lean_dec_ref(v___x_5329_);
lean_inc(v___y_5323_);
lean_inc_ref(v___y_5322_);
lean_inc(v___y_5321_);
lean_inc_ref(v___y_5320_);
lean_inc(v___y_5319_);
lean_inc_ref(v___y_5318_);
lean_inc(v___y_5317_);
lean_inc_ref(v___y_5316_);
v_r_5331_ = lean_apply_9(v_x_5314_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_, v___y_5323_, lean_box(0));
if (lean_obj_tag(v_r_5331_) == 0)
{
lean_object* v_a_5332_; lean_object* v___x_5334_; uint8_t v_isShared_5335_; uint8_t v_isSharedCheck_5356_; 
v_a_5332_ = lean_ctor_get(v_r_5331_, 0);
v_isSharedCheck_5356_ = !lean_is_exclusive(v_r_5331_);
if (v_isSharedCheck_5356_ == 0)
{
v___x_5334_ = v_r_5331_;
v_isShared_5335_ = v_isSharedCheck_5356_;
goto v_resetjp_5333_;
}
else
{
lean_inc(v_a_5332_);
lean_dec(v_r_5331_);
v___x_5334_ = lean_box(0);
v_isShared_5335_ = v_isSharedCheck_5356_;
goto v_resetjp_5333_;
}
v_resetjp_5333_:
{
lean_object* v___x_5337_; 
lean_inc(v_a_5332_);
if (v_isShared_5335_ == 0)
{
lean_ctor_set_tag(v___x_5334_, 1);
v___x_5337_ = v___x_5334_;
goto v_reusejp_5336_;
}
else
{
lean_object* v_reuseFailAlloc_5355_; 
v_reuseFailAlloc_5355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5355_, 0, v_a_5332_);
v___x_5337_ = v_reuseFailAlloc_5355_;
goto v_reusejp_5336_;
}
v_reusejp_5336_:
{
lean_object* v___x_5338_; 
v___x_5338_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5323_, v_mkInfoTree_5315_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_, v_a_5330_, v___x_5337_);
lean_dec_ref(v___x_5337_);
if (lean_obj_tag(v___x_5338_) == 0)
{
lean_object* v___x_5340_; uint8_t v_isShared_5341_; uint8_t v_isSharedCheck_5345_; 
v_isSharedCheck_5345_ = !lean_is_exclusive(v___x_5338_);
if (v_isSharedCheck_5345_ == 0)
{
lean_object* v_unused_5346_; 
v_unused_5346_ = lean_ctor_get(v___x_5338_, 0);
lean_dec(v_unused_5346_);
v___x_5340_ = v___x_5338_;
v_isShared_5341_ = v_isSharedCheck_5345_;
goto v_resetjp_5339_;
}
else
{
lean_dec(v___x_5338_);
v___x_5340_ = lean_box(0);
v_isShared_5341_ = v_isSharedCheck_5345_;
goto v_resetjp_5339_;
}
v_resetjp_5339_:
{
lean_object* v___x_5343_; 
if (v_isShared_5341_ == 0)
{
lean_ctor_set(v___x_5340_, 0, v_a_5332_);
v___x_5343_ = v___x_5340_;
goto v_reusejp_5342_;
}
else
{
lean_object* v_reuseFailAlloc_5344_; 
v_reuseFailAlloc_5344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5344_, 0, v_a_5332_);
v___x_5343_ = v_reuseFailAlloc_5344_;
goto v_reusejp_5342_;
}
v_reusejp_5342_:
{
return v___x_5343_;
}
}
}
else
{
lean_object* v_a_5347_; lean_object* v___x_5349_; uint8_t v_isShared_5350_; uint8_t v_isSharedCheck_5354_; 
lean_dec(v_a_5332_);
v_a_5347_ = lean_ctor_get(v___x_5338_, 0);
v_isSharedCheck_5354_ = !lean_is_exclusive(v___x_5338_);
if (v_isSharedCheck_5354_ == 0)
{
v___x_5349_ = v___x_5338_;
v_isShared_5350_ = v_isSharedCheck_5354_;
goto v_resetjp_5348_;
}
else
{
lean_inc(v_a_5347_);
lean_dec(v___x_5338_);
v___x_5349_ = lean_box(0);
v_isShared_5350_ = v_isSharedCheck_5354_;
goto v_resetjp_5348_;
}
v_resetjp_5348_:
{
lean_object* v___x_5352_; 
if (v_isShared_5350_ == 0)
{
v___x_5352_ = v___x_5349_;
goto v_reusejp_5351_;
}
else
{
lean_object* v_reuseFailAlloc_5353_; 
v_reuseFailAlloc_5353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5353_, 0, v_a_5347_);
v___x_5352_ = v_reuseFailAlloc_5353_;
goto v_reusejp_5351_;
}
v_reusejp_5351_:
{
return v___x_5352_;
}
}
}
}
}
}
else
{
lean_object* v_a_5357_; lean_object* v___x_5358_; lean_object* v___x_5359_; 
v_a_5357_ = lean_ctor_get(v_r_5331_, 0);
lean_inc(v_a_5357_);
lean_dec_ref_known(v_r_5331_, 1);
v___x_5358_ = lean_box(0);
v___x_5359_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5323_, v_mkInfoTree_5315_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_, v_a_5330_, v___x_5358_);
if (lean_obj_tag(v___x_5359_) == 0)
{
lean_object* v___x_5361_; uint8_t v_isShared_5362_; uint8_t v_isSharedCheck_5366_; 
v_isSharedCheck_5366_ = !lean_is_exclusive(v___x_5359_);
if (v_isSharedCheck_5366_ == 0)
{
lean_object* v_unused_5367_; 
v_unused_5367_ = lean_ctor_get(v___x_5359_, 0);
lean_dec(v_unused_5367_);
v___x_5361_ = v___x_5359_;
v_isShared_5362_ = v_isSharedCheck_5366_;
goto v_resetjp_5360_;
}
else
{
lean_dec(v___x_5359_);
v___x_5361_ = lean_box(0);
v_isShared_5362_ = v_isSharedCheck_5366_;
goto v_resetjp_5360_;
}
v_resetjp_5360_:
{
lean_object* v___x_5364_; 
if (v_isShared_5362_ == 0)
{
lean_ctor_set_tag(v___x_5361_, 1);
lean_ctor_set(v___x_5361_, 0, v_a_5357_);
v___x_5364_ = v___x_5361_;
goto v_reusejp_5363_;
}
else
{
lean_object* v_reuseFailAlloc_5365_; 
v_reuseFailAlloc_5365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5365_, 0, v_a_5357_);
v___x_5364_ = v_reuseFailAlloc_5365_;
goto v_reusejp_5363_;
}
v_reusejp_5363_:
{
return v___x_5364_;
}
}
}
else
{
lean_object* v_a_5368_; lean_object* v___x_5370_; uint8_t v_isShared_5371_; uint8_t v_isSharedCheck_5375_; 
lean_dec(v_a_5357_);
v_a_5368_ = lean_ctor_get(v___x_5359_, 0);
v_isSharedCheck_5375_ = !lean_is_exclusive(v___x_5359_);
if (v_isSharedCheck_5375_ == 0)
{
v___x_5370_ = v___x_5359_;
v_isShared_5371_ = v_isSharedCheck_5375_;
goto v_resetjp_5369_;
}
else
{
lean_inc(v_a_5368_);
lean_dec(v___x_5359_);
v___x_5370_ = lean_box(0);
v_isShared_5371_ = v_isSharedCheck_5375_;
goto v_resetjp_5369_;
}
v_resetjp_5369_:
{
lean_object* v___x_5373_; 
if (v_isShared_5371_ == 0)
{
v___x_5373_ = v___x_5370_;
goto v_reusejp_5372_;
}
else
{
lean_object* v_reuseFailAlloc_5374_; 
v_reuseFailAlloc_5374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5374_, 0, v_a_5368_);
v___x_5373_ = v_reuseFailAlloc_5374_;
goto v_reusejp_5372_;
}
v_reusejp_5372_:
{
return v___x_5373_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___boxed(lean_object* v_x_5376_, lean_object* v_mkInfoTree_5377_, lean_object* v___y_5378_, lean_object* v___y_5379_, lean_object* v___y_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_){
_start:
{
lean_object* v_res_5387_; 
v_res_5387_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v_x_5376_, v_mkInfoTree_5377_, v___y_5378_, v___y_5379_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_, v___y_5385_);
lean_dec(v___y_5385_);
lean_dec_ref(v___y_5384_);
lean_dec(v___y_5383_);
lean_dec_ref(v___y_5382_);
lean_dec(v___y_5381_);
lean_dec_ref(v___y_5380_);
lean_dec(v___y_5379_);
lean_dec_ref(v___y_5378_);
return v_res_5387_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1(lean_object* v_a_5388_, lean_object* v_trees_5389_, lean_object* v___y_5390_, lean_object* v___y_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_, lean_object* v___y_5394_, lean_object* v___y_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_){
_start:
{
lean_object* v___x_5399_; 
lean_inc(v___y_5397_);
lean_inc_ref(v___y_5396_);
lean_inc(v___y_5395_);
lean_inc_ref(v___y_5394_);
lean_inc(v___y_5393_);
lean_inc_ref(v___y_5392_);
lean_inc(v___y_5391_);
lean_inc_ref(v___y_5390_);
v___x_5399_ = lean_apply_9(v_a_5388_, v___y_5390_, v___y_5391_, v___y_5392_, v___y_5393_, v___y_5394_, v___y_5395_, v___y_5396_, v___y_5397_, lean_box(0));
if (lean_obj_tag(v___x_5399_) == 0)
{
lean_object* v_a_5400_; lean_object* v___x_5402_; uint8_t v_isShared_5403_; uint8_t v_isSharedCheck_5408_; 
v_a_5400_ = lean_ctor_get(v___x_5399_, 0);
v_isSharedCheck_5408_ = !lean_is_exclusive(v___x_5399_);
if (v_isSharedCheck_5408_ == 0)
{
v___x_5402_ = v___x_5399_;
v_isShared_5403_ = v_isSharedCheck_5408_;
goto v_resetjp_5401_;
}
else
{
lean_inc(v_a_5400_);
lean_dec(v___x_5399_);
v___x_5402_ = lean_box(0);
v_isShared_5403_ = v_isSharedCheck_5408_;
goto v_resetjp_5401_;
}
v_resetjp_5401_:
{
lean_object* v___x_5404_; lean_object* v___x_5406_; 
v___x_5404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5404_, 0, v_a_5400_);
lean_ctor_set(v___x_5404_, 1, v_trees_5389_);
if (v_isShared_5403_ == 0)
{
lean_ctor_set(v___x_5402_, 0, v___x_5404_);
v___x_5406_ = v___x_5402_;
goto v_reusejp_5405_;
}
else
{
lean_object* v_reuseFailAlloc_5407_; 
v_reuseFailAlloc_5407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5407_, 0, v___x_5404_);
v___x_5406_ = v_reuseFailAlloc_5407_;
goto v_reusejp_5405_;
}
v_reusejp_5405_:
{
return v___x_5406_;
}
}
}
else
{
lean_object* v_a_5409_; lean_object* v___x_5411_; uint8_t v_isShared_5412_; uint8_t v_isSharedCheck_5416_; 
lean_dec_ref(v_trees_5389_);
v_a_5409_ = lean_ctor_get(v___x_5399_, 0);
v_isSharedCheck_5416_ = !lean_is_exclusive(v___x_5399_);
if (v_isSharedCheck_5416_ == 0)
{
v___x_5411_ = v___x_5399_;
v_isShared_5412_ = v_isSharedCheck_5416_;
goto v_resetjp_5410_;
}
else
{
lean_inc(v_a_5409_);
lean_dec(v___x_5399_);
v___x_5411_ = lean_box(0);
v_isShared_5412_ = v_isSharedCheck_5416_;
goto v_resetjp_5410_;
}
v_resetjp_5410_:
{
lean_object* v___x_5414_; 
if (v_isShared_5412_ == 0)
{
v___x_5414_ = v___x_5411_;
goto v_reusejp_5413_;
}
else
{
lean_object* v_reuseFailAlloc_5415_; 
v_reuseFailAlloc_5415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5415_, 0, v_a_5409_);
v___x_5414_ = v_reuseFailAlloc_5415_;
goto v_reusejp_5413_;
}
v_reusejp_5413_:
{
return v___x_5414_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1___boxed(lean_object* v_a_5417_, lean_object* v_trees_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_, lean_object* v___y_5422_, lean_object* v___y_5423_, lean_object* v___y_5424_, lean_object* v___y_5425_, lean_object* v___y_5426_, lean_object* v___y_5427_){
_start:
{
lean_object* v_res_5428_; 
v_res_5428_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1(v_a_5417_, v_trees_5418_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_, v___y_5425_, v___y_5426_);
lean_dec(v___y_5426_);
lean_dec_ref(v___y_5425_);
lean_dec(v___y_5424_);
lean_dec_ref(v___y_5423_);
lean_dec(v___y_5422_);
lean_dec_ref(v___y_5421_);
lean_dec(v___y_5420_);
lean_dec_ref(v___y_5419_);
return v_res_5428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2(lean_object* v___x_5429_, lean_object* v_ref_5430_, lean_object* v_tactic_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_, lean_object* v___y_5434_, lean_object* v___y_5435_, lean_object* v___y_5436_, lean_object* v___y_5437_, lean_object* v___y_5438_, lean_object* v___y_5439_){
_start:
{
lean_object* v___x_5441_; 
v___x_5441_ = l_Lean_Elab_Tactic_setGoals___redArg(v___x_5429_, v___y_5433_);
if (lean_obj_tag(v___x_5441_) == 0)
{
lean_object* v___x_5442_; 
lean_dec_ref_known(v___x_5441_, 1);
v___x_5442_ = l_Lean_Elab_WF_applyCleanWfTactic(v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_, v___y_5436_, v___y_5437_, v___y_5438_, v___y_5439_);
if (lean_obj_tag(v___x_5442_) == 0)
{
lean_object* v___x_5443_; 
lean_dec_ref_known(v___x_5442_, 1);
v___x_5443_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v_ref_5430_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_, v___y_5436_, v___y_5437_, v___y_5438_, v___y_5439_);
if (lean_obj_tag(v___x_5443_) == 0)
{
lean_object* v_a_5444_; lean_object* v___f_5445_; lean_object* v___x_5446_; lean_object* v___x_5447_; 
v_a_5444_ = lean_ctor_get(v___x_5443_, 0);
lean_inc(v_a_5444_);
lean_dec_ref_known(v___x_5443_, 1);
v___f_5445_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1___boxed), 11, 1);
lean_closure_set(v___f_5445_, 0, v_a_5444_);
v___x_5446_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_5446_, 0, v_tactic_5431_);
v___x_5447_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v___x_5446_, v___f_5445_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_, v___y_5436_, v___y_5437_, v___y_5438_, v___y_5439_);
return v___x_5447_;
}
else
{
lean_object* v_a_5448_; lean_object* v___x_5450_; uint8_t v_isShared_5451_; uint8_t v_isSharedCheck_5455_; 
lean_dec(v_tactic_5431_);
v_a_5448_ = lean_ctor_get(v___x_5443_, 0);
v_isSharedCheck_5455_ = !lean_is_exclusive(v___x_5443_);
if (v_isSharedCheck_5455_ == 0)
{
v___x_5450_ = v___x_5443_;
v_isShared_5451_ = v_isSharedCheck_5455_;
goto v_resetjp_5449_;
}
else
{
lean_inc(v_a_5448_);
lean_dec(v___x_5443_);
v___x_5450_ = lean_box(0);
v_isShared_5451_ = v_isSharedCheck_5455_;
goto v_resetjp_5449_;
}
v_resetjp_5449_:
{
lean_object* v___x_5453_; 
if (v_isShared_5451_ == 0)
{
v___x_5453_ = v___x_5450_;
goto v_reusejp_5452_;
}
else
{
lean_object* v_reuseFailAlloc_5454_; 
v_reuseFailAlloc_5454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5454_, 0, v_a_5448_);
v___x_5453_ = v_reuseFailAlloc_5454_;
goto v_reusejp_5452_;
}
v_reusejp_5452_:
{
return v___x_5453_;
}
}
}
}
else
{
lean_dec(v_tactic_5431_);
lean_dec(v_ref_5430_);
return v___x_5442_;
}
}
else
{
lean_dec(v_tactic_5431_);
lean_dec(v_ref_5430_);
return v___x_5441_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2___boxed(lean_object* v___x_5456_, lean_object* v_ref_5457_, lean_object* v_tactic_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_, lean_object* v___y_5463_, lean_object* v___y_5464_, lean_object* v___y_5465_, lean_object* v___y_5466_, lean_object* v___y_5467_){
_start:
{
lean_object* v_res_5468_; 
v_res_5468_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2(v___x_5456_, v_ref_5457_, v_tactic_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_, v___y_5463_, v___y_5464_, v___y_5465_, v___y_5466_);
lean_dec(v___y_5466_);
lean_dec_ref(v___y_5465_);
lean_dec(v___y_5464_);
lean_dec_ref(v___y_5463_);
lean_dec(v___y_5462_);
lean_dec_ref(v___y_5461_);
lean_dec(v___y_5460_);
lean_dec_ref(v___y_5459_);
return v_res_5468_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5469_; lean_object* v___x_5470_; 
v___x_5469_ = lean_box(1);
v___x_5470_ = l_Lean_MessageData_ofFormat(v___x_5469_);
return v___x_5470_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5474_; lean_object* v___x_5475_; 
v___x_5474_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__2));
v___x_5475_ = l_Lean_MessageData_ofFormat(v___x_5474_);
return v___x_5475_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3(lean_object* v_x_5476_, lean_object* v_x_5477_){
_start:
{
if (lean_obj_tag(v_x_5477_) == 0)
{
return v_x_5476_;
}
else
{
lean_object* v_head_5478_; lean_object* v_tail_5479_; lean_object* v___x_5481_; uint8_t v_isShared_5482_; uint8_t v_isSharedCheck_5501_; 
v_head_5478_ = lean_ctor_get(v_x_5477_, 0);
v_tail_5479_ = lean_ctor_get(v_x_5477_, 1);
v_isSharedCheck_5501_ = !lean_is_exclusive(v_x_5477_);
if (v_isSharedCheck_5501_ == 0)
{
v___x_5481_ = v_x_5477_;
v_isShared_5482_ = v_isSharedCheck_5501_;
goto v_resetjp_5480_;
}
else
{
lean_inc(v_tail_5479_);
lean_inc(v_head_5478_);
lean_dec(v_x_5477_);
v___x_5481_ = lean_box(0);
v_isShared_5482_ = v_isSharedCheck_5501_;
goto v_resetjp_5480_;
}
v_resetjp_5480_:
{
lean_object* v_before_5483_; lean_object* v___x_5485_; uint8_t v_isShared_5486_; uint8_t v_isSharedCheck_5499_; 
v_before_5483_ = lean_ctor_get(v_head_5478_, 0);
v_isSharedCheck_5499_ = !lean_is_exclusive(v_head_5478_);
if (v_isSharedCheck_5499_ == 0)
{
lean_object* v_unused_5500_; 
v_unused_5500_ = lean_ctor_get(v_head_5478_, 1);
lean_dec(v_unused_5500_);
v___x_5485_ = v_head_5478_;
v_isShared_5486_ = v_isSharedCheck_5499_;
goto v_resetjp_5484_;
}
else
{
lean_inc(v_before_5483_);
lean_dec(v_head_5478_);
v___x_5485_ = lean_box(0);
v_isShared_5486_ = v_isSharedCheck_5499_;
goto v_resetjp_5484_;
}
v_resetjp_5484_:
{
lean_object* v___x_5487_; lean_object* v___x_5489_; 
v___x_5487_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_5486_ == 0)
{
lean_ctor_set_tag(v___x_5485_, 7);
lean_ctor_set(v___x_5485_, 1, v___x_5487_);
lean_ctor_set(v___x_5485_, 0, v_x_5476_);
v___x_5489_ = v___x_5485_;
goto v_reusejp_5488_;
}
else
{
lean_object* v_reuseFailAlloc_5498_; 
v_reuseFailAlloc_5498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5498_, 0, v_x_5476_);
lean_ctor_set(v_reuseFailAlloc_5498_, 1, v___x_5487_);
v___x_5489_ = v_reuseFailAlloc_5498_;
goto v_reusejp_5488_;
}
v_reusejp_5488_:
{
lean_object* v___x_5490_; lean_object* v___x_5492_; 
v___x_5490_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3);
if (v_isShared_5482_ == 0)
{
lean_ctor_set_tag(v___x_5481_, 7);
lean_ctor_set(v___x_5481_, 1, v___x_5490_);
lean_ctor_set(v___x_5481_, 0, v___x_5489_);
v___x_5492_ = v___x_5481_;
goto v_reusejp_5491_;
}
else
{
lean_object* v_reuseFailAlloc_5497_; 
v_reuseFailAlloc_5497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5497_, 0, v___x_5489_);
lean_ctor_set(v_reuseFailAlloc_5497_, 1, v___x_5490_);
v___x_5492_ = v_reuseFailAlloc_5497_;
goto v_reusejp_5491_;
}
v_reusejp_5491_:
{
lean_object* v___x_5493_; lean_object* v___x_5494_; lean_object* v___x_5495_; 
v___x_5493_ = l_Lean_MessageData_ofSyntax(v_before_5483_);
v___x_5494_ = l_Lean_indentD(v___x_5493_);
v___x_5495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5495_, 0, v___x_5492_);
lean_ctor_set(v___x_5495_, 1, v___x_5494_);
v_x_5476_ = v___x_5495_;
v_x_5477_ = v_tail_5479_;
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
lean_object* v___x_5505_; lean_object* v___x_5506_; 
v___x_5505_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__1));
v___x_5506_ = l_Lean_MessageData_ofFormat(v___x_5505_);
return v___x_5506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(lean_object* v_msgData_5507_, lean_object* v_macroStack_5508_, lean_object* v___y_5509_){
_start:
{
lean_object* v_toCold_5511_; lean_object* v_options_5512_; lean_object* v___x_5513_; uint8_t v___x_5514_; 
v_toCold_5511_ = lean_ctor_get(v___y_5509_, 0);
v_options_5512_ = lean_ctor_get(v_toCold_5511_, 2);
v___x_5513_ = l_Lean_Elab_pp_macroStack;
v___x_5514_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v_options_5512_, v___x_5513_);
if (v___x_5514_ == 0)
{
lean_object* v___x_5515_; 
lean_dec(v_macroStack_5508_);
v___x_5515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5515_, 0, v_msgData_5507_);
return v___x_5515_;
}
else
{
if (lean_obj_tag(v_macroStack_5508_) == 0)
{
lean_object* v___x_5516_; 
v___x_5516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5516_, 0, v_msgData_5507_);
return v___x_5516_;
}
else
{
lean_object* v_head_5517_; lean_object* v_after_5518_; lean_object* v___x_5520_; uint8_t v_isShared_5521_; uint8_t v_isSharedCheck_5533_; 
v_head_5517_ = lean_ctor_get(v_macroStack_5508_, 0);
lean_inc(v_head_5517_);
v_after_5518_ = lean_ctor_get(v_head_5517_, 1);
v_isSharedCheck_5533_ = !lean_is_exclusive(v_head_5517_);
if (v_isSharedCheck_5533_ == 0)
{
lean_object* v_unused_5534_; 
v_unused_5534_ = lean_ctor_get(v_head_5517_, 0);
lean_dec(v_unused_5534_);
v___x_5520_ = v_head_5517_;
v_isShared_5521_ = v_isSharedCheck_5533_;
goto v_resetjp_5519_;
}
else
{
lean_inc(v_after_5518_);
lean_dec(v_head_5517_);
v___x_5520_ = lean_box(0);
v_isShared_5521_ = v_isSharedCheck_5533_;
goto v_resetjp_5519_;
}
v_resetjp_5519_:
{
lean_object* v___x_5522_; lean_object* v___x_5524_; 
v___x_5522_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_5521_ == 0)
{
lean_ctor_set_tag(v___x_5520_, 7);
lean_ctor_set(v___x_5520_, 1, v___x_5522_);
lean_ctor_set(v___x_5520_, 0, v_msgData_5507_);
v___x_5524_ = v___x_5520_;
goto v_reusejp_5523_;
}
else
{
lean_object* v_reuseFailAlloc_5532_; 
v_reuseFailAlloc_5532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5532_, 0, v_msgData_5507_);
lean_ctor_set(v_reuseFailAlloc_5532_, 1, v___x_5522_);
v___x_5524_ = v_reuseFailAlloc_5532_;
goto v_reusejp_5523_;
}
v_reusejp_5523_:
{
lean_object* v___x_5525_; lean_object* v___x_5526_; lean_object* v___x_5527_; lean_object* v___x_5528_; lean_object* v_msgData_5529_; lean_object* v___x_5530_; lean_object* v___x_5531_; 
v___x_5525_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2);
v___x_5526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5526_, 0, v___x_5524_);
lean_ctor_set(v___x_5526_, 1, v___x_5525_);
v___x_5527_ = l_Lean_MessageData_ofSyntax(v_after_5518_);
v___x_5528_ = l_Lean_indentD(v___x_5527_);
v_msgData_5529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_5529_, 0, v___x_5526_);
lean_ctor_set(v_msgData_5529_, 1, v___x_5528_);
v___x_5530_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3(v_msgData_5529_, v_macroStack_5508_);
v___x_5531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5531_, 0, v___x_5530_);
return v___x_5531_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_5535_, lean_object* v_macroStack_5536_, lean_object* v___y_5537_, lean_object* v___y_5538_){
_start:
{
lean_object* v_res_5539_; 
v_res_5539_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_msgData_5535_, v_macroStack_5536_, v___y_5537_);
lean_dec_ref(v___y_5537_);
return v_res_5539_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(lean_object* v_msg_5540_, lean_object* v___y_5541_, lean_object* v___y_5542_, lean_object* v___y_5543_, lean_object* v___y_5544_, lean_object* v___y_5545_, lean_object* v___y_5546_){
_start:
{
lean_object* v_ref_5548_; lean_object* v___x_5549_; lean_object* v_a_5550_; lean_object* v_macroStack_5551_; lean_object* v___x_5552_; lean_object* v___x_5553_; lean_object* v_a_5554_; lean_object* v___x_5556_; uint8_t v_isShared_5557_; uint8_t v_isSharedCheck_5562_; 
v_ref_5548_ = lean_ctor_get(v___y_5545_, 2);
v___x_5549_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_5540_, v___y_5543_, v___y_5544_, v___y_5545_, v___y_5546_);
v_a_5550_ = lean_ctor_get(v___x_5549_, 0);
lean_inc(v_a_5550_);
lean_dec_ref(v___x_5549_);
v_macroStack_5551_ = lean_ctor_get(v___y_5541_, 1);
v___x_5552_ = l_Lean_Elab_getBetterRef(v_ref_5548_, v_macroStack_5551_);
lean_inc(v_macroStack_5551_);
v___x_5553_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_a_5550_, v_macroStack_5551_, v___y_5545_);
v_a_5554_ = lean_ctor_get(v___x_5553_, 0);
v_isSharedCheck_5562_ = !lean_is_exclusive(v___x_5553_);
if (v_isSharedCheck_5562_ == 0)
{
v___x_5556_ = v___x_5553_;
v_isShared_5557_ = v_isSharedCheck_5562_;
goto v_resetjp_5555_;
}
else
{
lean_inc(v_a_5554_);
lean_dec(v___x_5553_);
v___x_5556_ = lean_box(0);
v_isShared_5557_ = v_isSharedCheck_5562_;
goto v_resetjp_5555_;
}
v_resetjp_5555_:
{
lean_object* v___x_5558_; lean_object* v___x_5560_; 
v___x_5558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5558_, 0, v___x_5552_);
lean_ctor_set(v___x_5558_, 1, v_a_5554_);
if (v_isShared_5557_ == 0)
{
lean_ctor_set_tag(v___x_5556_, 1);
lean_ctor_set(v___x_5556_, 0, v___x_5558_);
v___x_5560_ = v___x_5556_;
goto v_reusejp_5559_;
}
else
{
lean_object* v_reuseFailAlloc_5561_; 
v_reuseFailAlloc_5561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5561_, 0, v___x_5558_);
v___x_5560_ = v_reuseFailAlloc_5561_;
goto v_reusejp_5559_;
}
v_reusejp_5559_:
{
return v___x_5560_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg___boxed(lean_object* v_msg_5563_, lean_object* v___y_5564_, lean_object* v___y_5565_, lean_object* v___y_5566_, lean_object* v___y_5567_, lean_object* v___y_5568_, lean_object* v___y_5569_, lean_object* v___y_5570_){
_start:
{
lean_object* v_res_5571_; 
v_res_5571_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v_msg_5563_, v___y_5564_, v___y_5565_, v___y_5566_, v___y_5567_, v___y_5568_, v___y_5569_);
lean_dec(v___y_5569_);
lean_dec_ref(v___y_5568_);
lean_dec(v___y_5567_);
lean_dec_ref(v___y_5566_);
lean_dec(v___y_5565_);
lean_dec_ref(v___y_5564_);
return v_res_5571_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1(void){
_start:
{
lean_object* v___x_5573_; lean_object* v___x_5574_; 
v___x_5573_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__0));
v___x_5574_ = l_Lean_stringToMessageData(v___x_5573_);
return v___x_5574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(lean_object* v_as_5575_, size_t v_sz_5576_, size_t v_i_5577_, lean_object* v_b_5578_, lean_object* v___y_5579_, lean_object* v___y_5580_, lean_object* v___y_5581_, lean_object* v___y_5582_, lean_object* v___y_5583_, lean_object* v___y_5584_){
_start:
{
lean_object* v_a_5587_; uint8_t v___x_5591_; 
v___x_5591_ = lean_usize_dec_lt(v_i_5577_, v_sz_5576_);
if (v___x_5591_ == 0)
{
lean_object* v___x_5592_; 
v___x_5592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5592_, 0, v_b_5578_);
return v___x_5592_;
}
else
{
lean_object* v_a_5593_; lean_object* v___x_5594_; 
v_a_5593_ = lean_array_uget_borrowed(v_as_5575_, v_i_5577_);
lean_inc(v_a_5593_);
v___x_5594_ = l_Lean_MVarId_getType(v_a_5593_, v___y_5581_, v___y_5582_, v___y_5583_, v___y_5584_);
if (lean_obj_tag(v___x_5594_) == 0)
{
lean_object* v_a_5595_; lean_object* v___x_5596_; 
v_a_5595_ = lean_ctor_get(v___x_5594_, 0);
lean_inc(v_a_5595_);
lean_dec_ref_known(v___x_5594_, 1);
lean_inc(v_a_5593_);
v___x_5596_ = l_Lean_MVarId_getType(v_a_5593_, v___y_5581_, v___y_5582_, v___y_5583_, v___y_5584_);
if (lean_obj_tag(v___x_5596_) == 0)
{
lean_object* v_a_5597_; lean_object* v___x_5598_; lean_object* v___x_5599_; 
v_a_5597_ = lean_ctor_get(v___x_5596_, 0);
lean_inc(v_a_5597_);
lean_dec_ref_known(v___x_5596_, 1);
v___x_5598_ = lean_box(0);
v___x_5599_ = l_Lean_getRecAppSyntax_x3f(v_a_5597_);
lean_dec(v_a_5597_);
if (lean_obj_tag(v___x_5599_) == 1)
{
lean_object* v_val_5600_; lean_object* v___x_5601_; lean_object* v___x_5602_; 
v_val_5600_ = lean_ctor_get(v___x_5599_, 0);
lean_inc(v_val_5600_);
lean_dec_ref_known(v___x_5599_, 1);
v___x_5601_ = l_Lean_Expr_mdataExpr_x21(v_a_5595_);
lean_dec(v_a_5595_);
lean_inc(v_a_5593_);
v___x_5602_ = l_Lean_MVarId_setType___redArg(v_a_5593_, v___x_5601_, v___y_5582_);
if (lean_obj_tag(v___x_5602_) == 0)
{
lean_object* v_toCold_5603_; lean_object* v_currRecDepth_5604_; lean_object* v_ref_5605_; uint8_t v_diag_5606_; uint8_t v_suppressElabErrors_5607_; lean_object* v_ref_5608_; lean_object* v___x_5609_; lean_object* v___x_5610_; 
lean_dec_ref_known(v___x_5602_, 1);
v_toCold_5603_ = lean_ctor_get(v___y_5583_, 0);
v_currRecDepth_5604_ = lean_ctor_get(v___y_5583_, 1);
v_ref_5605_ = lean_ctor_get(v___y_5583_, 2);
v_diag_5606_ = lean_ctor_get_uint8(v___y_5583_, sizeof(void*)*3);
v_suppressElabErrors_5607_ = lean_ctor_get_uint8(v___y_5583_, sizeof(void*)*3 + 1);
v_ref_5608_ = l_Lean_replaceRef(v_val_5600_, v_ref_5605_);
lean_dec(v_val_5600_);
lean_inc(v_currRecDepth_5604_);
lean_inc_ref(v_toCold_5603_);
v___x_5609_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5609_, 0, v_toCold_5603_);
lean_ctor_set(v___x_5609_, 1, v_currRecDepth_5604_);
lean_ctor_set(v___x_5609_, 2, v_ref_5608_);
lean_ctor_set_uint8(v___x_5609_, sizeof(void*)*3, v_diag_5606_);
lean_ctor_set_uint8(v___x_5609_, sizeof(void*)*3 + 1, v_suppressElabErrors_5607_);
lean_inc(v_a_5593_);
v___x_5610_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(v_a_5593_, v___y_5579_, v___y_5580_, v___y_5581_, v___y_5582_, v___x_5609_, v___y_5584_);
lean_dec_ref_known(v___x_5609_, 3);
if (lean_obj_tag(v___x_5610_) == 0)
{
lean_dec_ref_known(v___x_5610_, 1);
v_a_5587_ = v___x_5598_;
goto v___jp_5586_;
}
else
{
return v___x_5610_;
}
}
else
{
lean_dec(v_val_5600_);
return v___x_5602_;
}
}
else
{
lean_object* v___x_5611_; lean_object* v___x_5612_; lean_object* v___x_5613_; lean_object* v___x_5614_; 
lean_dec(v___x_5599_);
v___x_5611_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1);
v___x_5612_ = l_Lean_indentExpr(v_a_5595_);
v___x_5613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5613_, 0, v___x_5611_);
lean_ctor_set(v___x_5613_, 1, v___x_5612_);
v___x_5614_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v___x_5613_, v___y_5579_, v___y_5580_, v___y_5581_, v___y_5582_, v___y_5583_, v___y_5584_);
if (lean_obj_tag(v___x_5614_) == 0)
{
lean_dec_ref_known(v___x_5614_, 1);
v_a_5587_ = v___x_5598_;
goto v___jp_5586_;
}
else
{
return v___x_5614_;
}
}
}
else
{
lean_object* v_a_5615_; lean_object* v___x_5617_; uint8_t v_isShared_5618_; uint8_t v_isSharedCheck_5622_; 
lean_dec(v_a_5595_);
v_a_5615_ = lean_ctor_get(v___x_5596_, 0);
v_isSharedCheck_5622_ = !lean_is_exclusive(v___x_5596_);
if (v_isSharedCheck_5622_ == 0)
{
v___x_5617_ = v___x_5596_;
v_isShared_5618_ = v_isSharedCheck_5622_;
goto v_resetjp_5616_;
}
else
{
lean_inc(v_a_5615_);
lean_dec(v___x_5596_);
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
else
{
lean_object* v_a_5623_; lean_object* v___x_5625_; uint8_t v_isShared_5626_; uint8_t v_isSharedCheck_5630_; 
v_a_5623_ = lean_ctor_get(v___x_5594_, 0);
v_isSharedCheck_5630_ = !lean_is_exclusive(v___x_5594_);
if (v_isSharedCheck_5630_ == 0)
{
v___x_5625_ = v___x_5594_;
v_isShared_5626_ = v_isSharedCheck_5630_;
goto v_resetjp_5624_;
}
else
{
lean_inc(v_a_5623_);
lean_dec(v___x_5594_);
v___x_5625_ = lean_box(0);
v_isShared_5626_ = v_isSharedCheck_5630_;
goto v_resetjp_5624_;
}
v_resetjp_5624_:
{
lean_object* v___x_5628_; 
if (v_isShared_5626_ == 0)
{
v___x_5628_ = v___x_5625_;
goto v_reusejp_5627_;
}
else
{
lean_object* v_reuseFailAlloc_5629_; 
v_reuseFailAlloc_5629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5629_, 0, v_a_5623_);
v___x_5628_ = v_reuseFailAlloc_5629_;
goto v_reusejp_5627_;
}
v_reusejp_5627_:
{
return v___x_5628_;
}
}
}
}
v___jp_5586_:
{
size_t v___x_5588_; size_t v___x_5589_; 
v___x_5588_ = ((size_t)1ULL);
v___x_5589_ = lean_usize_add(v_i_5577_, v___x_5588_);
v_i_5577_ = v___x_5589_;
v_b_5578_ = v_a_5587_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___boxed(lean_object* v_as_5631_, lean_object* v_sz_5632_, lean_object* v_i_5633_, lean_object* v_b_5634_, lean_object* v___y_5635_, lean_object* v___y_5636_, lean_object* v___y_5637_, lean_object* v___y_5638_, lean_object* v___y_5639_, lean_object* v___y_5640_, lean_object* v___y_5641_){
_start:
{
size_t v_sz_boxed_5642_; size_t v_i_boxed_5643_; lean_object* v_res_5644_; 
v_sz_boxed_5642_ = lean_unbox_usize(v_sz_5632_);
lean_dec(v_sz_5632_);
v_i_boxed_5643_ = lean_unbox_usize(v_i_5633_);
lean_dec(v_i_5633_);
v_res_5644_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(v_as_5631_, v_sz_boxed_5642_, v_i_boxed_5643_, v_b_5634_, v___y_5635_, v___y_5636_, v___y_5637_, v___y_5638_, v___y_5639_, v___y_5640_);
lean_dec(v___y_5640_);
lean_dec_ref(v___y_5639_);
lean_dec(v___y_5638_);
lean_dec_ref(v___y_5637_);
lean_dec(v___y_5636_);
lean_dec_ref(v___y_5635_);
lean_dec_ref(v_as_5631_);
return v_res_5644_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(lean_object* v_as_5645_, size_t v_i_5646_, size_t v_stop_5647_, lean_object* v_b_5648_, lean_object* v___y_5649_, lean_object* v___y_5650_, lean_object* v___y_5651_, lean_object* v___y_5652_){
_start:
{
uint8_t v___x_5654_; 
v___x_5654_ = lean_usize_dec_eq(v_i_5646_, v_stop_5647_);
if (v___x_5654_ == 0)
{
lean_object* v___x_5655_; lean_object* v___x_5656_; 
v___x_5655_ = lean_array_uget_borrowed(v_as_5645_, v_i_5646_);
lean_inc(v___x_5655_);
v___x_5656_ = l_Lean_MVarId_getType(v___x_5655_, v___y_5649_, v___y_5650_, v___y_5651_, v___y_5652_);
if (lean_obj_tag(v___x_5656_) == 0)
{
lean_object* v_a_5657_; lean_object* v___x_5658_; lean_object* v___x_5659_; 
v_a_5657_ = lean_ctor_get(v___x_5656_, 0);
lean_inc(v_a_5657_);
lean_dec_ref_known(v___x_5656_, 1);
v___x_5658_ = l_Lean_Expr_mdataExpr_x21(v_a_5657_);
lean_dec(v_a_5657_);
lean_inc(v___x_5655_);
v___x_5659_ = l_Lean_MVarId_setType___redArg(v___x_5655_, v___x_5658_, v___y_5650_);
if (lean_obj_tag(v___x_5659_) == 0)
{
lean_object* v_a_5660_; size_t v___x_5661_; size_t v___x_5662_; 
v_a_5660_ = lean_ctor_get(v___x_5659_, 0);
lean_inc(v_a_5660_);
lean_dec_ref_known(v___x_5659_, 1);
v___x_5661_ = ((size_t)1ULL);
v___x_5662_ = lean_usize_add(v_i_5646_, v___x_5661_);
v_i_5646_ = v___x_5662_;
v_b_5648_ = v_a_5660_;
goto _start;
}
else
{
return v___x_5659_;
}
}
else
{
lean_object* v_a_5664_; lean_object* v___x_5666_; uint8_t v_isShared_5667_; uint8_t v_isSharedCheck_5671_; 
v_a_5664_ = lean_ctor_get(v___x_5656_, 0);
v_isSharedCheck_5671_ = !lean_is_exclusive(v___x_5656_);
if (v_isSharedCheck_5671_ == 0)
{
v___x_5666_ = v___x_5656_;
v_isShared_5667_ = v_isSharedCheck_5671_;
goto v_resetjp_5665_;
}
else
{
lean_inc(v_a_5664_);
lean_dec(v___x_5656_);
v___x_5666_ = lean_box(0);
v_isShared_5667_ = v_isSharedCheck_5671_;
goto v_resetjp_5665_;
}
v_resetjp_5665_:
{
lean_object* v___x_5669_; 
if (v_isShared_5667_ == 0)
{
v___x_5669_ = v___x_5666_;
goto v_reusejp_5668_;
}
else
{
lean_object* v_reuseFailAlloc_5670_; 
v_reuseFailAlloc_5670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5670_, 0, v_a_5664_);
v___x_5669_ = v_reuseFailAlloc_5670_;
goto v_reusejp_5668_;
}
v_reusejp_5668_:
{
return v___x_5669_;
}
}
}
}
else
{
lean_object* v___x_5672_; 
v___x_5672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5672_, 0, v_b_5648_);
return v___x_5672_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg___boxed(lean_object* v_as_5673_, lean_object* v_i_5674_, lean_object* v_stop_5675_, lean_object* v_b_5676_, lean_object* v___y_5677_, lean_object* v___y_5678_, lean_object* v___y_5679_, lean_object* v___y_5680_, lean_object* v___y_5681_){
_start:
{
size_t v_i_boxed_5682_; size_t v_stop_boxed_5683_; lean_object* v_res_5684_; 
v_i_boxed_5682_ = lean_unbox_usize(v_i_5674_);
lean_dec(v_i_5674_);
v_stop_boxed_5683_ = lean_unbox_usize(v_stop_5675_);
lean_dec(v_stop_5675_);
v_res_5684_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v_as_5673_, v_i_boxed_5682_, v_stop_boxed_5683_, v_b_5676_, v___y_5677_, v___y_5678_, v___y_5679_, v___y_5680_);
lean_dec(v___y_5680_);
lean_dec_ref(v___y_5679_);
lean_dec(v___y_5678_);
lean_dec_ref(v___y_5677_);
lean_dec_ref(v_as_5673_);
return v_res_5684_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3(lean_object* v___x_5685_, lean_object* v___x_5686_, lean_object* v___x_5687_, lean_object* v___y_5688_, lean_object* v___y_5689_, lean_object* v___y_5690_, lean_object* v___y_5691_, lean_object* v___y_5692_, lean_object* v___y_5693_){
_start:
{
if (lean_obj_tag(v___x_5685_) == 0)
{
lean_object* v___x_5695_; size_t v_sz_5696_; size_t v___x_5697_; lean_object* v___x_5698_; 
v___x_5695_ = lean_box(0);
v_sz_5696_ = lean_array_size(v___x_5686_);
v___x_5697_ = ((size_t)0ULL);
v___x_5698_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(v___x_5686_, v_sz_5696_, v___x_5697_, v___x_5695_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_, v___y_5692_, v___y_5693_);
lean_dec_ref(v___x_5686_);
if (lean_obj_tag(v___x_5698_) == 0)
{
lean_object* v___x_5700_; uint8_t v_isShared_5701_; uint8_t v_isSharedCheck_5705_; 
v_isSharedCheck_5705_ = !lean_is_exclusive(v___x_5698_);
if (v_isSharedCheck_5705_ == 0)
{
lean_object* v_unused_5706_; 
v_unused_5706_ = lean_ctor_get(v___x_5698_, 0);
lean_dec(v_unused_5706_);
v___x_5700_ = v___x_5698_;
v_isShared_5701_ = v_isSharedCheck_5705_;
goto v_resetjp_5699_;
}
else
{
lean_dec(v___x_5698_);
v___x_5700_ = lean_box(0);
v_isShared_5701_ = v_isSharedCheck_5705_;
goto v_resetjp_5699_;
}
v_resetjp_5699_:
{
lean_object* v___x_5703_; 
if (v_isShared_5701_ == 0)
{
lean_ctor_set(v___x_5700_, 0, v___x_5695_);
v___x_5703_ = v___x_5700_;
goto v_reusejp_5702_;
}
else
{
lean_object* v_reuseFailAlloc_5704_; 
v_reuseFailAlloc_5704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5704_, 0, v___x_5695_);
v___x_5703_ = v_reuseFailAlloc_5704_;
goto v_reusejp_5702_;
}
v_reusejp_5702_:
{
return v___x_5703_;
}
}
}
else
{
return v___x_5698_;
}
}
else
{
lean_object* v_val_5707_; lean_object* v___x_5709_; uint8_t v_isShared_5710_; uint8_t v_isSharedCheck_5774_; 
v_val_5707_ = lean_ctor_get(v___x_5685_, 0);
v_isSharedCheck_5774_ = !lean_is_exclusive(v___x_5685_);
if (v_isSharedCheck_5774_ == 0)
{
v___x_5709_ = v___x_5685_;
v_isShared_5710_ = v_isSharedCheck_5774_;
goto v_resetjp_5708_;
}
else
{
lean_inc(v_val_5707_);
lean_dec(v___x_5685_);
v___x_5709_ = lean_box(0);
v_isShared_5710_ = v_isSharedCheck_5774_;
goto v_resetjp_5708_;
}
v_resetjp_5708_:
{
lean_object* v_ref_5711_; lean_object* v_tactic_5712_; lean_object* v_toCold_5713_; lean_object* v_currRecDepth_5714_; lean_object* v_ref_5715_; uint8_t v_diag_5716_; uint8_t v_suppressElabErrors_5717_; lean_object* v___x_5718_; lean_object* v___x_5719_; lean_object* v_ref_5720_; lean_object* v___x_5721_; lean_object* v___y_5747_; lean_object* v___y_5764_; uint8_t v___x_5765_; 
v_ref_5711_ = lean_ctor_get(v_val_5707_, 0);
lean_inc(v_ref_5711_);
v_tactic_5712_ = lean_ctor_get(v_val_5707_, 1);
lean_inc(v_tactic_5712_);
lean_dec(v_val_5707_);
v_toCold_5713_ = lean_ctor_get(v___y_5692_, 0);
v_currRecDepth_5714_ = lean_ctor_get(v___y_5692_, 1);
v_ref_5715_ = lean_ctor_get(v___y_5692_, 2);
v_diag_5716_ = lean_ctor_get_uint8(v___y_5692_, sizeof(void*)*3);
v_suppressElabErrors_5717_ = lean_ctor_get_uint8(v___y_5692_, sizeof(void*)*3 + 1);
v___x_5718_ = lean_unsigned_to_nat(0u);
v___x_5719_ = lean_array_get_size(v___x_5686_);
v_ref_5720_ = l_Lean_replaceRef(v_ref_5711_, v_ref_5715_);
lean_inc(v_currRecDepth_5714_);
lean_inc_ref(v_toCold_5713_);
v___x_5721_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5721_, 0, v_toCold_5713_);
lean_ctor_set(v___x_5721_, 1, v_currRecDepth_5714_);
lean_ctor_set(v___x_5721_, 2, v_ref_5720_);
lean_ctor_set_uint8(v___x_5721_, sizeof(void*)*3, v_diag_5716_);
lean_ctor_set_uint8(v___x_5721_, sizeof(void*)*3 + 1, v_suppressElabErrors_5717_);
v___x_5765_ = lean_nat_dec_lt(v___x_5718_, v___x_5719_);
if (v___x_5765_ == 0)
{
goto v___jp_5748_;
}
else
{
lean_object* v___x_5766_; uint8_t v___x_5767_; 
v___x_5766_ = lean_box(0);
v___x_5767_ = lean_nat_dec_le(v___x_5719_, v___x_5719_);
if (v___x_5767_ == 0)
{
if (v___x_5765_ == 0)
{
goto v___jp_5748_;
}
else
{
size_t v___x_5768_; size_t v___x_5769_; lean_object* v___x_5770_; 
v___x_5768_ = ((size_t)0ULL);
v___x_5769_ = lean_usize_of_nat(v___x_5719_);
v___x_5770_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v___x_5686_, v___x_5768_, v___x_5769_, v___x_5766_, v___y_5690_, v___y_5691_, v___x_5721_, v___y_5693_);
v___y_5764_ = v___x_5770_;
goto v___jp_5763_;
}
}
else
{
size_t v___x_5771_; size_t v___x_5772_; lean_object* v___x_5773_; 
v___x_5771_ = ((size_t)0ULL);
v___x_5772_ = lean_usize_of_nat(v___x_5719_);
v___x_5773_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v___x_5686_, v___x_5771_, v___x_5772_, v___x_5766_, v___y_5690_, v___y_5691_, v___x_5721_, v___y_5693_);
v___y_5764_ = v___x_5773_;
goto v___jp_5763_;
}
}
v___jp_5722_:
{
lean_object* v___x_5723_; lean_object* v___x_5724_; lean_object* v___f_5725_; lean_object* v___x_5726_; 
v___x_5723_ = lean_array_get(v___x_5687_, v___x_5686_, v___x_5718_);
v___x_5724_ = lean_array_to_list(v___x_5686_);
v___f_5725_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2___boxed), 12, 3);
lean_closure_set(v___f_5725_, 0, v___x_5724_);
lean_closure_set(v___f_5725_, 1, v_ref_5711_);
lean_closure_set(v___f_5725_, 2, v_tactic_5712_);
v___x_5726_ = l_Lean_Elab_Tactic_run(v___x_5723_, v___f_5725_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_, v___x_5721_, v___y_5693_);
if (lean_obj_tag(v___x_5726_) == 0)
{
lean_object* v_a_5727_; lean_object* v___x_5729_; uint8_t v_isShared_5730_; uint8_t v_isSharedCheck_5737_; 
v_a_5727_ = lean_ctor_get(v___x_5726_, 0);
v_isSharedCheck_5737_ = !lean_is_exclusive(v___x_5726_);
if (v_isSharedCheck_5737_ == 0)
{
v___x_5729_ = v___x_5726_;
v_isShared_5730_ = v_isSharedCheck_5737_;
goto v_resetjp_5728_;
}
else
{
lean_inc(v_a_5727_);
lean_dec(v___x_5726_);
v___x_5729_ = lean_box(0);
v_isShared_5730_ = v_isSharedCheck_5737_;
goto v_resetjp_5728_;
}
v_resetjp_5728_:
{
uint8_t v___x_5731_; 
v___x_5731_ = l_List_isEmpty___redArg(v_a_5727_);
if (v___x_5731_ == 0)
{
lean_object* v___x_5732_; 
lean_del_object(v___x_5729_);
v___x_5732_ = l_Lean_Elab_Term_reportUnsolvedGoals(v_a_5727_, v___y_5690_, v___y_5691_, v___x_5721_, v___y_5693_);
lean_dec_ref_known(v___x_5721_, 3);
return v___x_5732_;
}
else
{
lean_object* v___x_5733_; lean_object* v___x_5735_; 
lean_dec(v_a_5727_);
lean_dec_ref_known(v___x_5721_, 3);
v___x_5733_ = lean_box(0);
if (v_isShared_5730_ == 0)
{
lean_ctor_set(v___x_5729_, 0, v___x_5733_);
v___x_5735_ = v___x_5729_;
goto v_reusejp_5734_;
}
else
{
lean_object* v_reuseFailAlloc_5736_; 
v_reuseFailAlloc_5736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5736_, 0, v___x_5733_);
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
else
{
lean_object* v_a_5738_; lean_object* v___x_5740_; uint8_t v_isShared_5741_; uint8_t v_isSharedCheck_5745_; 
lean_dec_ref_known(v___x_5721_, 3);
v_a_5738_ = lean_ctor_get(v___x_5726_, 0);
v_isSharedCheck_5745_ = !lean_is_exclusive(v___x_5726_);
if (v_isSharedCheck_5745_ == 0)
{
v___x_5740_ = v___x_5726_;
v_isShared_5741_ = v_isSharedCheck_5745_;
goto v_resetjp_5739_;
}
else
{
lean_inc(v_a_5738_);
lean_dec(v___x_5726_);
v___x_5740_ = lean_box(0);
v_isShared_5741_ = v_isSharedCheck_5745_;
goto v_resetjp_5739_;
}
v_resetjp_5739_:
{
lean_object* v___x_5743_; 
if (v_isShared_5741_ == 0)
{
v___x_5743_ = v___x_5740_;
goto v_reusejp_5742_;
}
else
{
lean_object* v_reuseFailAlloc_5744_; 
v_reuseFailAlloc_5744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5744_, 0, v_a_5738_);
v___x_5743_ = v_reuseFailAlloc_5744_;
goto v_reusejp_5742_;
}
v_reusejp_5742_:
{
return v___x_5743_;
}
}
}
}
v___jp_5746_:
{
if (lean_obj_tag(v___y_5747_) == 0)
{
lean_dec_ref_known(v___y_5747_, 1);
goto v___jp_5722_;
}
else
{
lean_dec_ref_known(v___x_5721_, 3);
lean_dec(v_tactic_5712_);
lean_dec(v_ref_5711_);
lean_dec_ref(v___x_5686_);
return v___y_5747_;
}
}
v___jp_5748_:
{
uint8_t v___x_5749_; 
v___x_5749_ = lean_nat_dec_eq(v___x_5719_, v___x_5718_);
if (v___x_5749_ == 0)
{
uint8_t v___x_5750_; 
lean_del_object(v___x_5709_);
v___x_5750_ = lean_nat_dec_lt(v___x_5718_, v___x_5719_);
if (v___x_5750_ == 0)
{
goto v___jp_5722_;
}
else
{
lean_object* v___x_5751_; uint8_t v___x_5752_; 
v___x_5751_ = lean_box(0);
v___x_5752_ = lean_nat_dec_le(v___x_5719_, v___x_5719_);
if (v___x_5752_ == 0)
{
if (v___x_5750_ == 0)
{
goto v___jp_5722_;
}
else
{
size_t v___x_5753_; size_t v___x_5754_; lean_object* v___x_5755_; 
v___x_5753_ = ((size_t)0ULL);
v___x_5754_ = lean_usize_of_nat(v___x_5719_);
v___x_5755_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v___x_5686_, v___x_5753_, v___x_5754_, v___x_5751_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_, v___x_5721_, v___y_5693_);
v___y_5747_ = v___x_5755_;
goto v___jp_5746_;
}
}
else
{
size_t v___x_5756_; size_t v___x_5757_; lean_object* v___x_5758_; 
v___x_5756_ = ((size_t)0ULL);
v___x_5757_ = lean_usize_of_nat(v___x_5719_);
v___x_5758_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v___x_5686_, v___x_5756_, v___x_5757_, v___x_5751_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_, v___x_5721_, v___y_5693_);
v___y_5747_ = v___x_5758_;
goto v___jp_5746_;
}
}
}
else
{
lean_object* v___x_5759_; lean_object* v___x_5761_; 
lean_dec_ref_known(v___x_5721_, 3);
lean_dec(v_tactic_5712_);
lean_dec(v_ref_5711_);
lean_dec_ref(v___x_5686_);
v___x_5759_ = lean_box(0);
if (v_isShared_5710_ == 0)
{
lean_ctor_set_tag(v___x_5709_, 0);
lean_ctor_set(v___x_5709_, 0, v___x_5759_);
v___x_5761_ = v___x_5709_;
goto v_reusejp_5760_;
}
else
{
lean_object* v_reuseFailAlloc_5762_; 
v_reuseFailAlloc_5762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5762_, 0, v___x_5759_);
v___x_5761_ = v_reuseFailAlloc_5762_;
goto v_reusejp_5760_;
}
v_reusejp_5760_:
{
return v___x_5761_;
}
}
}
v___jp_5763_:
{
if (lean_obj_tag(v___y_5764_) == 0)
{
lean_dec_ref_known(v___y_5764_, 1);
goto v___jp_5748_;
}
else
{
lean_dec_ref_known(v___x_5721_, 3);
lean_dec(v_tactic_5712_);
lean_dec(v_ref_5711_);
lean_del_object(v___x_5709_);
lean_dec_ref(v___x_5686_);
return v___y_5764_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3___boxed(lean_object* v___x_5775_, lean_object* v___x_5776_, lean_object* v___x_5777_, lean_object* v___y_5778_, lean_object* v___y_5779_, lean_object* v___y_5780_, lean_object* v___y_5781_, lean_object* v___y_5782_, lean_object* v___y_5783_, lean_object* v___y_5784_){
_start:
{
lean_object* v_res_5785_; 
v_res_5785_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3(v___x_5775_, v___x_5776_, v___x_5777_, v___y_5778_, v___y_5779_, v___y_5780_, v___y_5781_, v___y_5782_, v___y_5783_);
lean_dec(v___y_5783_);
lean_dec_ref(v___y_5782_);
lean_dec(v___y_5781_);
lean_dec_ref(v___y_5780_);
lean_dec(v___y_5779_);
lean_dec_ref(v___y_5778_);
lean_dec(v___x_5777_);
return v_res_5785_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0(lean_object* v_x_5786_){
_start:
{
uint8_t v___x_5787_; 
v___x_5787_ = 0;
return v___x_5787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0___boxed(lean_object* v_x_5788_){
_start:
{
uint8_t v_res_5789_; lean_object* v_r_5790_; 
v_res_5789_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0(v_x_5788_);
lean_dec(v_x_5788_);
v_r_5790_ = lean_box(v_res_5789_);
return v_r_5790_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(lean_object* v_as_5797_, size_t v_sz_5798_, size_t v_i_5799_, lean_object* v_b_5800_, lean_object* v___y_5801_, lean_object* v___y_5802_, lean_object* v___y_5803_, lean_object* v___y_5804_){
_start:
{
uint8_t v___x_5806_; 
v___x_5806_ = lean_usize_dec_lt(v_i_5799_, v_sz_5798_);
if (v___x_5806_ == 0)
{
lean_object* v___x_5807_; 
v___x_5807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5807_, 0, v_b_5800_);
return v___x_5807_;
}
else
{
lean_object* v_snd_5808_; lean_object* v_fst_5809_; lean_object* v___x_5811_; uint8_t v_isShared_5812_; uint8_t v_isSharedCheck_5881_; 
v_snd_5808_ = lean_ctor_get(v_b_5800_, 1);
v_fst_5809_ = lean_ctor_get(v_b_5800_, 0);
v_isSharedCheck_5881_ = !lean_is_exclusive(v_b_5800_);
if (v_isSharedCheck_5881_ == 0)
{
v___x_5811_ = v_b_5800_;
v_isShared_5812_ = v_isSharedCheck_5881_;
goto v_resetjp_5810_;
}
else
{
lean_inc(v_snd_5808_);
lean_inc(v_fst_5809_);
lean_dec(v_b_5800_);
v___x_5811_ = lean_box(0);
v_isShared_5812_ = v_isSharedCheck_5881_;
goto v_resetjp_5810_;
}
v_resetjp_5810_:
{
lean_object* v_array_5813_; lean_object* v_start_5814_; lean_object* v_stop_5815_; uint8_t v___x_5816_; 
v_array_5813_ = lean_ctor_get(v_snd_5808_, 0);
v_start_5814_ = lean_ctor_get(v_snd_5808_, 1);
v_stop_5815_ = lean_ctor_get(v_snd_5808_, 2);
v___x_5816_ = lean_nat_dec_lt(v_start_5814_, v_stop_5815_);
if (v___x_5816_ == 0)
{
lean_object* v___x_5818_; 
if (v_isShared_5812_ == 0)
{
v___x_5818_ = v___x_5811_;
goto v_reusejp_5817_;
}
else
{
lean_object* v_reuseFailAlloc_5820_; 
v_reuseFailAlloc_5820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5820_, 0, v_fst_5809_);
lean_ctor_set(v_reuseFailAlloc_5820_, 1, v_snd_5808_);
v___x_5818_ = v_reuseFailAlloc_5820_;
goto v_reusejp_5817_;
}
v_reusejp_5817_:
{
lean_object* v___x_5819_; 
v___x_5819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5819_, 0, v___x_5818_);
return v___x_5819_;
}
}
else
{
lean_object* v___x_5822_; uint8_t v_isShared_5823_; uint8_t v_isSharedCheck_5877_; 
lean_inc(v_stop_5815_);
lean_inc(v_start_5814_);
lean_inc_ref(v_array_5813_);
v_isSharedCheck_5877_ = !lean_is_exclusive(v_snd_5808_);
if (v_isSharedCheck_5877_ == 0)
{
lean_object* v_unused_5878_; lean_object* v_unused_5879_; lean_object* v_unused_5880_; 
v_unused_5878_ = lean_ctor_get(v_snd_5808_, 2);
lean_dec(v_unused_5878_);
v_unused_5879_ = lean_ctor_get(v_snd_5808_, 1);
lean_dec(v_unused_5879_);
v_unused_5880_ = lean_ctor_get(v_snd_5808_, 0);
lean_dec(v_unused_5880_);
v___x_5822_ = v_snd_5808_;
v_isShared_5823_ = v_isSharedCheck_5877_;
goto v_resetjp_5821_;
}
else
{
lean_dec(v_snd_5808_);
v___x_5822_ = lean_box(0);
v_isShared_5823_ = v_isSharedCheck_5877_;
goto v_resetjp_5821_;
}
v_resetjp_5821_:
{
lean_object* v_array_5824_; lean_object* v_start_5825_; lean_object* v_stop_5826_; lean_object* v___x_5827_; lean_object* v___x_5828_; lean_object* v___x_5829_; lean_object* v___x_5831_; 
v_array_5824_ = lean_ctor_get(v_fst_5809_, 0);
v_start_5825_ = lean_ctor_get(v_fst_5809_, 1);
v_stop_5826_ = lean_ctor_get(v_fst_5809_, 2);
v___x_5827_ = lean_array_fget(v_array_5813_, v_start_5814_);
v___x_5828_ = lean_unsigned_to_nat(1u);
v___x_5829_ = lean_nat_add(v_start_5814_, v___x_5828_);
lean_dec(v_start_5814_);
if (v_isShared_5823_ == 0)
{
lean_ctor_set(v___x_5822_, 1, v___x_5829_);
v___x_5831_ = v___x_5822_;
goto v_reusejp_5830_;
}
else
{
lean_object* v_reuseFailAlloc_5876_; 
v_reuseFailAlloc_5876_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5876_, 0, v_array_5813_);
lean_ctor_set(v_reuseFailAlloc_5876_, 1, v___x_5829_);
lean_ctor_set(v_reuseFailAlloc_5876_, 2, v_stop_5815_);
v___x_5831_ = v_reuseFailAlloc_5876_;
goto v_reusejp_5830_;
}
v_reusejp_5830_:
{
uint8_t v___x_5832_; 
v___x_5832_ = lean_nat_dec_lt(v_start_5825_, v_stop_5826_);
if (v___x_5832_ == 0)
{
lean_object* v___x_5834_; 
lean_dec(v___x_5827_);
if (v_isShared_5812_ == 0)
{
lean_ctor_set(v___x_5811_, 1, v___x_5831_);
v___x_5834_ = v___x_5811_;
goto v_reusejp_5833_;
}
else
{
lean_object* v_reuseFailAlloc_5836_; 
v_reuseFailAlloc_5836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5836_, 0, v_fst_5809_);
lean_ctor_set(v_reuseFailAlloc_5836_, 1, v___x_5831_);
v___x_5834_ = v_reuseFailAlloc_5836_;
goto v_reusejp_5833_;
}
v_reusejp_5833_:
{
lean_object* v___x_5835_; 
v___x_5835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5835_, 0, v___x_5834_);
return v___x_5835_;
}
}
else
{
lean_object* v___x_5838_; uint8_t v_isShared_5839_; uint8_t v_isSharedCheck_5872_; 
lean_inc(v_stop_5826_);
lean_inc(v_start_5825_);
lean_inc_ref(v_array_5824_);
v_isSharedCheck_5872_ = !lean_is_exclusive(v_fst_5809_);
if (v_isSharedCheck_5872_ == 0)
{
lean_object* v_unused_5873_; lean_object* v_unused_5874_; lean_object* v_unused_5875_; 
v_unused_5873_ = lean_ctor_get(v_fst_5809_, 2);
lean_dec(v_unused_5873_);
v_unused_5874_ = lean_ctor_get(v_fst_5809_, 1);
lean_dec(v_unused_5874_);
v_unused_5875_ = lean_ctor_get(v_fst_5809_, 0);
lean_dec(v_unused_5875_);
v___x_5838_ = v_fst_5809_;
v_isShared_5839_ = v_isSharedCheck_5872_;
goto v_resetjp_5837_;
}
else
{
lean_dec(v_fst_5809_);
v___x_5838_ = lean_box(0);
v_isShared_5839_ = v_isSharedCheck_5872_;
goto v_resetjp_5837_;
}
v_resetjp_5837_:
{
lean_object* v___f_5840_; lean_object* v___x_5841_; lean_object* v_a_5842_; lean_object* v___x_5843_; lean_object* v___y_5844_; lean_object* v___x_5845_; lean_object* v___x_5846_; lean_object* v___x_5847_; lean_object* v___x_5848_; uint8_t v___x_5849_; lean_object* v___x_5850_; lean_object* v___x_5851_; lean_object* v___x_5852_; lean_object* v___x_5853_; 
v___f_5840_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__0));
v___x_5841_ = lean_box(0);
v_a_5842_ = lean_array_uget_borrowed(v_as_5797_, v_i_5799_);
v___x_5843_ = lean_array_fget_borrowed(v_array_5824_, v_start_5825_);
lean_inc(v___x_5843_);
v___y_5844_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3___boxed), 10, 3);
lean_closure_set(v___y_5844_, 0, v___x_5827_);
lean_closure_set(v___y_5844_, 1, v___x_5843_);
lean_closure_set(v___y_5844_, 2, v___x_5841_);
lean_inc(v_a_5842_);
v___x_5845_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withDeclName___boxed), 10, 3);
lean_closure_set(v___x_5845_, 0, lean_box(0));
lean_closure_set(v___x_5845_, 1, v_a_5842_);
lean_closure_set(v___x_5845_, 2, v___y_5844_);
v___x_5846_ = lean_box(0);
v___x_5847_ = lean_box(0);
v___x_5848_ = lean_box(1);
v___x_5849_ = 0;
v___x_5850_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__1));
v___x_5851_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_5851_, 0, v___x_5846_);
lean_ctor_set(v___x_5851_, 1, v___x_5847_);
lean_ctor_set(v___x_5851_, 2, v___x_5846_);
lean_ctor_set(v___x_5851_, 3, v___f_5840_);
lean_ctor_set(v___x_5851_, 4, v___x_5848_);
lean_ctor_set(v___x_5851_, 5, v___x_5848_);
lean_ctor_set(v___x_5851_, 6, v___x_5846_);
lean_ctor_set(v___x_5851_, 7, v___x_5850_);
lean_ctor_set_uint8(v___x_5851_, sizeof(void*)*8, v___x_5832_);
lean_ctor_set_uint8(v___x_5851_, sizeof(void*)*8 + 1, v___x_5832_);
lean_ctor_set_uint8(v___x_5851_, sizeof(void*)*8 + 2, v___x_5832_);
lean_ctor_set_uint8(v___x_5851_, sizeof(void*)*8 + 3, v___x_5832_);
lean_ctor_set_uint8(v___x_5851_, sizeof(void*)*8 + 4, v___x_5849_);
lean_ctor_set_uint8(v___x_5851_, sizeof(void*)*8 + 5, v___x_5849_);
lean_ctor_set_uint8(v___x_5851_, sizeof(void*)*8 + 6, v___x_5849_);
lean_ctor_set_uint8(v___x_5851_, sizeof(void*)*8 + 7, v___x_5849_);
lean_ctor_set_uint8(v___x_5851_, sizeof(void*)*8 + 8, v___x_5832_);
lean_ctor_set_uint8(v___x_5851_, sizeof(void*)*8 + 9, v___x_5849_);
lean_ctor_set_uint8(v___x_5851_, sizeof(void*)*8 + 10, v___x_5832_);
v___x_5852_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__2));
v___x_5853_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_5845_, v___x_5851_, v___x_5852_, v___y_5801_, v___y_5802_, v___y_5803_, v___y_5804_);
if (lean_obj_tag(v___x_5853_) == 0)
{
lean_object* v___x_5854_; lean_object* v___x_5856_; 
lean_dec_ref_known(v___x_5853_, 1);
v___x_5854_ = lean_nat_add(v_start_5825_, v___x_5828_);
lean_dec(v_start_5825_);
if (v_isShared_5839_ == 0)
{
lean_ctor_set(v___x_5838_, 1, v___x_5854_);
v___x_5856_ = v___x_5838_;
goto v_reusejp_5855_;
}
else
{
lean_object* v_reuseFailAlloc_5863_; 
v_reuseFailAlloc_5863_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5863_, 0, v_array_5824_);
lean_ctor_set(v_reuseFailAlloc_5863_, 1, v___x_5854_);
lean_ctor_set(v_reuseFailAlloc_5863_, 2, v_stop_5826_);
v___x_5856_ = v_reuseFailAlloc_5863_;
goto v_reusejp_5855_;
}
v_reusejp_5855_:
{
lean_object* v___x_5858_; 
if (v_isShared_5812_ == 0)
{
lean_ctor_set(v___x_5811_, 1, v___x_5831_);
lean_ctor_set(v___x_5811_, 0, v___x_5856_);
v___x_5858_ = v___x_5811_;
goto v_reusejp_5857_;
}
else
{
lean_object* v_reuseFailAlloc_5862_; 
v_reuseFailAlloc_5862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5862_, 0, v___x_5856_);
lean_ctor_set(v_reuseFailAlloc_5862_, 1, v___x_5831_);
v___x_5858_ = v_reuseFailAlloc_5862_;
goto v_reusejp_5857_;
}
v_reusejp_5857_:
{
size_t v___x_5859_; size_t v___x_5860_; 
v___x_5859_ = ((size_t)1ULL);
v___x_5860_ = lean_usize_add(v_i_5799_, v___x_5859_);
v_i_5799_ = v___x_5860_;
v_b_5800_ = v___x_5858_;
goto _start;
}
}
}
else
{
lean_object* v_a_5864_; lean_object* v___x_5866_; uint8_t v_isShared_5867_; uint8_t v_isSharedCheck_5871_; 
lean_del_object(v___x_5838_);
lean_dec_ref(v___x_5831_);
lean_dec(v_stop_5826_);
lean_dec(v_start_5825_);
lean_dec_ref(v_array_5824_);
lean_del_object(v___x_5811_);
v_a_5864_ = lean_ctor_get(v___x_5853_, 0);
v_isSharedCheck_5871_ = !lean_is_exclusive(v___x_5853_);
if (v_isSharedCheck_5871_ == 0)
{
v___x_5866_ = v___x_5853_;
v_isShared_5867_ = v_isSharedCheck_5871_;
goto v_resetjp_5865_;
}
else
{
lean_inc(v_a_5864_);
lean_dec(v___x_5853_);
v___x_5866_ = lean_box(0);
v_isShared_5867_ = v_isSharedCheck_5871_;
goto v_resetjp_5865_;
}
v_resetjp_5865_:
{
lean_object* v___x_5869_; 
if (v_isShared_5867_ == 0)
{
v___x_5869_ = v___x_5866_;
goto v_reusejp_5868_;
}
else
{
lean_object* v_reuseFailAlloc_5870_; 
v_reuseFailAlloc_5870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5870_, 0, v_a_5864_);
v___x_5869_ = v_reuseFailAlloc_5870_;
goto v_reusejp_5868_;
}
v_reusejp_5868_:
{
return v___x_5869_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___boxed(lean_object* v_as_5882_, lean_object* v_sz_5883_, lean_object* v_i_5884_, lean_object* v_b_5885_, lean_object* v___y_5886_, lean_object* v___y_5887_, lean_object* v___y_5888_, lean_object* v___y_5889_, lean_object* v___y_5890_){
_start:
{
size_t v_sz_boxed_5891_; size_t v_i_boxed_5892_; lean_object* v_res_5893_; 
v_sz_boxed_5891_ = lean_unbox_usize(v_sz_5883_);
lean_dec(v_sz_5883_);
v_i_boxed_5892_ = lean_unbox_usize(v_i_5884_);
lean_dec(v_i_5884_);
v_res_5893_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(v_as_5882_, v_sz_boxed_5891_, v_i_boxed_5892_, v_b_5885_, v___y_5886_, v___y_5887_, v___y_5888_, v___y_5889_);
lean_dec(v___y_5889_);
lean_dec_ref(v___y_5888_);
lean_dec(v___y_5887_);
lean_dec_ref(v___y_5886_);
lean_dec_ref(v_as_5882_);
return v_res_5893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___lam__0(lean_object* v_value_5894_, lean_object* v_decrTactics_5895_, lean_object* v_argsPacker_5896_, lean_object* v_funNames_5897_, lean_object* v___y_5898_, lean_object* v___y_5899_, lean_object* v___y_5900_, lean_object* v___y_5901_){
_start:
{
lean_object* v___x_5903_; 
lean_inc_ref(v_value_5894_);
v___x_5903_ = l_Lean_Meta_getMVarsNoDelayed(v_value_5894_, v___y_5898_, v___y_5899_, v___y_5900_, v___y_5901_);
if (lean_obj_tag(v___x_5903_) == 0)
{
lean_object* v_a_5904_; lean_object* v___x_5905_; 
v_a_5904_ = lean_ctor_get(v___x_5903_, 0);
lean_inc(v_a_5904_);
lean_dec_ref_known(v___x_5903_, 1);
v___x_5905_ = l_Lean_Elab_WF_assignSubsumed(v_a_5904_, v___y_5898_, v___y_5899_, v___y_5900_, v___y_5901_);
lean_dec(v_a_5904_);
if (lean_obj_tag(v___x_5905_) == 0)
{
lean_object* v_a_5906_; lean_object* v___x_5907_; lean_object* v___x_5908_; 
v_a_5906_ = lean_ctor_get(v___x_5905_, 0);
lean_inc(v_a_5906_);
lean_dec_ref_known(v___x_5905_, 1);
v___x_5907_ = lean_array_get_size(v_decrTactics_5895_);
v___x_5908_ = l_Lean_Elab_WF_groupGoalsByFunction(v_argsPacker_5896_, v___x_5907_, v_a_5906_, v___y_5898_, v___y_5899_, v___y_5900_, v___y_5901_);
lean_dec(v_a_5906_);
if (lean_obj_tag(v___x_5908_) == 0)
{
lean_object* v_a_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; size_t v_sz_5915_; size_t v___x_5916_; lean_object* v___x_5917_; 
v_a_5909_ = lean_ctor_get(v___x_5908_, 0);
lean_inc(v_a_5909_);
lean_dec_ref_known(v___x_5908_, 1);
v___x_5910_ = lean_unsigned_to_nat(0u);
v___x_5911_ = lean_array_get_size(v_a_5909_);
v___x_5912_ = l_Array_toSubarray___redArg(v_a_5909_, v___x_5910_, v___x_5911_);
v___x_5913_ = l_Array_toSubarray___redArg(v_decrTactics_5895_, v___x_5910_, v___x_5907_);
v___x_5914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5914_, 0, v___x_5912_);
lean_ctor_set(v___x_5914_, 1, v___x_5913_);
v_sz_5915_ = lean_array_size(v_funNames_5897_);
v___x_5916_ = ((size_t)0ULL);
v___x_5917_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(v_funNames_5897_, v_sz_5915_, v___x_5916_, v___x_5914_, v___y_5898_, v___y_5899_, v___y_5900_, v___y_5901_);
if (lean_obj_tag(v___x_5917_) == 0)
{
lean_object* v___x_5918_; 
lean_dec_ref_known(v___x_5917_, 1);
v___x_5918_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_value_5894_, v___y_5899_);
return v___x_5918_;
}
else
{
lean_object* v_a_5919_; lean_object* v___x_5921_; uint8_t v_isShared_5922_; uint8_t v_isSharedCheck_5926_; 
lean_dec_ref(v_value_5894_);
v_a_5919_ = lean_ctor_get(v___x_5917_, 0);
v_isSharedCheck_5926_ = !lean_is_exclusive(v___x_5917_);
if (v_isSharedCheck_5926_ == 0)
{
v___x_5921_ = v___x_5917_;
v_isShared_5922_ = v_isSharedCheck_5926_;
goto v_resetjp_5920_;
}
else
{
lean_inc(v_a_5919_);
lean_dec(v___x_5917_);
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
lean_dec_ref(v_decrTactics_5895_);
lean_dec_ref(v_value_5894_);
v_a_5927_ = lean_ctor_get(v___x_5908_, 0);
v_isSharedCheck_5934_ = !lean_is_exclusive(v___x_5908_);
if (v_isSharedCheck_5934_ == 0)
{
v___x_5929_ = v___x_5908_;
v_isShared_5930_ = v_isSharedCheck_5934_;
goto v_resetjp_5928_;
}
else
{
lean_inc(v_a_5927_);
lean_dec(v___x_5908_);
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
lean_dec_ref(v_decrTactics_5895_);
lean_dec_ref(v_value_5894_);
v_a_5935_ = lean_ctor_get(v___x_5905_, 0);
v_isSharedCheck_5942_ = !lean_is_exclusive(v___x_5905_);
if (v_isSharedCheck_5942_ == 0)
{
v___x_5937_ = v___x_5905_;
v_isShared_5938_ = v_isSharedCheck_5942_;
goto v_resetjp_5936_;
}
else
{
lean_inc(v_a_5935_);
lean_dec(v___x_5905_);
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
else
{
lean_object* v_a_5943_; lean_object* v___x_5945_; uint8_t v_isShared_5946_; uint8_t v_isSharedCheck_5950_; 
lean_dec_ref(v_decrTactics_5895_);
lean_dec_ref(v_value_5894_);
v_a_5943_ = lean_ctor_get(v___x_5903_, 0);
v_isSharedCheck_5950_ = !lean_is_exclusive(v___x_5903_);
if (v_isSharedCheck_5950_ == 0)
{
v___x_5945_ = v___x_5903_;
v_isShared_5946_ = v_isSharedCheck_5950_;
goto v_resetjp_5944_;
}
else
{
lean_inc(v_a_5943_);
lean_dec(v___x_5903_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___lam__0___boxed(lean_object* v_value_5951_, lean_object* v_decrTactics_5952_, lean_object* v_argsPacker_5953_, lean_object* v_funNames_5954_, lean_object* v___y_5955_, lean_object* v___y_5956_, lean_object* v___y_5957_, lean_object* v___y_5958_, lean_object* v___y_5959_){
_start:
{
lean_object* v_res_5960_; 
v_res_5960_ = l_Lean_Elab_WF_solveDecreasingGoals___lam__0(v_value_5951_, v_decrTactics_5952_, v_argsPacker_5953_, v_funNames_5954_, v___y_5955_, v___y_5956_, v___y_5957_, v___y_5958_);
lean_dec(v___y_5958_);
lean_dec_ref(v___y_5957_);
lean_dec(v___y_5956_);
lean_dec_ref(v___y_5955_);
lean_dec_ref(v_funNames_5954_);
lean_dec_ref(v_argsPacker_5953_);
return v_res_5960_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(lean_object* v___y_5961_, uint8_t v_isExporting_5962_, lean_object* v___x_5963_, lean_object* v___y_5964_, lean_object* v___x_5965_, lean_object* v_a_x3f_5966_){
_start:
{
lean_object* v___x_5968_; lean_object* v_env_5969_; lean_object* v_nextMacroScope_5970_; lean_object* v_ngen_5971_; lean_object* v_auxDeclNGen_5972_; lean_object* v_traceState_5973_; lean_object* v_messages_5974_; lean_object* v_infoState_5975_; lean_object* v_snapshotTasks_5976_; lean_object* v___x_5978_; uint8_t v_isShared_5979_; uint8_t v_isSharedCheck_6001_; 
v___x_5968_ = lean_st_ref_take(v___y_5961_);
v_env_5969_ = lean_ctor_get(v___x_5968_, 0);
v_nextMacroScope_5970_ = lean_ctor_get(v___x_5968_, 1);
v_ngen_5971_ = lean_ctor_get(v___x_5968_, 2);
v_auxDeclNGen_5972_ = lean_ctor_get(v___x_5968_, 3);
v_traceState_5973_ = lean_ctor_get(v___x_5968_, 4);
v_messages_5974_ = lean_ctor_get(v___x_5968_, 6);
v_infoState_5975_ = lean_ctor_get(v___x_5968_, 7);
v_snapshotTasks_5976_ = lean_ctor_get(v___x_5968_, 8);
v_isSharedCheck_6001_ = !lean_is_exclusive(v___x_5968_);
if (v_isSharedCheck_6001_ == 0)
{
lean_object* v_unused_6002_; 
v_unused_6002_ = lean_ctor_get(v___x_5968_, 5);
lean_dec(v_unused_6002_);
v___x_5978_ = v___x_5968_;
v_isShared_5979_ = v_isSharedCheck_6001_;
goto v_resetjp_5977_;
}
else
{
lean_inc(v_snapshotTasks_5976_);
lean_inc(v_infoState_5975_);
lean_inc(v_messages_5974_);
lean_inc(v_traceState_5973_);
lean_inc(v_auxDeclNGen_5972_);
lean_inc(v_ngen_5971_);
lean_inc(v_nextMacroScope_5970_);
lean_inc(v_env_5969_);
lean_dec(v___x_5968_);
v___x_5978_ = lean_box(0);
v_isShared_5979_ = v_isSharedCheck_6001_;
goto v_resetjp_5977_;
}
v_resetjp_5977_:
{
lean_object* v___x_5980_; lean_object* v___x_5982_; 
v___x_5980_ = l_Lean_Environment_setExporting(v_env_5969_, v_isExporting_5962_);
if (v_isShared_5979_ == 0)
{
lean_ctor_set(v___x_5978_, 5, v___x_5963_);
lean_ctor_set(v___x_5978_, 0, v___x_5980_);
v___x_5982_ = v___x_5978_;
goto v_reusejp_5981_;
}
else
{
lean_object* v_reuseFailAlloc_6000_; 
v_reuseFailAlloc_6000_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6000_, 0, v___x_5980_);
lean_ctor_set(v_reuseFailAlloc_6000_, 1, v_nextMacroScope_5970_);
lean_ctor_set(v_reuseFailAlloc_6000_, 2, v_ngen_5971_);
lean_ctor_set(v_reuseFailAlloc_6000_, 3, v_auxDeclNGen_5972_);
lean_ctor_set(v_reuseFailAlloc_6000_, 4, v_traceState_5973_);
lean_ctor_set(v_reuseFailAlloc_6000_, 5, v___x_5963_);
lean_ctor_set(v_reuseFailAlloc_6000_, 6, v_messages_5974_);
lean_ctor_set(v_reuseFailAlloc_6000_, 7, v_infoState_5975_);
lean_ctor_set(v_reuseFailAlloc_6000_, 8, v_snapshotTasks_5976_);
v___x_5982_ = v_reuseFailAlloc_6000_;
goto v_reusejp_5981_;
}
v_reusejp_5981_:
{
lean_object* v___x_5983_; lean_object* v___x_5984_; lean_object* v_mctx_5985_; lean_object* v_zetaDeltaFVarIds_5986_; lean_object* v_postponed_5987_; lean_object* v_diag_5988_; lean_object* v___x_5990_; uint8_t v_isShared_5991_; uint8_t v_isSharedCheck_5998_; 
v___x_5983_ = lean_st_ref_put(v___y_5961_, v___x_5982_);
v___x_5984_ = lean_st_ref_take(v___y_5964_);
v_mctx_5985_ = lean_ctor_get(v___x_5984_, 0);
v_zetaDeltaFVarIds_5986_ = lean_ctor_get(v___x_5984_, 2);
v_postponed_5987_ = lean_ctor_get(v___x_5984_, 3);
v_diag_5988_ = lean_ctor_get(v___x_5984_, 4);
v_isSharedCheck_5998_ = !lean_is_exclusive(v___x_5984_);
if (v_isSharedCheck_5998_ == 0)
{
lean_object* v_unused_5999_; 
v_unused_5999_ = lean_ctor_get(v___x_5984_, 1);
lean_dec(v_unused_5999_);
v___x_5990_ = v___x_5984_;
v_isShared_5991_ = v_isSharedCheck_5998_;
goto v_resetjp_5989_;
}
else
{
lean_inc(v_diag_5988_);
lean_inc(v_postponed_5987_);
lean_inc(v_zetaDeltaFVarIds_5986_);
lean_inc(v_mctx_5985_);
lean_dec(v___x_5984_);
v___x_5990_ = lean_box(0);
v_isShared_5991_ = v_isSharedCheck_5998_;
goto v_resetjp_5989_;
}
v_resetjp_5989_:
{
lean_object* v___x_5993_; 
if (v_isShared_5991_ == 0)
{
lean_ctor_set(v___x_5990_, 1, v___x_5965_);
v___x_5993_ = v___x_5990_;
goto v_reusejp_5992_;
}
else
{
lean_object* v_reuseFailAlloc_5997_; 
v_reuseFailAlloc_5997_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5997_, 0, v_mctx_5985_);
lean_ctor_set(v_reuseFailAlloc_5997_, 1, v___x_5965_);
lean_ctor_set(v_reuseFailAlloc_5997_, 2, v_zetaDeltaFVarIds_5986_);
lean_ctor_set(v_reuseFailAlloc_5997_, 3, v_postponed_5987_);
lean_ctor_set(v_reuseFailAlloc_5997_, 4, v_diag_5988_);
v___x_5993_ = v_reuseFailAlloc_5997_;
goto v_reusejp_5992_;
}
v_reusejp_5992_:
{
lean_object* v___x_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; 
v___x_5994_ = lean_st_ref_put(v___y_5964_, v___x_5993_);
v___x_5995_ = lean_box(0);
v___x_5996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5996_, 0, v___x_5995_);
return v___x_5996_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0___boxed(lean_object* v___y_6003_, lean_object* v_isExporting_6004_, lean_object* v___x_6005_, lean_object* v___y_6006_, lean_object* v___x_6007_, lean_object* v_a_x3f_6008_, lean_object* v___y_6009_){
_start:
{
uint8_t v_isExporting_boxed_6010_; lean_object* v_res_6011_; 
v_isExporting_boxed_6010_ = lean_unbox(v_isExporting_6004_);
v_res_6011_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6003_, v_isExporting_boxed_6010_, v___x_6005_, v___y_6006_, v___x_6007_, v_a_x3f_6008_);
lean_dec(v_a_x3f_6008_);
lean_dec(v___y_6006_);
lean_dec(v___y_6003_);
return v_res_6011_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_6012_; 
v___x_6012_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_6012_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_6013_; lean_object* v___x_6014_; 
v___x_6013_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0);
v___x_6014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6014_, 0, v___x_6013_);
return v___x_6014_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_6015_; lean_object* v___x_6016_; 
v___x_6015_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1);
v___x_6016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6016_, 0, v___x_6015_);
lean_ctor_set(v___x_6016_, 1, v___x_6015_);
return v___x_6016_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_6017_; lean_object* v___x_6018_; 
v___x_6017_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1);
v___x_6018_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6018_, 0, v___x_6017_);
lean_ctor_set(v___x_6018_, 1, v___x_6017_);
lean_ctor_set(v___x_6018_, 2, v___x_6017_);
lean_ctor_set(v___x_6018_, 3, v___x_6017_);
lean_ctor_set(v___x_6018_, 4, v___x_6017_);
lean_ctor_set(v___x_6018_, 5, v___x_6017_);
return v___x_6018_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(lean_object* v_x_6019_, uint8_t v_isExporting_6020_, lean_object* v___y_6021_, lean_object* v___y_6022_, lean_object* v___y_6023_, lean_object* v___y_6024_){
_start:
{
lean_object* v___x_6026_; lean_object* v_env_6027_; lean_object* v___x_6028_; uint8_t v_isModule_6029_; 
v___x_6026_ = lean_st_ref_get(v___y_6024_);
v_env_6027_ = lean_ctor_get(v___x_6026_, 0);
lean_inc_ref(v_env_6027_);
lean_dec(v___x_6026_);
v___x_6028_ = l_Lean_Environment_header(v_env_6027_);
v_isModule_6029_ = lean_ctor_get_uint8(v___x_6028_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_6028_);
if (v_isModule_6029_ == 0)
{
lean_object* v___x_6030_; 
lean_dec_ref(v_env_6027_);
lean_inc(v___y_6024_);
lean_inc_ref(v___y_6023_);
lean_inc(v___y_6022_);
lean_inc_ref(v___y_6021_);
v___x_6030_ = lean_apply_5(v_x_6019_, v___y_6021_, v___y_6022_, v___y_6023_, v___y_6024_, lean_box(0));
return v___x_6030_;
}
else
{
uint8_t v_isExporting_6031_; 
v_isExporting_6031_ = lean_ctor_get_uint8(v_env_6027_, sizeof(void*)*8);
lean_dec_ref(v_env_6027_);
if (v_isExporting_6020_ == 0)
{
if (v_isExporting_6031_ == 0)
{
lean_object* v___x_6097_; 
lean_inc(v___y_6024_);
lean_inc_ref(v___y_6023_);
lean_inc(v___y_6022_);
lean_inc_ref(v___y_6021_);
v___x_6097_ = lean_apply_5(v_x_6019_, v___y_6021_, v___y_6022_, v___y_6023_, v___y_6024_, lean_box(0));
return v___x_6097_;
}
else
{
goto v___jp_6032_;
}
}
else
{
if (v_isExporting_6031_ == 0)
{
goto v___jp_6032_;
}
else
{
lean_object* v___x_6098_; 
lean_inc(v___y_6024_);
lean_inc_ref(v___y_6023_);
lean_inc(v___y_6022_);
lean_inc_ref(v___y_6021_);
v___x_6098_ = lean_apply_5(v_x_6019_, v___y_6021_, v___y_6022_, v___y_6023_, v___y_6024_, lean_box(0));
return v___x_6098_;
}
}
v___jp_6032_:
{
lean_object* v___x_6033_; lean_object* v_env_6034_; lean_object* v_nextMacroScope_6035_; lean_object* v_ngen_6036_; lean_object* v_auxDeclNGen_6037_; lean_object* v_traceState_6038_; lean_object* v_messages_6039_; lean_object* v_infoState_6040_; lean_object* v_snapshotTasks_6041_; lean_object* v___x_6043_; uint8_t v_isShared_6044_; uint8_t v_isSharedCheck_6095_; 
v___x_6033_ = lean_st_ref_take(v___y_6024_);
v_env_6034_ = lean_ctor_get(v___x_6033_, 0);
v_nextMacroScope_6035_ = lean_ctor_get(v___x_6033_, 1);
v_ngen_6036_ = lean_ctor_get(v___x_6033_, 2);
v_auxDeclNGen_6037_ = lean_ctor_get(v___x_6033_, 3);
v_traceState_6038_ = lean_ctor_get(v___x_6033_, 4);
v_messages_6039_ = lean_ctor_get(v___x_6033_, 6);
v_infoState_6040_ = lean_ctor_get(v___x_6033_, 7);
v_snapshotTasks_6041_ = lean_ctor_get(v___x_6033_, 8);
v_isSharedCheck_6095_ = !lean_is_exclusive(v___x_6033_);
if (v_isSharedCheck_6095_ == 0)
{
lean_object* v_unused_6096_; 
v_unused_6096_ = lean_ctor_get(v___x_6033_, 5);
lean_dec(v_unused_6096_);
v___x_6043_ = v___x_6033_;
v_isShared_6044_ = v_isSharedCheck_6095_;
goto v_resetjp_6042_;
}
else
{
lean_inc(v_snapshotTasks_6041_);
lean_inc(v_infoState_6040_);
lean_inc(v_messages_6039_);
lean_inc(v_traceState_6038_);
lean_inc(v_auxDeclNGen_6037_);
lean_inc(v_ngen_6036_);
lean_inc(v_nextMacroScope_6035_);
lean_inc(v_env_6034_);
lean_dec(v___x_6033_);
v___x_6043_ = lean_box(0);
v_isShared_6044_ = v_isSharedCheck_6095_;
goto v_resetjp_6042_;
}
v_resetjp_6042_:
{
lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6048_; 
v___x_6045_ = l_Lean_Environment_setExporting(v_env_6034_, v_isExporting_6020_);
v___x_6046_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2);
if (v_isShared_6044_ == 0)
{
lean_ctor_set(v___x_6043_, 5, v___x_6046_);
lean_ctor_set(v___x_6043_, 0, v___x_6045_);
v___x_6048_ = v___x_6043_;
goto v_reusejp_6047_;
}
else
{
lean_object* v_reuseFailAlloc_6094_; 
v_reuseFailAlloc_6094_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6094_, 0, v___x_6045_);
lean_ctor_set(v_reuseFailAlloc_6094_, 1, v_nextMacroScope_6035_);
lean_ctor_set(v_reuseFailAlloc_6094_, 2, v_ngen_6036_);
lean_ctor_set(v_reuseFailAlloc_6094_, 3, v_auxDeclNGen_6037_);
lean_ctor_set(v_reuseFailAlloc_6094_, 4, v_traceState_6038_);
lean_ctor_set(v_reuseFailAlloc_6094_, 5, v___x_6046_);
lean_ctor_set(v_reuseFailAlloc_6094_, 6, v_messages_6039_);
lean_ctor_set(v_reuseFailAlloc_6094_, 7, v_infoState_6040_);
lean_ctor_set(v_reuseFailAlloc_6094_, 8, v_snapshotTasks_6041_);
v___x_6048_ = v_reuseFailAlloc_6094_;
goto v_reusejp_6047_;
}
v_reusejp_6047_:
{
lean_object* v___x_6049_; lean_object* v___x_6050_; lean_object* v_mctx_6051_; lean_object* v_zetaDeltaFVarIds_6052_; lean_object* v_postponed_6053_; lean_object* v_diag_6054_; lean_object* v___x_6056_; uint8_t v_isShared_6057_; uint8_t v_isSharedCheck_6092_; 
v___x_6049_ = lean_st_ref_put(v___y_6024_, v___x_6048_);
v___x_6050_ = lean_st_ref_take(v___y_6022_);
v_mctx_6051_ = lean_ctor_get(v___x_6050_, 0);
v_zetaDeltaFVarIds_6052_ = lean_ctor_get(v___x_6050_, 2);
v_postponed_6053_ = lean_ctor_get(v___x_6050_, 3);
v_diag_6054_ = lean_ctor_get(v___x_6050_, 4);
v_isSharedCheck_6092_ = !lean_is_exclusive(v___x_6050_);
if (v_isSharedCheck_6092_ == 0)
{
lean_object* v_unused_6093_; 
v_unused_6093_ = lean_ctor_get(v___x_6050_, 1);
lean_dec(v_unused_6093_);
v___x_6056_ = v___x_6050_;
v_isShared_6057_ = v_isSharedCheck_6092_;
goto v_resetjp_6055_;
}
else
{
lean_inc(v_diag_6054_);
lean_inc(v_postponed_6053_);
lean_inc(v_zetaDeltaFVarIds_6052_);
lean_inc(v_mctx_6051_);
lean_dec(v___x_6050_);
v___x_6056_ = lean_box(0);
v_isShared_6057_ = v_isSharedCheck_6092_;
goto v_resetjp_6055_;
}
v_resetjp_6055_:
{
lean_object* v___x_6058_; lean_object* v___x_6060_; 
v___x_6058_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3);
if (v_isShared_6057_ == 0)
{
lean_ctor_set(v___x_6056_, 1, v___x_6058_);
v___x_6060_ = v___x_6056_;
goto v_reusejp_6059_;
}
else
{
lean_object* v_reuseFailAlloc_6091_; 
v_reuseFailAlloc_6091_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6091_, 0, v_mctx_6051_);
lean_ctor_set(v_reuseFailAlloc_6091_, 1, v___x_6058_);
lean_ctor_set(v_reuseFailAlloc_6091_, 2, v_zetaDeltaFVarIds_6052_);
lean_ctor_set(v_reuseFailAlloc_6091_, 3, v_postponed_6053_);
lean_ctor_set(v_reuseFailAlloc_6091_, 4, v_diag_6054_);
v___x_6060_ = v_reuseFailAlloc_6091_;
goto v_reusejp_6059_;
}
v_reusejp_6059_:
{
lean_object* v___x_6061_; lean_object* v_r_6062_; 
v___x_6061_ = lean_st_ref_put(v___y_6022_, v___x_6060_);
lean_inc(v___y_6024_);
lean_inc_ref(v___y_6023_);
lean_inc(v___y_6022_);
lean_inc_ref(v___y_6021_);
v_r_6062_ = lean_apply_5(v_x_6019_, v___y_6021_, v___y_6022_, v___y_6023_, v___y_6024_, lean_box(0));
if (lean_obj_tag(v_r_6062_) == 0)
{
lean_object* v_a_6063_; lean_object* v___x_6065_; uint8_t v_isShared_6066_; uint8_t v_isSharedCheck_6079_; 
v_a_6063_ = lean_ctor_get(v_r_6062_, 0);
v_isSharedCheck_6079_ = !lean_is_exclusive(v_r_6062_);
if (v_isSharedCheck_6079_ == 0)
{
v___x_6065_ = v_r_6062_;
v_isShared_6066_ = v_isSharedCheck_6079_;
goto v_resetjp_6064_;
}
else
{
lean_inc(v_a_6063_);
lean_dec(v_r_6062_);
v___x_6065_ = lean_box(0);
v_isShared_6066_ = v_isSharedCheck_6079_;
goto v_resetjp_6064_;
}
v_resetjp_6064_:
{
lean_object* v___x_6068_; 
lean_inc(v_a_6063_);
if (v_isShared_6066_ == 0)
{
lean_ctor_set_tag(v___x_6065_, 1);
v___x_6068_ = v___x_6065_;
goto v_reusejp_6067_;
}
else
{
lean_object* v_reuseFailAlloc_6078_; 
v_reuseFailAlloc_6078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6078_, 0, v_a_6063_);
v___x_6068_ = v_reuseFailAlloc_6078_;
goto v_reusejp_6067_;
}
v_reusejp_6067_:
{
lean_object* v___x_6069_; lean_object* v___x_6071_; uint8_t v_isShared_6072_; uint8_t v_isSharedCheck_6076_; 
v___x_6069_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6024_, v_isExporting_6031_, v___x_6046_, v___y_6022_, v___x_6058_, v___x_6068_);
lean_dec_ref(v___x_6068_);
v_isSharedCheck_6076_ = !lean_is_exclusive(v___x_6069_);
if (v_isSharedCheck_6076_ == 0)
{
lean_object* v_unused_6077_; 
v_unused_6077_ = lean_ctor_get(v___x_6069_, 0);
lean_dec(v_unused_6077_);
v___x_6071_ = v___x_6069_;
v_isShared_6072_ = v_isSharedCheck_6076_;
goto v_resetjp_6070_;
}
else
{
lean_dec(v___x_6069_);
v___x_6071_ = lean_box(0);
v_isShared_6072_ = v_isSharedCheck_6076_;
goto v_resetjp_6070_;
}
v_resetjp_6070_:
{
lean_object* v___x_6074_; 
if (v_isShared_6072_ == 0)
{
lean_ctor_set(v___x_6071_, 0, v_a_6063_);
v___x_6074_ = v___x_6071_;
goto v_reusejp_6073_;
}
else
{
lean_object* v_reuseFailAlloc_6075_; 
v_reuseFailAlloc_6075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6075_, 0, v_a_6063_);
v___x_6074_ = v_reuseFailAlloc_6075_;
goto v_reusejp_6073_;
}
v_reusejp_6073_:
{
return v___x_6074_;
}
}
}
}
}
else
{
lean_object* v_a_6080_; lean_object* v___x_6081_; lean_object* v___x_6082_; lean_object* v___x_6084_; uint8_t v_isShared_6085_; uint8_t v_isSharedCheck_6089_; 
v_a_6080_ = lean_ctor_get(v_r_6062_, 0);
lean_inc(v_a_6080_);
lean_dec_ref_known(v_r_6062_, 1);
v___x_6081_ = lean_box(0);
v___x_6082_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6024_, v_isExporting_6031_, v___x_6046_, v___y_6022_, v___x_6058_, v___x_6081_);
v_isSharedCheck_6089_ = !lean_is_exclusive(v___x_6082_);
if (v_isSharedCheck_6089_ == 0)
{
lean_object* v_unused_6090_; 
v_unused_6090_ = lean_ctor_get(v___x_6082_, 0);
lean_dec(v_unused_6090_);
v___x_6084_ = v___x_6082_;
v_isShared_6085_ = v_isSharedCheck_6089_;
goto v_resetjp_6083_;
}
else
{
lean_dec(v___x_6082_);
v___x_6084_ = lean_box(0);
v_isShared_6085_ = v_isSharedCheck_6089_;
goto v_resetjp_6083_;
}
v_resetjp_6083_:
{
lean_object* v___x_6087_; 
if (v_isShared_6085_ == 0)
{
lean_ctor_set_tag(v___x_6084_, 1);
lean_ctor_set(v___x_6084_, 0, v_a_6080_);
v___x_6087_ = v___x_6084_;
goto v_reusejp_6086_;
}
else
{
lean_object* v_reuseFailAlloc_6088_; 
v_reuseFailAlloc_6088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6088_, 0, v_a_6080_);
v___x_6087_ = v_reuseFailAlloc_6088_;
goto v_reusejp_6086_;
}
v_reusejp_6086_:
{
return v___x_6087_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___boxed(lean_object* v_x_6099_, lean_object* v_isExporting_6100_, lean_object* v___y_6101_, lean_object* v___y_6102_, lean_object* v___y_6103_, lean_object* v___y_6104_, lean_object* v___y_6105_){
_start:
{
uint8_t v_isExporting_boxed_6106_; lean_object* v_res_6107_; 
v_isExporting_boxed_6106_ = lean_unbox(v_isExporting_6100_);
v_res_6107_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6099_, v_isExporting_boxed_6106_, v___y_6101_, v___y_6102_, v___y_6103_, v___y_6104_);
lean_dec(v___y_6104_);
lean_dec_ref(v___y_6103_);
lean_dec(v___y_6102_);
lean_dec_ref(v___y_6101_);
return v_res_6107_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(lean_object* v_x_6108_, uint8_t v_when_6109_, lean_object* v___y_6110_, lean_object* v___y_6111_, lean_object* v___y_6112_, lean_object* v___y_6113_){
_start:
{
if (v_when_6109_ == 0)
{
lean_object* v___x_6115_; 
lean_inc(v___y_6113_);
lean_inc_ref(v___y_6112_);
lean_inc(v___y_6111_);
lean_inc_ref(v___y_6110_);
v___x_6115_ = lean_apply_5(v_x_6108_, v___y_6110_, v___y_6111_, v___y_6112_, v___y_6113_, lean_box(0));
return v___x_6115_;
}
else
{
uint8_t v___x_6116_; lean_object* v___x_6117_; 
v___x_6116_ = 0;
v___x_6117_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6108_, v___x_6116_, v___y_6110_, v___y_6111_, v___y_6112_, v___y_6113_);
return v___x_6117_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg___boxed(lean_object* v_x_6118_, lean_object* v_when_6119_, lean_object* v___y_6120_, lean_object* v___y_6121_, lean_object* v___y_6122_, lean_object* v___y_6123_, lean_object* v___y_6124_){
_start:
{
uint8_t v_when_boxed_6125_; lean_object* v_res_6126_; 
v_when_boxed_6125_ = lean_unbox(v_when_6119_);
v_res_6126_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v_x_6118_, v_when_boxed_6125_, v___y_6120_, v___y_6121_, v___y_6122_, v___y_6123_);
lean_dec(v___y_6123_);
lean_dec_ref(v___y_6122_);
lean_dec(v___y_6121_);
lean_dec_ref(v___y_6120_);
return v_res_6126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals(lean_object* v_funNames_6127_, lean_object* v_argsPacker_6128_, lean_object* v_decrTactics_6129_, lean_object* v_value_6130_, lean_object* v_a_6131_, lean_object* v_a_6132_, lean_object* v_a_6133_, lean_object* v_a_6134_){
_start:
{
lean_object* v___f_6136_; uint8_t v___x_6137_; lean_object* v___x_6138_; 
v___f_6136_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_solveDecreasingGoals___lam__0___boxed), 9, 4);
lean_closure_set(v___f_6136_, 0, v_value_6130_);
lean_closure_set(v___f_6136_, 1, v_decrTactics_6129_);
lean_closure_set(v___f_6136_, 2, v_argsPacker_6128_);
lean_closure_set(v___f_6136_, 3, v_funNames_6127_);
v___x_6137_ = 1;
v___x_6138_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v___f_6136_, v___x_6137_, v_a_6131_, v_a_6132_, v_a_6133_, v_a_6134_);
return v___x_6138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___boxed(lean_object* v_funNames_6139_, lean_object* v_argsPacker_6140_, lean_object* v_decrTactics_6141_, lean_object* v_value_6142_, lean_object* v_a_6143_, lean_object* v_a_6144_, lean_object* v_a_6145_, lean_object* v_a_6146_, lean_object* v_a_6147_){
_start:
{
lean_object* v_res_6148_; 
v_res_6148_ = l_Lean_Elab_WF_solveDecreasingGoals(v_funNames_6139_, v_argsPacker_6140_, v_decrTactics_6141_, v_value_6142_, v_a_6143_, v_a_6144_, v_a_6145_, v_a_6146_);
lean_dec(v_a_6146_);
lean_dec_ref(v_a_6145_);
lean_dec(v_a_6144_);
lean_dec_ref(v_a_6143_);
return v_res_6148_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1(lean_object* v_00_u03b1_6149_, lean_object* v_msg_6150_, lean_object* v___y_6151_, lean_object* v___y_6152_, lean_object* v___y_6153_, lean_object* v___y_6154_, lean_object* v___y_6155_, lean_object* v___y_6156_){
_start:
{
lean_object* v___x_6158_; 
v___x_6158_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v_msg_6150_, v___y_6151_, v___y_6152_, v___y_6153_, v___y_6154_, v___y_6155_, v___y_6156_);
return v___x_6158_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___boxed(lean_object* v_00_u03b1_6159_, lean_object* v_msg_6160_, lean_object* v___y_6161_, lean_object* v___y_6162_, lean_object* v___y_6163_, lean_object* v___y_6164_, lean_object* v___y_6165_, lean_object* v___y_6166_, lean_object* v___y_6167_){
_start:
{
lean_object* v_res_6168_; 
v_res_6168_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1(v_00_u03b1_6159_, v_msg_6160_, v___y_6161_, v___y_6162_, v___y_6163_, v___y_6164_, v___y_6165_, v___y_6166_);
lean_dec(v___y_6166_);
lean_dec_ref(v___y_6165_);
lean_dec(v___y_6164_);
lean_dec_ref(v___y_6163_);
lean_dec(v___y_6162_);
lean_dec_ref(v___y_6161_);
return v_res_6168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4(lean_object* v___y_6169_, lean_object* v___y_6170_, lean_object* v___y_6171_, lean_object* v___y_6172_, lean_object* v___y_6173_, lean_object* v___y_6174_, lean_object* v___y_6175_, lean_object* v___y_6176_){
_start:
{
lean_object* v___x_6178_; 
v___x_6178_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_6176_);
return v___x_6178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___boxed(lean_object* v___y_6179_, lean_object* v___y_6180_, lean_object* v___y_6181_, lean_object* v___y_6182_, lean_object* v___y_6183_, lean_object* v___y_6184_, lean_object* v___y_6185_, lean_object* v___y_6186_, lean_object* v___y_6187_){
_start:
{
lean_object* v_res_6188_; 
v_res_6188_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4(v___y_6179_, v___y_6180_, v___y_6181_, v___y_6182_, v___y_6183_, v___y_6184_, v___y_6185_, v___y_6186_);
lean_dec(v___y_6186_);
lean_dec_ref(v___y_6185_);
lean_dec(v___y_6184_);
lean_dec_ref(v___y_6183_);
lean_dec(v___y_6182_);
lean_dec_ref(v___y_6181_);
lean_dec(v___y_6180_);
lean_dec_ref(v___y_6179_);
return v_res_6188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3(lean_object* v_00_u03b1_6189_, lean_object* v_x_6190_, lean_object* v_mkInfoTree_6191_, lean_object* v___y_6192_, lean_object* v___y_6193_, lean_object* v___y_6194_, lean_object* v___y_6195_, lean_object* v___y_6196_, lean_object* v___y_6197_, lean_object* v___y_6198_, lean_object* v___y_6199_){
_start:
{
lean_object* v___x_6201_; 
v___x_6201_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v_x_6190_, v_mkInfoTree_6191_, v___y_6192_, v___y_6193_, v___y_6194_, v___y_6195_, v___y_6196_, v___y_6197_, v___y_6198_, v___y_6199_);
return v___x_6201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___boxed(lean_object* v_00_u03b1_6202_, lean_object* v_x_6203_, lean_object* v_mkInfoTree_6204_, lean_object* v___y_6205_, lean_object* v___y_6206_, lean_object* v___y_6207_, lean_object* v___y_6208_, lean_object* v___y_6209_, lean_object* v___y_6210_, lean_object* v___y_6211_, lean_object* v___y_6212_, lean_object* v___y_6213_){
_start:
{
lean_object* v_res_6214_; 
v_res_6214_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3(v_00_u03b1_6202_, v_x_6203_, v_mkInfoTree_6204_, v___y_6205_, v___y_6206_, v___y_6207_, v___y_6208_, v___y_6209_, v___y_6210_, v___y_6211_, v___y_6212_);
lean_dec(v___y_6212_);
lean_dec_ref(v___y_6211_);
lean_dec(v___y_6210_);
lean_dec_ref(v___y_6209_);
lean_dec(v___y_6208_);
lean_dec_ref(v___y_6207_);
lean_dec(v___y_6206_);
lean_dec_ref(v___y_6205_);
return v_res_6214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5(lean_object* v_as_6215_, size_t v_i_6216_, size_t v_stop_6217_, lean_object* v_b_6218_, lean_object* v___y_6219_, lean_object* v___y_6220_, lean_object* v___y_6221_, lean_object* v___y_6222_, lean_object* v___y_6223_, lean_object* v___y_6224_){
_start:
{
lean_object* v___x_6226_; 
v___x_6226_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v_as_6215_, v_i_6216_, v_stop_6217_, v_b_6218_, v___y_6221_, v___y_6222_, v___y_6223_, v___y_6224_);
return v___x_6226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___boxed(lean_object* v_as_6227_, lean_object* v_i_6228_, lean_object* v_stop_6229_, lean_object* v_b_6230_, lean_object* v___y_6231_, lean_object* v___y_6232_, lean_object* v___y_6233_, lean_object* v___y_6234_, lean_object* v___y_6235_, lean_object* v___y_6236_, lean_object* v___y_6237_){
_start:
{
size_t v_i_boxed_6238_; size_t v_stop_boxed_6239_; lean_object* v_res_6240_; 
v_i_boxed_6238_ = lean_unbox_usize(v_i_6228_);
lean_dec(v_i_6228_);
v_stop_boxed_6239_ = lean_unbox_usize(v_stop_6229_);
lean_dec(v_stop_6229_);
v_res_6240_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5(v_as_6227_, v_i_boxed_6238_, v_stop_boxed_6239_, v_b_6230_, v___y_6231_, v___y_6232_, v___y_6233_, v___y_6234_, v___y_6235_, v___y_6236_);
lean_dec(v___y_6236_);
lean_dec_ref(v___y_6235_);
lean_dec(v___y_6234_);
lean_dec_ref(v___y_6233_);
lean_dec(v___y_6232_);
lean_dec_ref(v___y_6231_);
lean_dec_ref(v_as_6227_);
return v_res_6240_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10(lean_object* v_00_u03b1_6241_, lean_object* v_x_6242_, uint8_t v_isExporting_6243_, lean_object* v___y_6244_, lean_object* v___y_6245_, lean_object* v___y_6246_, lean_object* v___y_6247_){
_start:
{
lean_object* v___x_6249_; 
v___x_6249_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6242_, v_isExporting_6243_, v___y_6244_, v___y_6245_, v___y_6246_, v___y_6247_);
return v___x_6249_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___boxed(lean_object* v_00_u03b1_6250_, lean_object* v_x_6251_, lean_object* v_isExporting_6252_, lean_object* v___y_6253_, lean_object* v___y_6254_, lean_object* v___y_6255_, lean_object* v___y_6256_, lean_object* v___y_6257_){
_start:
{
uint8_t v_isExporting_boxed_6258_; lean_object* v_res_6259_; 
v_isExporting_boxed_6258_ = lean_unbox(v_isExporting_6252_);
v_res_6259_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10(v_00_u03b1_6250_, v_x_6251_, v_isExporting_boxed_6258_, v___y_6253_, v___y_6254_, v___y_6255_, v___y_6256_);
lean_dec(v___y_6256_);
lean_dec_ref(v___y_6255_);
lean_dec(v___y_6254_);
lean_dec_ref(v___y_6253_);
return v_res_6259_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8(lean_object* v_00_u03b1_6260_, lean_object* v_x_6261_, uint8_t v_when_6262_, lean_object* v___y_6263_, lean_object* v___y_6264_, lean_object* v___y_6265_, lean_object* v___y_6266_){
_start:
{
lean_object* v___x_6268_; 
v___x_6268_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v_x_6261_, v_when_6262_, v___y_6263_, v___y_6264_, v___y_6265_, v___y_6266_);
return v___x_6268_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___boxed(lean_object* v_00_u03b1_6269_, lean_object* v_x_6270_, lean_object* v_when_6271_, lean_object* v___y_6272_, lean_object* v___y_6273_, lean_object* v___y_6274_, lean_object* v___y_6275_, lean_object* v___y_6276_){
_start:
{
uint8_t v_when_boxed_6277_; lean_object* v_res_6278_; 
v_when_boxed_6277_ = lean_unbox(v_when_6271_);
v_res_6278_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8(v_00_u03b1_6269_, v_x_6270_, v_when_boxed_6277_, v___y_6272_, v___y_6273_, v___y_6274_, v___y_6275_);
lean_dec(v___y_6275_);
lean_dec_ref(v___y_6274_);
lean_dec(v___y_6273_);
lean_dec_ref(v___y_6272_);
return v_res_6278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1(lean_object* v_msgData_6279_, lean_object* v_macroStack_6280_, lean_object* v___y_6281_, lean_object* v___y_6282_, lean_object* v___y_6283_, lean_object* v___y_6284_, lean_object* v___y_6285_, lean_object* v___y_6286_){
_start:
{
lean_object* v___x_6288_; 
v___x_6288_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_msgData_6279_, v_macroStack_6280_, v___y_6285_);
return v___x_6288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___boxed(lean_object* v_msgData_6289_, lean_object* v_macroStack_6290_, lean_object* v___y_6291_, lean_object* v___y_6292_, lean_object* v___y_6293_, lean_object* v___y_6294_, lean_object* v___y_6295_, lean_object* v___y_6296_, lean_object* v___y_6297_){
_start:
{
lean_object* v_res_6298_; 
v_res_6298_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1(v_msgData_6289_, v_macroStack_6290_, v___y_6291_, v___y_6292_, v___y_6293_, v___y_6294_, v___y_6295_, v___y_6296_);
lean_dec(v___y_6296_);
lean_dec_ref(v___y_6295_);
lean_dec(v___y_6294_);
lean_dec_ref(v___y_6293_);
lean_dec(v___y_6292_);
lean_dec_ref(v___y_6291_);
return v_res_6298_;
}
}
static lean_object* _init_l_Lean_Elab_WF_isNatLtWF___closed__4(void){
_start:
{
lean_object* v___x_6305_; lean_object* v___x_6306_; lean_object* v___x_6307_; 
v___x_6305_ = lean_box(0);
v___x_6306_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__3));
v___x_6307_ = l_Lean_mkConst(v___x_6306_, v___x_6305_);
return v___x_6307_;
}
}
static lean_object* _init_l_Lean_Elab_WF_isNatLtWF___closed__7(void){
_start:
{
lean_object* v___x_6312_; lean_object* v___x_6313_; lean_object* v___x_6314_; 
v___x_6312_ = lean_box(0);
v___x_6313_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__6));
v___x_6314_ = l_Lean_mkConst(v___x_6313_, v___x_6312_);
return v___x_6314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isNatLtWF(lean_object* v_wfRel_6315_, lean_object* v_a_6316_, lean_object* v_a_6317_, lean_object* v_a_6318_, lean_object* v_a_6319_){
_start:
{
lean_object* v___x_6321_; 
v___x_6321_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_wfRel_6315_, v_a_6317_);
if (lean_obj_tag(v___x_6321_) == 0)
{
lean_object* v_a_6322_; lean_object* v___x_6324_; uint8_t v_isShared_6325_; uint8_t v_isSharedCheck_6389_; 
v_a_6322_ = lean_ctor_get(v___x_6321_, 0);
v_isSharedCheck_6389_ = !lean_is_exclusive(v___x_6321_);
if (v_isSharedCheck_6389_ == 0)
{
v___x_6324_ = v___x_6321_;
v_isShared_6325_ = v_isSharedCheck_6389_;
goto v_resetjp_6323_;
}
else
{
lean_inc(v_a_6322_);
lean_dec(v___x_6321_);
v___x_6324_ = lean_box(0);
v_isShared_6325_ = v_isSharedCheck_6389_;
goto v_resetjp_6323_;
}
v_resetjp_6323_:
{
lean_object* v___x_6331_; uint8_t v___x_6332_; 
v___x_6331_ = l_Lean_Expr_cleanupAnnotations(v_a_6322_);
v___x_6332_ = l_Lean_Expr_isApp(v___x_6331_);
if (v___x_6332_ == 0)
{
lean_dec_ref(v___x_6331_);
goto v___jp_6326_;
}
else
{
lean_object* v_arg_6333_; lean_object* v___x_6334_; uint8_t v___x_6335_; 
v_arg_6333_ = lean_ctor_get(v___x_6331_, 1);
lean_inc_ref(v_arg_6333_);
v___x_6334_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6331_);
v___x_6335_ = l_Lean_Expr_isApp(v___x_6334_);
if (v___x_6335_ == 0)
{
lean_dec_ref(v___x_6334_);
lean_dec_ref(v_arg_6333_);
goto v___jp_6326_;
}
else
{
lean_object* v_arg_6336_; lean_object* v___x_6337_; uint8_t v___x_6338_; 
v_arg_6336_ = lean_ctor_get(v___x_6334_, 1);
lean_inc_ref(v_arg_6336_);
v___x_6337_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6334_);
v___x_6338_ = l_Lean_Expr_isApp(v___x_6337_);
if (v___x_6338_ == 0)
{
lean_dec_ref(v___x_6337_);
lean_dec_ref(v_arg_6336_);
lean_dec_ref(v_arg_6333_);
goto v___jp_6326_;
}
else
{
lean_object* v_arg_6339_; lean_object* v___x_6340_; uint8_t v___x_6341_; 
v_arg_6339_ = lean_ctor_get(v___x_6337_, 1);
lean_inc_ref(v_arg_6339_);
v___x_6340_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6337_);
v___x_6341_ = l_Lean_Expr_isApp(v___x_6340_);
if (v___x_6341_ == 0)
{
lean_dec_ref(v___x_6340_);
lean_dec_ref(v_arg_6339_);
lean_dec_ref(v_arg_6336_);
lean_dec_ref(v_arg_6333_);
goto v___jp_6326_;
}
else
{
lean_object* v___x_6342_; lean_object* v___x_6343_; uint8_t v___x_6344_; 
v___x_6342_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6340_);
v___x_6343_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__1));
v___x_6344_ = l_Lean_Expr_isConstOf(v___x_6342_, v___x_6343_);
lean_dec_ref(v___x_6342_);
if (v___x_6344_ == 0)
{
lean_dec_ref(v_arg_6339_);
lean_dec_ref(v_arg_6336_);
lean_dec_ref(v_arg_6333_);
goto v___jp_6326_;
}
else
{
lean_object* v___x_6345_; lean_object* v___x_6346_; 
lean_del_object(v___x_6324_);
v___x_6345_ = lean_obj_once(&l_Lean_Elab_WF_isNatLtWF___closed__4, &l_Lean_Elab_WF_isNatLtWF___closed__4_once, _init_l_Lean_Elab_WF_isNatLtWF___closed__4);
v___x_6346_ = l_Lean_Meta_isExprDefEq(v_arg_6339_, v___x_6345_, v_a_6316_, v_a_6317_, v_a_6318_, v_a_6319_);
if (lean_obj_tag(v___x_6346_) == 0)
{
lean_object* v_a_6347_; lean_object* v___x_6349_; uint8_t v_isShared_6350_; uint8_t v_isSharedCheck_6380_; 
v_a_6347_ = lean_ctor_get(v___x_6346_, 0);
v_isSharedCheck_6380_ = !lean_is_exclusive(v___x_6346_);
if (v_isSharedCheck_6380_ == 0)
{
v___x_6349_ = v___x_6346_;
v_isShared_6350_ = v_isSharedCheck_6380_;
goto v_resetjp_6348_;
}
else
{
lean_inc(v_a_6347_);
lean_dec(v___x_6346_);
v___x_6349_ = lean_box(0);
v_isShared_6350_ = v_isSharedCheck_6380_;
goto v_resetjp_6348_;
}
v_resetjp_6348_:
{
uint8_t v___x_6351_; 
v___x_6351_ = lean_unbox(v_a_6347_);
lean_dec(v_a_6347_);
if (v___x_6351_ == 0)
{
lean_object* v___x_6352_; lean_object* v___x_6354_; 
lean_dec_ref(v_arg_6336_);
lean_dec_ref(v_arg_6333_);
v___x_6352_ = lean_box(0);
if (v_isShared_6350_ == 0)
{
lean_ctor_set(v___x_6349_, 0, v___x_6352_);
v___x_6354_ = v___x_6349_;
goto v_reusejp_6353_;
}
else
{
lean_object* v_reuseFailAlloc_6355_; 
v_reuseFailAlloc_6355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6355_, 0, v___x_6352_);
v___x_6354_ = v_reuseFailAlloc_6355_;
goto v_reusejp_6353_;
}
v_reusejp_6353_:
{
return v___x_6354_;
}
}
else
{
lean_object* v___x_6356_; lean_object* v___x_6357_; 
lean_del_object(v___x_6349_);
v___x_6356_ = lean_obj_once(&l_Lean_Elab_WF_isNatLtWF___closed__7, &l_Lean_Elab_WF_isNatLtWF___closed__7_once, _init_l_Lean_Elab_WF_isNatLtWF___closed__7);
v___x_6357_ = l_Lean_Meta_isExprDefEq(v_arg_6333_, v___x_6356_, v_a_6316_, v_a_6317_, v_a_6318_, v_a_6319_);
if (lean_obj_tag(v___x_6357_) == 0)
{
lean_object* v_a_6358_; lean_object* v___x_6360_; uint8_t v_isShared_6361_; uint8_t v_isSharedCheck_6371_; 
v_a_6358_ = lean_ctor_get(v___x_6357_, 0);
v_isSharedCheck_6371_ = !lean_is_exclusive(v___x_6357_);
if (v_isSharedCheck_6371_ == 0)
{
v___x_6360_ = v___x_6357_;
v_isShared_6361_ = v_isSharedCheck_6371_;
goto v_resetjp_6359_;
}
else
{
lean_inc(v_a_6358_);
lean_dec(v___x_6357_);
v___x_6360_ = lean_box(0);
v_isShared_6361_ = v_isSharedCheck_6371_;
goto v_resetjp_6359_;
}
v_resetjp_6359_:
{
uint8_t v___x_6362_; 
v___x_6362_ = lean_unbox(v_a_6358_);
lean_dec(v_a_6358_);
if (v___x_6362_ == 0)
{
lean_object* v___x_6363_; lean_object* v___x_6365_; 
lean_dec_ref(v_arg_6336_);
v___x_6363_ = lean_box(0);
if (v_isShared_6361_ == 0)
{
lean_ctor_set(v___x_6360_, 0, v___x_6363_);
v___x_6365_ = v___x_6360_;
goto v_reusejp_6364_;
}
else
{
lean_object* v_reuseFailAlloc_6366_; 
v_reuseFailAlloc_6366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6366_, 0, v___x_6363_);
v___x_6365_ = v_reuseFailAlloc_6366_;
goto v_reusejp_6364_;
}
v_reusejp_6364_:
{
return v___x_6365_;
}
}
else
{
lean_object* v___x_6367_; lean_object* v___x_6369_; 
v___x_6367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6367_, 0, v_arg_6336_);
if (v_isShared_6361_ == 0)
{
lean_ctor_set(v___x_6360_, 0, v___x_6367_);
v___x_6369_ = v___x_6360_;
goto v_reusejp_6368_;
}
else
{
lean_object* v_reuseFailAlloc_6370_; 
v_reuseFailAlloc_6370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6370_, 0, v___x_6367_);
v___x_6369_ = v_reuseFailAlloc_6370_;
goto v_reusejp_6368_;
}
v_reusejp_6368_:
{
return v___x_6369_;
}
}
}
}
else
{
lean_object* v_a_6372_; lean_object* v___x_6374_; uint8_t v_isShared_6375_; uint8_t v_isSharedCheck_6379_; 
lean_dec_ref(v_arg_6336_);
v_a_6372_ = lean_ctor_get(v___x_6357_, 0);
v_isSharedCheck_6379_ = !lean_is_exclusive(v___x_6357_);
if (v_isSharedCheck_6379_ == 0)
{
v___x_6374_ = v___x_6357_;
v_isShared_6375_ = v_isSharedCheck_6379_;
goto v_resetjp_6373_;
}
else
{
lean_inc(v_a_6372_);
lean_dec(v___x_6357_);
v___x_6374_ = lean_box(0);
v_isShared_6375_ = v_isSharedCheck_6379_;
goto v_resetjp_6373_;
}
v_resetjp_6373_:
{
lean_object* v___x_6377_; 
if (v_isShared_6375_ == 0)
{
v___x_6377_ = v___x_6374_;
goto v_reusejp_6376_;
}
else
{
lean_object* v_reuseFailAlloc_6378_; 
v_reuseFailAlloc_6378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6378_, 0, v_a_6372_);
v___x_6377_ = v_reuseFailAlloc_6378_;
goto v_reusejp_6376_;
}
v_reusejp_6376_:
{
return v___x_6377_;
}
}
}
}
}
}
else
{
lean_object* v_a_6381_; lean_object* v___x_6383_; uint8_t v_isShared_6384_; uint8_t v_isSharedCheck_6388_; 
lean_dec_ref(v_arg_6336_);
lean_dec_ref(v_arg_6333_);
v_a_6381_ = lean_ctor_get(v___x_6346_, 0);
v_isSharedCheck_6388_ = !lean_is_exclusive(v___x_6346_);
if (v_isSharedCheck_6388_ == 0)
{
v___x_6383_ = v___x_6346_;
v_isShared_6384_ = v_isSharedCheck_6388_;
goto v_resetjp_6382_;
}
else
{
lean_inc(v_a_6381_);
lean_dec(v___x_6346_);
v___x_6383_ = lean_box(0);
v_isShared_6384_ = v_isSharedCheck_6388_;
goto v_resetjp_6382_;
}
v_resetjp_6382_:
{
lean_object* v___x_6386_; 
if (v_isShared_6384_ == 0)
{
v___x_6386_ = v___x_6383_;
goto v_reusejp_6385_;
}
else
{
lean_object* v_reuseFailAlloc_6387_; 
v_reuseFailAlloc_6387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6387_, 0, v_a_6381_);
v___x_6386_ = v_reuseFailAlloc_6387_;
goto v_reusejp_6385_;
}
v_reusejp_6385_:
{
return v___x_6386_;
}
}
}
}
}
}
}
}
v___jp_6326_:
{
lean_object* v___x_6327_; lean_object* v___x_6329_; 
v___x_6327_ = lean_box(0);
if (v_isShared_6325_ == 0)
{
lean_ctor_set(v___x_6324_, 0, v___x_6327_);
v___x_6329_ = v___x_6324_;
goto v_reusejp_6328_;
}
else
{
lean_object* v_reuseFailAlloc_6330_; 
v_reuseFailAlloc_6330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6330_, 0, v___x_6327_);
v___x_6329_ = v_reuseFailAlloc_6330_;
goto v_reusejp_6328_;
}
v_reusejp_6328_:
{
return v___x_6329_;
}
}
}
}
else
{
lean_object* v_a_6390_; lean_object* v___x_6392_; uint8_t v_isShared_6393_; uint8_t v_isSharedCheck_6397_; 
v_a_6390_ = lean_ctor_get(v___x_6321_, 0);
v_isSharedCheck_6397_ = !lean_is_exclusive(v___x_6321_);
if (v_isSharedCheck_6397_ == 0)
{
v___x_6392_ = v___x_6321_;
v_isShared_6393_ = v_isSharedCheck_6397_;
goto v_resetjp_6391_;
}
else
{
lean_inc(v_a_6390_);
lean_dec(v___x_6321_);
v___x_6392_ = lean_box(0);
v_isShared_6393_ = v_isSharedCheck_6397_;
goto v_resetjp_6391_;
}
v_resetjp_6391_:
{
lean_object* v___x_6395_; 
if (v_isShared_6393_ == 0)
{
v___x_6395_ = v___x_6392_;
goto v_reusejp_6394_;
}
else
{
lean_object* v_reuseFailAlloc_6396_; 
v_reuseFailAlloc_6396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6396_, 0, v_a_6390_);
v___x_6395_ = v_reuseFailAlloc_6396_;
goto v_reusejp_6394_;
}
v_reusejp_6394_:
{
return v___x_6395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isNatLtWF___boxed(lean_object* v_wfRel_6398_, lean_object* v_a_6399_, lean_object* v_a_6400_, lean_object* v_a_6401_, lean_object* v_a_6402_, lean_object* v_a_6403_){
_start:
{
lean_object* v_res_6404_; 
v_res_6404_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_6398_, v_a_6399_, v_a_6400_, v_a_6401_, v_a_6402_);
lean_dec(v_a_6402_);
lean_dec_ref(v_a_6401_);
lean_dec(v_a_6400_);
lean_dec_ref(v_a_6399_);
return v_res_6404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(lean_object* v_type_6405_, lean_object* v_maxFVars_x3f_6406_, lean_object* v_k_6407_, uint8_t v_cleanupAnnotations_6408_, uint8_t v_whnfType_6409_, lean_object* v___y_6410_, lean_object* v___y_6411_, lean_object* v___y_6412_, lean_object* v___y_6413_, lean_object* v___y_6414_, lean_object* v___y_6415_){
_start:
{
lean_object* v___f_6417_; lean_object* v___x_6418_; 
lean_inc(v___y_6411_);
lean_inc_ref(v___y_6410_);
v___f_6417_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_6417_, 0, v_k_6407_);
lean_closure_set(v___f_6417_, 1, v___y_6410_);
lean_closure_set(v___f_6417_, 2, v___y_6411_);
v___x_6418_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_6405_, v_maxFVars_x3f_6406_, v___f_6417_, v_cleanupAnnotations_6408_, v_whnfType_6409_, v___y_6412_, v___y_6413_, v___y_6414_, v___y_6415_);
if (lean_obj_tag(v___x_6418_) == 0)
{
return v___x_6418_;
}
else
{
lean_object* v_a_6419_; lean_object* v___x_6421_; uint8_t v_isShared_6422_; uint8_t v_isSharedCheck_6426_; 
v_a_6419_ = lean_ctor_get(v___x_6418_, 0);
v_isSharedCheck_6426_ = !lean_is_exclusive(v___x_6418_);
if (v_isSharedCheck_6426_ == 0)
{
v___x_6421_ = v___x_6418_;
v_isShared_6422_ = v_isSharedCheck_6426_;
goto v_resetjp_6420_;
}
else
{
lean_inc(v_a_6419_);
lean_dec(v___x_6418_);
v___x_6421_ = lean_box(0);
v_isShared_6422_ = v_isSharedCheck_6426_;
goto v_resetjp_6420_;
}
v_resetjp_6420_:
{
lean_object* v___x_6424_; 
if (v_isShared_6422_ == 0)
{
v___x_6424_ = v___x_6421_;
goto v_reusejp_6423_;
}
else
{
lean_object* v_reuseFailAlloc_6425_; 
v_reuseFailAlloc_6425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6425_, 0, v_a_6419_);
v___x_6424_ = v_reuseFailAlloc_6425_;
goto v_reusejp_6423_;
}
v_reusejp_6423_:
{
return v___x_6424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg___boxed(lean_object* v_type_6427_, lean_object* v_maxFVars_x3f_6428_, lean_object* v_k_6429_, lean_object* v_cleanupAnnotations_6430_, lean_object* v_whnfType_6431_, lean_object* v___y_6432_, lean_object* v___y_6433_, lean_object* v___y_6434_, lean_object* v___y_6435_, lean_object* v___y_6436_, lean_object* v___y_6437_, lean_object* v___y_6438_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_6439_; uint8_t v_whnfType_boxed_6440_; lean_object* v_res_6441_; 
v_cleanupAnnotations_boxed_6439_ = lean_unbox(v_cleanupAnnotations_6430_);
v_whnfType_boxed_6440_ = lean_unbox(v_whnfType_6431_);
v_res_6441_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_type_6427_, v_maxFVars_x3f_6428_, v_k_6429_, v_cleanupAnnotations_boxed_6439_, v_whnfType_boxed_6440_, v___y_6432_, v___y_6433_, v___y_6434_, v___y_6435_, v___y_6436_, v___y_6437_);
lean_dec(v___y_6437_);
lean_dec_ref(v___y_6436_);
lean_dec(v___y_6435_);
lean_dec_ref(v___y_6434_);
lean_dec(v___y_6433_);
lean_dec_ref(v___y_6432_);
return v_res_6441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0(lean_object* v_00_u03b1_6442_, lean_object* v_type_6443_, lean_object* v_maxFVars_x3f_6444_, lean_object* v_k_6445_, uint8_t v_cleanupAnnotations_6446_, uint8_t v_whnfType_6447_, lean_object* v___y_6448_, lean_object* v___y_6449_, lean_object* v___y_6450_, lean_object* v___y_6451_, lean_object* v___y_6452_, lean_object* v___y_6453_){
_start:
{
lean_object* v___x_6455_; 
v___x_6455_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_type_6443_, v_maxFVars_x3f_6444_, v_k_6445_, v_cleanupAnnotations_6446_, v_whnfType_6447_, v___y_6448_, v___y_6449_, v___y_6450_, v___y_6451_, v___y_6452_, v___y_6453_);
return v___x_6455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___boxed(lean_object* v_00_u03b1_6456_, lean_object* v_type_6457_, lean_object* v_maxFVars_x3f_6458_, lean_object* v_k_6459_, lean_object* v_cleanupAnnotations_6460_, lean_object* v_whnfType_6461_, lean_object* v___y_6462_, lean_object* v___y_6463_, lean_object* v___y_6464_, lean_object* v___y_6465_, lean_object* v___y_6466_, lean_object* v___y_6467_, lean_object* v___y_6468_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_6469_; uint8_t v_whnfType_boxed_6470_; lean_object* v_res_6471_; 
v_cleanupAnnotations_boxed_6469_ = lean_unbox(v_cleanupAnnotations_6460_);
v_whnfType_boxed_6470_ = lean_unbox(v_whnfType_6461_);
v_res_6471_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0(v_00_u03b1_6456_, v_type_6457_, v_maxFVars_x3f_6458_, v_k_6459_, v_cleanupAnnotations_boxed_6469_, v_whnfType_boxed_6470_, v___y_6462_, v___y_6463_, v___y_6464_, v___y_6465_, v___y_6466_, v___y_6467_);
lean_dec(v___y_6467_);
lean_dec_ref(v___y_6466_);
lean_dec(v___y_6465_);
lean_dec_ref(v___y_6464_);
lean_dec(v___y_6463_);
lean_dec_ref(v___y_6462_);
return v_res_6471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(lean_object* v_lctx_6472_, lean_object* v_x_6473_, lean_object* v___y_6474_, lean_object* v___y_6475_, lean_object* v___y_6476_, lean_object* v___y_6477_, lean_object* v___y_6478_, lean_object* v___y_6479_){
_start:
{
lean_object* v_keyedConfig_6481_; uint8_t v_trackZetaDelta_6482_; lean_object* v_zetaDeltaSet_6483_; lean_object* v_localInstances_6484_; lean_object* v_defEqCtx_x3f_6485_; lean_object* v_synthPendingDepth_6486_; lean_object* v_customCanUnfoldPredicate_x3f_6487_; uint8_t v_univApprox_6488_; uint8_t v_inTypeClassResolution_6489_; uint8_t v_cacheInferType_6490_; lean_object* v___x_6491_; lean_object* v___x_6492_; 
v_keyedConfig_6481_ = lean_ctor_get(v___y_6476_, 0);
v_trackZetaDelta_6482_ = lean_ctor_get_uint8(v___y_6476_, sizeof(void*)*7);
v_zetaDeltaSet_6483_ = lean_ctor_get(v___y_6476_, 1);
v_localInstances_6484_ = lean_ctor_get(v___y_6476_, 3);
v_defEqCtx_x3f_6485_ = lean_ctor_get(v___y_6476_, 4);
v_synthPendingDepth_6486_ = lean_ctor_get(v___y_6476_, 5);
v_customCanUnfoldPredicate_x3f_6487_ = lean_ctor_get(v___y_6476_, 6);
v_univApprox_6488_ = lean_ctor_get_uint8(v___y_6476_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_6489_ = lean_ctor_get_uint8(v___y_6476_, sizeof(void*)*7 + 2);
v_cacheInferType_6490_ = lean_ctor_get_uint8(v___y_6476_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_6487_);
lean_inc(v_synthPendingDepth_6486_);
lean_inc(v_defEqCtx_x3f_6485_);
lean_inc_ref(v_localInstances_6484_);
lean_inc(v_zetaDeltaSet_6483_);
lean_inc_ref(v_keyedConfig_6481_);
v___x_6491_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6491_, 0, v_keyedConfig_6481_);
lean_ctor_set(v___x_6491_, 1, v_zetaDeltaSet_6483_);
lean_ctor_set(v___x_6491_, 2, v_lctx_6472_);
lean_ctor_set(v___x_6491_, 3, v_localInstances_6484_);
lean_ctor_set(v___x_6491_, 4, v_defEqCtx_x3f_6485_);
lean_ctor_set(v___x_6491_, 5, v_synthPendingDepth_6486_);
lean_ctor_set(v___x_6491_, 6, v_customCanUnfoldPredicate_x3f_6487_);
lean_ctor_set_uint8(v___x_6491_, sizeof(void*)*7, v_trackZetaDelta_6482_);
lean_ctor_set_uint8(v___x_6491_, sizeof(void*)*7 + 1, v_univApprox_6488_);
lean_ctor_set_uint8(v___x_6491_, sizeof(void*)*7 + 2, v_inTypeClassResolution_6489_);
lean_ctor_set_uint8(v___x_6491_, sizeof(void*)*7 + 3, v_cacheInferType_6490_);
lean_inc(v___y_6479_);
lean_inc_ref(v___y_6478_);
lean_inc(v___y_6477_);
lean_inc(v___y_6475_);
lean_inc_ref(v___y_6474_);
v___x_6492_ = lean_apply_7(v_x_6473_, v___y_6474_, v___y_6475_, v___x_6491_, v___y_6477_, v___y_6478_, v___y_6479_, lean_box(0));
if (lean_obj_tag(v___x_6492_) == 0)
{
lean_object* v_a_6493_; lean_object* v___x_6495_; uint8_t v_isShared_6496_; uint8_t v_isSharedCheck_6500_; 
v_a_6493_ = lean_ctor_get(v___x_6492_, 0);
v_isSharedCheck_6500_ = !lean_is_exclusive(v___x_6492_);
if (v_isSharedCheck_6500_ == 0)
{
v___x_6495_ = v___x_6492_;
v_isShared_6496_ = v_isSharedCheck_6500_;
goto v_resetjp_6494_;
}
else
{
lean_inc(v_a_6493_);
lean_dec(v___x_6492_);
v___x_6495_ = lean_box(0);
v_isShared_6496_ = v_isSharedCheck_6500_;
goto v_resetjp_6494_;
}
v_resetjp_6494_:
{
lean_object* v___x_6498_; 
if (v_isShared_6496_ == 0)
{
v___x_6498_ = v___x_6495_;
goto v_reusejp_6497_;
}
else
{
lean_object* v_reuseFailAlloc_6499_; 
v_reuseFailAlloc_6499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6499_, 0, v_a_6493_);
v___x_6498_ = v_reuseFailAlloc_6499_;
goto v_reusejp_6497_;
}
v_reusejp_6497_:
{
return v___x_6498_;
}
}
}
else
{
return v___x_6492_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg___boxed(lean_object* v_lctx_6501_, lean_object* v_x_6502_, lean_object* v___y_6503_, lean_object* v___y_6504_, lean_object* v___y_6505_, lean_object* v___y_6506_, lean_object* v___y_6507_, lean_object* v___y_6508_, lean_object* v___y_6509_){
_start:
{
lean_object* v_res_6510_; 
v_res_6510_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v_lctx_6501_, v_x_6502_, v___y_6503_, v___y_6504_, v___y_6505_, v___y_6506_, v___y_6507_, v___y_6508_);
lean_dec(v___y_6508_);
lean_dec_ref(v___y_6507_);
lean_dec(v___y_6506_);
lean_dec_ref(v___y_6505_);
lean_dec(v___y_6504_);
lean_dec_ref(v___y_6503_);
return v_res_6510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1(lean_object* v_00_u03b1_6511_, lean_object* v_lctx_6512_, lean_object* v_x_6513_, lean_object* v___y_6514_, lean_object* v___y_6515_, lean_object* v___y_6516_, lean_object* v___y_6517_, lean_object* v___y_6518_, lean_object* v___y_6519_){
_start:
{
lean_object* v___x_6521_; 
v___x_6521_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v_lctx_6512_, v_x_6513_, v___y_6514_, v___y_6515_, v___y_6516_, v___y_6517_, v___y_6518_, v___y_6519_);
return v___x_6521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___boxed(lean_object* v_00_u03b1_6522_, lean_object* v_lctx_6523_, lean_object* v_x_6524_, lean_object* v___y_6525_, lean_object* v___y_6526_, lean_object* v___y_6527_, lean_object* v___y_6528_, lean_object* v___y_6529_, lean_object* v___y_6530_, lean_object* v___y_6531_){
_start:
{
lean_object* v_res_6532_; 
v_res_6532_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1(v_00_u03b1_6522_, v_lctx_6523_, v_x_6524_, v___y_6525_, v___y_6526_, v___y_6527_, v___y_6528_, v___y_6529_, v___y_6530_);
lean_dec(v___y_6530_);
lean_dec_ref(v___y_6529_);
lean_dec(v___y_6528_);
lean_dec_ref(v___y_6527_);
lean_dec(v___y_6526_);
lean_dec_ref(v___y_6525_);
return v_res_6532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__0(lean_object* v___x_6549_, lean_object* v___x_6550_, lean_object* v_wfRel_6551_, lean_object* v_x_6552_, lean_object* v_type_6553_, lean_object* v___y_6554_, lean_object* v___y_6555_, lean_object* v___y_6556_, lean_object* v___y_6557_, lean_object* v___y_6558_, lean_object* v___y_6559_){
_start:
{
lean_object* v___x_6561_; lean_object* v___x_6562_; lean_object* v___x_6563_; lean_object* v___x_6564_; 
v___x_6561_ = lean_unsigned_to_nat(0u);
v___x_6562_ = lean_array_get_borrowed(v___x_6549_, v_x_6552_, v___x_6561_);
v___x_6563_ = l_Lean_Expr_fvarId_x21(v___x_6562_);
v___x_6564_ = l_Lean_FVarId_getUserName___redArg(v___x_6563_, v___y_6556_, v___y_6558_, v___y_6559_);
if (lean_obj_tag(v___x_6564_) == 0)
{
lean_object* v_a_6565_; lean_object* v___x_6566_; 
v_a_6565_ = lean_ctor_get(v___x_6564_, 0);
lean_inc(v_a_6565_);
lean_dec_ref_known(v___x_6564_, 1);
lean_inc(v___y_6559_);
lean_inc_ref(v___y_6558_);
lean_inc(v___y_6557_);
lean_inc_ref(v___y_6556_);
lean_inc(v___x_6562_);
v___x_6566_ = lean_infer_type(v___x_6562_, v___y_6556_, v___y_6557_, v___y_6558_, v___y_6559_);
if (lean_obj_tag(v___x_6566_) == 0)
{
lean_object* v_a_6567_; lean_object* v___x_6568_; 
v_a_6567_ = lean_ctor_get(v___x_6566_, 0);
lean_inc_n(v_a_6567_, 2);
lean_dec_ref_known(v___x_6566_, 1);
v___x_6568_ = l_Lean_Meta_getLevel(v_a_6567_, v___y_6556_, v___y_6557_, v___y_6558_, v___y_6559_);
if (lean_obj_tag(v___x_6568_) == 0)
{
lean_object* v_a_6569_; lean_object* v___x_6570_; 
v_a_6569_ = lean_ctor_get(v___x_6568_, 0);
lean_inc(v_a_6569_);
lean_dec_ref_known(v___x_6568_, 1);
lean_inc_ref(v_type_6553_);
v___x_6570_ = l_Lean_Meta_getLevel(v_type_6553_, v___y_6556_, v___y_6557_, v___y_6558_, v___y_6559_);
if (lean_obj_tag(v___x_6570_) == 0)
{
lean_object* v_a_6571_; lean_object* v___x_6572_; lean_object* v___x_6573_; uint8_t v___x_6574_; uint8_t v___x_6575_; uint8_t v___x_6576_; lean_object* v___x_6577_; 
v_a_6571_ = lean_ctor_get(v___x_6570_, 0);
lean_inc(v_a_6571_);
lean_dec_ref_known(v___x_6570_, 1);
v___x_6572_ = lean_mk_empty_array_with_capacity(v___x_6550_);
lean_inc(v___x_6562_);
lean_inc_ref(v___x_6572_);
v___x_6573_ = lean_array_push(v___x_6572_, v___x_6562_);
v___x_6574_ = 0;
v___x_6575_ = 1;
v___x_6576_ = 1;
v___x_6577_ = l_Lean_Meta_mkLambdaFVars(v___x_6573_, v_type_6553_, v___x_6574_, v___x_6575_, v___x_6574_, v___x_6575_, v___x_6576_, v___y_6556_, v___y_6557_, v___y_6558_, v___y_6559_);
lean_dec_ref(v___x_6573_);
if (lean_obj_tag(v___x_6577_) == 0)
{
lean_object* v_a_6578_; lean_object* v___x_6579_; 
v_a_6578_ = lean_ctor_get(v___x_6577_, 0);
lean_inc(v_a_6578_);
lean_dec_ref_known(v___x_6577_, 1);
lean_inc_ref(v_wfRel_6551_);
v___x_6579_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_6551_, v___y_6556_, v___y_6557_, v___y_6558_, v___y_6559_);
if (lean_obj_tag(v___x_6579_) == 0)
{
lean_object* v_a_6580_; lean_object* v___x_6582_; uint8_t v_isShared_6583_; uint8_t v_isSharedCheck_6624_; 
v_a_6580_ = lean_ctor_get(v___x_6579_, 0);
v_isSharedCheck_6624_ = !lean_is_exclusive(v___x_6579_);
if (v_isSharedCheck_6624_ == 0)
{
v___x_6582_ = v___x_6579_;
v_isShared_6583_ = v_isSharedCheck_6624_;
goto v_resetjp_6581_;
}
else
{
lean_inc(v_a_6580_);
lean_dec(v___x_6579_);
v___x_6582_ = lean_box(0);
v_isShared_6583_ = v_isSharedCheck_6624_;
goto v_resetjp_6581_;
}
v_resetjp_6581_:
{
if (lean_obj_tag(v_a_6580_) == 1)
{
lean_object* v_val_6584_; lean_object* v___x_6585_; lean_object* v___x_6586_; lean_object* v___x_6587_; lean_object* v___x_6588_; lean_object* v___x_6589_; lean_object* v___x_6590_; lean_object* v___x_6591_; lean_object* v___x_6593_; 
lean_dec_ref(v___x_6572_);
lean_dec_ref(v_wfRel_6551_);
lean_dec(v___x_6550_);
v_val_6584_ = lean_ctor_get(v_a_6580_, 0);
lean_inc(v_val_6584_);
lean_dec_ref_known(v_a_6580_, 1);
v___x_6585_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__2));
v___x_6586_ = lean_box(0);
v___x_6587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6587_, 0, v_a_6571_);
lean_ctor_set(v___x_6587_, 1, v___x_6586_);
v___x_6588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6588_, 0, v_a_6569_);
lean_ctor_set(v___x_6588_, 1, v___x_6587_);
v___x_6589_ = l_Lean_mkConst(v___x_6585_, v___x_6588_);
v___x_6590_ = l_Lean_mkApp3(v___x_6589_, v_a_6567_, v_a_6578_, v_val_6584_);
v___x_6591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6591_, 0, v___x_6590_);
lean_ctor_set(v___x_6591_, 1, v_a_6565_);
if (v_isShared_6583_ == 0)
{
lean_ctor_set(v___x_6582_, 0, v___x_6591_);
v___x_6593_ = v___x_6582_;
goto v_reusejp_6592_;
}
else
{
lean_object* v_reuseFailAlloc_6594_; 
v_reuseFailAlloc_6594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6594_, 0, v___x_6591_);
v___x_6593_ = v_reuseFailAlloc_6594_;
goto v_reusejp_6592_;
}
v_reusejp_6592_:
{
return v___x_6593_;
}
}
else
{
lean_object* v___x_6595_; lean_object* v___x_6596_; lean_object* v___x_6597_; lean_object* v___x_6598_; lean_object* v___x_6599_; lean_object* v___x_6600_; 
lean_del_object(v___x_6582_);
lean_dec(v_a_6580_);
v___x_6595_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__4));
lean_inc_ref(v_wfRel_6551_);
v___x_6596_ = l_Lean_mkProj(v___x_6595_, v___x_6561_, v_wfRel_6551_);
v___x_6597_ = l_Lean_mkProj(v___x_6595_, v___x_6550_, v_wfRel_6551_);
v___x_6598_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__6));
v___x_6599_ = lean_array_push(v___x_6572_, v___x_6597_);
v___x_6600_ = l_Lean_Meta_mkAppM(v___x_6598_, v___x_6599_, v___y_6556_, v___y_6557_, v___y_6558_, v___y_6559_);
if (lean_obj_tag(v___x_6600_) == 0)
{
lean_object* v_a_6601_; lean_object* v___x_6603_; uint8_t v_isShared_6604_; uint8_t v_isSharedCheck_6615_; 
v_a_6601_ = lean_ctor_get(v___x_6600_, 0);
v_isSharedCheck_6615_ = !lean_is_exclusive(v___x_6600_);
if (v_isSharedCheck_6615_ == 0)
{
v___x_6603_ = v___x_6600_;
v_isShared_6604_ = v_isSharedCheck_6615_;
goto v_resetjp_6602_;
}
else
{
lean_inc(v_a_6601_);
lean_dec(v___x_6600_);
v___x_6603_ = lean_box(0);
v_isShared_6604_ = v_isSharedCheck_6615_;
goto v_resetjp_6602_;
}
v_resetjp_6602_:
{
lean_object* v___x_6605_; lean_object* v___x_6606_; lean_object* v___x_6607_; lean_object* v___x_6608_; lean_object* v___x_6609_; lean_object* v___x_6610_; lean_object* v___x_6611_; lean_object* v___x_6613_; 
v___x_6605_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__7));
v___x_6606_ = lean_box(0);
v___x_6607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6607_, 0, v_a_6571_);
lean_ctor_set(v___x_6607_, 1, v___x_6606_);
v___x_6608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6608_, 0, v_a_6569_);
lean_ctor_set(v___x_6608_, 1, v___x_6607_);
v___x_6609_ = l_Lean_mkConst(v___x_6605_, v___x_6608_);
v___x_6610_ = l_Lean_mkApp4(v___x_6609_, v_a_6567_, v_a_6578_, v___x_6596_, v_a_6601_);
v___x_6611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6611_, 0, v___x_6610_);
lean_ctor_set(v___x_6611_, 1, v_a_6565_);
if (v_isShared_6604_ == 0)
{
lean_ctor_set(v___x_6603_, 0, v___x_6611_);
v___x_6613_ = v___x_6603_;
goto v_reusejp_6612_;
}
else
{
lean_object* v_reuseFailAlloc_6614_; 
v_reuseFailAlloc_6614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6614_, 0, v___x_6611_);
v___x_6613_ = v_reuseFailAlloc_6614_;
goto v_reusejp_6612_;
}
v_reusejp_6612_:
{
return v___x_6613_;
}
}
}
else
{
lean_object* v_a_6616_; lean_object* v___x_6618_; uint8_t v_isShared_6619_; uint8_t v_isSharedCheck_6623_; 
lean_dec_ref(v___x_6596_);
lean_dec(v_a_6578_);
lean_dec(v_a_6571_);
lean_dec(v_a_6569_);
lean_dec(v_a_6567_);
lean_dec(v_a_6565_);
v_a_6616_ = lean_ctor_get(v___x_6600_, 0);
v_isSharedCheck_6623_ = !lean_is_exclusive(v___x_6600_);
if (v_isSharedCheck_6623_ == 0)
{
v___x_6618_ = v___x_6600_;
v_isShared_6619_ = v_isSharedCheck_6623_;
goto v_resetjp_6617_;
}
else
{
lean_inc(v_a_6616_);
lean_dec(v___x_6600_);
v___x_6618_ = lean_box(0);
v_isShared_6619_ = v_isSharedCheck_6623_;
goto v_resetjp_6617_;
}
v_resetjp_6617_:
{
lean_object* v___x_6621_; 
if (v_isShared_6619_ == 0)
{
v___x_6621_ = v___x_6618_;
goto v_reusejp_6620_;
}
else
{
lean_object* v_reuseFailAlloc_6622_; 
v_reuseFailAlloc_6622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6622_, 0, v_a_6616_);
v___x_6621_ = v_reuseFailAlloc_6622_;
goto v_reusejp_6620_;
}
v_reusejp_6620_:
{
return v___x_6621_;
}
}
}
}
}
}
else
{
lean_object* v_a_6625_; lean_object* v___x_6627_; uint8_t v_isShared_6628_; uint8_t v_isSharedCheck_6632_; 
lean_dec(v_a_6578_);
lean_dec_ref(v___x_6572_);
lean_dec(v_a_6571_);
lean_dec(v_a_6569_);
lean_dec(v_a_6567_);
lean_dec(v_a_6565_);
lean_dec_ref(v_wfRel_6551_);
lean_dec(v___x_6550_);
v_a_6625_ = lean_ctor_get(v___x_6579_, 0);
v_isSharedCheck_6632_ = !lean_is_exclusive(v___x_6579_);
if (v_isSharedCheck_6632_ == 0)
{
v___x_6627_ = v___x_6579_;
v_isShared_6628_ = v_isSharedCheck_6632_;
goto v_resetjp_6626_;
}
else
{
lean_inc(v_a_6625_);
lean_dec(v___x_6579_);
v___x_6627_ = lean_box(0);
v_isShared_6628_ = v_isSharedCheck_6632_;
goto v_resetjp_6626_;
}
v_resetjp_6626_:
{
lean_object* v___x_6630_; 
if (v_isShared_6628_ == 0)
{
v___x_6630_ = v___x_6627_;
goto v_reusejp_6629_;
}
else
{
lean_object* v_reuseFailAlloc_6631_; 
v_reuseFailAlloc_6631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6631_, 0, v_a_6625_);
v___x_6630_ = v_reuseFailAlloc_6631_;
goto v_reusejp_6629_;
}
v_reusejp_6629_:
{
return v___x_6630_;
}
}
}
}
else
{
lean_object* v_a_6633_; lean_object* v___x_6635_; uint8_t v_isShared_6636_; uint8_t v_isSharedCheck_6640_; 
lean_dec_ref(v___x_6572_);
lean_dec(v_a_6571_);
lean_dec(v_a_6569_);
lean_dec(v_a_6567_);
lean_dec(v_a_6565_);
lean_dec_ref(v_wfRel_6551_);
lean_dec(v___x_6550_);
v_a_6633_ = lean_ctor_get(v___x_6577_, 0);
v_isSharedCheck_6640_ = !lean_is_exclusive(v___x_6577_);
if (v_isSharedCheck_6640_ == 0)
{
v___x_6635_ = v___x_6577_;
v_isShared_6636_ = v_isSharedCheck_6640_;
goto v_resetjp_6634_;
}
else
{
lean_inc(v_a_6633_);
lean_dec(v___x_6577_);
v___x_6635_ = lean_box(0);
v_isShared_6636_ = v_isSharedCheck_6640_;
goto v_resetjp_6634_;
}
v_resetjp_6634_:
{
lean_object* v___x_6638_; 
if (v_isShared_6636_ == 0)
{
v___x_6638_ = v___x_6635_;
goto v_reusejp_6637_;
}
else
{
lean_object* v_reuseFailAlloc_6639_; 
v_reuseFailAlloc_6639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6639_, 0, v_a_6633_);
v___x_6638_ = v_reuseFailAlloc_6639_;
goto v_reusejp_6637_;
}
v_reusejp_6637_:
{
return v___x_6638_;
}
}
}
}
else
{
lean_object* v_a_6641_; lean_object* v___x_6643_; uint8_t v_isShared_6644_; uint8_t v_isSharedCheck_6648_; 
lean_dec(v_a_6569_);
lean_dec(v_a_6567_);
lean_dec(v_a_6565_);
lean_dec_ref(v_type_6553_);
lean_dec_ref(v_wfRel_6551_);
lean_dec(v___x_6550_);
v_a_6641_ = lean_ctor_get(v___x_6570_, 0);
v_isSharedCheck_6648_ = !lean_is_exclusive(v___x_6570_);
if (v_isSharedCheck_6648_ == 0)
{
v___x_6643_ = v___x_6570_;
v_isShared_6644_ = v_isSharedCheck_6648_;
goto v_resetjp_6642_;
}
else
{
lean_inc(v_a_6641_);
lean_dec(v___x_6570_);
v___x_6643_ = lean_box(0);
v_isShared_6644_ = v_isSharedCheck_6648_;
goto v_resetjp_6642_;
}
v_resetjp_6642_:
{
lean_object* v___x_6646_; 
if (v_isShared_6644_ == 0)
{
v___x_6646_ = v___x_6643_;
goto v_reusejp_6645_;
}
else
{
lean_object* v_reuseFailAlloc_6647_; 
v_reuseFailAlloc_6647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6647_, 0, v_a_6641_);
v___x_6646_ = v_reuseFailAlloc_6647_;
goto v_reusejp_6645_;
}
v_reusejp_6645_:
{
return v___x_6646_;
}
}
}
}
else
{
lean_object* v_a_6649_; lean_object* v___x_6651_; uint8_t v_isShared_6652_; uint8_t v_isSharedCheck_6656_; 
lean_dec(v_a_6567_);
lean_dec(v_a_6565_);
lean_dec_ref(v_type_6553_);
lean_dec_ref(v_wfRel_6551_);
lean_dec(v___x_6550_);
v_a_6649_ = lean_ctor_get(v___x_6568_, 0);
v_isSharedCheck_6656_ = !lean_is_exclusive(v___x_6568_);
if (v_isSharedCheck_6656_ == 0)
{
v___x_6651_ = v___x_6568_;
v_isShared_6652_ = v_isSharedCheck_6656_;
goto v_resetjp_6650_;
}
else
{
lean_inc(v_a_6649_);
lean_dec(v___x_6568_);
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
lean_dec(v_a_6565_);
lean_dec_ref(v_type_6553_);
lean_dec_ref(v_wfRel_6551_);
lean_dec(v___x_6550_);
v_a_6657_ = lean_ctor_get(v___x_6566_, 0);
v_isSharedCheck_6664_ = !lean_is_exclusive(v___x_6566_);
if (v_isSharedCheck_6664_ == 0)
{
v___x_6659_ = v___x_6566_;
v_isShared_6660_ = v_isSharedCheck_6664_;
goto v_resetjp_6658_;
}
else
{
lean_inc(v_a_6657_);
lean_dec(v___x_6566_);
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
lean_dec_ref(v_type_6553_);
lean_dec_ref(v_wfRel_6551_);
lean_dec(v___x_6550_);
v_a_6665_ = lean_ctor_get(v___x_6564_, 0);
v_isSharedCheck_6672_ = !lean_is_exclusive(v___x_6564_);
if (v_isSharedCheck_6672_ == 0)
{
v___x_6667_ = v___x_6564_;
v_isShared_6668_ = v_isSharedCheck_6672_;
goto v_resetjp_6666_;
}
else
{
lean_inc(v_a_6665_);
lean_dec(v___x_6564_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__0___boxed(lean_object* v___x_6673_, lean_object* v___x_6674_, lean_object* v_wfRel_6675_, lean_object* v_x_6676_, lean_object* v_type_6677_, lean_object* v___y_6678_, lean_object* v___y_6679_, lean_object* v___y_6680_, lean_object* v___y_6681_, lean_object* v___y_6682_, lean_object* v___y_6683_, lean_object* v___y_6684_){
_start:
{
lean_object* v_res_6685_; 
v_res_6685_ = l_Lean_Elab_WF_mkFix___lam__0(v___x_6673_, v___x_6674_, v_wfRel_6675_, v_x_6676_, v_type_6677_, v___y_6678_, v___y_6679_, v___y_6680_, v___y_6681_, v___y_6682_, v___y_6683_);
lean_dec(v___y_6683_);
lean_dec_ref(v___y_6682_);
lean_dec(v___y_6681_);
lean_dec_ref(v___y_6680_);
lean_dec(v___y_6679_);
lean_dec_ref(v___y_6678_);
lean_dec_ref(v_x_6676_);
lean_dec_ref(v___x_6673_);
return v_res_6685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__1(lean_object* v_prefixArgs_6686_, lean_object* v_declName_6687_, lean_object* v_x_6688_, lean_object* v_F_6689_, lean_object* v_val_6690_, lean_object* v___y_6691_, lean_object* v___y_6692_, lean_object* v___y_6693_, lean_object* v___y_6694_, lean_object* v___y_6695_, lean_object* v___y_6696_){
_start:
{
lean_object* v___x_6698_; lean_object* v___x_6699_; lean_object* v___x_6700_; 
v___x_6698_ = lean_array_get_size(v_prefixArgs_6686_);
v___x_6699_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___boxed), 11, 2);
lean_closure_set(v___x_6699_, 0, v_declName_6687_);
lean_closure_set(v___x_6699_, 1, v___x_6698_);
v___x_6700_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v_x_6688_, v_F_6689_, v_val_6690_, v___x_6699_, v___y_6691_, v___y_6692_, v___y_6693_, v___y_6694_, v___y_6695_, v___y_6696_);
return v___x_6700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__1___boxed(lean_object* v_prefixArgs_6701_, lean_object* v_declName_6702_, lean_object* v_x_6703_, lean_object* v_F_6704_, lean_object* v_val_6705_, lean_object* v___y_6706_, lean_object* v___y_6707_, lean_object* v___y_6708_, lean_object* v___y_6709_, lean_object* v___y_6710_, lean_object* v___y_6711_, lean_object* v___y_6712_){
_start:
{
lean_object* v_res_6713_; 
v_res_6713_ = l_Lean_Elab_WF_mkFix___lam__1(v_prefixArgs_6701_, v_declName_6702_, v_x_6703_, v_F_6704_, v_val_6705_, v___y_6706_, v___y_6707_, v___y_6708_, v___y_6709_, v___y_6710_, v___y_6711_);
lean_dec(v___y_6711_);
lean_dec_ref(v___y_6710_);
lean_dec(v___y_6709_);
lean_dec_ref(v___y_6708_);
lean_dec(v___y_6707_);
lean_dec_ref(v___y_6706_);
lean_dec_ref(v_prefixArgs_6701_);
return v_res_6713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__2(lean_object* v___x_6714_, lean_object* v___x_6715_, lean_object* v___x_6716_, lean_object* v___f_6717_, lean_object* v_funNames_6718_, lean_object* v_argsPacker_6719_, lean_object* v_decrTactics_6720_, uint8_t v___x_6721_, lean_object* v_fst_6722_, lean_object* v_prefixArgs_6723_, lean_object* v___y_6724_, lean_object* v___y_6725_, lean_object* v___y_6726_, lean_object* v___y_6727_, lean_object* v___y_6728_, lean_object* v___y_6729_){
_start:
{
lean_object* v___x_6731_; 
lean_inc_ref(v___x_6715_);
lean_inc_ref(v___x_6714_);
v___x_6731_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v___x_6714_, v___x_6715_, v___x_6716_, v___f_6717_, v___y_6724_, v___y_6725_, v___y_6726_, v___y_6727_, v___y_6728_, v___y_6729_);
if (lean_obj_tag(v___x_6731_) == 0)
{
lean_object* v_a_6732_; lean_object* v___x_6733_; 
v_a_6732_ = lean_ctor_get(v___x_6731_, 0);
lean_inc(v_a_6732_);
lean_dec_ref_known(v___x_6731_, 1);
v___x_6733_ = l_Lean_Elab_WF_solveDecreasingGoals(v_funNames_6718_, v_argsPacker_6719_, v_decrTactics_6720_, v_a_6732_, v___y_6726_, v___y_6727_, v___y_6728_, v___y_6729_);
if (lean_obj_tag(v___x_6733_) == 0)
{
lean_object* v_a_6734_; lean_object* v___x_6735_; lean_object* v___x_6736_; lean_object* v___x_6737_; lean_object* v___x_6738_; uint8_t v___x_6739_; uint8_t v___x_6740_; lean_object* v___x_6741_; 
v_a_6734_ = lean_ctor_get(v___x_6733_, 0);
lean_inc(v_a_6734_);
lean_dec_ref_known(v___x_6733_, 1);
v___x_6735_ = lean_unsigned_to_nat(2u);
v___x_6736_ = lean_mk_empty_array_with_capacity(v___x_6735_);
v___x_6737_ = lean_array_push(v___x_6736_, v___x_6714_);
v___x_6738_ = lean_array_push(v___x_6737_, v___x_6715_);
v___x_6739_ = 1;
v___x_6740_ = 1;
v___x_6741_ = l_Lean_Meta_mkLambdaFVars(v___x_6738_, v_a_6734_, v___x_6721_, v___x_6739_, v___x_6721_, v___x_6739_, v___x_6740_, v___y_6726_, v___y_6727_, v___y_6728_, v___y_6729_);
lean_dec_ref(v___x_6738_);
if (lean_obj_tag(v___x_6741_) == 0)
{
lean_object* v_a_6742_; lean_object* v___x_6743_; lean_object* v___x_6744_; 
v_a_6742_ = lean_ctor_get(v___x_6741_, 0);
lean_inc(v_a_6742_);
lean_dec_ref_known(v___x_6741_, 1);
v___x_6743_ = l_Lean_Expr_app___override(v_fst_6722_, v_a_6742_);
v___x_6744_ = l_Lean_Meta_mkLambdaFVars(v_prefixArgs_6723_, v___x_6743_, v___x_6721_, v___x_6739_, v___x_6721_, v___x_6739_, v___x_6740_, v___y_6726_, v___y_6727_, v___y_6728_, v___y_6729_);
return v___x_6744_;
}
else
{
lean_dec_ref(v_fst_6722_);
return v___x_6741_;
}
}
else
{
lean_dec_ref(v_fst_6722_);
lean_dec_ref(v___x_6715_);
lean_dec_ref(v___x_6714_);
return v___x_6733_;
}
}
else
{
lean_dec_ref(v_fst_6722_);
lean_dec_ref(v_decrTactics_6720_);
lean_dec_ref(v_argsPacker_6719_);
lean_dec_ref(v_funNames_6718_);
lean_dec_ref(v___x_6715_);
lean_dec_ref(v___x_6714_);
return v___x_6731_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__2___boxed(lean_object** _args){
lean_object* v___x_6745_ = _args[0];
lean_object* v___x_6746_ = _args[1];
lean_object* v___x_6747_ = _args[2];
lean_object* v___f_6748_ = _args[3];
lean_object* v_funNames_6749_ = _args[4];
lean_object* v_argsPacker_6750_ = _args[5];
lean_object* v_decrTactics_6751_ = _args[6];
lean_object* v___x_6752_ = _args[7];
lean_object* v_fst_6753_ = _args[8];
lean_object* v_prefixArgs_6754_ = _args[9];
lean_object* v___y_6755_ = _args[10];
lean_object* v___y_6756_ = _args[11];
lean_object* v___y_6757_ = _args[12];
lean_object* v___y_6758_ = _args[13];
lean_object* v___y_6759_ = _args[14];
lean_object* v___y_6760_ = _args[15];
lean_object* v___y_6761_ = _args[16];
_start:
{
uint8_t v___x_5938__boxed_6762_; lean_object* v_res_6763_; 
v___x_5938__boxed_6762_ = lean_unbox(v___x_6752_);
v_res_6763_ = l_Lean_Elab_WF_mkFix___lam__2(v___x_6745_, v___x_6746_, v___x_6747_, v___f_6748_, v_funNames_6749_, v_argsPacker_6750_, v_decrTactics_6751_, v___x_5938__boxed_6762_, v_fst_6753_, v_prefixArgs_6754_, v___y_6755_, v___y_6756_, v___y_6757_, v___y_6758_, v___y_6759_, v___y_6760_);
lean_dec(v___y_6760_);
lean_dec_ref(v___y_6759_);
lean_dec(v___y_6758_);
lean_dec_ref(v___y_6757_);
lean_dec(v___y_6756_);
lean_dec_ref(v___y_6755_);
lean_dec_ref(v_prefixArgs_6754_);
return v_res_6763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__3(lean_object* v___x_6764_, lean_object* v_snd_6765_, lean_object* v___x_6766_, lean_object* v_prefixArgs_6767_, lean_object* v_value_6768_, lean_object* v___f_6769_, lean_object* v_funNames_6770_, lean_object* v_argsPacker_6771_, lean_object* v_decrTactics_6772_, uint8_t v___x_6773_, lean_object* v_fst_6774_, lean_object* v_xs_6775_, lean_object* v_x_6776_, lean_object* v___y_6777_, lean_object* v___y_6778_, lean_object* v___y_6779_, lean_object* v___y_6780_, lean_object* v___y_6781_, lean_object* v___y_6782_){
_start:
{
lean_object* v_lctx_6784_; lean_object* v___x_6785_; lean_object* v___x_6786_; lean_object* v___x_6787_; lean_object* v___x_6788_; lean_object* v___x_6789_; lean_object* v___x_6790_; lean_object* v___x_6791_; lean_object* v___x_6792_; lean_object* v___f_6793_; lean_object* v___x_6794_; 
v_lctx_6784_ = lean_ctor_get(v___y_6779_, 2);
v___x_6785_ = lean_unsigned_to_nat(0u);
v___x_6786_ = lean_array_get_borrowed(v___x_6764_, v_xs_6775_, v___x_6785_);
v___x_6787_ = l_Lean_Expr_fvarId_x21(v___x_6786_);
lean_inc_ref(v_lctx_6784_);
v___x_6788_ = l_Lean_LocalContext_setUserName(v_lctx_6784_, v___x_6787_, v_snd_6765_);
v___x_6789_ = lean_array_get_borrowed(v___x_6764_, v_xs_6775_, v___x_6766_);
lean_inc_n(v___x_6786_, 2);
lean_inc_ref(v_prefixArgs_6767_);
v___x_6790_ = lean_array_push(v_prefixArgs_6767_, v___x_6786_);
v___x_6791_ = l_Lean_Expr_beta(v_value_6768_, v___x_6790_);
v___x_6792_ = lean_box(v___x_6773_);
lean_inc(v___x_6789_);
v___f_6793_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__2___boxed), 17, 10);
lean_closure_set(v___f_6793_, 0, v___x_6786_);
lean_closure_set(v___f_6793_, 1, v___x_6789_);
lean_closure_set(v___f_6793_, 2, v___x_6791_);
lean_closure_set(v___f_6793_, 3, v___f_6769_);
lean_closure_set(v___f_6793_, 4, v_funNames_6770_);
lean_closure_set(v___f_6793_, 5, v_argsPacker_6771_);
lean_closure_set(v___f_6793_, 6, v_decrTactics_6772_);
lean_closure_set(v___f_6793_, 7, v___x_6792_);
lean_closure_set(v___f_6793_, 8, v_fst_6774_);
lean_closure_set(v___f_6793_, 9, v_prefixArgs_6767_);
v___x_6794_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v___x_6788_, v___f_6793_, v___y_6777_, v___y_6778_, v___y_6779_, v___y_6780_, v___y_6781_, v___y_6782_);
return v___x_6794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__3___boxed(lean_object** _args){
lean_object* v___x_6795_ = _args[0];
lean_object* v_snd_6796_ = _args[1];
lean_object* v___x_6797_ = _args[2];
lean_object* v_prefixArgs_6798_ = _args[3];
lean_object* v_value_6799_ = _args[4];
lean_object* v___f_6800_ = _args[5];
lean_object* v_funNames_6801_ = _args[6];
lean_object* v_argsPacker_6802_ = _args[7];
lean_object* v_decrTactics_6803_ = _args[8];
lean_object* v___x_6804_ = _args[9];
lean_object* v_fst_6805_ = _args[10];
lean_object* v_xs_6806_ = _args[11];
lean_object* v_x_6807_ = _args[12];
lean_object* v___y_6808_ = _args[13];
lean_object* v___y_6809_ = _args[14];
lean_object* v___y_6810_ = _args[15];
lean_object* v___y_6811_ = _args[16];
lean_object* v___y_6812_ = _args[17];
lean_object* v___y_6813_ = _args[18];
lean_object* v___y_6814_ = _args[19];
_start:
{
uint8_t v___x_6008__boxed_6815_; lean_object* v_res_6816_; 
v___x_6008__boxed_6815_ = lean_unbox(v___x_6804_);
v_res_6816_ = l_Lean_Elab_WF_mkFix___lam__3(v___x_6795_, v_snd_6796_, v___x_6797_, v_prefixArgs_6798_, v_value_6799_, v___f_6800_, v_funNames_6801_, v_argsPacker_6802_, v_decrTactics_6803_, v___x_6008__boxed_6815_, v_fst_6805_, v_xs_6806_, v_x_6807_, v___y_6808_, v___y_6809_, v___y_6810_, v___y_6811_, v___y_6812_, v___y_6813_);
lean_dec(v___y_6813_);
lean_dec_ref(v___y_6812_);
lean_dec(v___y_6811_);
lean_dec_ref(v___y_6810_);
lean_dec(v___y_6809_);
lean_dec_ref(v___y_6808_);
lean_dec_ref(v_x_6807_);
lean_dec_ref(v_xs_6806_);
lean_dec(v___x_6797_);
lean_dec_ref(v___x_6795_);
return v_res_6816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix(lean_object* v_preDef_6821_, lean_object* v_prefixArgs_6822_, lean_object* v_argsPacker_6823_, lean_object* v_wfRel_6824_, lean_object* v_funNames_6825_, lean_object* v_decrTactics_6826_, lean_object* v_a_6827_, lean_object* v_a_6828_, lean_object* v_a_6829_, lean_object* v_a_6830_, lean_object* v_a_6831_, lean_object* v_a_6832_){
_start:
{
lean_object* v_declName_6834_; lean_object* v_type_6835_; lean_object* v_value_6836_; lean_object* v___x_6837_; 
v_declName_6834_ = lean_ctor_get(v_preDef_6821_, 3);
lean_inc(v_declName_6834_);
v_type_6835_ = lean_ctor_get(v_preDef_6821_, 6);
lean_inc_ref(v_type_6835_);
v_value_6836_ = lean_ctor_get(v_preDef_6821_, 7);
lean_inc_ref(v_value_6836_);
lean_dec_ref(v_preDef_6821_);
v___x_6837_ = l_Lean_Meta_instantiateForall(v_type_6835_, v_prefixArgs_6822_, v_a_6829_, v_a_6830_, v_a_6831_, v_a_6832_);
if (lean_obj_tag(v___x_6837_) == 0)
{
lean_object* v_a_6838_; lean_object* v___x_6839_; lean_object* v___x_6840_; lean_object* v___f_6841_; lean_object* v___x_6842_; uint8_t v___x_6843_; lean_object* v___x_6844_; 
v_a_6838_ = lean_ctor_get(v___x_6837_, 0);
lean_inc(v_a_6838_);
lean_dec_ref_known(v___x_6837_, 1);
v___x_6839_ = l_Lean_instInhabitedExpr;
v___x_6840_ = lean_unsigned_to_nat(1u);
v___f_6841_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__0___boxed), 12, 3);
lean_closure_set(v___f_6841_, 0, v___x_6839_);
lean_closure_set(v___f_6841_, 1, v___x_6840_);
lean_closure_set(v___f_6841_, 2, v_wfRel_6824_);
v___x_6842_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___closed__0));
v___x_6843_ = 0;
v___x_6844_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_a_6838_, v___x_6842_, v___f_6841_, v___x_6843_, v___x_6843_, v_a_6827_, v_a_6828_, v_a_6829_, v_a_6830_, v_a_6831_, v_a_6832_);
if (lean_obj_tag(v___x_6844_) == 0)
{
lean_object* v_a_6845_; lean_object* v_fst_6846_; lean_object* v_snd_6847_; lean_object* v___x_6848_; 
v_a_6845_ = lean_ctor_get(v___x_6844_, 0);
lean_inc(v_a_6845_);
lean_dec_ref_known(v___x_6844_, 1);
v_fst_6846_ = lean_ctor_get(v_a_6845_, 0);
lean_inc_n(v_fst_6846_, 2);
v_snd_6847_ = lean_ctor_get(v_a_6845_, 1);
lean_inc(v_snd_6847_);
lean_dec(v_a_6845_);
lean_inc(v_a_6832_);
lean_inc_ref(v_a_6831_);
lean_inc(v_a_6830_);
lean_inc_ref(v_a_6829_);
v___x_6848_ = lean_infer_type(v_fst_6846_, v_a_6829_, v_a_6830_, v_a_6831_, v_a_6832_);
if (lean_obj_tag(v___x_6848_) == 0)
{
lean_object* v_a_6849_; lean_object* v___x_6850_; 
v_a_6849_ = lean_ctor_get(v___x_6848_, 0);
lean_inc(v_a_6849_);
lean_dec_ref_known(v___x_6848_, 1);
lean_inc(v_a_6832_);
lean_inc_ref(v_a_6831_);
lean_inc(v_a_6830_);
lean_inc_ref(v_a_6829_);
v___x_6850_ = lean_whnf(v_a_6849_, v_a_6829_, v_a_6830_, v_a_6831_, v_a_6832_);
if (lean_obj_tag(v___x_6850_) == 0)
{
lean_object* v_a_6851_; lean_object* v___f_6852_; lean_object* v___x_6853_; lean_object* v___f_6854_; lean_object* v___x_6855_; lean_object* v___x_6856_; lean_object* v___x_6857_; 
v_a_6851_ = lean_ctor_get(v___x_6850_, 0);
lean_inc(v_a_6851_);
lean_dec_ref_known(v___x_6850_, 1);
lean_inc_ref(v_prefixArgs_6822_);
v___f_6852_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__1___boxed), 12, 2);
lean_closure_set(v___f_6852_, 0, v_prefixArgs_6822_);
lean_closure_set(v___f_6852_, 1, v_declName_6834_);
v___x_6853_ = lean_box(v___x_6843_);
v___f_6854_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__3___boxed), 20, 11);
lean_closure_set(v___f_6854_, 0, v___x_6839_);
lean_closure_set(v___f_6854_, 1, v_snd_6847_);
lean_closure_set(v___f_6854_, 2, v___x_6840_);
lean_closure_set(v___f_6854_, 3, v_prefixArgs_6822_);
lean_closure_set(v___f_6854_, 4, v_value_6836_);
lean_closure_set(v___f_6854_, 5, v___f_6852_);
lean_closure_set(v___f_6854_, 6, v_funNames_6825_);
lean_closure_set(v___f_6854_, 7, v_argsPacker_6823_);
lean_closure_set(v___f_6854_, 8, v_decrTactics_6826_);
lean_closure_set(v___f_6854_, 9, v___x_6853_);
lean_closure_set(v___f_6854_, 10, v_fst_6846_);
v___x_6855_ = l_Lean_Expr_bindingDomain_x21(v_a_6851_);
lean_dec(v_a_6851_);
v___x_6856_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___closed__1));
v___x_6857_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v___x_6855_, v___x_6856_, v___f_6854_, v___x_6843_, v___x_6843_, v_a_6827_, v_a_6828_, v_a_6829_, v_a_6830_, v_a_6831_, v_a_6832_);
return v___x_6857_;
}
else
{
lean_dec(v_snd_6847_);
lean_dec(v_fst_6846_);
lean_dec_ref(v_value_6836_);
lean_dec(v_declName_6834_);
lean_dec_ref(v_decrTactics_6826_);
lean_dec_ref(v_funNames_6825_);
lean_dec_ref(v_argsPacker_6823_);
lean_dec_ref(v_prefixArgs_6822_);
return v___x_6850_;
}
}
else
{
lean_dec(v_snd_6847_);
lean_dec(v_fst_6846_);
lean_dec_ref(v_value_6836_);
lean_dec(v_declName_6834_);
lean_dec_ref(v_decrTactics_6826_);
lean_dec_ref(v_funNames_6825_);
lean_dec_ref(v_argsPacker_6823_);
lean_dec_ref(v_prefixArgs_6822_);
return v___x_6848_;
}
}
else
{
lean_object* v_a_6858_; lean_object* v___x_6860_; uint8_t v_isShared_6861_; uint8_t v_isSharedCheck_6865_; 
lean_dec_ref(v_value_6836_);
lean_dec(v_declName_6834_);
lean_dec_ref(v_decrTactics_6826_);
lean_dec_ref(v_funNames_6825_);
lean_dec_ref(v_argsPacker_6823_);
lean_dec_ref(v_prefixArgs_6822_);
v_a_6858_ = lean_ctor_get(v___x_6844_, 0);
v_isSharedCheck_6865_ = !lean_is_exclusive(v___x_6844_);
if (v_isSharedCheck_6865_ == 0)
{
v___x_6860_ = v___x_6844_;
v_isShared_6861_ = v_isSharedCheck_6865_;
goto v_resetjp_6859_;
}
else
{
lean_inc(v_a_6858_);
lean_dec(v___x_6844_);
v___x_6860_ = lean_box(0);
v_isShared_6861_ = v_isSharedCheck_6865_;
goto v_resetjp_6859_;
}
v_resetjp_6859_:
{
lean_object* v___x_6863_; 
if (v_isShared_6861_ == 0)
{
v___x_6863_ = v___x_6860_;
goto v_reusejp_6862_;
}
else
{
lean_object* v_reuseFailAlloc_6864_; 
v_reuseFailAlloc_6864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6864_, 0, v_a_6858_);
v___x_6863_ = v_reuseFailAlloc_6864_;
goto v_reusejp_6862_;
}
v_reusejp_6862_:
{
return v___x_6863_;
}
}
}
}
else
{
lean_dec_ref(v_value_6836_);
lean_dec(v_declName_6834_);
lean_dec_ref(v_decrTactics_6826_);
lean_dec_ref(v_funNames_6825_);
lean_dec_ref(v_wfRel_6824_);
lean_dec_ref(v_argsPacker_6823_);
lean_dec_ref(v_prefixArgs_6822_);
return v___x_6837_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___boxed(lean_object* v_preDef_6866_, lean_object* v_prefixArgs_6867_, lean_object* v_argsPacker_6868_, lean_object* v_wfRel_6869_, lean_object* v_funNames_6870_, lean_object* v_decrTactics_6871_, lean_object* v_a_6872_, lean_object* v_a_6873_, lean_object* v_a_6874_, lean_object* v_a_6875_, lean_object* v_a_6876_, lean_object* v_a_6877_, lean_object* v_a_6878_){
_start:
{
lean_object* v_res_6879_; 
v_res_6879_ = l_Lean_Elab_WF_mkFix(v_preDef_6866_, v_prefixArgs_6867_, v_argsPacker_6868_, v_wfRel_6869_, v_funNames_6870_, v_decrTactics_6871_, v_a_6872_, v_a_6873_, v_a_6874_, v_a_6875_, v_a_6876_, v_a_6877_);
lean_dec(v_a_6877_);
lean_dec_ref(v_a_6876_);
lean_dec(v_a_6875_);
lean_dec_ref(v_a_6874_);
lean_dec(v_a_6873_);
lean_dec_ref(v_a_6872_);
return v_res_6879_;
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
