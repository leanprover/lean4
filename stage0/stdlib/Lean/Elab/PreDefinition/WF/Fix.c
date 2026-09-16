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
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addPPExplicitToExposeDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v_ref_509_ = lean_ctor_get(v___y_506_, 5);
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
lean_object* v_fileName_819_; lean_object* v_fileMap_820_; lean_object* v_options_821_; lean_object* v_currRecDepth_822_; lean_object* v_maxRecDepth_823_; lean_object* v_ref_824_; lean_object* v_currNamespace_825_; lean_object* v_openDecls_826_; lean_object* v_initHeartbeats_827_; lean_object* v_maxHeartbeats_828_; lean_object* v_quotContext_829_; lean_object* v_currMacroScope_830_; uint8_t v_diag_831_; lean_object* v_cancelTk_x3f_832_; uint8_t v_suppressElabErrors_833_; lean_object* v_inheritedTraceOptions_834_; lean_object* v_ref_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v_fileName_819_ = lean_ctor_get(v___y_816_, 0);
v_fileMap_820_ = lean_ctor_get(v___y_816_, 1);
v_options_821_ = lean_ctor_get(v___y_816_, 2);
v_currRecDepth_822_ = lean_ctor_get(v___y_816_, 3);
v_maxRecDepth_823_ = lean_ctor_get(v___y_816_, 4);
v_ref_824_ = lean_ctor_get(v___y_816_, 5);
v_currNamespace_825_ = lean_ctor_get(v___y_816_, 6);
v_openDecls_826_ = lean_ctor_get(v___y_816_, 7);
v_initHeartbeats_827_ = lean_ctor_get(v___y_816_, 8);
v_maxHeartbeats_828_ = lean_ctor_get(v___y_816_, 9);
v_quotContext_829_ = lean_ctor_get(v___y_816_, 10);
v_currMacroScope_830_ = lean_ctor_get(v___y_816_, 11);
v_diag_831_ = lean_ctor_get_uint8(v___y_816_, sizeof(void*)*14);
v_cancelTk_x3f_832_ = lean_ctor_get(v___y_816_, 12);
v_suppressElabErrors_833_ = lean_ctor_get_uint8(v___y_816_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_834_ = lean_ctor_get(v___y_816_, 13);
v_ref_835_ = l_Lean_replaceRef(v_ref_808_, v_ref_824_);
lean_inc_ref(v_inheritedTraceOptions_834_);
lean_inc(v_cancelTk_x3f_832_);
lean_inc(v_currMacroScope_830_);
lean_inc(v_quotContext_829_);
lean_inc(v_maxHeartbeats_828_);
lean_inc(v_initHeartbeats_827_);
lean_inc(v_openDecls_826_);
lean_inc(v_currNamespace_825_);
lean_inc(v_maxRecDepth_823_);
lean_inc(v_currRecDepth_822_);
lean_inc_ref(v_options_821_);
lean_inc_ref(v_fileMap_820_);
lean_inc_ref(v_fileName_819_);
v___x_836_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_836_, 0, v_fileName_819_);
lean_ctor_set(v___x_836_, 1, v_fileMap_820_);
lean_ctor_set(v___x_836_, 2, v_options_821_);
lean_ctor_set(v___x_836_, 3, v_currRecDepth_822_);
lean_ctor_set(v___x_836_, 4, v_maxRecDepth_823_);
lean_ctor_set(v___x_836_, 5, v_ref_835_);
lean_ctor_set(v___x_836_, 6, v_currNamespace_825_);
lean_ctor_set(v___x_836_, 7, v_openDecls_826_);
lean_ctor_set(v___x_836_, 8, v_initHeartbeats_827_);
lean_ctor_set(v___x_836_, 9, v_maxHeartbeats_828_);
lean_ctor_set(v___x_836_, 10, v_quotContext_829_);
lean_ctor_set(v___x_836_, 11, v_currMacroScope_830_);
lean_ctor_set(v___x_836_, 12, v_cancelTk_x3f_832_);
lean_ctor_set(v___x_836_, 13, v_inheritedTraceOptions_834_);
lean_ctor_set_uint8(v___x_836_, sizeof(void*)*14, v_diag_831_);
lean_ctor_set_uint8(v___x_836_, sizeof(void*)*14 + 1, v_suppressElabErrors_833_);
v___x_837_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v_msg_809_, v___y_814_, v___y_815_, v___x_836_, v___y_817_);
lean_dec_ref_known(v___x_836_, 14);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg___boxed(lean_object* v_ref_838_, lean_object* v_msg_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(v_ref_838_, v_msg_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
lean_dec(v___y_840_);
lean_dec(v_ref_838_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(lean_object* v_ref_850_, lean_object* v_msg_851_, lean_object* v_declHint_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v___x_862_; lean_object* v_a_863_; lean_object* v___x_864_; 
v___x_862_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30(v_msg_851_, v_declHint_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
v_a_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_a_863_);
lean_dec_ref(v___x_862_);
v___x_864_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(v_ref_850_, v_a_863_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg___boxed(lean_object* v_ref_865_, lean_object* v_msg_866_, lean_object* v_declHint_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(v_ref_865_, v_msg_866_, v_declHint_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec(v___y_869_);
lean_dec(v___y_868_);
lean_dec(v_ref_865_);
return v_res_877_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__0));
v___x_880_ = l_Lean_stringToMessageData(v___x_879_);
return v___x_880_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__2));
v___x_883_ = l_Lean_stringToMessageData(v___x_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(lean_object* v_ref_884_, lean_object* v_constName_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
lean_object* v___x_895_; uint8_t v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_895_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__1);
v___x_896_ = 0;
lean_inc(v_constName_885_);
v___x_897_ = l_Lean_MessageData_ofConstName(v_constName_885_, v___x_896_);
v___x_898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_895_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___closed__3);
v___x_900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_898_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(v_ref_884_, v___x_900_, v_constName_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg___boxed(lean_object* v_ref_902_, lean_object* v_constName_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(v_ref_902_, v_constName_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec(v___y_904_);
lean_dec(v_ref_902_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(lean_object* v_constName_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v_ref_924_; lean_object* v___x_925_; 
v_ref_924_ = lean_ctor_get(v___y_921_, 5);
v___x_925_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(v_ref_924_, v_constName_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg___boxed(lean_object* v_constName_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(v_constName_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec(v___y_927_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(lean_object* v_constName_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v___x_947_; lean_object* v_env_948_; uint8_t v___x_949_; lean_object* v___x_950_; 
v___x_947_ = lean_st_ref_get(v___y_945_);
v_env_948_ = lean_ctor_get(v___x_947_, 0);
lean_inc_ref(v_env_948_);
lean_dec(v___x_947_);
v___x_949_ = 0;
lean_inc(v_constName_937_);
v___x_950_ = l_Lean_Environment_find_x3f(v_env_948_, v_constName_937_, v___x_949_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v___x_951_; 
v___x_951_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(v_constName_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
return v___x_951_;
}
else
{
lean_object* v_val_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
lean_dec(v_constName_937_);
v_val_952_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_959_ == 0)
{
v___x_954_ = v___x_950_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_val_952_);
lean_dec(v___x_950_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
lean_ctor_set_tag(v___x_954_, 0);
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_val_952_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18___boxed(lean_object* v_constName_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(v_constName_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec(v___y_961_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(lean_object* v_declName_971_, lean_object* v___y_972_){
_start:
{
lean_object* v___x_974_; lean_object* v_env_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_974_ = lean_st_ref_get(v___y_972_);
v_env_975_ = lean_ctor_get(v___x_974_, 0);
lean_inc_ref(v_env_975_);
lean_dec(v___x_974_);
v___x_976_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_975_, v_declName_971_);
v___x_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg___boxed(lean_object* v_declName_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(v_declName_978_, v___y_979_);
lean_dec(v___y_979_);
return v_res_981_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0(void){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_instMonadEIO(lean_box(0));
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19(lean_object* v_msg_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v_toApplicative_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1094_; 
v___x_999_ = lean_obj_once(&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0, &l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0_once, _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__0);
v___x_1000_ = l_StateRefT_x27_instMonad___redArg(v___x_999_);
v_toApplicative_1001_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1094_ == 0)
{
lean_object* v_unused_1095_; 
v_unused_1095_ = lean_ctor_get(v___x_1000_, 1);
lean_dec(v_unused_1095_);
v___x_1003_ = v___x_1000_;
v_isShared_1004_ = v_isSharedCheck_1094_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_toApplicative_1001_);
lean_dec(v___x_1000_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1094_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v_toFunctor_1005_; lean_object* v_toSeq_1006_; lean_object* v_toSeqLeft_1007_; lean_object* v_toSeqRight_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1092_; 
v_toFunctor_1005_ = lean_ctor_get(v_toApplicative_1001_, 0);
v_toSeq_1006_ = lean_ctor_get(v_toApplicative_1001_, 2);
v_toSeqLeft_1007_ = lean_ctor_get(v_toApplicative_1001_, 3);
v_toSeqRight_1008_ = lean_ctor_get(v_toApplicative_1001_, 4);
v_isSharedCheck_1092_ = !lean_is_exclusive(v_toApplicative_1001_);
if (v_isSharedCheck_1092_ == 0)
{
lean_object* v_unused_1093_; 
v_unused_1093_ = lean_ctor_get(v_toApplicative_1001_, 1);
lean_dec(v_unused_1093_);
v___x_1010_ = v_toApplicative_1001_;
v_isShared_1011_ = v_isSharedCheck_1092_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_toSeqRight_1008_);
lean_inc(v_toSeqLeft_1007_);
lean_inc(v_toSeq_1006_);
lean_inc(v_toFunctor_1005_);
lean_dec(v_toApplicative_1001_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1092_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___f_1012_; lean_object* v___f_1013_; lean_object* v___f_1014_; lean_object* v___f_1015_; lean_object* v___x_1016_; lean_object* v___f_1017_; lean_object* v___f_1018_; lean_object* v___f_1019_; lean_object* v___x_1021_; 
v___f_1012_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__1));
v___f_1013_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__2));
lean_inc_ref(v_toFunctor_1005_);
v___f_1014_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1014_, 0, v_toFunctor_1005_);
v___f_1015_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1015_, 0, v_toFunctor_1005_);
v___x_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___f_1014_);
lean_ctor_set(v___x_1016_, 1, v___f_1015_);
v___f_1017_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1017_, 0, v_toSeqRight_1008_);
v___f_1018_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1018_, 0, v_toSeqLeft_1007_);
v___f_1019_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1019_, 0, v_toSeq_1006_);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 4, v___f_1017_);
lean_ctor_set(v___x_1010_, 3, v___f_1018_);
lean_ctor_set(v___x_1010_, 2, v___f_1019_);
lean_ctor_set(v___x_1010_, 1, v___f_1012_);
lean_ctor_set(v___x_1010_, 0, v___x_1016_);
v___x_1021_ = v___x_1010_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1016_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v___f_1012_);
lean_ctor_set(v_reuseFailAlloc_1091_, 2, v___f_1019_);
lean_ctor_set(v_reuseFailAlloc_1091_, 3, v___f_1018_);
lean_ctor_set(v_reuseFailAlloc_1091_, 4, v___f_1017_);
v___x_1021_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
lean_object* v___x_1023_; 
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 1, v___f_1013_);
lean_ctor_set(v___x_1003_, 0, v___x_1021_);
v___x_1023_ = v___x_1003_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1021_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v___f_1013_);
v___x_1023_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
lean_object* v___x_1024_; lean_object* v_toApplicative_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1088_; 
v___x_1024_ = l_StateRefT_x27_instMonad___redArg(v___x_1023_);
v_toApplicative_1025_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1088_ == 0)
{
lean_object* v_unused_1089_; 
v_unused_1089_ = lean_ctor_get(v___x_1024_, 1);
lean_dec(v_unused_1089_);
v___x_1027_ = v___x_1024_;
v_isShared_1028_ = v_isSharedCheck_1088_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_toApplicative_1025_);
lean_dec(v___x_1024_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1088_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v_toFunctor_1029_; lean_object* v_toSeq_1030_; lean_object* v_toSeqLeft_1031_; lean_object* v_toSeqRight_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1086_; 
v_toFunctor_1029_ = lean_ctor_get(v_toApplicative_1025_, 0);
v_toSeq_1030_ = lean_ctor_get(v_toApplicative_1025_, 2);
v_toSeqLeft_1031_ = lean_ctor_get(v_toApplicative_1025_, 3);
v_toSeqRight_1032_ = lean_ctor_get(v_toApplicative_1025_, 4);
v_isSharedCheck_1086_ = !lean_is_exclusive(v_toApplicative_1025_);
if (v_isSharedCheck_1086_ == 0)
{
lean_object* v_unused_1087_; 
v_unused_1087_ = lean_ctor_get(v_toApplicative_1025_, 1);
lean_dec(v_unused_1087_);
v___x_1034_ = v_toApplicative_1025_;
v_isShared_1035_ = v_isSharedCheck_1086_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_toSeqRight_1032_);
lean_inc(v_toSeqLeft_1031_);
lean_inc(v_toSeq_1030_);
lean_inc(v_toFunctor_1029_);
lean_dec(v_toApplicative_1025_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1086_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___f_1036_; lean_object* v___f_1037_; lean_object* v___f_1038_; lean_object* v___f_1039_; lean_object* v___x_1040_; lean_object* v___f_1041_; lean_object* v___f_1042_; lean_object* v___f_1043_; lean_object* v___x_1045_; 
v___f_1036_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__3));
v___f_1037_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__4));
lean_inc_ref(v_toFunctor_1029_);
v___f_1038_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1038_, 0, v_toFunctor_1029_);
v___f_1039_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1039_, 0, v_toFunctor_1029_);
v___x_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___f_1038_);
lean_ctor_set(v___x_1040_, 1, v___f_1039_);
v___f_1041_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1041_, 0, v_toSeqRight_1032_);
v___f_1042_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1042_, 0, v_toSeqLeft_1031_);
v___f_1043_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1043_, 0, v_toSeq_1030_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 4, v___f_1041_);
lean_ctor_set(v___x_1034_, 3, v___f_1042_);
lean_ctor_set(v___x_1034_, 2, v___f_1043_);
lean_ctor_set(v___x_1034_, 1, v___f_1036_);
lean_ctor_set(v___x_1034_, 0, v___x_1040_);
v___x_1045_ = v___x_1034_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1040_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v___f_1036_);
lean_ctor_set(v_reuseFailAlloc_1085_, 2, v___f_1043_);
lean_ctor_set(v_reuseFailAlloc_1085_, 3, v___f_1042_);
lean_ctor_set(v_reuseFailAlloc_1085_, 4, v___f_1041_);
v___x_1045_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
lean_object* v___x_1047_; 
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 1, v___f_1037_);
lean_ctor_set(v___x_1027_, 0, v___x_1045_);
v___x_1047_ = v___x_1027_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v___f_1037_);
v___x_1047_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
lean_object* v___x_1048_; lean_object* v_toApplicative_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1082_; 
v___x_1048_ = l_StateRefT_x27_instMonad___redArg(v___x_1047_);
v_toApplicative_1049_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1082_ == 0)
{
lean_object* v_unused_1083_; 
v_unused_1083_ = lean_ctor_get(v___x_1048_, 1);
lean_dec(v_unused_1083_);
v___x_1051_ = v___x_1048_;
v_isShared_1052_ = v_isSharedCheck_1082_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_toApplicative_1049_);
lean_dec(v___x_1048_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1082_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v_toFunctor_1053_; lean_object* v_toSeq_1054_; lean_object* v_toSeqLeft_1055_; lean_object* v_toSeqRight_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1080_; 
v_toFunctor_1053_ = lean_ctor_get(v_toApplicative_1049_, 0);
v_toSeq_1054_ = lean_ctor_get(v_toApplicative_1049_, 2);
v_toSeqLeft_1055_ = lean_ctor_get(v_toApplicative_1049_, 3);
v_toSeqRight_1056_ = lean_ctor_get(v_toApplicative_1049_, 4);
v_isSharedCheck_1080_ = !lean_is_exclusive(v_toApplicative_1049_);
if (v_isSharedCheck_1080_ == 0)
{
lean_object* v_unused_1081_; 
v_unused_1081_ = lean_ctor_get(v_toApplicative_1049_, 1);
lean_dec(v_unused_1081_);
v___x_1058_ = v_toApplicative_1049_;
v_isShared_1059_ = v_isSharedCheck_1080_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_toSeqRight_1056_);
lean_inc(v_toSeqLeft_1055_);
lean_inc(v_toSeq_1054_);
lean_inc(v_toFunctor_1053_);
lean_dec(v_toApplicative_1049_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1080_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___f_1060_; lean_object* v___f_1061_; lean_object* v___f_1062_; lean_object* v___f_1063_; lean_object* v___x_1064_; lean_object* v___f_1065_; lean_object* v___f_1066_; lean_object* v___f_1067_; lean_object* v___x_1069_; 
v___f_1060_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__5));
v___f_1061_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___closed__6));
lean_inc_ref(v_toFunctor_1053_);
v___f_1062_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1062_, 0, v_toFunctor_1053_);
v___f_1063_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1063_, 0, v_toFunctor_1053_);
v___x_1064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___f_1062_);
lean_ctor_set(v___x_1064_, 1, v___f_1063_);
v___f_1065_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1065_, 0, v_toSeqRight_1056_);
v___f_1066_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1066_, 0, v_toSeqLeft_1055_);
v___f_1067_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1067_, 0, v_toSeq_1054_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 4, v___f_1065_);
lean_ctor_set(v___x_1058_, 3, v___f_1066_);
lean_ctor_set(v___x_1058_, 2, v___f_1067_);
lean_ctor_set(v___x_1058_, 1, v___f_1060_);
lean_ctor_set(v___x_1058_, 0, v___x_1064_);
v___x_1069_ = v___x_1058_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1064_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v___f_1060_);
lean_ctor_set(v_reuseFailAlloc_1079_, 2, v___f_1067_);
lean_ctor_set(v_reuseFailAlloc_1079_, 3, v___f_1066_);
lean_ctor_set(v_reuseFailAlloc_1079_, 4, v___f_1065_);
v___x_1069_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
lean_object* v___x_1071_; 
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 1, v___f_1061_);
lean_ctor_set(v___x_1051_, 0, v___x_1069_);
v___x_1071_ = v___x_1051_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1069_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v___f_1061_);
v___x_1071_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_49571__overap_1076_; lean_object* v___x_1077_; 
v___x_1072_ = l_StateRefT_x27_instMonad___redArg(v___x_1071_);
v___x_1073_ = l_StateRefT_x27_instMonad___redArg(v___x_1072_);
v___x_1074_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_1075_ = l_instInhabitedOfMonad___redArg(v___x_1073_, v___x_1074_);
v___x_49571__overap_1076_ = lean_panic_fn_borrowed(v___x_1075_, v_msg_989_);
lean_dec(v___x_1075_);
lean_inc(v___y_997_);
lean_inc_ref(v___y_996_);
lean_inc(v___y_995_);
lean_inc_ref(v___y_994_);
lean_inc(v___y_993_);
lean_inc_ref(v___y_992_);
lean_inc(v___y_991_);
lean_inc(v___y_990_);
v___x_1077_ = lean_apply_9(v___x_49571__overap_1076_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, lean_box(0));
return v___x_1077_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19___boxed(lean_object* v_msg_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19(v_msg_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec(v___y_1097_);
return v_res_1106_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3(void){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1110_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__2));
v___x_1111_ = lean_unsigned_to_nat(53u);
v___x_1112_ = lean_unsigned_to_nat(62u);
v___x_1113_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__1));
v___x_1114_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__0));
v___x_1115_ = l_mkPanicMessageWithDecl(v___x_1114_, v___x_1113_, v___x_1112_, v___x_1111_, v___x_1110_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21(size_t v_sz_1116_, size_t v_i_1117_, lean_object* v_bs_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
uint8_t v___x_1128_; 
v___x_1128_ = lean_usize_dec_lt(v_i_1117_, v_sz_1116_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1129_; 
v___x_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1129_, 0, v_bs_1118_);
return v___x_1129_;
}
else
{
lean_object* v_v_1130_; lean_object* v___x_1131_; 
v_v_1130_ = lean_array_uget_borrowed(v_bs_1118_, v_i_1117_);
lean_inc(v_v_1130_);
v___x_1131_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(v_v_1130_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v_a_1132_; lean_object* v___x_1133_; lean_object* v_bs_x27_1134_; lean_object* v_a_1136_; 
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
lean_inc(v_a_1132_);
lean_dec_ref_known(v___x_1131_, 1);
v___x_1133_ = lean_unsigned_to_nat(0u);
v_bs_x27_1134_ = lean_array_uset(v_bs_1118_, v_i_1117_, v___x_1133_);
if (lean_obj_tag(v_a_1132_) == 6)
{
lean_object* v_val_1141_; lean_object* v_numFields_1142_; uint8_t v___x_1143_; lean_object* v___x_1144_; 
v_val_1141_ = lean_ctor_get(v_a_1132_, 0);
lean_inc_ref(v_val_1141_);
lean_dec_ref_known(v_a_1132_, 1);
v_numFields_1142_ = lean_ctor_get(v_val_1141_, 4);
lean_inc(v_numFields_1142_);
lean_dec_ref(v_val_1141_);
v___x_1143_ = 0;
v___x_1144_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1144_, 0, v_numFields_1142_);
lean_ctor_set(v___x_1144_, 1, v___x_1133_);
lean_ctor_set_uint8(v___x_1144_, sizeof(void*)*2, v___x_1143_);
v_a_1136_ = v___x_1144_;
goto v___jp_1135_;
}
else
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
lean_dec(v_a_1132_);
v___x_1145_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___closed__3);
v___x_1146_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__19(v___x_1145_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; 
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
lean_inc(v_a_1147_);
lean_dec_ref_known(v___x_1146_, 1);
v_a_1136_ = v_a_1147_;
goto v___jp_1135_;
}
else
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1155_; 
lean_dec_ref(v_bs_x27_1134_);
v_a_1148_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1150_ = v___x_1146_;
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1146_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1148_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
v___jp_1135_:
{
size_t v___x_1137_; size_t v___x_1138_; lean_object* v___x_1139_; 
v___x_1137_ = ((size_t)1ULL);
v___x_1138_ = lean_usize_add(v_i_1117_, v___x_1137_);
v___x_1139_ = lean_array_uset(v_bs_x27_1134_, v_i_1117_, v_a_1136_);
v_i_1117_ = v___x_1138_;
v_bs_1118_ = v___x_1139_;
goto _start;
}
}
else
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
lean_dec_ref(v_bs_1118_);
v_a_1156_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_1131_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1131_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21___boxed(lean_object* v_sz_1164_, lean_object* v_i_1165_, lean_object* v_bs_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
size_t v_sz_boxed_1176_; size_t v_i_boxed_1177_; lean_object* v_res_1178_; 
v_sz_boxed_1176_ = lean_unbox_usize(v_sz_1164_);
lean_dec(v_sz_1164_);
v_i_boxed_1177_ = lean_unbox_usize(v_i_1165_);
lean_dec(v_i_1165_);
v_res_1178_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21(v_sz_boxed_1176_, v_i_boxed_1177_, v_bs_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec(v___y_1167_);
return v_res_1178_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0(void){
_start:
{
lean_object* v___x_1179_; lean_object* v_dummy_1180_; 
v___x_1179_ = lean_box(0);
v_dummy_1180_ = l_Lean_Expr_sort___override(v___x_1179_);
return v_dummy_1180_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1(void){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1181_ = lean_box(0);
v___x_1182_ = lean_unsigned_to_nat(16u);
v___x_1183_ = lean_mk_array(v___x_1182_, v___x_1181_);
return v___x_1183_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2(void){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1184_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__1);
v___x_1185_ = lean_unsigned_to_nat(0u);
v___x_1186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
lean_ctor_set(v___x_1186_, 1, v___x_1184_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(lean_object* v_e_1189_, uint8_t v_alsoCasesOn_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
uint8_t v___x_1203_; 
v___x_1203_ = l_Lean_Expr_isApp(v_e_1189_);
if (v___x_1203_ == 0)
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
lean_dec_ref(v_e_1189_);
v___x_1204_ = lean_box(0);
v___x_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1204_);
return v___x_1205_;
}
else
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Lean_Expr_getAppFn(v_e_1189_);
if (lean_obj_tag(v___x_1206_) == 4)
{
lean_object* v_declName_1207_; lean_object* v_us_1208_; lean_object* v___x_1209_; lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1363_; 
v_declName_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc_n(v_declName_1207_, 2);
v_us_1208_ = lean_ctor_get(v___x_1206_, 1);
lean_inc(v_us_1208_);
lean_dec_ref_known(v___x_1206_, 2);
v___x_1209_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(v_declName_1207_, v___y_1198_);
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1212_ = v___x_1209_;
v_isShared_1213_ = v_isSharedCheck_1363_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1209_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1363_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1214_; 
v___x_1214_ = l_Lean_instInhabitedExpr;
if (lean_obj_tag(v_a_1210_) == 1)
{
lean_object* v_val_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1256_; 
v_val_1215_ = lean_ctor_get(v_a_1210_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v_a_1210_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1217_ = v_a_1210_;
v_isShared_1218_ = v_isSharedCheck_1256_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_val_1215_);
lean_dec(v_a_1210_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1256_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v_dummy_1219_; lean_object* v_nargs_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v_args_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; uint8_t v___x_1227_; 
v_dummy_1219_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
v_nargs_1220_ = l_Lean_Expr_getAppNumArgs(v_e_1189_);
lean_inc(v_nargs_1220_);
v___x_1221_ = lean_mk_array(v_nargs_1220_, v_dummy_1219_);
v___x_1222_ = lean_unsigned_to_nat(1u);
v___x_1223_ = lean_nat_sub(v_nargs_1220_, v___x_1222_);
lean_dec(v_nargs_1220_);
v_args_1224_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1189_, v___x_1221_, v___x_1223_);
v___x_1225_ = lean_array_get_size(v_args_1224_);
v___x_1226_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_1215_);
v___x_1227_ = lean_nat_dec_lt(v___x_1225_, v___x_1226_);
lean_dec(v___x_1226_);
if (v___x_1227_ == 0)
{
lean_object* v_numParams_1228_; lean_object* v_numDiscrs_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1247_; 
v_numParams_1228_ = lean_ctor_get(v_val_1215_, 0);
v_numDiscrs_1229_ = lean_ctor_get(v_val_1215_, 1);
v___x_1230_ = lean_array_mk(v_us_1208_);
v___x_1231_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1228_);
v___x_1232_ = l_Array_extract___redArg(v_args_1224_, v___x_1231_, v_numParams_1228_);
v___x_1233_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_1215_);
v___x_1234_ = lean_array_get(v___x_1214_, v_args_1224_, v___x_1233_);
lean_dec(v___x_1233_);
v___x_1235_ = lean_nat_add(v_numParams_1228_, v___x_1222_);
v___x_1236_ = lean_nat_add(v___x_1235_, v_numDiscrs_1229_);
lean_inc(v___x_1236_);
lean_inc_ref_n(v_args_1224_, 2);
v___x_1237_ = l_Array_toSubarray___redArg(v_args_1224_, v___x_1235_, v___x_1236_);
v___x_1238_ = l_Subarray_copy___redArg(v___x_1237_);
v___x_1239_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1215_);
v___x_1240_ = lean_nat_add(v___x_1236_, v___x_1239_);
lean_dec(v___x_1239_);
lean_inc(v___x_1240_);
v___x_1241_ = l_Array_toSubarray___redArg(v_args_1224_, v___x_1236_, v___x_1240_);
v___x_1242_ = l_Subarray_copy___redArg(v___x_1241_);
v___x_1243_ = l_Array_toSubarray___redArg(v_args_1224_, v___x_1240_, v___x_1225_);
v___x_1244_ = l_Subarray_copy___redArg(v___x_1243_);
v___x_1245_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1245_, 0, v_val_1215_);
lean_ctor_set(v___x_1245_, 1, v_declName_1207_);
lean_ctor_set(v___x_1245_, 2, v___x_1230_);
lean_ctor_set(v___x_1245_, 3, v___x_1232_);
lean_ctor_set(v___x_1245_, 4, v___x_1234_);
lean_ctor_set(v___x_1245_, 5, v___x_1238_);
lean_ctor_set(v___x_1245_, 6, v___x_1242_);
lean_ctor_set(v___x_1245_, 7, v___x_1244_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1245_);
v___x_1247_ = v___x_1217_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1245_);
v___x_1247_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
lean_object* v___x_1249_; 
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 0, v___x_1247_);
v___x_1249_ = v___x_1212_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1247_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
else
{
lean_object* v___x_1252_; lean_object* v___x_1254_; 
lean_dec_ref(v_args_1224_);
lean_del_object(v___x_1217_);
lean_dec(v_val_1215_);
lean_dec(v_us_1208_);
lean_dec(v_declName_1207_);
v___x_1252_ = lean_box(0);
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 0, v___x_1252_);
v___x_1254_ = v___x_1212_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1252_);
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
else
{
lean_object* v___x_1257_; 
lean_del_object(v___x_1212_);
lean_dec(v_a_1210_);
v___x_1257_ = lean_st_ref_get(v___y_1198_);
if (v_alsoCasesOn_1190_ == 0)
{
lean_dec(v___x_1257_);
lean_dec(v_us_1208_);
lean_dec(v_declName_1207_);
lean_dec_ref(v_e_1189_);
goto v___jp_1200_;
}
else
{
lean_object* v_env_1258_; uint8_t v___x_1259_; 
v_env_1258_ = lean_ctor_get(v___x_1257_, 0);
lean_inc_ref(v_env_1258_);
lean_dec(v___x_1257_);
lean_inc(v_declName_1207_);
v___x_1259_ = l_Lean_isCasesOnRecursor(v_env_1258_, v_declName_1207_);
if (v___x_1259_ == 0)
{
lean_dec(v_us_1208_);
lean_dec(v_declName_1207_);
lean_dec_ref(v_e_1189_);
goto v___jp_1200_;
}
else
{
lean_object* v_indName_1260_; lean_object* v___x_1261_; 
v_indName_1260_ = l_Lean_Name_getPrefix(v_declName_1207_);
v___x_1261_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18(v_indName_1260_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1354_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1264_ = v___x_1261_;
v_isShared_1265_ = v_isSharedCheck_1354_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1261_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1354_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
if (lean_obj_tag(v_a_1262_) == 5)
{
lean_object* v_val_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1349_; 
v_val_1266_ = lean_ctor_get(v_a_1262_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v_a_1262_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1268_ = v_a_1262_;
v_isShared_1269_ = v_isSharedCheck_1349_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_val_1266_);
lean_dec(v_a_1262_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1349_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v_toConstantVal_1270_; lean_object* v_numParams_1271_; lean_object* v_numIndices_1272_; lean_object* v_ctors_1273_; lean_object* v_nargs_1274_; lean_object* v_dummy_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v_args_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; 
v_toConstantVal_1270_ = lean_ctor_get(v_val_1266_, 0);
lean_inc_ref(v_toConstantVal_1270_);
v_numParams_1271_ = lean_ctor_get(v_val_1266_, 1);
lean_inc(v_numParams_1271_);
v_numIndices_1272_ = lean_ctor_get(v_val_1266_, 2);
lean_inc(v_numIndices_1272_);
v_ctors_1273_ = lean_ctor_get(v_val_1266_, 4);
lean_inc(v_ctors_1273_);
v_nargs_1274_ = l_Lean_Expr_getAppNumArgs(v_e_1189_);
v_dummy_1275_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v_nargs_1274_);
v___x_1276_ = lean_mk_array(v_nargs_1274_, v_dummy_1275_);
v___x_1277_ = lean_unsigned_to_nat(1u);
v___x_1278_ = lean_nat_sub(v_nargs_1274_, v___x_1277_);
lean_dec(v_nargs_1274_);
v_args_1279_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1189_, v___x_1276_, v___x_1278_);
v___x_1280_ = lean_nat_add(v_numParams_1271_, v___x_1277_);
v___x_1281_ = lean_nat_add(v___x_1280_, v_numIndices_1272_);
v___x_1282_ = lean_nat_add(v___x_1281_, v___x_1277_);
lean_dec(v___x_1281_);
v___x_1283_ = l_Lean_InductiveVal_numCtors(v_val_1266_);
lean_dec_ref(v_val_1266_);
v___x_1284_ = lean_nat_add(v___x_1282_, v___x_1283_);
lean_dec(v___x_1283_);
v___x_1285_ = lean_array_get_size(v_args_1279_);
v___x_1286_ = lean_nat_dec_le(v___x_1284_, v___x_1285_);
if (v___x_1286_ == 0)
{
lean_object* v___x_1287_; lean_object* v___x_1289_; 
lean_dec(v___x_1284_);
lean_dec(v___x_1282_);
lean_dec(v___x_1280_);
lean_dec_ref(v_args_1279_);
lean_dec(v_ctors_1273_);
lean_dec(v_numIndices_1272_);
lean_dec(v_numParams_1271_);
lean_dec_ref(v_toConstantVal_1270_);
lean_del_object(v___x_1268_);
lean_dec(v_us_1208_);
lean_dec(v_declName_1207_);
v___x_1287_ = lean_box(0);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 0, v___x_1287_);
v___x_1289_ = v___x_1264_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1287_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
else
{
lean_object* v___x_1291_; lean_object* v_params_1292_; lean_object* v_motive_1293_; lean_object* v_discrs_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v_discrInfos_1297_; lean_object* v_alts_1298_; lean_object* v___y_1300_; lean_object* v___y_1301_; lean_object* v_lower_1340_; lean_object* v_upper_1341_; uint8_t v___x_1348_; 
lean_del_object(v___x_1264_);
v___x_1291_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1271_);
lean_inc_ref_n(v_args_1279_, 3);
v_params_1292_ = l_Array_toSubarray___redArg(v_args_1279_, v___x_1291_, v_numParams_1271_);
v_motive_1293_ = lean_array_get(v___x_1214_, v_args_1279_, v_numParams_1271_);
lean_dec(v_numParams_1271_);
lean_inc(v___x_1282_);
v_discrs_1294_ = l_Array_toSubarray___redArg(v_args_1279_, v___x_1280_, v___x_1282_);
v___x_1295_ = lean_nat_add(v_numIndices_1272_, v___x_1277_);
lean_dec(v_numIndices_1272_);
v___x_1296_ = lean_box(0);
v_discrInfos_1297_ = lean_mk_array(v___x_1295_, v___x_1296_);
lean_inc(v___x_1284_);
v_alts_1298_ = l_Array_toSubarray___redArg(v_args_1279_, v___x_1282_, v___x_1284_);
v___x_1348_ = lean_nat_dec_le(v___x_1284_, v___x_1291_);
if (v___x_1348_ == 0)
{
v_lower_1340_ = v___x_1284_;
v_upper_1341_ = v___x_1285_;
goto v___jp_1339_;
}
else
{
lean_dec(v___x_1284_);
v_lower_1340_ = v___x_1291_;
v_upper_1341_ = v___x_1285_;
goto v___jp_1339_;
}
v___jp_1299_:
{
lean_object* v___x_1302_; size_t v_sz_1303_; size_t v___x_1304_; lean_object* v___x_1305_; 
v___x_1302_ = lean_array_mk(v_ctors_1273_);
v_sz_1303_ = lean_array_size(v___x_1302_);
v___x_1304_ = ((size_t)0ULL);
v___x_1305_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21(v_sz_1303_, v___x_1304_, v___x_1302_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1330_; 
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1308_ = v___x_1305_;
v_isShared_1309_ = v_isSharedCheck_1330_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1305_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1330_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v_start_1310_; lean_object* v_stop_1311_; lean_object* v_start_1312_; lean_object* v_stop_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1325_; 
v_start_1310_ = lean_ctor_get(v_params_1292_, 1);
lean_inc(v_start_1310_);
v_stop_1311_ = lean_ctor_get(v_params_1292_, 2);
lean_inc(v_stop_1311_);
v_start_1312_ = lean_ctor_get(v_discrs_1294_, 1);
lean_inc(v_start_1312_);
v_stop_1313_ = lean_ctor_get(v_discrs_1294_, 2);
lean_inc(v_stop_1313_);
v___x_1314_ = lean_nat_sub(v_stop_1311_, v_start_1310_);
lean_dec(v_start_1310_);
lean_dec(v_stop_1311_);
v___x_1315_ = lean_nat_sub(v_stop_1313_, v_start_1312_);
lean_dec(v_start_1312_);
lean_dec(v_stop_1313_);
v___x_1316_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2);
v___x_1317_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1314_);
lean_ctor_set(v___x_1317_, 1, v___x_1315_);
lean_ctor_set(v___x_1317_, 2, v_a_1306_);
lean_ctor_set(v___x_1317_, 3, v___y_1301_);
lean_ctor_set(v___x_1317_, 4, v_discrInfos_1297_);
lean_ctor_set(v___x_1317_, 5, v___x_1316_);
v___x_1318_ = lean_array_mk(v_us_1208_);
v___x_1319_ = l_Subarray_copy___redArg(v_params_1292_);
v___x_1320_ = l_Subarray_copy___redArg(v_discrs_1294_);
v___x_1321_ = l_Subarray_copy___redArg(v_alts_1298_);
v___x_1322_ = l_Subarray_copy___redArg(v___y_1300_);
v___x_1323_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1317_);
lean_ctor_set(v___x_1323_, 1, v_declName_1207_);
lean_ctor_set(v___x_1323_, 2, v___x_1318_);
lean_ctor_set(v___x_1323_, 3, v___x_1319_);
lean_ctor_set(v___x_1323_, 4, v_motive_1293_);
lean_ctor_set(v___x_1323_, 5, v___x_1320_);
lean_ctor_set(v___x_1323_, 6, v___x_1321_);
lean_ctor_set(v___x_1323_, 7, v___x_1322_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set_tag(v___x_1268_, 1);
lean_ctor_set(v___x_1268_, 0, v___x_1323_);
v___x_1325_ = v___x_1268_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1323_);
v___x_1325_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
lean_object* v___x_1327_; 
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 0, v___x_1325_);
v___x_1327_ = v___x_1308_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v___x_1325_);
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
else
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1338_; 
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec_ref(v_alts_1298_);
lean_dec_ref(v_discrInfos_1297_);
lean_dec_ref(v_discrs_1294_);
lean_dec(v_motive_1293_);
lean_dec_ref(v_params_1292_);
lean_del_object(v___x_1268_);
lean_dec(v_us_1208_);
lean_dec(v_declName_1207_);
v_a_1331_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1333_ = v___x_1305_;
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1305_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1336_; 
if (v_isShared_1334_ == 0)
{
v___x_1336_ = v___x_1333_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_a_1331_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
}
v___jp_1339_:
{
lean_object* v_levelParams_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; 
v_levelParams_1342_ = lean_ctor_get(v_toConstantVal_1270_, 1);
lean_inc(v_levelParams_1342_);
lean_dec_ref(v_toConstantVal_1270_);
v___x_1343_ = l_Array_toSubarray___redArg(v_args_1279_, v_lower_1340_, v_upper_1341_);
v___x_1344_ = l_List_lengthTR___redArg(v_levelParams_1342_);
lean_dec(v_levelParams_1342_);
v___x_1345_ = l_List_lengthTR___redArg(v_us_1208_);
v___x_1346_ = lean_nat_dec_eq(v___x_1344_, v___x_1345_);
lean_dec(v___x_1345_);
lean_dec(v___x_1344_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1347_; 
v___x_1347_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__3));
v___y_1300_ = v___x_1343_;
v___y_1301_ = v___x_1347_;
goto v___jp_1299_;
}
else
{
v___y_1300_ = v___x_1343_;
v___y_1301_ = v___x_1296_;
goto v___jp_1299_;
}
}
}
}
}
else
{
lean_object* v___x_1350_; lean_object* v___x_1352_; 
lean_dec(v_a_1262_);
lean_dec(v_us_1208_);
lean_dec(v_declName_1207_);
lean_dec_ref(v_e_1189_);
v___x_1350_ = lean_box(0);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 0, v___x_1350_);
v___x_1352_ = v___x_1264_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1350_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
lean_dec(v_us_1208_);
lean_dec(v_declName_1207_);
lean_dec_ref(v_e_1189_);
v_a_1355_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1261_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1261_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
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
lean_dec_ref(v___x_1206_);
lean_dec_ref(v_e_1189_);
goto v___jp_1200_;
}
}
v___jp_1200_:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1201_ = lean_box(0);
v___x_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
return v___x_1202_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___boxed(lean_object* v_e_1364_, lean_object* v_alsoCasesOn_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
uint8_t v_alsoCasesOn_boxed_1375_; lean_object* v_res_1376_; 
v_alsoCasesOn_boxed_1375_ = lean_unbox(v_alsoCasesOn_1365_);
v_res_1376_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(v_e_1364_, v_alsoCasesOn_boxed_1375_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec(v___y_1367_);
lean_dec(v___y_1366_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0(lean_object* v_k_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v_b_1382_, lean_object* v_c_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v___x_1389_; 
lean_inc(v___y_1387_);
lean_inc_ref(v___y_1386_);
lean_inc(v___y_1385_);
lean_inc_ref(v___y_1384_);
lean_inc(v___y_1381_);
lean_inc_ref(v___y_1380_);
lean_inc(v___y_1379_);
lean_inc(v___y_1378_);
v___x_1389_ = lean_apply_11(v_k_1377_, v_b_1382_, v_c_1383_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, lean_box(0));
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0___boxed(lean_object* v_k_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v_b_1395_, lean_object* v_c_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0(v_k_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v_b_1395_, v_c_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec(v___y_1392_);
lean_dec(v___y_1391_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(lean_object* v_e_1403_, lean_object* v_maxFVars_1404_, lean_object* v_k_1405_, uint8_t v_cleanupAnnotations_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v___f_1416_; uint8_t v___x_1417_; uint8_t v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
lean_inc(v___y_1410_);
lean_inc_ref(v___y_1409_);
lean_inc(v___y_1408_);
lean_inc(v___y_1407_);
v___f_1416_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1416_, 0, v_k_1405_);
lean_closure_set(v___f_1416_, 1, v___y_1407_);
lean_closure_set(v___f_1416_, 2, v___y_1408_);
lean_closure_set(v___f_1416_, 3, v___y_1409_);
lean_closure_set(v___f_1416_, 4, v___y_1410_);
v___x_1417_ = 1;
v___x_1418_ = 0;
v___x_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1419_, 0, v_maxFVars_1404_);
v___x_1420_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1403_, v___x_1417_, v___x_1418_, v___x_1417_, v___x_1418_, v___x_1419_, v___f_1416_, v_cleanupAnnotations_1406_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
lean_dec_ref_known(v___x_1419_, 1);
if (lean_obj_tag(v___x_1420_) == 0)
{
return v___x_1420_;
}
else
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1423_ = v___x_1420_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1420_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1424_ == 0)
{
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1421_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___boxed(lean_object* v_e_1429_, lean_object* v_maxFVars_1430_, lean_object* v_k_1431_, lean_object* v_cleanupAnnotations_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1442_; lean_object* v_res_1443_; 
v_cleanupAnnotations_boxed_1442_ = lean_unbox(v_cleanupAnnotations_1432_);
v_res_1443_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(v_e_1429_, v_maxFVars_1430_, v_k_1431_, v_cleanupAnnotations_boxed_1442_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec(v___y_1434_);
lean_dec(v___y_1433_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0(lean_object* v_k_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v_b_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v___x_1455_; 
lean_inc(v___y_1453_);
lean_inc_ref(v___y_1452_);
lean_inc(v___y_1451_);
lean_inc_ref(v___y_1450_);
lean_inc(v___y_1448_);
lean_inc_ref(v___y_1447_);
lean_inc(v___y_1446_);
lean_inc(v___y_1445_);
v___x_1455_ = lean_apply_10(v_k_1444_, v_b_1449_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, lean_box(0));
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0___boxed(lean_object* v_k_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v_b_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0(v_k_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v_b_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec(v___y_1458_);
lean_dec(v___y_1457_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(lean_object* v_name_1468_, lean_object* v_type_1469_, lean_object* v_val_1470_, lean_object* v_k_1471_, uint8_t v_nondep_1472_, uint8_t v_kind_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v___f_1483_; lean_object* v___x_1484_; 
lean_inc(v___y_1477_);
lean_inc_ref(v___y_1476_);
lean_inc(v___y_1475_);
lean_inc(v___y_1474_);
v___f_1483_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1483_, 0, v_k_1471_);
lean_closure_set(v___f_1483_, 1, v___y_1474_);
lean_closure_set(v___f_1483_, 2, v___y_1475_);
lean_closure_set(v___f_1483_, 3, v___y_1476_);
lean_closure_set(v___f_1483_, 4, v___y_1477_);
v___x_1484_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1468_, v_type_1469_, v_val_1470_, v___f_1483_, v_nondep_1472_, v_kind_1473_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
if (lean_obj_tag(v___x_1484_) == 0)
{
return v___x_1484_;
}
else
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v___x_1484_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1484_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1485_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg___boxed(lean_object* v_name_1493_, lean_object* v_type_1494_, lean_object* v_val_1495_, lean_object* v_k_1496_, lean_object* v_nondep_1497_, lean_object* v_kind_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
uint8_t v_nondep_boxed_1508_; uint8_t v_kind_boxed_1509_; lean_object* v_res_1510_; 
v_nondep_boxed_1508_ = lean_unbox(v_nondep_1497_);
v_kind_boxed_1509_ = lean_unbox(v_kind_1498_);
v_res_1510_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(v_name_1493_, v_type_1494_, v_val_1495_, v_k_1496_, v_nondep_boxed_1508_, v_kind_boxed_1509_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v___y_1500_);
lean_dec(v___y_1499_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0(lean_object* v_k_1511_, uint8_t v_usedLetOnly_1512_, lean_object* v_x_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v___x_1523_; 
lean_inc(v___y_1521_);
lean_inc_ref(v___y_1520_);
lean_inc(v___y_1519_);
lean_inc_ref(v___y_1518_);
lean_inc(v___y_1517_);
lean_inc_ref(v___y_1516_);
lean_inc(v___y_1515_);
lean_inc(v___y_1514_);
lean_inc_ref(v_x_1513_);
v___x_1523_ = lean_apply_10(v_k_1511_, v_x_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, lean_box(0));
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_a_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; uint8_t v___x_1528_; uint8_t v___x_1529_; lean_object* v___x_1530_; 
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_a_1524_);
lean_dec_ref_known(v___x_1523_, 1);
v___x_1525_ = lean_unsigned_to_nat(1u);
v___x_1526_ = lean_mk_empty_array_with_capacity(v___x_1525_);
v___x_1527_ = lean_array_push(v___x_1526_, v_x_1513_);
v___x_1528_ = 0;
v___x_1529_ = 1;
v___x_1530_ = l_Lean_Meta_mkLetFVars(v___x_1527_, v_a_1524_, v_usedLetOnly_1512_, v___x_1528_, v___x_1529_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
lean_dec_ref(v___x_1527_);
return v___x_1530_;
}
else
{
lean_dec_ref(v_x_1513_);
return v___x_1523_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0___boxed(lean_object* v_k_1531_, lean_object* v_usedLetOnly_1532_, lean_object* v_x_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
uint8_t v_usedLetOnly_boxed_1543_; lean_object* v_res_1544_; 
v_usedLetOnly_boxed_1543_ = lean_unbox(v_usedLetOnly_1532_);
v_res_1544_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0(v_k_1531_, v_usedLetOnly_boxed_1543_, v_x_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec(v___y_1534_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(lean_object* v_name_1545_, lean_object* v_type_1546_, lean_object* v_val_1547_, lean_object* v_k_1548_, uint8_t v_nondep_1549_, uint8_t v_kind_1550_, uint8_t v_usedLetOnly_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_){
_start:
{
lean_object* v___x_1561_; lean_object* v___f_1562_; lean_object* v___x_1563_; 
v___x_1561_ = lean_box(v_usedLetOnly_1551_);
v___f_1562_ = lean_alloc_closure((void*)(l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0___boxed), 12, 2);
lean_closure_set(v___f_1562_, 0, v_k_1548_);
lean_closure_set(v___f_1562_, 1, v___x_1561_);
v___x_1563_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(v_name_1545_, v_type_1546_, v_val_1547_, v___f_1562_, v_nondep_1549_, v_kind_1550_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___boxed(lean_object* v_name_1564_, lean_object* v_type_1565_, lean_object* v_val_1566_, lean_object* v_k_1567_, lean_object* v_nondep_1568_, lean_object* v_kind_1569_, lean_object* v_usedLetOnly_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
uint8_t v_nondep_boxed_1580_; uint8_t v_kind_boxed_1581_; uint8_t v_usedLetOnly_boxed_1582_; lean_object* v_res_1583_; 
v_nondep_boxed_1580_ = lean_unbox(v_nondep_1568_);
v_kind_boxed_1581_ = lean_unbox(v_kind_1569_);
v_usedLetOnly_boxed_1582_ = lean_unbox(v_usedLetOnly_1570_);
v_res_1583_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(v_name_1564_, v_type_1565_, v_val_1566_, v_k_1567_, v_nondep_boxed_1580_, v_kind_boxed_1581_, v_usedLetOnly_boxed_1582_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
lean_dec(v___y_1572_);
lean_dec(v___y_1571_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(lean_object* v_name_1584_, uint8_t v_bi_1585_, lean_object* v_type_1586_, lean_object* v_k_1587_, uint8_t v_kind_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v___f_1598_; lean_object* v___x_1599_; 
lean_inc(v___y_1592_);
lean_inc_ref(v___y_1591_);
lean_inc(v___y_1590_);
lean_inc(v___y_1589_);
v___f_1598_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1598_, 0, v_k_1587_);
lean_closure_set(v___f_1598_, 1, v___y_1589_);
lean_closure_set(v___f_1598_, 2, v___y_1590_);
lean_closure_set(v___f_1598_, 3, v___y_1591_);
lean_closure_set(v___f_1598_, 4, v___y_1592_);
v___x_1599_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1584_, v_bi_1585_, v_type_1586_, v___f_1598_, v_kind_1588_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
if (lean_obj_tag(v___x_1599_) == 0)
{
return v___x_1599_;
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
v_a_1600_ = lean_ctor_get(v___x_1599_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1599_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1599_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___boxed(lean_object* v_name_1608_, lean_object* v_bi_1609_, lean_object* v_type_1610_, lean_object* v_k_1611_, lean_object* v_kind_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
uint8_t v_bi_boxed_1622_; uint8_t v_kind_boxed_1623_; lean_object* v_res_1624_; 
v_bi_boxed_1622_ = lean_unbox(v_bi_1609_);
v_kind_boxed_1623_ = lean_unbox(v_kind_1612_);
v_res_1624_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_name_1608_, v_bi_boxed_1622_, v_type_1610_, v_k_1611_, v_kind_boxed_1623_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec(v___y_1613_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0(lean_object* v_k_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v___x_1635_; 
lean_inc(v___y_1629_);
lean_inc_ref(v___y_1628_);
lean_inc(v___y_1627_);
lean_inc(v___y_1626_);
v___x_1635_ = lean_apply_9(v_k_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, lean_box(0));
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0___boxed(lean_object* v_k_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0(v_k_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec(v___y_1638_);
lean_dec(v___y_1637_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(lean_object* v_k_1647_, uint8_t v_allowLevelAssignments_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v___f_1658_; lean_object* v___x_1659_; 
lean_inc(v___y_1652_);
lean_inc_ref(v___y_1651_);
lean_inc(v___y_1650_);
lean_inc(v___y_1649_);
v___f_1658_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1658_, 0, v_k_1647_);
lean_closure_set(v___f_1658_, 1, v___y_1649_);
lean_closure_set(v___f_1658_, 2, v___y_1650_);
lean_closure_set(v___f_1658_, 3, v___y_1651_);
lean_closure_set(v___f_1658_, 4, v___y_1652_);
v___x_1659_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1648_, v___f_1658_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
if (lean_obj_tag(v___x_1659_) == 0)
{
return v___x_1659_;
}
else
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1659_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1659_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___boxed(lean_object* v_k_1668_, lean_object* v_allowLevelAssignments_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1679_; lean_object* v_res_1680_; 
v_allowLevelAssignments_boxed_1679_ = lean_unbox(v_allowLevelAssignments_1669_);
v_res_1680_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v_k_1668_, v_allowLevelAssignments_boxed_1679_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec(v___y_1670_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(lean_object* v_a_1681_, lean_object* v_x_1682_){
_start:
{
if (lean_obj_tag(v_x_1682_) == 0)
{
lean_object* v___x_1683_; 
v___x_1683_ = lean_box(0);
return v___x_1683_;
}
else
{
lean_object* v_key_1684_; lean_object* v_value_1685_; lean_object* v_tail_1686_; uint8_t v___x_1687_; 
v_key_1684_ = lean_ctor_get(v_x_1682_, 0);
v_value_1685_ = lean_ctor_get(v_x_1682_, 1);
v_tail_1686_ = lean_ctor_get(v_x_1682_, 2);
v___x_1687_ = lean_expr_eqv(v_key_1684_, v_a_1681_);
if (v___x_1687_ == 0)
{
v_x_1682_ = v_tail_1686_;
goto _start;
}
else
{
lean_object* v___x_1689_; 
lean_inc(v_value_1685_);
v___x_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1689_, 0, v_value_1685_);
return v___x_1689_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg___boxed(lean_object* v_a_1690_, lean_object* v_x_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(v_a_1690_, v_x_1691_);
lean_dec(v_x_1691_);
lean_dec_ref(v_a_1690_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(lean_object* v_m_1693_, lean_object* v_a_1694_){
_start:
{
lean_object* v_buckets_1695_; lean_object* v___x_1696_; uint64_t v___x_1697_; uint64_t v___x_1698_; uint64_t v___x_1699_; uint64_t v_fold_1700_; uint64_t v___x_1701_; uint64_t v___x_1702_; uint64_t v___x_1703_; size_t v___x_1704_; size_t v___x_1705_; size_t v___x_1706_; size_t v___x_1707_; size_t v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v_buckets_1695_ = lean_ctor_get(v_m_1693_, 1);
v___x_1696_ = lean_array_get_size(v_buckets_1695_);
v___x_1697_ = l_Lean_Expr_hash(v_a_1694_);
v___x_1698_ = 32ULL;
v___x_1699_ = lean_uint64_shift_right(v___x_1697_, v___x_1698_);
v_fold_1700_ = lean_uint64_xor(v___x_1697_, v___x_1699_);
v___x_1701_ = 16ULL;
v___x_1702_ = lean_uint64_shift_right(v_fold_1700_, v___x_1701_);
v___x_1703_ = lean_uint64_xor(v_fold_1700_, v___x_1702_);
v___x_1704_ = lean_uint64_to_usize(v___x_1703_);
v___x_1705_ = lean_usize_of_nat(v___x_1696_);
v___x_1706_ = ((size_t)1ULL);
v___x_1707_ = lean_usize_sub(v___x_1705_, v___x_1706_);
v___x_1708_ = lean_usize_land(v___x_1704_, v___x_1707_);
v___x_1709_ = lean_array_uget_borrowed(v_buckets_1695_, v___x_1708_);
v___x_1710_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(v_a_1694_, v___x_1709_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg___boxed(lean_object* v_m_1711_, lean_object* v_a_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v_m_1711_, v_a_1712_);
lean_dec_ref(v_a_1712_);
lean_dec_ref(v_m_1711_);
return v_res_1713_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(lean_object* v_opts_1714_, lean_object* v_opt_1715_){
_start:
{
lean_object* v_name_1716_; lean_object* v_defValue_1717_; lean_object* v_map_1718_; lean_object* v___x_1719_; 
v_name_1716_ = lean_ctor_get(v_opt_1715_, 0);
v_defValue_1717_ = lean_ctor_get(v_opt_1715_, 1);
v_map_1718_ = lean_ctor_get(v_opts_1714_, 0);
v___x_1719_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1718_, v_name_1716_);
if (lean_obj_tag(v___x_1719_) == 0)
{
uint8_t v___x_1720_; 
v___x_1720_ = lean_unbox(v_defValue_1717_);
return v___x_1720_;
}
else
{
lean_object* v_val_1721_; 
v_val_1721_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_val_1721_);
lean_dec_ref_known(v___x_1719_, 1);
if (lean_obj_tag(v_val_1721_) == 1)
{
uint8_t v_v_1722_; 
v_v_1722_ = lean_ctor_get_uint8(v_val_1721_, 0);
lean_dec_ref_known(v_val_1721_, 0);
return v_v_1722_;
}
else
{
uint8_t v___x_1723_; 
lean_dec(v_val_1721_);
v___x_1723_ = lean_unbox(v_defValue_1717_);
return v___x_1723_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5___boxed(lean_object* v_opts_1724_, lean_object* v_opt_1725_){
_start:
{
uint8_t v_res_1726_; lean_object* v_r_1727_; 
v_res_1726_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v_opts_1724_, v_opt_1725_);
lean_dec_ref(v_opt_1725_);
lean_dec_ref(v_opts_1724_);
v_r_1727_ = lean_box(v_res_1726_);
return v_r_1727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(lean_object* v_a_1728_, lean_object* v_b_1729_){
_start:
{
lean_object* v_array_1730_; lean_object* v_start_1731_; lean_object* v_stop_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1745_; 
v_array_1730_ = lean_ctor_get(v_a_1728_, 0);
v_start_1731_ = lean_ctor_get(v_a_1728_, 1);
v_stop_1732_ = lean_ctor_get(v_a_1728_, 2);
v_isSharedCheck_1745_ = !lean_is_exclusive(v_a_1728_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1734_ = v_a_1728_;
v_isShared_1735_ = v_isSharedCheck_1745_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_stop_1732_);
lean_inc(v_start_1731_);
lean_inc(v_array_1730_);
lean_dec(v_a_1728_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1745_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
uint8_t v___x_1736_; 
v___x_1736_ = lean_nat_dec_lt(v_start_1731_, v_stop_1732_);
if (v___x_1736_ == 0)
{
lean_del_object(v___x_1734_);
lean_dec(v_stop_1732_);
lean_dec(v_start_1731_);
lean_dec_ref(v_array_1730_);
return v_b_1729_;
}
else
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1740_; 
v___x_1737_ = lean_unsigned_to_nat(1u);
v___x_1738_ = lean_nat_add(v_start_1731_, v___x_1737_);
lean_inc_ref(v_array_1730_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 1, v___x_1738_);
v___x_1740_ = v___x_1734_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_array_1730_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v___x_1738_);
lean_ctor_set(v_reuseFailAlloc_1744_, 2, v_stop_1732_);
v___x_1740_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1741_ = lean_array_fget(v_array_1730_, v_start_1731_);
lean_dec(v_start_1731_);
lean_dec_ref(v_array_1730_);
v___x_1742_ = lean_array_push(v_b_1729_, v___x_1741_);
v_a_1728_ = v___x_1740_;
v_b_1729_ = v___x_1742_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0(lean_object* v_body_1746_, lean_object* v_recFnName_1747_, lean_object* v_fixedPrefixSize_1748_, lean_object* v_F_1749_, lean_object* v_x_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1760_ = lean_expr_instantiate1(v_body_1746_, v_x_1750_);
v___x_1761_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1747_, v_fixedPrefixSize_1748_, v_F_1749_, v___x_1760_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; uint8_t v___x_1766_; uint8_t v___x_1767_; uint8_t v___x_1768_; lean_object* v___x_1769_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_a_1762_);
lean_dec_ref_known(v___x_1761_, 1);
v___x_1763_ = lean_unsigned_to_nat(1u);
v___x_1764_ = lean_mk_empty_array_with_capacity(v___x_1763_);
v___x_1765_ = lean_array_push(v___x_1764_, v_x_1750_);
v___x_1766_ = 0;
v___x_1767_ = 1;
v___x_1768_ = 1;
v___x_1769_ = l_Lean_Meta_mkLambdaFVars(v___x_1765_, v_a_1762_, v___x_1766_, v___x_1767_, v___x_1766_, v___x_1767_, v___x_1768_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
lean_dec_ref(v___x_1765_);
return v___x_1769_;
}
else
{
lean_dec_ref(v_x_1750_);
return v___x_1761_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0___boxed(lean_object* v_body_1770_, lean_object* v_recFnName_1771_, lean_object* v_fixedPrefixSize_1772_, lean_object* v_F_1773_, lean_object* v_x_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0(v_body_1770_, v_recFnName_1771_, v_fixedPrefixSize_1772_, v_F_1773_, v_x_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
lean_dec(v___y_1776_);
lean_dec(v___y_1775_);
lean_dec_ref(v_body_1770_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1(lean_object* v_body_1785_, lean_object* v_recFnName_1786_, lean_object* v_fixedPrefixSize_1787_, lean_object* v_F_1788_, lean_object* v_x_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1799_ = lean_expr_instantiate1(v_body_1785_, v_x_1789_);
v___x_1800_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1786_, v_fixedPrefixSize_1787_, v_F_1788_, v___x_1799_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v_a_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; uint8_t v___x_1805_; uint8_t v___x_1806_; uint8_t v___x_1807_; lean_object* v___x_1808_; 
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
lean_inc(v_a_1801_);
lean_dec_ref_known(v___x_1800_, 1);
v___x_1802_ = lean_unsigned_to_nat(1u);
v___x_1803_ = lean_mk_empty_array_with_capacity(v___x_1802_);
v___x_1804_ = lean_array_push(v___x_1803_, v_x_1789_);
v___x_1805_ = 0;
v___x_1806_ = 1;
v___x_1807_ = 1;
v___x_1808_ = l_Lean_Meta_mkForallFVars(v___x_1804_, v_a_1801_, v___x_1805_, v___x_1806_, v___x_1806_, v___x_1807_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
lean_dec_ref(v___x_1804_);
return v___x_1808_;
}
else
{
lean_dec_ref(v_x_1789_);
return v___x_1800_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1___boxed(lean_object* v_body_1809_, lean_object* v_recFnName_1810_, lean_object* v_fixedPrefixSize_1811_, lean_object* v_F_1812_, lean_object* v_x_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1(v_body_1809_, v_recFnName_1810_, v_fixedPrefixSize_1811_, v_F_1812_, v_x_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v_body_1809_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2___boxed(lean_object* v_body_1824_, lean_object* v_recFnName_1825_, lean_object* v_fixedPrefixSize_1826_, lean_object* v_F_1827_, lean_object* v_x_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2(v_body_1824_, v_recFnName_1825_, v_fixedPrefixSize_1826_, v_F_1827_, v_x_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v_x_1828_);
lean_dec_ref(v_body_1824_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(lean_object* v_recFnName_1841_, lean_object* v_fixedPrefixSize_1842_, lean_object* v_F_1843_, size_t v_sz_1844_, size_t v_i_1845_, lean_object* v_bs_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
uint8_t v___x_1856_; 
v___x_1856_ = lean_usize_dec_lt(v_i_1845_, v_sz_1844_);
if (v___x_1856_ == 0)
{
lean_object* v___x_1857_; 
lean_dec_ref(v_F_1843_);
lean_dec(v_fixedPrefixSize_1842_);
lean_dec(v_recFnName_1841_);
v___x_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1857_, 0, v_bs_1846_);
return v___x_1857_;
}
else
{
lean_object* v_v_1858_; lean_object* v___x_1859_; 
v_v_1858_ = lean_array_uget_borrowed(v_bs_1846_, v_i_1845_);
lean_inc(v_v_1858_);
lean_inc_ref(v_F_1843_);
lean_inc(v_fixedPrefixSize_1842_);
lean_inc(v_recFnName_1841_);
v___x_1859_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1841_, v_fixedPrefixSize_1842_, v_F_1843_, v_v_1858_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_a_1860_; lean_object* v___x_1861_; lean_object* v_bs_x27_1862_; size_t v___x_1863_; size_t v___x_1864_; lean_object* v___x_1865_; 
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
lean_inc(v_a_1860_);
lean_dec_ref_known(v___x_1859_, 1);
v___x_1861_ = lean_unsigned_to_nat(0u);
v_bs_x27_1862_ = lean_array_uset(v_bs_1846_, v_i_1845_, v___x_1861_);
v___x_1863_ = ((size_t)1ULL);
v___x_1864_ = lean_usize_add(v_i_1845_, v___x_1863_);
v___x_1865_ = lean_array_uset(v_bs_x27_1862_, v_i_1845_, v_a_1860_);
v_i_1845_ = v___x_1864_;
v_bs_1846_ = v___x_1865_;
goto _start;
}
else
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1874_; 
lean_dec_ref(v_bs_1846_);
lean_dec_ref(v_F_1843_);
lean_dec(v_fixedPrefixSize_1842_);
lean_dec(v_recFnName_1841_);
v_a_1867_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1869_ = v___x_1859_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1859_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1872_; 
if (v_isShared_1870_ == 0)
{
v___x_1872_ = v___x_1869_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_a_1867_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4(void){
_start:
{
lean_object* v_cls_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v_cls_1882_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_1883_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__3));
v___x_1884_ = l_Lean_Name_append(v___x_1883_, v_cls_1882_);
return v___x_1884_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6(void){
_start:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1886_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5));
v___x_1887_ = l_Lean_stringToMessageData(v___x_1886_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(lean_object* v_recFnName_1888_, lean_object* v_fixedPrefixSize_1889_, lean_object* v_F_1890_, lean_object* v_e_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_){
_start:
{
lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; uint8_t v___x_1916_; 
v___x_1913_ = l_Lean_Expr_getAppNumArgs(v_e_1891_);
v___x_1914_ = lean_unsigned_to_nat(1u);
v___x_1915_ = lean_nat_add(v_fixedPrefixSize_1889_, v___x_1914_);
v___x_1916_ = lean_nat_dec_lt(v___x_1913_, v___x_1915_);
if (v___x_1916_ == 0)
{
lean_object* v___x_1917_; lean_object* v_dummy_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v_args_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1917_ = l_Lean_instInhabitedExpr;
v_dummy_1918_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_1913_);
v___x_1919_ = lean_mk_array(v___x_1913_, v_dummy_1918_);
v___x_1920_ = lean_nat_sub(v___x_1913_, v___x_1914_);
lean_dec(v___x_1913_);
v_args_1921_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1891_, v___x_1919_, v___x_1920_);
v___x_1922_ = lean_array_get(v___x_1917_, v_args_1921_, v_fixedPrefixSize_1889_);
lean_inc_ref(v_F_1890_);
lean_inc(v_fixedPrefixSize_1889_);
lean_inc(v_recFnName_1888_);
v___x_1923_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1888_, v_fixedPrefixSize_1889_, v_F_1890_, v___x_1922_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1924_);
lean_dec_ref_known(v___x_1923_, 1);
lean_inc_ref(v_F_1890_);
v___x_1925_ = l_Lean_Expr_app___override(v_F_1890_, v_a_1924_);
lean_inc(v_a_1899_);
lean_inc_ref(v_a_1898_);
lean_inc(v_a_1897_);
lean_inc_ref(v_a_1896_);
lean_inc_ref(v___x_1925_);
v___x_1926_ = lean_infer_type(v___x_1925_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v_a_1927_; lean_object* v___x_1928_; 
v_a_1927_ = lean_ctor_get(v___x_1926_, 0);
lean_inc(v_a_1927_);
lean_dec_ref_known(v___x_1926_, 1);
lean_inc(v_a_1899_);
lean_inc_ref(v_a_1898_);
lean_inc(v_a_1897_);
lean_inc_ref(v_a_1896_);
v___x_1928_ = lean_whnf(v_a_1927_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_a_1929_);
lean_dec_ref_known(v___x_1928_, 1);
v___x_1930_ = l_Lean_Expr_bindingDomain_x21(v_a_1929_);
lean_dec(v_a_1929_);
v___x_1931_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg(v___x_1930_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_a_1932_; lean_object* v___x_1933_; lean_object* v_lower_1935_; lean_object* v_upper_1936_; lean_object* v___x_1960_; lean_object* v___x_1961_; uint8_t v___x_1962_; 
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1932_);
lean_dec_ref_known(v___x_1931_, 1);
v___x_1933_ = l_Lean_Expr_app___override(v___x_1925_, v_a_1932_);
v___x_1960_ = lean_unsigned_to_nat(0u);
v___x_1961_ = lean_array_get_size(v_args_1921_);
v___x_1962_ = lean_nat_dec_le(v___x_1915_, v___x_1960_);
if (v___x_1962_ == 0)
{
v_lower_1935_ = v___x_1915_;
v_upper_1936_ = v___x_1961_;
goto v___jp_1934_;
}
else
{
lean_dec(v___x_1915_);
v_lower_1935_ = v___x_1960_;
v_upper_1936_ = v___x_1961_;
goto v___jp_1934_;
}
v___jp_1934_:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; size_t v_sz_1940_; size_t v___x_1941_; lean_object* v___x_1942_; 
v___x_1937_ = l_Array_toSubarray___redArg(v_args_1921_, v_lower_1935_, v_upper_1936_);
v___x_1938_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
v___x_1939_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(v___x_1937_, v___x_1938_);
v_sz_1940_ = lean_array_size(v___x_1939_);
v___x_1941_ = ((size_t)0ULL);
v___x_1942_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_1888_, v_fixedPrefixSize_1889_, v_F_1890_, v_sz_1940_, v___x_1941_, v___x_1939_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1951_; 
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1945_ = v___x_1942_;
v_isShared_1946_ = v_isSharedCheck_1951_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1942_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1951_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1947_; lean_object* v___x_1949_; 
v___x_1947_ = l_Lean_mkAppN(v___x_1933_, v_a_1943_);
lean_dec(v_a_1943_);
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 0, v___x_1947_);
v___x_1949_ = v___x_1945_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1947_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
lean_dec_ref(v___x_1933_);
v_a_1952_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1942_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1942_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1925_);
lean_dec_ref(v_args_1921_);
lean_dec(v___x_1915_);
lean_dec_ref(v_F_1890_);
lean_dec(v_fixedPrefixSize_1889_);
lean_dec(v_recFnName_1888_);
return v___x_1931_;
}
}
else
{
lean_dec_ref(v___x_1925_);
lean_dec_ref(v_args_1921_);
lean_dec(v___x_1915_);
lean_dec_ref(v_F_1890_);
lean_dec(v_fixedPrefixSize_1889_);
lean_dec(v_recFnName_1888_);
return v___x_1928_;
}
}
else
{
lean_dec_ref(v___x_1925_);
lean_dec_ref(v_args_1921_);
lean_dec(v___x_1915_);
lean_dec_ref(v_F_1890_);
lean_dec(v_fixedPrefixSize_1889_);
lean_dec(v_recFnName_1888_);
return v___x_1926_;
}
}
else
{
lean_dec_ref(v_args_1921_);
lean_dec(v___x_1915_);
lean_dec_ref(v_F_1890_);
lean_dec(v_fixedPrefixSize_1889_);
lean_dec(v_recFnName_1888_);
return v___x_1923_;
}
}
else
{
lean_object* v_options_1963_; uint8_t v_hasTrace_1964_; 
lean_dec(v___x_1915_);
lean_dec(v___x_1913_);
v_options_1963_ = lean_ctor_get(v_a_1898_, 2);
v_hasTrace_1964_ = lean_ctor_get_uint8(v_options_1963_, sizeof(void*)*1);
if (v_hasTrace_1964_ == 0)
{
v___y_1902_ = v_a_1892_;
v___y_1903_ = v_a_1893_;
v___y_1904_ = v_a_1894_;
v___y_1905_ = v_a_1895_;
v___y_1906_ = v_a_1896_;
v___y_1907_ = v_a_1897_;
v___y_1908_ = v_a_1898_;
v___y_1909_ = v_a_1899_;
goto v___jp_1901_;
}
else
{
lean_object* v_inheritedTraceOptions_1965_; lean_object* v_cls_1966_; lean_object* v___x_1967_; uint8_t v___x_1968_; 
v_inheritedTraceOptions_1965_ = lean_ctor_get(v_a_1898_, 13);
v_cls_1966_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_1967_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_1968_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1965_, v_options_1963_, v___x_1967_);
if (v___x_1968_ == 0)
{
v___y_1902_ = v_a_1892_;
v___y_1903_ = v_a_1893_;
v___y_1904_ = v_a_1894_;
v___y_1905_ = v_a_1895_;
v___y_1906_ = v_a_1896_;
v___y_1907_ = v_a_1897_;
v___y_1908_ = v_a_1898_;
v___y_1909_ = v_a_1899_;
goto v___jp_1901_;
}
else
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1969_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6);
lean_inc_ref(v_e_1891_);
v___x_1970_ = l_Lean_indentExpr(v_e_1891_);
v___x_1971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1969_);
lean_ctor_set(v___x_1971_, 1, v___x_1970_);
v___x_1972_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(v_cls_1966_, v___x_1971_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_dec_ref_known(v___x_1972_, 1);
v___y_1902_ = v_a_1892_;
v___y_1903_ = v_a_1893_;
v___y_1904_ = v_a_1894_;
v___y_1905_ = v_a_1895_;
v___y_1906_ = v_a_1896_;
v___y_1907_ = v_a_1897_;
v___y_1908_ = v_a_1898_;
v___y_1909_ = v_a_1899_;
goto v___jp_1901_;
}
else
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1980_; 
lean_dec_ref(v_e_1891_);
lean_dec_ref(v_F_1890_);
lean_dec(v_fixedPrefixSize_1889_);
lean_dec(v_recFnName_1888_);
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1975_ = v___x_1972_;
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1972_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_a_1973_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
}
}
v___jp_1901_:
{
lean_object* v___x_1910_; 
v___x_1910_ = l_Lean_Meta_etaExpand(v_e_1891_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_a_1911_; lean_object* v___x_1912_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
lean_inc(v_a_1911_);
lean_dec_ref_known(v___x_1910_, 1);
v___x_1912_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1888_, v_fixedPrefixSize_1889_, v_F_1890_, v_a_1911_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
return v___x_1912_;
}
else
{
lean_dec_ref(v_F_1890_);
lean_dec(v_fixedPrefixSize_1889_);
lean_dec(v_recFnName_1888_);
return v___x_1910_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(lean_object* v_recFnName_1981_, lean_object* v_fixedPrefixSize_1982_, lean_object* v_F_1983_, lean_object* v_x_1984_, lean_object* v_x_1985_, lean_object* v_x_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
if (lean_obj_tag(v_x_1984_) == 5)
{
lean_object* v_fn_1996_; lean_object* v_arg_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v_fn_1996_ = lean_ctor_get(v_x_1984_, 0);
lean_inc_ref(v_fn_1996_);
v_arg_1997_ = lean_ctor_get(v_x_1984_, 1);
lean_inc_ref(v_arg_1997_);
lean_dec_ref_known(v_x_1984_, 2);
v___x_1998_ = lean_array_set(v_x_1985_, v_x_1986_, v_arg_1997_);
v___x_1999_ = lean_unsigned_to_nat(1u);
v___x_2000_ = lean_nat_sub(v_x_1986_, v___x_1999_);
lean_dec(v_x_1986_);
v_x_1984_ = v_fn_1996_;
v_x_1985_ = v___x_1998_;
v_x_1986_ = v___x_2000_;
goto _start;
}
else
{
lean_object* v___x_2002_; 
lean_dec(v_x_1986_);
lean_inc_ref(v_F_1983_);
lean_inc(v_fixedPrefixSize_1982_);
lean_inc(v_recFnName_1981_);
v___x_2002_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1981_, v_fixedPrefixSize_1982_, v_F_1983_, v_x_1984_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; size_t v_sz_2004_; size_t v___x_2005_; lean_object* v___x_2006_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_a_2003_);
lean_dec_ref_known(v___x_2002_, 1);
v_sz_2004_ = lean_array_size(v_x_1985_);
v___x_2005_ = ((size_t)0ULL);
v___x_2006_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_1981_, v_fixedPrefixSize_1982_, v_F_1983_, v_sz_2004_, v___x_2005_, v_x_1985_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2015_; 
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2009_ = v___x_2006_;
v_isShared_2010_ = v_isSharedCheck_2015_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v___x_2006_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2015_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2011_; lean_object* v___x_2013_; 
v___x_2011_ = l_Lean_mkAppN(v_a_2003_, v_a_2007_);
lean_dec(v_a_2007_);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 0, v___x_2011_);
v___x_2013_ = v___x_2009_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2011_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
lean_dec(v_a_2003_);
v_a_2016_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_2006_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_2006_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
else
{
lean_dec_ref(v_x_1985_);
lean_dec_ref(v_F_1983_);
lean_dec(v_fixedPrefixSize_1982_);
lean_dec(v_recFnName_1981_);
return v___x_2002_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(lean_object* v_recFnName_2024_, lean_object* v_fixedPrefixSize_2025_, lean_object* v_F_2026_, lean_object* v_e_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_){
_start:
{
uint8_t v___x_2037_; 
v___x_2037_ = l_Lean_Expr_isAppOf(v_e_2027_, v_recFnName_2024_);
if (v___x_2037_ == 0)
{
lean_object* v_dummy_2038_; lean_object* v_nargs_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v_dummy_2038_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
v_nargs_2039_ = l_Lean_Expr_getAppNumArgs(v_e_2027_);
lean_inc(v_nargs_2039_);
v___x_2040_ = lean_mk_array(v_nargs_2039_, v_dummy_2038_);
v___x_2041_ = lean_unsigned_to_nat(1u);
v___x_2042_ = lean_nat_sub(v_nargs_2039_, v___x_2041_);
lean_dec(v_nargs_2039_);
v___x_2043_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(v_recFnName_2024_, v_fixedPrefixSize_2025_, v_F_2026_, v_e_2027_, v___x_2040_, v___x_2042_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_);
return v___x_2043_;
}
else
{
lean_object* v___x_2044_; 
v___x_2044_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2024_, v_fixedPrefixSize_2025_, v_F_2026_, v_e_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_);
return v___x_2044_;
}
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__0));
v___x_2047_ = l_Lean_stringToMessageData(v___x_2046_);
return v___x_2047_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2049_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__2));
v___x_2050_ = l_Lean_stringToMessageData(v___x_2049_);
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0(lean_object* v___x_2051_, lean_object* v_b_2052_, lean_object* v_recFnName_2053_, lean_object* v_fixedPrefixSize_2054_, uint8_t v___x_2055_, lean_object* v___x_2056_, lean_object* v_a_2057_, lean_object* v_e_2058_, lean_object* v_xs_2059_, lean_object* v_altBody_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_){
_start:
{
lean_object* v___x_2077_; uint8_t v___x_2078_; 
v___x_2077_ = lean_array_get_size(v_xs_2059_);
v___x_2078_ = lean_nat_dec_eq(v___x_2077_, v___x_2056_);
if (v___x_2078_ == 0)
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
lean_dec_ref(v_altBody_2060_);
lean_dec(v_fixedPrefixSize_2054_);
lean_dec(v_recFnName_2053_);
v___x_2079_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1);
v___x_2080_ = l_Lean_indentExpr(v_a_2057_);
v___x_2081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2079_);
lean_ctor_set(v___x_2081_, 1, v___x_2080_);
v___x_2082_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3);
v___x_2083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2081_);
lean_ctor_set(v___x_2083_, 1, v___x_2082_);
v___x_2084_ = l_Lean_indentExpr(v_e_2058_);
v___x_2085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2083_);
lean_ctor_set(v___x_2085_, 1, v___x_2084_);
v___x_2086_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v___x_2085_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2086_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2086_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
else
{
lean_dec_ref(v_e_2058_);
lean_dec_ref(v_a_2057_);
goto v___jp_2070_;
}
v___jp_2070_:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2071_ = lean_array_get_borrowed(v___x_2051_, v_xs_2059_, v_b_2052_);
lean_inc(v___x_2071_);
v___x_2072_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2053_, v_fixedPrefixSize_2054_, v___x_2071_, v_altBody_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v_a_2073_; uint8_t v___x_2074_; uint8_t v___x_2075_; lean_object* v___x_2076_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
lean_inc(v_a_2073_);
lean_dec_ref_known(v___x_2072_, 1);
v___x_2074_ = 0;
v___x_2075_ = 1;
v___x_2076_ = l_Lean_Meta_mkLambdaFVars(v_xs_2059_, v_a_2073_, v___x_2074_, v___x_2055_, v___x_2074_, v___x_2055_, v___x_2075_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
return v___x_2076_;
}
else
{
return v___x_2072_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___boxed(lean_object** _args){
lean_object* v___x_2095_ = _args[0];
lean_object* v_b_2096_ = _args[1];
lean_object* v_recFnName_2097_ = _args[2];
lean_object* v_fixedPrefixSize_2098_ = _args[3];
lean_object* v___x_2099_ = _args[4];
lean_object* v___x_2100_ = _args[5];
lean_object* v_a_2101_ = _args[6];
lean_object* v_e_2102_ = _args[7];
lean_object* v_xs_2103_ = _args[8];
lean_object* v_altBody_2104_ = _args[9];
lean_object* v___y_2105_ = _args[10];
lean_object* v___y_2106_ = _args[11];
lean_object* v___y_2107_ = _args[12];
lean_object* v___y_2108_ = _args[13];
lean_object* v___y_2109_ = _args[14];
lean_object* v___y_2110_ = _args[15];
lean_object* v___y_2111_ = _args[16];
lean_object* v___y_2112_ = _args[17];
lean_object* v___y_2113_ = _args[18];
_start:
{
uint8_t v___x_57933__boxed_2114_; lean_object* v_res_2115_; 
v___x_57933__boxed_2114_ = lean_unbox(v___x_2099_);
v_res_2115_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0(v___x_2095_, v_b_2096_, v_recFnName_2097_, v_fixedPrefixSize_2098_, v___x_57933__boxed_2114_, v___x_2100_, v_a_2101_, v_e_2102_, v_xs_2103_, v_altBody_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec(v___y_2106_);
lean_dec(v___y_2105_);
lean_dec_ref(v_xs_2103_);
lean_dec(v___x_2100_);
lean_dec(v_b_2096_);
lean_dec_ref(v___x_2095_);
return v_res_2115_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(lean_object* v_recFnName_2116_, lean_object* v_fixedPrefixSize_2117_, lean_object* v_e_2118_, lean_object* v_as_2119_, lean_object* v_bs_2120_, lean_object* v_i_2121_, lean_object* v_cs_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v___x_2132_; uint8_t v___x_2133_; 
v___x_2132_ = lean_array_get_size(v_as_2119_);
v___x_2133_ = lean_nat_dec_lt(v_i_2121_, v___x_2132_);
if (v___x_2133_ == 0)
{
lean_object* v___x_2134_; 
lean_dec(v_i_2121_);
lean_dec_ref(v_e_2118_);
lean_dec(v_fixedPrefixSize_2117_);
lean_dec(v_recFnName_2116_);
v___x_2134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2134_, 0, v_cs_2122_);
return v___x_2134_;
}
else
{
lean_object* v___x_2135_; uint8_t v___x_2136_; 
v___x_2135_ = lean_array_get_size(v_bs_2120_);
v___x_2136_ = lean_nat_dec_lt(v_i_2121_, v___x_2135_);
if (v___x_2136_ == 0)
{
lean_object* v___x_2137_; 
lean_dec(v_i_2121_);
lean_dec_ref(v_e_2118_);
lean_dec(v_fixedPrefixSize_2117_);
lean_dec(v_recFnName_2116_);
v___x_2137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2137_, 0, v_cs_2122_);
return v___x_2137_;
}
else
{
lean_object* v___x_2138_; lean_object* v_a_2139_; lean_object* v_b_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___f_2144_; uint8_t v___x_2145_; lean_object* v___x_2146_; 
v___x_2138_ = l_Lean_instInhabitedExpr;
v_a_2139_ = lean_array_fget_borrowed(v_as_2119_, v_i_2121_);
v_b_2140_ = lean_array_fget_borrowed(v_bs_2120_, v_i_2121_);
v___x_2141_ = lean_unsigned_to_nat(1u);
v___x_2142_ = lean_nat_add(v_b_2140_, v___x_2141_);
v___x_2143_ = lean_box(v___x_2136_);
lean_inc_ref(v_e_2118_);
lean_inc_n(v_a_2139_, 2);
lean_inc(v___x_2142_);
lean_inc(v_fixedPrefixSize_2117_);
lean_inc(v_recFnName_2116_);
lean_inc(v_b_2140_);
v___f_2144_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___boxed), 19, 8);
lean_closure_set(v___f_2144_, 0, v___x_2138_);
lean_closure_set(v___f_2144_, 1, v_b_2140_);
lean_closure_set(v___f_2144_, 2, v_recFnName_2116_);
lean_closure_set(v___f_2144_, 3, v_fixedPrefixSize_2117_);
lean_closure_set(v___f_2144_, 4, v___x_2143_);
lean_closure_set(v___f_2144_, 5, v___x_2142_);
lean_closure_set(v___f_2144_, 6, v_a_2139_);
lean_closure_set(v___f_2144_, 7, v_e_2118_);
v___x_2145_ = 0;
v___x_2146_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(v_a_2139_, v___x_2142_, v___f_2144_, v___x_2145_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_a_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc(v_a_2147_);
lean_dec_ref_known(v___x_2146_, 1);
v___x_2148_ = lean_nat_add(v_i_2121_, v___x_2141_);
lean_dec(v_i_2121_);
v___x_2149_ = lean_array_push(v_cs_2122_, v_a_2147_);
v_i_2121_ = v___x_2148_;
v_cs_2122_ = v___x_2149_;
goto _start;
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
lean_dec_ref(v_cs_2122_);
lean_dec(v_i_2121_);
lean_dec_ref(v_e_2118_);
lean_dec(v_fixedPrefixSize_2117_);
lean_dec(v_recFnName_2116_);
v_a_2151_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2146_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2146_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(lean_object* v_recFnName_2159_, lean_object* v_fixedPrefixSize_2160_, lean_object* v_F_2161_, lean_object* v_e_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_){
_start:
{
switch(lean_obj_tag(v_e_2162_))
{
case 6:
{
lean_object* v_binderName_2172_; lean_object* v_binderType_2173_; lean_object* v_body_2174_; uint8_t v_binderInfo_2175_; lean_object* v___x_2176_; 
v_binderName_2172_ = lean_ctor_get(v_e_2162_, 0);
lean_inc(v_binderName_2172_);
v_binderType_2173_ = lean_ctor_get(v_e_2162_, 1);
lean_inc_ref(v_binderType_2173_);
v_body_2174_ = lean_ctor_get(v_e_2162_, 2);
lean_inc_ref(v_body_2174_);
v_binderInfo_2175_ = lean_ctor_get_uint8(v_e_2162_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2162_, 3);
lean_inc_ref(v_F_2161_);
lean_inc(v_fixedPrefixSize_2160_);
lean_inc(v_recFnName_2159_);
v___x_2176_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2159_, v_fixedPrefixSize_2160_, v_F_2161_, v_binderType_2173_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; lean_object* v___f_2178_; uint8_t v___x_2179_; lean_object* v___x_2180_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_a_2177_);
lean_dec_ref_known(v___x_2176_, 1);
v___f_2178_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0___boxed), 14, 4);
lean_closure_set(v___f_2178_, 0, v_body_2174_);
lean_closure_set(v___f_2178_, 1, v_recFnName_2159_);
lean_closure_set(v___f_2178_, 2, v_fixedPrefixSize_2160_);
lean_closure_set(v___f_2178_, 3, v_F_2161_);
v___x_2179_ = 0;
v___x_2180_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_binderName_2172_, v_binderInfo_2175_, v_a_2177_, v___f_2178_, v___x_2179_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_);
return v___x_2180_;
}
else
{
lean_dec_ref(v_body_2174_);
lean_dec(v_binderName_2172_);
lean_dec_ref(v_F_2161_);
lean_dec(v_fixedPrefixSize_2160_);
lean_dec(v_recFnName_2159_);
return v___x_2176_;
}
}
case 7:
{
lean_object* v_binderName_2181_; lean_object* v_binderType_2182_; lean_object* v_body_2183_; uint8_t v_binderInfo_2184_; lean_object* v___x_2185_; 
v_binderName_2181_ = lean_ctor_get(v_e_2162_, 0);
lean_inc(v_binderName_2181_);
v_binderType_2182_ = lean_ctor_get(v_e_2162_, 1);
lean_inc_ref(v_binderType_2182_);
v_body_2183_ = lean_ctor_get(v_e_2162_, 2);
lean_inc_ref(v_body_2183_);
v_binderInfo_2184_ = lean_ctor_get_uint8(v_e_2162_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2162_, 3);
lean_inc_ref(v_F_2161_);
lean_inc(v_fixedPrefixSize_2160_);
lean_inc(v_recFnName_2159_);
v___x_2185_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2159_, v_fixedPrefixSize_2160_, v_F_2161_, v_binderType_2182_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v_a_2186_; lean_object* v___f_2187_; uint8_t v___x_2188_; lean_object* v___x_2189_; 
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
lean_inc(v_a_2186_);
lean_dec_ref_known(v___x_2185_, 1);
v___f_2187_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1___boxed), 14, 4);
lean_closure_set(v___f_2187_, 0, v_body_2183_);
lean_closure_set(v___f_2187_, 1, v_recFnName_2159_);
lean_closure_set(v___f_2187_, 2, v_fixedPrefixSize_2160_);
lean_closure_set(v___f_2187_, 3, v_F_2161_);
v___x_2188_ = 0;
v___x_2189_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_binderName_2181_, v_binderInfo_2184_, v_a_2186_, v___f_2187_, v___x_2188_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_);
return v___x_2189_;
}
else
{
lean_dec_ref(v_body_2183_);
lean_dec(v_binderName_2181_);
lean_dec_ref(v_F_2161_);
lean_dec(v_fixedPrefixSize_2160_);
lean_dec(v_recFnName_2159_);
return v___x_2185_;
}
}
case 8:
{
lean_object* v_declName_2190_; lean_object* v_type_2191_; lean_object* v_value_2192_; lean_object* v_body_2193_; uint8_t v_nondep_2194_; lean_object* v___x_2195_; 
v_declName_2190_ = lean_ctor_get(v_e_2162_, 0);
lean_inc(v_declName_2190_);
v_type_2191_ = lean_ctor_get(v_e_2162_, 1);
lean_inc_ref(v_type_2191_);
v_value_2192_ = lean_ctor_get(v_e_2162_, 2);
lean_inc_ref(v_value_2192_);
v_body_2193_ = lean_ctor_get(v_e_2162_, 3);
lean_inc_ref(v_body_2193_);
v_nondep_2194_ = lean_ctor_get_uint8(v_e_2162_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2162_, 4);
lean_inc_ref(v_F_2161_);
lean_inc(v_fixedPrefixSize_2160_);
lean_inc(v_recFnName_2159_);
v___x_2195_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2159_, v_fixedPrefixSize_2160_, v_F_2161_, v_type_2191_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2196_; lean_object* v___x_2197_; 
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_a_2196_);
lean_dec_ref_known(v___x_2195_, 1);
lean_inc_ref(v_F_2161_);
lean_inc(v_fixedPrefixSize_2160_);
lean_inc(v_recFnName_2159_);
v___x_2197_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2159_, v_fixedPrefixSize_2160_, v_F_2161_, v_value_2192_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v_a_2198_; lean_object* v___f_2199_; uint8_t v___x_2200_; uint8_t v___x_2201_; lean_object* v___x_2202_; 
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
lean_inc(v_a_2198_);
lean_dec_ref_known(v___x_2197_, 1);
v___f_2199_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2___boxed), 14, 4);
lean_closure_set(v___f_2199_, 0, v_body_2193_);
lean_closure_set(v___f_2199_, 1, v_recFnName_2159_);
lean_closure_set(v___f_2199_, 2, v_fixedPrefixSize_2160_);
lean_closure_set(v___f_2199_, 3, v_F_2161_);
v___x_2200_ = 0;
v___x_2201_ = 0;
v___x_2202_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(v_declName_2190_, v_a_2196_, v_a_2198_, v___f_2199_, v_nondep_2194_, v___x_2200_, v___x_2201_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_);
return v___x_2202_;
}
else
{
lean_dec(v_a_2196_);
lean_dec_ref(v_body_2193_);
lean_dec(v_declName_2190_);
lean_dec_ref(v_F_2161_);
lean_dec(v_fixedPrefixSize_2160_);
lean_dec(v_recFnName_2159_);
return v___x_2197_;
}
}
else
{
lean_dec_ref(v_body_2193_);
lean_dec_ref(v_value_2192_);
lean_dec(v_declName_2190_);
lean_dec_ref(v_F_2161_);
lean_dec(v_fixedPrefixSize_2160_);
lean_dec(v_recFnName_2159_);
return v___x_2195_;
}
}
case 10:
{
lean_object* v_data_2203_; lean_object* v_expr_2204_; lean_object* v___x_2205_; 
v_data_2203_ = lean_ctor_get(v_e_2162_, 0);
lean_inc(v_data_2203_);
v_expr_2204_ = lean_ctor_get(v_e_2162_, 1);
lean_inc_ref(v_expr_2204_);
v___x_2205_ = l_Lean_getRecAppSyntax_x3f(v_e_2162_);
lean_dec_ref_known(v_e_2162_, 2);
if (lean_obj_tag(v___x_2205_) == 1)
{
lean_object* v_val_2206_; lean_object* v_fileName_2207_; lean_object* v_fileMap_2208_; lean_object* v_options_2209_; lean_object* v_currRecDepth_2210_; lean_object* v_maxRecDepth_2211_; lean_object* v_ref_2212_; lean_object* v_currNamespace_2213_; lean_object* v_openDecls_2214_; lean_object* v_initHeartbeats_2215_; lean_object* v_maxHeartbeats_2216_; lean_object* v_quotContext_2217_; lean_object* v_currMacroScope_2218_; uint8_t v_diag_2219_; lean_object* v_cancelTk_x3f_2220_; uint8_t v_suppressElabErrors_2221_; lean_object* v_inheritedTraceOptions_2222_; lean_object* v_ref_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
lean_dec(v_data_2203_);
v_val_2206_ = lean_ctor_get(v___x_2205_, 0);
lean_inc(v_val_2206_);
lean_dec_ref_known(v___x_2205_, 1);
v_fileName_2207_ = lean_ctor_get(v_a_2169_, 0);
v_fileMap_2208_ = lean_ctor_get(v_a_2169_, 1);
v_options_2209_ = lean_ctor_get(v_a_2169_, 2);
v_currRecDepth_2210_ = lean_ctor_get(v_a_2169_, 3);
v_maxRecDepth_2211_ = lean_ctor_get(v_a_2169_, 4);
v_ref_2212_ = lean_ctor_get(v_a_2169_, 5);
v_currNamespace_2213_ = lean_ctor_get(v_a_2169_, 6);
v_openDecls_2214_ = lean_ctor_get(v_a_2169_, 7);
v_initHeartbeats_2215_ = lean_ctor_get(v_a_2169_, 8);
v_maxHeartbeats_2216_ = lean_ctor_get(v_a_2169_, 9);
v_quotContext_2217_ = lean_ctor_get(v_a_2169_, 10);
v_currMacroScope_2218_ = lean_ctor_get(v_a_2169_, 11);
v_diag_2219_ = lean_ctor_get_uint8(v_a_2169_, sizeof(void*)*14);
v_cancelTk_x3f_2220_ = lean_ctor_get(v_a_2169_, 12);
v_suppressElabErrors_2221_ = lean_ctor_get_uint8(v_a_2169_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2222_ = lean_ctor_get(v_a_2169_, 13);
v_ref_2223_ = l_Lean_replaceRef(v_val_2206_, v_ref_2212_);
lean_dec(v_val_2206_);
lean_inc_ref(v_inheritedTraceOptions_2222_);
lean_inc(v_cancelTk_x3f_2220_);
lean_inc(v_currMacroScope_2218_);
lean_inc(v_quotContext_2217_);
lean_inc(v_maxHeartbeats_2216_);
lean_inc(v_initHeartbeats_2215_);
lean_inc(v_openDecls_2214_);
lean_inc(v_currNamespace_2213_);
lean_inc(v_maxRecDepth_2211_);
lean_inc(v_currRecDepth_2210_);
lean_inc_ref(v_options_2209_);
lean_inc_ref(v_fileMap_2208_);
lean_inc_ref(v_fileName_2207_);
v___x_2224_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2224_, 0, v_fileName_2207_);
lean_ctor_set(v___x_2224_, 1, v_fileMap_2208_);
lean_ctor_set(v___x_2224_, 2, v_options_2209_);
lean_ctor_set(v___x_2224_, 3, v_currRecDepth_2210_);
lean_ctor_set(v___x_2224_, 4, v_maxRecDepth_2211_);
lean_ctor_set(v___x_2224_, 5, v_ref_2223_);
lean_ctor_set(v___x_2224_, 6, v_currNamespace_2213_);
lean_ctor_set(v___x_2224_, 7, v_openDecls_2214_);
lean_ctor_set(v___x_2224_, 8, v_initHeartbeats_2215_);
lean_ctor_set(v___x_2224_, 9, v_maxHeartbeats_2216_);
lean_ctor_set(v___x_2224_, 10, v_quotContext_2217_);
lean_ctor_set(v___x_2224_, 11, v_currMacroScope_2218_);
lean_ctor_set(v___x_2224_, 12, v_cancelTk_x3f_2220_);
lean_ctor_set(v___x_2224_, 13, v_inheritedTraceOptions_2222_);
lean_ctor_set_uint8(v___x_2224_, sizeof(void*)*14, v_diag_2219_);
lean_ctor_set_uint8(v___x_2224_, sizeof(void*)*14 + 1, v_suppressElabErrors_2221_);
v___x_2225_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2159_, v_fixedPrefixSize_2160_, v_F_2161_, v_expr_2204_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v___x_2224_, v_a_2170_);
lean_dec_ref_known(v___x_2224_, 14);
return v___x_2225_;
}
else
{
lean_object* v___x_2226_; 
lean_dec(v___x_2205_);
v___x_2226_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2159_, v_fixedPrefixSize_2160_, v_F_2161_, v_expr_2204_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2235_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2229_ = v___x_2226_;
v_isShared_2230_ = v_isSharedCheck_2235_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2226_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2235_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2231_; lean_object* v___x_2233_; 
v___x_2231_ = l_Lean_mkMData(v_data_2203_, v_a_2227_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 0, v___x_2231_);
v___x_2233_ = v___x_2229_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2231_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
else
{
lean_dec(v_data_2203_);
return v___x_2226_;
}
}
}
case 11:
{
lean_object* v_typeName_2236_; lean_object* v_idx_2237_; lean_object* v_struct_2238_; lean_object* v___x_2239_; 
v_typeName_2236_ = lean_ctor_get(v_e_2162_, 0);
lean_inc(v_typeName_2236_);
v_idx_2237_ = lean_ctor_get(v_e_2162_, 1);
lean_inc(v_idx_2237_);
v_struct_2238_ = lean_ctor_get(v_e_2162_, 2);
lean_inc_ref(v_struct_2238_);
lean_dec_ref_known(v_e_2162_, 3);
v___x_2239_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2159_, v_fixedPrefixSize_2160_, v_F_2161_, v_struct_2238_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2248_; 
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2242_ = v___x_2239_;
v_isShared_2243_ = v_isSharedCheck_2248_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2239_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2248_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2244_; lean_object* v___x_2246_; 
v___x_2244_ = l_Lean_mkProj(v_typeName_2236_, v_idx_2237_, v_a_2240_);
if (v_isShared_2243_ == 0)
{
lean_ctor_set(v___x_2242_, 0, v___x_2244_);
v___x_2246_ = v___x_2242_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v___x_2244_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
else
{
lean_dec(v_idx_2237_);
lean_dec(v_typeName_2236_);
return v___x_2239_;
}
}
case 4:
{
uint8_t v___x_2249_; 
v___x_2249_ = l_Lean_Expr_isConstOf(v_e_2162_, v_recFnName_2159_);
if (v___x_2249_ == 0)
{
lean_object* v___x_2250_; 
lean_dec_ref(v_F_2161_);
lean_dec(v_fixedPrefixSize_2160_);
lean_dec(v_recFnName_2159_);
v___x_2250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2250_, 0, v_e_2162_);
return v___x_2250_;
}
else
{
lean_object* v___x_2251_; 
v___x_2251_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2159_, v_fixedPrefixSize_2160_, v_F_2161_, v_e_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_);
return v___x_2251_;
}
}
case 5:
{
uint8_t v___x_2252_; lean_object* v___x_2253_; 
v___x_2252_ = 1;
lean_inc_ref(v_e_2162_);
v___x_2253_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(v_e_2162_, v___x_2252_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_object* v_a_2254_; 
v_a_2254_ = lean_ctor_get(v___x_2253_, 0);
lean_inc(v_a_2254_);
lean_dec_ref_known(v___x_2253_, 1);
if (lean_obj_tag(v_a_2254_) == 0)
{
lean_object* v___x_2255_; 
v___x_2255_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2159_, v_fixedPrefixSize_2160_, v_F_2161_, v_e_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_);
return v___x_2255_;
}
else
{
lean_object* v_val_2256_; lean_object* v___x_2257_; 
v_val_2256_ = lean_ctor_get(v_a_2254_, 0);
lean_inc(v_val_2256_);
lean_dec_ref_known(v_a_2254_, 1);
lean_inc_ref(v_F_2161_);
v___x_2257_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_val_2256_, v_F_2161_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_);
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v_a_2258_; 
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
lean_inc(v_a_2258_);
lean_dec_ref_known(v___x_2257_, 1);
if (lean_obj_tag(v_a_2258_) == 1)
{
lean_object* v_val_2259_; lean_object* v_toMatcherInfo_2260_; lean_object* v_matcherName_2261_; lean_object* v_matcherLevels_2262_; lean_object* v_params_2263_; lean_object* v_motive_2264_; lean_object* v_discrs_2265_; lean_object* v_alts_2266_; lean_object* v_remaining_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
v_val_2259_ = lean_ctor_get(v_a_2258_, 0);
lean_inc(v_val_2259_);
lean_dec_ref_known(v_a_2258_, 1);
v_toMatcherInfo_2260_ = lean_ctor_get(v_val_2259_, 0);
lean_inc_ref(v_toMatcherInfo_2260_);
v_matcherName_2261_ = lean_ctor_get(v_val_2259_, 1);
lean_inc(v_matcherName_2261_);
v_matcherLevels_2262_ = lean_ctor_get(v_val_2259_, 2);
lean_inc_ref(v_matcherLevels_2262_);
v_params_2263_ = lean_ctor_get(v_val_2259_, 3);
lean_inc_ref(v_params_2263_);
v_motive_2264_ = lean_ctor_get(v_val_2259_, 4);
lean_inc_ref(v_motive_2264_);
v_discrs_2265_ = lean_ctor_get(v_val_2259_, 5);
lean_inc_ref(v_discrs_2265_);
v_alts_2266_ = lean_ctor_get(v_val_2259_, 6);
lean_inc_ref(v_alts_2266_);
v_remaining_2267_ = lean_ctor_get(v_val_2259_, 7);
lean_inc_ref(v_remaining_2267_);
v___x_2268_ = l_Lean_Meta_MatcherApp_altNumParams(v_val_2259_);
v___x_2269_ = lean_unsigned_to_nat(0u);
v___x_2270_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
lean_inc(v_fixedPrefixSize_2160_);
lean_inc(v_recFnName_2159_);
v___x_2271_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(v_recFnName_2159_, v_fixedPrefixSize_2160_, v_e_2162_, v_alts_2266_, v___x_2268_, v___x_2269_, v___x_2270_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_);
lean_dec_ref(v___x_2268_);
lean_dec_ref(v_alts_2266_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_object* v_a_2272_; size_t v_sz_2273_; size_t v___x_2274_; lean_object* v___x_2275_; 
v_a_2272_ = lean_ctor_get(v___x_2271_, 0);
lean_inc(v_a_2272_);
lean_dec_ref_known(v___x_2271_, 1);
v_sz_2273_ = lean_array_size(v_discrs_2265_);
v___x_2274_ = ((size_t)0ULL);
v___x_2275_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_2159_, v_fixedPrefixSize_2160_, v_F_2161_, v_sz_2273_, v___x_2274_, v_discrs_2265_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_);
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2285_; 
v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2275_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2278_ = v___x_2275_;
v_isShared_2279_ = v_isSharedCheck_2285_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2275_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2285_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2283_; 
v___x_2280_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2280_, 0, v_toMatcherInfo_2260_);
lean_ctor_set(v___x_2280_, 1, v_matcherName_2261_);
lean_ctor_set(v___x_2280_, 2, v_matcherLevels_2262_);
lean_ctor_set(v___x_2280_, 3, v_params_2263_);
lean_ctor_set(v___x_2280_, 4, v_motive_2264_);
lean_ctor_set(v___x_2280_, 5, v_a_2276_);
lean_ctor_set(v___x_2280_, 6, v_a_2272_);
lean_ctor_set(v___x_2280_, 7, v_remaining_2267_);
v___x_2281_ = l_Lean_Meta_MatcherApp_toExpr(v___x_2280_);
if (v_isShared_2279_ == 0)
{
lean_ctor_set(v___x_2278_, 0, v___x_2281_);
v___x_2283_ = v___x_2278_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v___x_2281_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
else
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2293_; 
lean_dec(v_a_2272_);
lean_dec_ref(v_remaining_2267_);
lean_dec_ref(v_motive_2264_);
lean_dec_ref(v_params_2263_);
lean_dec_ref(v_matcherLevels_2262_);
lean_dec(v_matcherName_2261_);
lean_dec_ref(v_toMatcherInfo_2260_);
v_a_2286_ = lean_ctor_get(v___x_2275_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2275_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2288_ = v___x_2275_;
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2275_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
if (v_isShared_2289_ == 0)
{
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2286_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
else
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2301_; 
lean_dec_ref(v_remaining_2267_);
lean_dec_ref(v_discrs_2265_);
lean_dec_ref(v_motive_2264_);
lean_dec_ref(v_params_2263_);
lean_dec_ref(v_matcherLevels_2262_);
lean_dec(v_matcherName_2261_);
lean_dec_ref(v_toMatcherInfo_2260_);
lean_dec_ref(v_F_2161_);
lean_dec(v_fixedPrefixSize_2160_);
lean_dec(v_recFnName_2159_);
v_a_2294_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2296_ = v___x_2271_;
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2271_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2299_; 
if (v_isShared_2297_ == 0)
{
v___x_2299_ = v___x_2296_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_a_2294_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
else
{
lean_object* v___x_2302_; 
lean_dec(v_a_2258_);
v___x_2302_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2159_, v_fixedPrefixSize_2160_, v_F_2161_, v_e_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_);
return v___x_2302_;
}
}
else
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2310_; 
lean_dec_ref_known(v_e_2162_, 2);
lean_dec_ref(v_F_2161_);
lean_dec(v_fixedPrefixSize_2160_);
lean_dec(v_recFnName_2159_);
v_a_2303_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2305_ = v___x_2257_;
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2257_);
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
}
else
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2318_; 
lean_dec_ref_known(v_e_2162_, 2);
lean_dec_ref(v_F_2161_);
lean_dec(v_fixedPrefixSize_2160_);
lean_dec(v_recFnName_2159_);
v_a_2311_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2313_ = v___x_2253_;
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2253_);
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
default: 
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
lean_dec_ref(v_F_2161_);
lean_dec(v_fixedPrefixSize_2160_);
v___x_2319_ = lean_unsigned_to_nat(1u);
v___x_2320_ = lean_mk_empty_array_with_capacity(v___x_2319_);
v___x_2321_ = lean_array_push(v___x_2320_, v_recFnName_2159_);
lean_inc_ref(v_e_2162_);
v___x_2322_ = l_Lean_Elab_ensureNoRecFn(v___x_2321_, v_e_2162_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_);
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2329_; 
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2329_ == 0)
{
lean_object* v_unused_2330_; 
v_unused_2330_ = lean_ctor_get(v___x_2322_, 0);
lean_dec(v_unused_2330_);
v___x_2324_ = v___x_2322_;
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
else
{
lean_dec(v___x_2322_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2327_; 
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 0, v_e_2162_);
v___x_2327_ = v___x_2324_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_e_2162_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
else
{
lean_object* v_a_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2338_; 
lean_dec_ref(v_e_2162_);
v_a_2331_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2333_ = v___x_2322_;
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_dec(v___x_2322_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2336_; 
if (v_isShared_2334_ == 0)
{
v___x_2336_ = v___x_2333_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2331_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(lean_object* v_recFnName_2339_, lean_object* v_fixedPrefixSize_2340_, lean_object* v_F_2341_, lean_object* v_e_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_){
_start:
{
lean_object* v___x_2352_; 
lean_inc_ref(v_e_2342_);
lean_inc(v_recFnName_2339_);
v___x_2352_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___redArg(v_recFnName_2339_, v_e_2342_, v_a_2343_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2460_; 
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2355_ = v___x_2352_;
v_isShared_2356_ = v_isSharedCheck_2460_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2352_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2460_;
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
lean_dec_ref(v_F_2341_);
lean_dec(v_fixedPrefixSize_2340_);
lean_dec(v_recFnName_2339_);
if (v_isShared_2356_ == 0)
{
lean_ctor_set(v___x_2355_, 0, v_e_2342_);
v___x_2359_ = v___x_2355_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_e_2342_);
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
lean_object* v___x_2361_; uint8_t v___x_2362_; lean_object* v___y_2364_; lean_object* v___y_2365_; lean_object* v___y_2366_; lean_object* v___y_2367_; lean_object* v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___x_2438_; 
lean_del_object(v___x_2355_);
v___x_2361_ = lean_st_ref_get(v_a_2344_);
v___x_2362_ = 0;
v___x_2438_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v___x_2361_, v_e_2342_);
lean_dec(v___x_2361_);
if (lean_obj_tag(v___x_2438_) == 1)
{
lean_object* v_val_2439_; lean_object* v_fst_2440_; lean_object* v_snd_2441_; lean_object* v___x_2442_; 
v_val_2439_ = lean_ctor_get(v___x_2438_, 0);
lean_inc(v_val_2439_);
lean_dec_ref_known(v___x_2438_, 1);
v_fst_2440_ = lean_ctor_get(v_val_2439_, 0);
lean_inc(v_fst_2440_);
v_snd_2441_ = lean_ctor_get(v_val_2439_, 1);
lean_inc(v_snd_2441_);
lean_dec(v_val_2439_);
v___x_2442_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___redArg(v_snd_2441_, v_a_2347_);
lean_dec(v_snd_2441_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2451_; 
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2445_ = v___x_2442_;
v_isShared_2446_ = v_isSharedCheck_2451_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2442_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2451_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
uint8_t v___x_2447_; 
v___x_2447_ = lean_unbox(v_a_2443_);
lean_dec(v_a_2443_);
if (v___x_2447_ == 0)
{
lean_del_object(v___x_2445_);
lean_dec(v_fst_2440_);
v___y_2364_ = v_a_2343_;
v___y_2365_ = v_a_2344_;
v___y_2366_ = v_a_2345_;
v___y_2367_ = v_a_2346_;
v___y_2368_ = v_a_2347_;
v___y_2369_ = v_a_2348_;
v___y_2370_ = v_a_2349_;
v___y_2371_ = v_a_2350_;
goto v___jp_2363_;
}
else
{
lean_object* v___x_2449_; 
lean_dec_ref(v_e_2342_);
lean_dec_ref(v_F_2341_);
lean_dec(v_fixedPrefixSize_2340_);
lean_dec(v_recFnName_2339_);
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 0, v_fst_2440_);
v___x_2449_ = v___x_2445_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_fst_2440_);
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
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2459_; 
lean_dec(v_fst_2440_);
lean_dec_ref(v_e_2342_);
lean_dec_ref(v_F_2341_);
lean_dec(v_fixedPrefixSize_2340_);
lean_dec(v_recFnName_2339_);
v_a_2452_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2454_ = v___x_2442_;
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2442_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2455_ == 0)
{
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_a_2452_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
}
else
{
lean_dec(v___x_2438_);
v___y_2364_ = v_a_2343_;
v___y_2365_ = v_a_2344_;
v___y_2366_ = v_a_2345_;
v___y_2367_ = v_a_2346_;
v___y_2368_ = v_a_2347_;
v___y_2369_ = v_a_2348_;
v___y_2370_ = v_a_2349_;
v___y_2371_ = v_a_2350_;
goto v___jp_2363_;
}
v___jp_2363_:
{
lean_object* v___x_2372_; 
lean_inc_ref(v_e_2342_);
v___x_2372_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(v_recFnName_2339_, v_fixedPrefixSize_2340_, v_F_2341_, v_e_2342_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v_a_2373_; lean_object* v___x_2374_; 
v_a_2373_ = lean_ctor_get(v___x_2372_, 0);
lean_inc(v_a_2373_);
lean_dec_ref_known(v___x_2372_, 1);
v___x_2374_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId(v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2429_; 
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2377_ = v___x_2374_;
v_isShared_2378_ = v_isSharedCheck_2429_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2374_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2429_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v_options_2383_; lean_object* v___x_2384_; uint8_t v___x_2385_; 
v___x_2379_ = lean_st_ref_take(v___y_2365_);
lean_inc(v_a_2373_);
v___x_2380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2380_, 0, v_a_2373_);
lean_ctor_set(v___x_2380_, 1, v_a_2375_);
lean_inc_ref(v_e_2342_);
v___x_2381_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4___redArg(v___x_2379_, v_e_2342_, v___x_2380_);
v___x_2382_ = lean_st_ref_put(v___y_2365_, v___x_2381_);
v_options_2383_ = lean_ctor_get(v___y_2370_, 2);
v___x_2384_ = l_Lean_Elab_WF_debug_definition_wf_replaceRecApps;
v___x_2385_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v_options_2383_, v___x_2384_);
if (v___x_2385_ == 0)
{
lean_object* v___x_2387_; 
lean_dec_ref(v_e_2342_);
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 0, v_a_2373_);
v___x_2387_ = v___x_2377_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2373_);
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
lean_object* v_keyedConfig_2389_; uint8_t v_trackZetaDelta_2390_; lean_object* v_zetaDeltaSet_2391_; lean_object* v_lctx_2392_; lean_object* v_localInstances_2393_; lean_object* v_defEqCtx_x3f_2394_; lean_object* v_synthPendingDepth_2395_; lean_object* v_customCanUnfoldPredicate_x3f_2396_; uint8_t v_univApprox_2397_; uint8_t v_inTypeClassResolution_2398_; uint8_t v_cacheInferType_2399_; lean_object* v___f_2400_; uint8_t v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
lean_del_object(v___x_2377_);
v_keyedConfig_2389_ = lean_ctor_get(v___y_2368_, 0);
v_trackZetaDelta_2390_ = lean_ctor_get_uint8(v___y_2368_, sizeof(void*)*7);
v_zetaDeltaSet_2391_ = lean_ctor_get(v___y_2368_, 1);
v_lctx_2392_ = lean_ctor_get(v___y_2368_, 2);
v_localInstances_2393_ = lean_ctor_get(v___y_2368_, 3);
v_defEqCtx_x3f_2394_ = lean_ctor_get(v___y_2368_, 4);
v_synthPendingDepth_2395_ = lean_ctor_get(v___y_2368_, 5);
v_customCanUnfoldPredicate_x3f_2396_ = lean_ctor_get(v___y_2368_, 6);
v_univApprox_2397_ = lean_ctor_get_uint8(v___y_2368_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2398_ = lean_ctor_get_uint8(v___y_2368_, sizeof(void*)*7 + 2);
v_cacheInferType_2399_ = lean_ctor_get_uint8(v___y_2368_, sizeof(void*)*7 + 3);
lean_inc(v_a_2373_);
v___f_2400_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___boxed), 11, 2);
lean_closure_set(v___f_2400_, 0, v_a_2373_);
lean_closure_set(v___f_2400_, 1, v_e_2342_);
v___x_2401_ = 0;
lean_inc_ref(v_keyedConfig_2389_);
v___x_2402_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2401_, v_keyedConfig_2389_);
lean_inc(v_customCanUnfoldPredicate_x3f_2396_);
lean_inc(v_synthPendingDepth_2395_);
lean_inc(v_defEqCtx_x3f_2394_);
lean_inc_ref(v_localInstances_2393_);
lean_inc_ref(v_lctx_2392_);
lean_inc(v_zetaDeltaSet_2391_);
v___x_2403_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2403_, 0, v___x_2402_);
lean_ctor_set(v___x_2403_, 1, v_zetaDeltaSet_2391_);
lean_ctor_set(v___x_2403_, 2, v_lctx_2392_);
lean_ctor_set(v___x_2403_, 3, v_localInstances_2393_);
lean_ctor_set(v___x_2403_, 4, v_defEqCtx_x3f_2394_);
lean_ctor_set(v___x_2403_, 5, v_synthPendingDepth_2395_);
lean_ctor_set(v___x_2403_, 6, v_customCanUnfoldPredicate_x3f_2396_);
lean_ctor_set_uint8(v___x_2403_, sizeof(void*)*7, v_trackZetaDelta_2390_);
lean_ctor_set_uint8(v___x_2403_, sizeof(void*)*7 + 1, v_univApprox_2397_);
lean_ctor_set_uint8(v___x_2403_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2398_);
lean_ctor_set_uint8(v___x_2403_, sizeof(void*)*7 + 3, v_cacheInferType_2399_);
v___x_2404_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v___f_2400_, v___x_2362_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___x_2403_, v___y_2369_, v___y_2370_, v___y_2371_);
lean_dec_ref_known(v___x_2403_, 7);
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2411_; 
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2411_ == 0)
{
lean_object* v_unused_2412_; 
v_unused_2412_ = lean_ctor_get(v___x_2404_, 0);
lean_dec(v_unused_2412_);
v___x_2406_ = v___x_2404_;
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
else
{
lean_dec(v___x_2404_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 0, v_a_2373_);
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2373_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
else
{
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2419_ == 0)
{
lean_object* v_unused_2420_; 
v_unused_2420_ = lean_ctor_get(v___x_2404_, 0);
lean_dec(v_unused_2420_);
v___x_2414_ = v___x_2404_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_dec(v___x_2404_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
lean_ctor_set_tag(v___x_2414_, 0);
lean_ctor_set(v___x_2414_, 0, v_a_2373_);
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_a_2373_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
else
{
lean_object* v_a_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2428_; 
lean_dec(v_a_2373_);
v_a_2421_ = lean_ctor_get(v___x_2404_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2423_ = v___x_2404_;
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_a_2421_);
lean_dec(v___x_2404_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2426_; 
if (v_isShared_2424_ == 0)
{
v___x_2426_ = v___x_2423_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_a_2421_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2437_; 
lean_dec(v_a_2373_);
lean_dec_ref(v_e_2342_);
v_a_2430_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2432_ = v___x_2374_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2374_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2435_; 
if (v_isShared_2433_ == 0)
{
v___x_2435_ = v___x_2432_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_a_2430_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
}
else
{
lean_dec_ref(v_e_2342_);
return v___x_2372_;
}
}
}
}
}
else
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2468_; 
lean_dec_ref(v_e_2342_);
lean_dec_ref(v_F_2341_);
lean_dec(v_fixedPrefixSize_2340_);
lean_dec(v_recFnName_2339_);
v_a_2461_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2463_ = v___x_2352_;
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2352_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2466_; 
if (v_isShared_2464_ == 0)
{
v___x_2466_ = v___x_2463_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2461_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2(lean_object* v_body_2469_, lean_object* v_recFnName_2470_, lean_object* v_fixedPrefixSize_2471_, lean_object* v_F_2472_, lean_object* v_x_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_){
_start:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; 
v___x_2483_ = lean_expr_instantiate1(v_body_2469_, v_x_2473_);
v___x_2484_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2470_, v_fixedPrefixSize_2471_, v_F_2472_, v___x_2483_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp___boxed(lean_object* v_recFnName_2485_, lean_object* v_fixedPrefixSize_2486_, lean_object* v_F_2487_, lean_object* v_e_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_){
_start:
{
lean_object* v_res_2498_; 
v_res_2498_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2485_, v_fixedPrefixSize_2486_, v_F_2487_, v_e_2488_, v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_);
lean_dec(v_a_2496_);
lean_dec_ref(v_a_2495_);
lean_dec(v_a_2494_);
lean_dec_ref(v_a_2493_);
lean_dec(v_a_2492_);
lean_dec_ref(v_a_2491_);
lean_dec(v_a_2490_);
lean_dec(v_a_2489_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1___boxed(lean_object* v_recFnName_2499_, lean_object* v_fixedPrefixSize_2500_, lean_object* v_F_2501_, lean_object* v_sz_2502_, lean_object* v_i_2503_, lean_object* v_bs_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
size_t v_sz_boxed_2514_; size_t v_i_boxed_2515_; lean_object* v_res_2516_; 
v_sz_boxed_2514_ = lean_unbox_usize(v_sz_2502_);
lean_dec(v_sz_2502_);
v_i_boxed_2515_ = lean_unbox_usize(v_i_2503_);
lean_dec(v_i_2503_);
v_res_2516_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_2499_, v_fixedPrefixSize_2500_, v_F_2501_, v_sz_boxed_2514_, v_i_boxed_2515_, v_bs_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec(v___y_2505_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16___boxed(lean_object* v_recFnName_2517_, lean_object* v_fixedPrefixSize_2518_, lean_object* v_F_2519_, lean_object* v_x_2520_, lean_object* v_x_2521_, lean_object* v_x_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(v_recFnName_2517_, v_fixedPrefixSize_2518_, v_F_2519_, v_x_2520_, v_x_2521_, v_x_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
lean_dec(v___y_2524_);
lean_dec(v___y_2523_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___boxed(lean_object* v_recFnName_2533_, lean_object* v_fixedPrefixSize_2534_, lean_object* v_e_2535_, lean_object* v_as_2536_, lean_object* v_bs_2537_, lean_object* v_i_2538_, lean_object* v_cs_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(v_recFnName_2533_, v_fixedPrefixSize_2534_, v_e_2535_, v_as_2536_, v_bs_2537_, v_i_2538_, v_cs_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
lean_dec(v___y_2543_);
lean_dec_ref(v___y_2542_);
lean_dec(v___y_2541_);
lean_dec(v___y_2540_);
lean_dec_ref(v_bs_2537_);
lean_dec_ref(v_as_2536_);
return v_res_2549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___boxed(lean_object* v_recFnName_2550_, lean_object* v_fixedPrefixSize_2551_, lean_object* v_F_2552_, lean_object* v_e_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2550_, v_fixedPrefixSize_2551_, v_F_2552_, v_e_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_);
lean_dec(v_a_2561_);
lean_dec_ref(v_a_2560_);
lean_dec(v_a_2559_);
lean_dec_ref(v_a_2558_);
lean_dec(v_a_2557_);
lean_dec_ref(v_a_2556_);
lean_dec(v_a_2555_);
lean_dec(v_a_2554_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___boxed(lean_object* v_recFnName_2564_, lean_object* v_fixedPrefixSize_2565_, lean_object* v_F_2566_, lean_object* v_e_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2564_, v_fixedPrefixSize_2565_, v_F_2566_, v_e_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_);
lean_dec(v_a_2575_);
lean_dec_ref(v_a_2574_);
lean_dec(v_a_2573_);
lean_dec_ref(v_a_2572_);
lean_dec(v_a_2571_);
lean_dec_ref(v_a_2570_);
lean_dec(v_a_2569_);
lean_dec(v_a_2568_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___boxed(lean_object* v_recFnName_2578_, lean_object* v_fixedPrefixSize_2579_, lean_object* v_F_2580_, lean_object* v_e_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(v_recFnName_2578_, v_fixedPrefixSize_2579_, v_F_2580_, v_e_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_);
lean_dec(v_a_2589_);
lean_dec_ref(v_a_2588_);
lean_dec(v_a_2587_);
lean_dec_ref(v_a_2586_);
lean_dec(v_a_2585_);
lean_dec_ref(v_a_2584_);
lean_dec(v_a_2583_);
lean_dec(v_a_2582_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7(lean_object* v_00_u03b1_2592_, lean_object* v_k_2593_, uint8_t v_allowLevelAssignments_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_){
_start:
{
lean_object* v___x_2604_; 
v___x_2604_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v_k_2593_, v_allowLevelAssignments_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
return v___x_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___boxed(lean_object* v_00_u03b1_2605_, lean_object* v_k_2606_, lean_object* v_allowLevelAssignments_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2617_; lean_object* v_res_2618_; 
v_allowLevelAssignments_boxed_2617_ = lean_unbox(v_allowLevelAssignments_2607_);
v_res_2618_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7(v_00_u03b1_2605_, v_k_2606_, v_allowLevelAssignments_boxed_2617_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec(v___y_2608_);
return v_res_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10(lean_object* v_00_u03b1_2619_, lean_object* v_name_2620_, uint8_t v_bi_2621_, lean_object* v_type_2622_, lean_object* v_k_2623_, uint8_t v_kind_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v___x_2634_; 
v___x_2634_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_name_2620_, v_bi_2621_, v_type_2622_, v_k_2623_, v_kind_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_);
return v___x_2634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___boxed(lean_object* v_00_u03b1_2635_, lean_object* v_name_2636_, lean_object* v_bi_2637_, lean_object* v_type_2638_, lean_object* v_k_2639_, lean_object* v_kind_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
uint8_t v_bi_boxed_2650_; uint8_t v_kind_boxed_2651_; lean_object* v_res_2652_; 
v_bi_boxed_2650_ = lean_unbox(v_bi_2637_);
v_kind_boxed_2651_ = lean_unbox(v_kind_2640_);
v_res_2652_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10(v_00_u03b1_2635_, v_name_2636_, v_bi_boxed_2650_, v_type_2638_, v_k_2639_, v_kind_boxed_2651_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
lean_dec(v___y_2642_);
lean_dec(v___y_2641_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(lean_object* v_00_u03b1_2653_, lean_object* v_e_2654_, lean_object* v_maxFVars_2655_, lean_object* v_k_2656_, uint8_t v_cleanupAnnotations_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
lean_object* v___x_2667_; 
v___x_2667_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(v_e_2654_, v_maxFVars_2655_, v_k_2656_, v_cleanupAnnotations_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
return v___x_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___boxed(lean_object* v_00_u03b1_2668_, lean_object* v_e_2669_, lean_object* v_maxFVars_2670_, lean_object* v_k_2671_, lean_object* v_cleanupAnnotations_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2682_; lean_object* v_res_2683_; 
v_cleanupAnnotations_boxed_2682_ = lean_unbox(v_cleanupAnnotations_2672_);
v_res_2683_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(v_00_u03b1_2668_, v_e_2669_, v_maxFVars_2670_, v_k_2671_, v_cleanupAnnotations_boxed_2682_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v___y_2674_);
lean_dec(v___y_2673_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0(lean_object* v_inst_2684_, lean_object* v_R_2685_, lean_object* v_a_2686_, lean_object* v_b_2687_){
_start:
{
lean_object* v___x_2688_; 
v___x_2688_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(v_a_2686_, v_b_2687_);
return v___x_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2(lean_object* v_cls_2689_, lean_object* v_msg_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
lean_object* v___x_2700_; 
v___x_2700_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(v_cls_2689_, v_msg_2690_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___boxed(lean_object* v_cls_2701_, lean_object* v_msg_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
lean_object* v_res_2712_; 
v_res_2712_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2(v_cls_2701_, v_msg_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec(v___y_2704_);
lean_dec(v___y_2703_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4(lean_object* v_00_u03b2_2713_, lean_object* v_m_2714_, lean_object* v_a_2715_, lean_object* v_b_2716_){
_start:
{
lean_object* v___x_2717_; 
v___x_2717_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4___redArg(v_m_2714_, v_a_2715_, v_b_2716_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(lean_object* v_00_u03b1_2718_, lean_object* v_msg_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v___x_2729_; 
v___x_2729_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v_msg_2719_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___boxed(lean_object* v_00_u03b1_2730_, lean_object* v_msg_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
lean_object* v_res_2741_; 
v_res_2741_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(v_00_u03b1_2730_, v_msg_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec(v___y_2732_);
return v_res_2741_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8(lean_object* v_00_u03b2_2742_, lean_object* v_m_2743_, lean_object* v_a_2744_){
_start:
{
lean_object* v___x_2745_; 
v___x_2745_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v_m_2743_, v_a_2744_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___boxed(lean_object* v_00_u03b2_2746_, lean_object* v_m_2747_, lean_object* v_a_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8(v_00_u03b2_2746_, v_m_2747_, v_a_2748_);
lean_dec_ref(v_a_2748_);
lean_dec_ref(v_m_2747_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15(lean_object* v_00_u03b1_2750_, lean_object* v_name_2751_, lean_object* v_type_2752_, lean_object* v_val_2753_, lean_object* v_k_2754_, uint8_t v_nondep_2755_, uint8_t v_kind_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_){
_start:
{
lean_object* v___x_2766_; 
v___x_2766_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(v_name_2751_, v_type_2752_, v_val_2753_, v_k_2754_, v_nondep_2755_, v_kind_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___boxed(lean_object* v_00_u03b1_2767_, lean_object* v_name_2768_, lean_object* v_type_2769_, lean_object* v_val_2770_, lean_object* v_k_2771_, lean_object* v_nondep_2772_, lean_object* v_kind_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_){
_start:
{
uint8_t v_nondep_boxed_2783_; uint8_t v_kind_boxed_2784_; lean_object* v_res_2785_; 
v_nondep_boxed_2783_ = lean_unbox(v_nondep_2772_);
v_kind_boxed_2784_ = lean_unbox(v_kind_2773_);
v_res_2785_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15(v_00_u03b1_2767_, v_name_2768_, v_type_2769_, v_val_2770_, v_k_2771_, v_nondep_boxed_2783_, v_kind_boxed_2784_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_);
lean_dec(v___y_2781_);
lean_dec_ref(v___y_2780_);
lean_dec(v___y_2779_);
lean_dec_ref(v___y_2778_);
lean_dec(v___y_2777_);
lean_dec_ref(v___y_2776_);
lean_dec(v___y_2775_);
lean_dec(v___y_2774_);
return v_res_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20(lean_object* v_declName_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_){
_start:
{
lean_object* v___x_2796_; 
v___x_2796_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(v_declName_2786_, v___y_2794_);
return v___x_2796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___boxed(lean_object* v_declName_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20(v_declName_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
lean_dec(v___y_2803_);
lean_dec_ref(v___y_2802_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec(v___y_2798_);
return v_res_2807_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4(lean_object* v_00_u03b2_2808_, lean_object* v_a_2809_, lean_object* v_x_2810_){
_start:
{
uint8_t v___x_2811_; 
v___x_2811_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg(v_a_2809_, v_x_2810_);
return v___x_2811_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___boxed(lean_object* v_00_u03b2_2812_, lean_object* v_a_2813_, lean_object* v_x_2814_){
_start:
{
uint8_t v_res_2815_; lean_object* v_r_2816_; 
v_res_2815_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4(v_00_u03b2_2812_, v_a_2813_, v_x_2814_);
lean_dec(v_x_2814_);
lean_dec_ref(v_a_2813_);
v_r_2816_ = lean_box(v_res_2815_);
return v_r_2816_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5(lean_object* v_00_u03b2_2817_, lean_object* v_data_2818_){
_start:
{
lean_object* v___x_2819_; 
v___x_2819_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5___redArg(v_data_2818_);
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6(lean_object* v_00_u03b2_2820_, lean_object* v_a_2821_, lean_object* v_b_2822_, lean_object* v_x_2823_){
_start:
{
lean_object* v___x_2824_; 
v___x_2824_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6___redArg(v_a_2821_, v_b_2822_, v_x_2823_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11(lean_object* v_00_u03b2_2825_, lean_object* v_a_2826_, lean_object* v_x_2827_){
_start:
{
lean_object* v___x_2828_; 
v___x_2828_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(v_a_2826_, v_x_2827_);
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___boxed(lean_object* v_00_u03b2_2829_, lean_object* v_a_2830_, lean_object* v_x_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11(v_00_u03b2_2829_, v_a_2830_, v_x_2831_);
lean_dec(v_x_2831_);
lean_dec_ref(v_a_2830_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12(lean_object* v_00_u03b2_2833_, lean_object* v_i_2834_, lean_object* v_source_2835_, lean_object* v_target_2836_){
_start:
{
lean_object* v___x_2837_; 
v___x_2837_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12___redArg(v_i_2834_, v_source_2835_, v_target_2836_);
return v___x_2837_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21(lean_object* v_00_u03b1_2838_, lean_object* v_constName_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_){
_start:
{
lean_object* v___x_2849_; 
v___x_2849_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(v_constName_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
return v___x_2849_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___boxed(lean_object* v_00_u03b1_2850_, lean_object* v_constName_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_){
_start:
{
lean_object* v_res_2861_; 
v_res_2861_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21(v_00_u03b1_2850_, v_constName_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12_spec__22(lean_object* v_00_u03b2_2862_, lean_object* v_x_2863_, lean_object* v_x_2864_){
_start:
{
lean_object* v___x_2865_; 
v___x_2865_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12_spec__22___redArg(v_x_2863_, v_x_2864_);
return v___x_2865_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27(lean_object* v_00_u03b1_2866_, lean_object* v_ref_2867_, lean_object* v_constName_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
lean_object* v___x_2878_; 
v___x_2878_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(v_ref_2867_, v_constName_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
return v___x_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___boxed(lean_object* v_00_u03b1_2879_, lean_object* v_ref_2880_, lean_object* v_constName_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_){
_start:
{
lean_object* v_res_2891_; 
v_res_2891_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27(v_00_u03b1_2879_, v_ref_2880_, v_constName_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec(v___y_2882_);
lean_dec(v_ref_2880_);
return v_res_2891_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29(lean_object* v_00_u03b1_2892_, lean_object* v_ref_2893_, lean_object* v_msg_2894_, lean_object* v_declHint_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_){
_start:
{
lean_object* v___x_2905_; 
v___x_2905_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(v_ref_2893_, v_msg_2894_, v_declHint_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___boxed(lean_object* v_00_u03b1_2906_, lean_object* v_ref_2907_, lean_object* v_msg_2908_, lean_object* v_declHint_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29(v_00_u03b1_2906_, v_ref_2907_, v_msg_2908_, v_declHint_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
lean_dec(v___y_2911_);
lean_dec(v___y_2910_);
lean_dec(v_ref_2907_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31(lean_object* v_msg_2920_, lean_object* v_declHint_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
lean_object* v___x_2931_; 
v___x_2931_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(v_msg_2920_, v_declHint_2921_, v___y_2929_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___boxed(lean_object* v_msg_2932_, lean_object* v_declHint_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31(v_msg_2932_, v_declHint_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2935_);
lean_dec(v___y_2934_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31(lean_object* v_00_u03b1_2944_, lean_object* v_ref_2945_, lean_object* v_msg_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_){
_start:
{
lean_object* v___x_2956_; 
v___x_2956_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(v_ref_2945_, v_msg_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___boxed(lean_object* v_00_u03b1_2957_, lean_object* v_ref_2958_, lean_object* v_msg_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
lean_object* v_res_2969_; 
v_res_2969_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31(v_00_u03b1_2957_, v_ref_2958_, v_msg_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
lean_dec(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec(v___y_2965_);
lean_dec_ref(v___y_2964_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec(v___y_2961_);
lean_dec(v___y_2960_);
lean_dec(v_ref_2958_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(lean_object* v_cls_2970_, lean_object* v_msg_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_){
_start:
{
lean_object* v_ref_2977_; lean_object* v___x_2978_; lean_object* v_a_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_3023_; 
v_ref_2977_ = lean_ctor_get(v___y_2974_, 5);
v___x_2978_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_);
v_a_2979_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_2981_ = v___x_2978_;
v_isShared_2982_ = v_isSharedCheck_3023_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_a_2979_);
lean_dec(v___x_2978_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_3023_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2983_; lean_object* v_traceState_2984_; lean_object* v_env_2985_; lean_object* v_nextMacroScope_2986_; lean_object* v_ngen_2987_; lean_object* v_auxDeclNGen_2988_; lean_object* v_cache_2989_; lean_object* v_messages_2990_; lean_object* v_infoState_2991_; lean_object* v_snapshotTasks_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_3022_; 
v___x_2983_ = lean_st_ref_take(v___y_2975_);
v_traceState_2984_ = lean_ctor_get(v___x_2983_, 4);
v_env_2985_ = lean_ctor_get(v___x_2983_, 0);
v_nextMacroScope_2986_ = lean_ctor_get(v___x_2983_, 1);
v_ngen_2987_ = lean_ctor_get(v___x_2983_, 2);
v_auxDeclNGen_2988_ = lean_ctor_get(v___x_2983_, 3);
v_cache_2989_ = lean_ctor_get(v___x_2983_, 5);
v_messages_2990_ = lean_ctor_get(v___x_2983_, 6);
v_infoState_2991_ = lean_ctor_get(v___x_2983_, 7);
v_snapshotTasks_2992_ = lean_ctor_get(v___x_2983_, 8);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_2994_ = v___x_2983_;
v_isShared_2995_ = v_isSharedCheck_3022_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_snapshotTasks_2992_);
lean_inc(v_infoState_2991_);
lean_inc(v_messages_2990_);
lean_inc(v_cache_2989_);
lean_inc(v_traceState_2984_);
lean_inc(v_auxDeclNGen_2988_);
lean_inc(v_ngen_2987_);
lean_inc(v_nextMacroScope_2986_);
lean_inc(v_env_2985_);
lean_dec(v___x_2983_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_3022_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
uint64_t v_tid_2996_; lean_object* v_traces_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3021_; 
v_tid_2996_ = lean_ctor_get_uint64(v_traceState_2984_, sizeof(void*)*1);
v_traces_2997_ = lean_ctor_get(v_traceState_2984_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v_traceState_2984_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_2999_ = v_traceState_2984_;
v_isShared_3000_ = v_isSharedCheck_3021_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_traces_2997_);
lean_dec(v_traceState_2984_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3021_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3001_; double v___x_3002_; uint8_t v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3011_; 
v___x_3001_ = lean_box(0);
v___x_3002_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0);
v___x_3003_ = 0;
v___x_3004_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__1));
v___x_3005_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3005_, 0, v_cls_2970_);
lean_ctor_set(v___x_3005_, 1, v___x_3001_);
lean_ctor_set(v___x_3005_, 2, v___x_3004_);
lean_ctor_set_float(v___x_3005_, sizeof(void*)*3, v___x_3002_);
lean_ctor_set_float(v___x_3005_, sizeof(void*)*3 + 8, v___x_3002_);
lean_ctor_set_uint8(v___x_3005_, sizeof(void*)*3 + 16, v___x_3003_);
v___x_3006_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__2));
v___x_3007_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3005_);
lean_ctor_set(v___x_3007_, 1, v_a_2979_);
lean_ctor_set(v___x_3007_, 2, v___x_3006_);
lean_inc(v_ref_2977_);
v___x_3008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3008_, 0, v_ref_2977_);
lean_ctor_set(v___x_3008_, 1, v___x_3007_);
v___x_3009_ = l_Lean_PersistentArray_push___redArg(v_traces_2997_, v___x_3008_);
if (v_isShared_3000_ == 0)
{
lean_ctor_set(v___x_2999_, 0, v___x_3009_);
v___x_3011_ = v___x_2999_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v___x_3009_);
lean_ctor_set_uint64(v_reuseFailAlloc_3020_, sizeof(void*)*1, v_tid_2996_);
v___x_3011_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
lean_object* v___x_3013_; 
if (v_isShared_2995_ == 0)
{
lean_ctor_set(v___x_2994_, 4, v___x_3011_);
v___x_3013_ = v___x_2994_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_env_2985_);
lean_ctor_set(v_reuseFailAlloc_3019_, 1, v_nextMacroScope_2986_);
lean_ctor_set(v_reuseFailAlloc_3019_, 2, v_ngen_2987_);
lean_ctor_set(v_reuseFailAlloc_3019_, 3, v_auxDeclNGen_2988_);
lean_ctor_set(v_reuseFailAlloc_3019_, 4, v___x_3011_);
lean_ctor_set(v_reuseFailAlloc_3019_, 5, v_cache_2989_);
lean_ctor_set(v_reuseFailAlloc_3019_, 6, v_messages_2990_);
lean_ctor_set(v_reuseFailAlloc_3019_, 7, v_infoState_2991_);
lean_ctor_set(v_reuseFailAlloc_3019_, 8, v_snapshotTasks_2992_);
v___x_3013_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3017_; 
v___x_3014_ = lean_st_ref_put(v___y_2975_, v___x_3013_);
v___x_3015_ = lean_box(0);
if (v_isShared_2982_ == 0)
{
lean_ctor_set(v___x_2981_, 0, v___x_3015_);
v___x_3017_ = v___x_2981_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v___x_3015_);
v___x_3017_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
return v___x_3017_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg___boxed(lean_object* v_cls_3024_, lean_object* v_msg_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_){
_start:
{
lean_object* v_res_3031_; 
v_res_3031_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3024_, v_msg_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_);
lean_dec(v___y_3029_);
lean_dec_ref(v___y_3028_);
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
return v_res_3031_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0(void){
_start:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3032_ = lean_box(0);
v___x_3033_ = lean_unsigned_to_nat(16u);
v___x_3034_ = lean_mk_array(v___x_3033_, v___x_3032_);
return v___x_3034_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1(void){
_start:
{
lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3035_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0);
v___x_3036_ = lean_unsigned_to_nat(0u);
v___x_3037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3036_);
lean_ctor_set(v___x_3037_, 1, v___x_3035_);
return v___x_3037_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3(void){
_start:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; 
v___x_3039_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__2));
v___x_3040_ = l_Lean_stringToMessageData(v___x_3039_);
return v___x_3040_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5(void){
_start:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3042_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__4));
v___x_3043_ = l_Lean_stringToMessageData(v___x_3042_);
return v___x_3043_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7(void){
_start:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3045_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__6));
v___x_3046_ = l_Lean_stringToMessageData(v___x_3045_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(lean_object* v_recFnName_3047_, lean_object* v_fixedPrefixSize_3048_, lean_object* v_F_3049_, lean_object* v_e_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_){
_start:
{
lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v_options_3079_; uint8_t v_hasTrace_3080_; 
v_options_3079_ = lean_ctor_get(v_a_3055_, 2);
v_hasTrace_3080_ = lean_ctor_get_uint8(v_options_3079_, sizeof(void*)*1);
if (v_hasTrace_3080_ == 0)
{
v___y_3059_ = v_a_3051_;
v___y_3060_ = v_a_3052_;
v___y_3061_ = v_a_3053_;
v___y_3062_ = v_a_3054_;
v___y_3063_ = v_a_3055_;
v___y_3064_ = v_a_3056_;
goto v___jp_3058_;
}
else
{
lean_object* v_inheritedTraceOptions_3081_; lean_object* v_cls_3082_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v_options_3089_; lean_object* v_inheritedTraceOptions_3090_; lean_object* v___y_3091_; lean_object* v___x_3112_; uint8_t v___x_3113_; 
v_inheritedTraceOptions_3081_ = lean_ctor_get(v_a_3055_, 13);
v_cls_3082_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_3112_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_3113_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3081_, v_options_3079_, v___x_3112_);
if (v___x_3113_ == 0)
{
v___y_3084_ = v_a_3051_;
v___y_3085_ = v_a_3052_;
v___y_3086_ = v_a_3053_;
v___y_3087_ = v_a_3054_;
v___y_3088_ = v_a_3055_;
v_options_3089_ = v_options_3079_;
v_inheritedTraceOptions_3090_ = v_inheritedTraceOptions_3081_;
v___y_3091_ = v_a_3056_;
goto v___jp_3083_;
}
else
{
lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3114_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7);
lean_inc_ref(v_e_3050_);
v___x_3115_ = l_Lean_indentExpr(v_e_3050_);
v___x_3116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3114_);
lean_ctor_set(v___x_3116_, 1, v___x_3115_);
v___x_3117_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3082_, v___x_3116_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_);
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_dec_ref_known(v___x_3117_, 1);
v___y_3084_ = v_a_3051_;
v___y_3085_ = v_a_3052_;
v___y_3086_ = v_a_3053_;
v___y_3087_ = v_a_3054_;
v___y_3088_ = v_a_3055_;
v_options_3089_ = v_options_3079_;
v_inheritedTraceOptions_3090_ = v_inheritedTraceOptions_3081_;
v___y_3091_ = v_a_3056_;
goto v___jp_3083_;
}
else
{
lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3125_; 
lean_dec_ref(v_e_3050_);
lean_dec_ref(v_F_3049_);
lean_dec(v_fixedPrefixSize_3048_);
lean_dec(v_recFnName_3047_);
v_a_3118_ = lean_ctor_get(v___x_3117_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3120_ = v___x_3117_;
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_dec(v___x_3117_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3123_; 
if (v_isShared_3121_ == 0)
{
v___x_3123_ = v___x_3120_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_a_3118_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
}
v___jp_3083_:
{
lean_object* v___x_3092_; uint8_t v___x_3093_; 
v___x_3092_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_3093_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3090_, v_options_3089_, v___x_3092_);
if (v___x_3093_ == 0)
{
v___y_3059_ = v___y_3084_;
v___y_3060_ = v___y_3085_;
v___y_3061_ = v___y_3086_;
v___y_3062_ = v___y_3087_;
v___y_3063_ = v___y_3088_;
v___y_3064_ = v___y_3091_;
goto v___jp_3058_;
}
else
{
lean_object* v___x_3094_; 
lean_inc(v___y_3091_);
lean_inc_ref(v___y_3088_);
lean_inc(v___y_3087_);
lean_inc_ref(v___y_3086_);
lean_inc_ref(v_F_3049_);
v___x_3094_ = lean_infer_type(v_F_3049_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3091_);
if (lean_obj_tag(v___x_3094_) == 0)
{
lean_object* v_a_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v_a_3095_ = lean_ctor_get(v___x_3094_, 0);
lean_inc(v_a_3095_);
lean_dec_ref_known(v___x_3094_, 1);
v___x_3096_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3);
lean_inc_ref(v_F_3049_);
v___x_3097_ = l_Lean_MessageData_ofExpr(v_F_3049_);
v___x_3098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3096_);
lean_ctor_set(v___x_3098_, 1, v___x_3097_);
v___x_3099_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5);
v___x_3100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3100_, 0, v___x_3098_);
lean_ctor_set(v___x_3100_, 1, v___x_3099_);
v___x_3101_ = l_Lean_indentExpr(v_a_3095_);
v___x_3102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3102_, 0, v___x_3100_);
lean_ctor_set(v___x_3102_, 1, v___x_3101_);
v___x_3103_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3082_, v___x_3102_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3091_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_dec_ref_known(v___x_3103_, 1);
v___y_3059_ = v___y_3084_;
v___y_3060_ = v___y_3085_;
v___y_3061_ = v___y_3086_;
v___y_3062_ = v___y_3087_;
v___y_3063_ = v___y_3088_;
v___y_3064_ = v___y_3091_;
goto v___jp_3058_;
}
else
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3111_; 
lean_dec_ref(v_e_3050_);
lean_dec_ref(v_F_3049_);
lean_dec(v_fixedPrefixSize_3048_);
lean_dec(v_recFnName_3047_);
v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3106_ = v___x_3103_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3103_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3109_; 
if (v_isShared_3107_ == 0)
{
v___x_3109_ = v___x_3106_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_a_3104_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
}
else
{
lean_dec_ref(v_e_3050_);
lean_dec_ref(v_F_3049_);
lean_dec(v_fixedPrefixSize_3048_);
lean_dec(v_recFnName_3047_);
return v___x_3094_;
}
}
}
}
v___jp_3058_:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3065_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1);
v___x_3066_ = lean_st_mk_ref(v___x_3065_);
v___x_3067_ = lean_st_mk_ref(v___x_3065_);
v___x_3068_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_3047_, v_fixedPrefixSize_3048_, v_F_3049_, v_e_3050_, v___x_3067_, v___x_3066_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_);
if (lean_obj_tag(v___x_3068_) == 0)
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3078_; 
v_a_3069_ = lean_ctor_get(v___x_3068_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_3068_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3071_ = v___x_3068_;
v_isShared_3072_ = v_isSharedCheck_3078_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_3068_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3078_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3076_; 
v___x_3073_ = lean_st_ref_get(v___x_3067_);
lean_dec(v___x_3067_);
lean_dec(v___x_3073_);
v___x_3074_ = lean_st_ref_get(v___x_3066_);
lean_dec(v___x_3066_);
lean_dec(v___x_3074_);
if (v_isShared_3072_ == 0)
{
v___x_3076_ = v___x_3071_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_a_3069_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
}
else
{
lean_dec(v___x_3067_);
lean_dec(v___x_3066_);
return v___x_3068_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___boxed(lean_object* v_recFnName_3126_, lean_object* v_fixedPrefixSize_3127_, lean_object* v_F_3128_, lean_object* v_e_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_){
_start:
{
lean_object* v_res_3137_; 
v_res_3137_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(v_recFnName_3126_, v_fixedPrefixSize_3127_, v_F_3128_, v_e_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_);
lean_dec(v_a_3135_);
lean_dec_ref(v_a_3134_);
lean_dec(v_a_3133_);
lean_dec_ref(v_a_3132_);
lean_dec(v_a_3131_);
lean_dec_ref(v_a_3130_);
return v_res_3137_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0(lean_object* v_cls_3138_, lean_object* v_msg_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_){
_start:
{
lean_object* v___x_3147_; 
v___x_3147_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3138_, v_msg_3139_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_);
return v___x_3147_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___boxed(lean_object* v_cls_3148_, lean_object* v_msg_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_){
_start:
{
lean_object* v_res_3157_; 
v_res_3157_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0(v_cls_3148_, v_msg_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
return v_res_3157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0(lean_object* v_k_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v_b_3161_, lean_object* v_c_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_){
_start:
{
lean_object* v___x_3168_; 
lean_inc(v___y_3166_);
lean_inc_ref(v___y_3165_);
lean_inc(v___y_3164_);
lean_inc_ref(v___y_3163_);
lean_inc(v___y_3160_);
lean_inc_ref(v___y_3159_);
v___x_3168_ = lean_apply_9(v_k_3158_, v_b_3161_, v_c_3162_, v___y_3159_, v___y_3160_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, lean_box(0));
return v___x_3168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed(lean_object* v_k_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v_b_3172_, lean_object* v_c_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_){
_start:
{
lean_object* v_res_3179_; 
v_res_3179_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0(v_k_3169_, v___y_3170_, v___y_3171_, v_b_3172_, v_c_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_);
lean_dec(v___y_3177_);
lean_dec_ref(v___y_3176_);
lean_dec(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
return v_res_3179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(lean_object* v_e_3180_, lean_object* v_k_3181_, uint8_t v_cleanupAnnotations_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_){
_start:
{
lean_object* v___f_3190_; uint8_t v___x_3191_; uint8_t v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
lean_inc(v___y_3184_);
lean_inc_ref(v___y_3183_);
v___f_3190_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3190_, 0, v_k_3181_);
lean_closure_set(v___f_3190_, 1, v___y_3183_);
lean_closure_set(v___f_3190_, 2, v___y_3184_);
v___x_3191_ = 1;
v___x_3192_ = 0;
v___x_3193_ = lean_box(0);
v___x_3194_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3180_, v___x_3191_, v___x_3192_, v___x_3191_, v___x_3192_, v___x_3193_, v___f_3190_, v_cleanupAnnotations_3182_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
if (lean_obj_tag(v___x_3194_) == 0)
{
return v___x_3194_;
}
else
{
lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3202_; 
v_a_3195_ = lean_ctor_get(v___x_3194_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3197_ = v___x_3194_;
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3194_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3200_; 
if (v_isShared_3198_ == 0)
{
v___x_3200_ = v___x_3197_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_a_3195_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___boxed(lean_object* v_e_3203_, lean_object* v_k_3204_, lean_object* v_cleanupAnnotations_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3213_; lean_object* v_res_3214_; 
v_cleanupAnnotations_boxed_3213_ = lean_unbox(v_cleanupAnnotations_3205_);
v_res_3214_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v_e_3203_, v_k_3204_, v_cleanupAnnotations_boxed_3213_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
return v_res_3214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0(lean_object* v_00_u03b1_3215_, lean_object* v_e_3216_, lean_object* v_k_3217_, uint8_t v_cleanupAnnotations_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_){
_start:
{
lean_object* v___x_3226_; 
v___x_3226_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v_e_3216_, v_k_3217_, v_cleanupAnnotations_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_);
return v___x_3226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___boxed(lean_object* v_00_u03b1_3227_, lean_object* v_e_3228_, lean_object* v_k_3229_, lean_object* v_cleanupAnnotations_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3238_; lean_object* v_res_3239_; 
v_cleanupAnnotations_boxed_3238_ = lean_unbox(v_cleanupAnnotations_3230_);
v_res_3239_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0(v_00_u03b1_3227_, v_e_3228_, v_k_3229_, v_cleanupAnnotations_boxed_3238_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
return v_res_3239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(lean_object* v_e_3240_, lean_object* v_maxFVars_3241_, lean_object* v_k_3242_, uint8_t v_cleanupAnnotations_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_){
_start:
{
lean_object* v___f_3251_; uint8_t v___x_3252_; uint8_t v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; 
lean_inc(v___y_3245_);
lean_inc_ref(v___y_3244_);
v___f_3251_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3251_, 0, v_k_3242_);
lean_closure_set(v___f_3251_, 1, v___y_3244_);
lean_closure_set(v___f_3251_, 2, v___y_3245_);
v___x_3252_ = 1;
v___x_3253_ = 0;
v___x_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3254_, 0, v_maxFVars_3241_);
v___x_3255_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3240_, v___x_3252_, v___x_3253_, v___x_3252_, v___x_3253_, v___x_3254_, v___f_3251_, v_cleanupAnnotations_3243_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_);
lean_dec_ref_known(v___x_3254_, 1);
if (lean_obj_tag(v___x_3255_) == 0)
{
return v___x_3255_;
}
else
{
lean_object* v_a_3256_; lean_object* v___x_3258_; uint8_t v_isShared_3259_; uint8_t v_isSharedCheck_3263_; 
v_a_3256_ = lean_ctor_get(v___x_3255_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3255_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3258_ = v___x_3255_;
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
else
{
lean_inc(v_a_3256_);
lean_dec(v___x_3255_);
v___x_3258_ = lean_box(0);
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
v_resetjp_3257_:
{
lean_object* v___x_3261_; 
if (v_isShared_3259_ == 0)
{
v___x_3261_ = v___x_3258_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_a_3256_);
v___x_3261_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
return v___x_3261_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg___boxed(lean_object* v_e_3264_, lean_object* v_maxFVars_3265_, lean_object* v_k_3266_, lean_object* v_cleanupAnnotations_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3275_; lean_object* v_res_3276_; 
v_cleanupAnnotations_boxed_3275_ = lean_unbox(v_cleanupAnnotations_3267_);
v_res_3276_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_e_3264_, v_maxFVars_3265_, v_k_3266_, v_cleanupAnnotations_boxed_3275_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec(v___y_3269_);
lean_dec_ref(v___y_3268_);
return v_res_3276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2(lean_object* v_00_u03b1_3277_, lean_object* v_e_3278_, lean_object* v_maxFVars_3279_, lean_object* v_k_3280_, uint8_t v_cleanupAnnotations_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_){
_start:
{
lean_object* v___x_3289_; 
v___x_3289_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_e_3278_, v_maxFVars_3279_, v_k_3280_, v_cleanupAnnotations_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_);
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___boxed(lean_object* v_00_u03b1_3290_, lean_object* v_e_3291_, lean_object* v_maxFVars_3292_, lean_object* v_k_3293_, lean_object* v_cleanupAnnotations_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3302_; lean_object* v_res_3303_; 
v_cleanupAnnotations_boxed_3302_ = lean_unbox(v_cleanupAnnotations_3294_);
v_res_3303_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2(v_00_u03b1_3290_, v_e_3291_, v_maxFVars_3292_, v_k_3293_, v_cleanupAnnotations_boxed_3302_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
return v_res_3303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0(lean_object* v_a_3304_, lean_object* v___x_3305_, lean_object* v___x_3306_, lean_object* v_x_3307_, uint8_t v___x_3308_, lean_object* v_xs_3309_, lean_object* v_type_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_){
_start:
{
lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; 
v___x_3318_ = l_Lean_LocalDecl_type(v_a_3304_);
v___x_3319_ = lean_array_get_borrowed(v___x_3305_, v_xs_3309_, v___x_3306_);
v___x_3320_ = l_Lean_Expr_replaceFVar(v___x_3318_, v_x_3307_, v___x_3319_);
lean_dec_ref(v___x_3318_);
v___x_3321_ = l_Lean_mkArrow(v___x_3320_, v_type_3310_, v___y_3315_, v___y_3316_);
if (lean_obj_tag(v___x_3321_) == 0)
{
lean_object* v_a_3322_; uint8_t v___x_3323_; uint8_t v___x_3324_; lean_object* v___x_3325_; 
v_a_3322_ = lean_ctor_get(v___x_3321_, 0);
lean_inc_n(v_a_3322_, 2);
lean_dec_ref_known(v___x_3321_, 1);
v___x_3323_ = 0;
v___x_3324_ = 1;
v___x_3325_ = l_Lean_Meta_mkLambdaFVars(v_xs_3309_, v_a_3322_, v___x_3323_, v___x_3308_, v___x_3323_, v___x_3308_, v___x_3324_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_);
if (lean_obj_tag(v___x_3325_) == 0)
{
lean_object* v_a_3326_; lean_object* v___x_3327_; 
v_a_3326_ = lean_ctor_get(v___x_3325_, 0);
lean_inc(v_a_3326_);
lean_dec_ref_known(v___x_3325_, 1);
v___x_3327_ = l_Lean_Meta_getLevel(v_a_3322_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_);
if (lean_obj_tag(v___x_3327_) == 0)
{
lean_object* v_a_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3336_; 
v_a_3328_ = lean_ctor_get(v___x_3327_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___x_3327_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3330_ = v___x_3327_;
v_isShared_3331_ = v_isSharedCheck_3336_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_a_3328_);
lean_dec(v___x_3327_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3336_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v___x_3332_; lean_object* v___x_3334_; 
v___x_3332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3332_, 0, v_a_3326_);
lean_ctor_set(v___x_3332_, 1, v_a_3328_);
if (v_isShared_3331_ == 0)
{
lean_ctor_set(v___x_3330_, 0, v___x_3332_);
v___x_3334_ = v___x_3330_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v___x_3332_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
}
else
{
lean_object* v_a_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3344_; 
lean_dec(v_a_3326_);
v_a_3337_ = lean_ctor_get(v___x_3327_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3327_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3339_ = v___x_3327_;
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_a_3337_);
lean_dec(v___x_3327_);
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
else
{
lean_object* v_a_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3352_; 
lean_dec(v_a_3322_);
v_a_3345_ = lean_ctor_get(v___x_3325_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3325_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3347_ = v___x_3325_;
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_a_3345_);
lean_dec(v___x_3325_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3350_; 
if (v_isShared_3348_ == 0)
{
v___x_3350_ = v___x_3347_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_a_3345_);
v___x_3350_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
return v___x_3350_;
}
}
}
}
else
{
lean_object* v_a_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3360_; 
v_a_3353_ = lean_ctor_get(v___x_3321_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3355_ = v___x_3321_;
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_a_3353_);
lean_dec(v___x_3321_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3358_; 
if (v_isShared_3356_ == 0)
{
v___x_3358_ = v___x_3355_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v_a_3353_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
return v___x_3358_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed(lean_object* v_a_3361_, lean_object* v___x_3362_, lean_object* v___x_3363_, lean_object* v_x_3364_, lean_object* v___x_3365_, lean_object* v_xs_3366_, lean_object* v_type_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_){
_start:
{
uint8_t v___x_6244__boxed_3375_; lean_object* v_res_3376_; 
v___x_6244__boxed_3375_ = lean_unbox(v___x_3365_);
v_res_3376_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0(v_a_3361_, v___x_3362_, v___x_3363_, v_x_3364_, v___x_6244__boxed_3375_, v_xs_3366_, v_type_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_);
lean_dec(v___y_3373_);
lean_dec_ref(v___y_3372_);
lean_dec(v___y_3371_);
lean_dec_ref(v___y_3370_);
lean_dec(v___y_3369_);
lean_dec_ref(v___y_3368_);
lean_dec_ref(v_xs_3366_);
lean_dec(v___x_3363_);
lean_dec_ref(v___x_3362_);
lean_dec_ref(v_a_3361_);
return v_res_3376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0(lean_object* v_k_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v_b_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_){
_start:
{
lean_object* v___x_3386_; 
lean_inc(v___y_3384_);
lean_inc_ref(v___y_3383_);
lean_inc(v___y_3382_);
lean_inc_ref(v___y_3381_);
lean_inc(v___y_3379_);
lean_inc_ref(v___y_3378_);
v___x_3386_ = lean_apply_8(v_k_3377_, v_b_3380_, v___y_3378_, v___y_3379_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, lean_box(0));
return v___x_3386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_k_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v_b_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_){
_start:
{
lean_object* v_res_3396_; 
v_res_3396_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0(v_k_3387_, v___y_3388_, v___y_3389_, v_b_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_);
lean_dec(v___y_3394_);
lean_dec_ref(v___y_3393_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec(v___y_3389_);
lean_dec_ref(v___y_3388_);
return v_res_3396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(lean_object* v_name_3397_, uint8_t v_bi_3398_, lean_object* v_type_3399_, lean_object* v_k_3400_, uint8_t v_kind_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_){
_start:
{
lean_object* v___f_3409_; lean_object* v___x_3410_; 
lean_inc(v___y_3403_);
lean_inc_ref(v___y_3402_);
v___f_3409_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3409_, 0, v_k_3400_);
lean_closure_set(v___f_3409_, 1, v___y_3402_);
lean_closure_set(v___f_3409_, 2, v___y_3403_);
v___x_3410_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3397_, v_bi_3398_, v_type_3399_, v___f_3409_, v_kind_3401_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_);
if (lean_obj_tag(v___x_3410_) == 0)
{
return v___x_3410_;
}
else
{
lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3418_; 
v_a_3411_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3413_ = v___x_3410_;
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3410_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3416_; 
if (v_isShared_3414_ == 0)
{
v___x_3416_ = v___x_3413_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_a_3411_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___boxed(lean_object* v_name_3419_, lean_object* v_bi_3420_, lean_object* v_type_3421_, lean_object* v_k_3422_, lean_object* v_kind_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_){
_start:
{
uint8_t v_bi_boxed_3431_; uint8_t v_kind_boxed_3432_; lean_object* v_res_3433_; 
v_bi_boxed_3431_ = lean_unbox(v_bi_3420_);
v_kind_boxed_3432_ = lean_unbox(v_kind_3423_);
v_res_3433_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(v_name_3419_, v_bi_boxed_3431_, v_type_3421_, v_k_3422_, v_kind_boxed_3432_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(lean_object* v_name_3434_, lean_object* v_type_3435_, lean_object* v_k_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_){
_start:
{
uint8_t v___x_3444_; uint8_t v___x_3445_; lean_object* v___x_3446_; 
v___x_3444_ = 0;
v___x_3445_ = 0;
v___x_3446_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(v_name_3434_, v___x_3444_, v_type_3435_, v_k_3436_, v___x_3445_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
return v___x_3446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___boxed(lean_object* v_name_3447_, lean_object* v_type_3448_, lean_object* v_k_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_){
_start:
{
lean_object* v_res_3457_; 
v_res_3457_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_name_3447_, v_type_3448_, v_k_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_);
lean_dec(v___y_3455_);
lean_dec_ref(v___y_3454_);
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
return v_res_3457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(lean_object* v_x_3471_, lean_object* v_F_3472_, lean_object* v_val_3473_, lean_object* v_k_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_){
_start:
{
lean_object* v___x_3482_; uint8_t v___y_3484_; uint8_t v___x_3598_; 
v___x_3482_ = l_Lean_instInhabitedExpr;
v___x_3598_ = l_Lean_Expr_isFVar(v_x_3471_);
if (v___x_3598_ == 0)
{
v___y_3484_ = v___x_3598_;
goto v___jp_3483_;
}
else
{
lean_object* v___x_3599_; lean_object* v___x_3600_; uint8_t v___x_3601_; 
v___x_3599_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6));
v___x_3600_ = lean_unsigned_to_nat(6u);
v___x_3601_ = l_Lean_Expr_isAppOfArity(v_val_3473_, v___x_3599_, v___x_3600_);
v___y_3484_ = v___x_3601_;
goto v___jp_3483_;
}
v___jp_3483_:
{
if (v___y_3484_ == 0)
{
lean_object* v___x_3485_; 
lean_inc(v_a_3480_);
lean_inc_ref(v_a_3479_);
lean_inc(v_a_3478_);
lean_inc_ref(v_a_3477_);
lean_inc(v_a_3476_);
lean_inc_ref(v_a_3475_);
v___x_3485_ = lean_apply_10(v_k_3474_, v_x_3471_, v_F_3472_, v_val_3473_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, lean_box(0));
return v___x_3485_;
}
else
{
lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; uint8_t v___x_3492_; 
v___x_3486_ = lean_unsigned_to_nat(3u);
v___x_3487_ = l_Lean_Expr_getAppNumArgs(v_val_3473_);
v___x_3488_ = lean_nat_sub(v___x_3487_, v___x_3486_);
v___x_3489_ = lean_unsigned_to_nat(1u);
v___x_3490_ = lean_nat_sub(v___x_3488_, v___x_3489_);
lean_dec(v___x_3488_);
v___x_3491_ = l_Lean_Expr_getRevArg_x21(v_val_3473_, v___x_3490_);
v___x_3492_ = lean_expr_eqv(v___x_3491_, v_x_3471_);
lean_dec_ref(v___x_3491_);
if (v___x_3492_ == 0)
{
lean_object* v___x_3493_; 
lean_dec(v___x_3487_);
lean_inc(v_a_3480_);
lean_inc_ref(v_a_3479_);
lean_inc(v_a_3478_);
lean_inc_ref(v_a_3477_);
lean_inc(v_a_3476_);
lean_inc_ref(v_a_3475_);
v___x_3493_ = lean_apply_10(v_k_3474_, v_x_3471_, v_F_3472_, v_val_3473_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, lean_box(0));
return v___x_3493_;
}
else
{
lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; uint8_t v___x_3498_; 
v___x_3494_ = lean_unsigned_to_nat(4u);
v___x_3495_ = lean_nat_sub(v___x_3487_, v___x_3494_);
v___x_3496_ = lean_nat_sub(v___x_3495_, v___x_3489_);
lean_dec(v___x_3495_);
v___x_3497_ = l_Lean_Expr_getRevArg_x21(v_val_3473_, v___x_3496_);
v___x_3498_ = l_Lean_Expr_isLambda(v___x_3497_);
lean_dec_ref(v___x_3497_);
if (v___x_3498_ == 0)
{
lean_object* v___x_3499_; 
lean_dec(v___x_3487_);
lean_inc(v_a_3480_);
lean_inc_ref(v_a_3479_);
lean_inc(v_a_3478_);
lean_inc_ref(v_a_3477_);
lean_inc(v_a_3476_);
lean_inc_ref(v_a_3475_);
v___x_3499_ = lean_apply_10(v_k_3474_, v_x_3471_, v_F_3472_, v_val_3473_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, lean_box(0));
return v___x_3499_;
}
else
{
lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; uint8_t v___x_3504_; 
v___x_3500_ = lean_unsigned_to_nat(5u);
v___x_3501_ = lean_nat_sub(v___x_3487_, v___x_3500_);
v___x_3502_ = lean_nat_sub(v___x_3501_, v___x_3489_);
lean_dec(v___x_3501_);
v___x_3503_ = l_Lean_Expr_getRevArg_x21(v_val_3473_, v___x_3502_);
v___x_3504_ = l_Lean_Expr_isLambda(v___x_3503_);
lean_dec_ref(v___x_3503_);
if (v___x_3504_ == 0)
{
lean_object* v___x_3505_; 
lean_dec(v___x_3487_);
lean_inc(v_a_3480_);
lean_inc_ref(v_a_3479_);
lean_inc(v_a_3478_);
lean_inc_ref(v_a_3477_);
lean_inc(v_a_3476_);
lean_inc_ref(v_a_3475_);
v___x_3505_ = lean_apply_10(v_k_3474_, v_x_3471_, v_F_3472_, v_val_3473_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, lean_box(0));
return v___x_3505_;
}
else
{
lean_object* v___x_3506_; lean_object* v___x_3507_; 
v___x_3506_ = l_Lean_Expr_fvarId_x21(v_F_3472_);
v___x_3507_ = l_Lean_FVarId_getDecl___redArg(v___x_3506_, v_a_3477_, v_a_3479_, v_a_3480_);
if (lean_obj_tag(v___x_3507_) == 0)
{
lean_object* v_a_3508_; lean_object* v_dummy_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v_args_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___f_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; uint8_t v___x_3518_; lean_object* v___x_3519_; 
v_a_3508_ = lean_ctor_get(v___x_3507_, 0);
lean_inc_n(v_a_3508_, 2);
lean_dec_ref_known(v___x_3507_, 1);
v_dummy_3509_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_3487_);
v___x_3510_ = lean_mk_array(v___x_3487_, v_dummy_3509_);
v___x_3511_ = lean_nat_sub(v___x_3487_, v___x_3489_);
lean_dec(v___x_3487_);
v_args_3512_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_3473_, v___x_3510_, v___x_3511_);
v___x_3513_ = lean_unsigned_to_nat(0u);
v___x_3514_ = lean_box(v___x_3498_);
lean_inc_ref(v_x_3471_);
v___f_3515_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed), 14, 5);
lean_closure_set(v___f_3515_, 0, v_a_3508_);
lean_closure_set(v___f_3515_, 1, v___x_3482_);
lean_closure_set(v___f_3515_, 2, v___x_3513_);
lean_closure_set(v___f_3515_, 3, v_x_3471_);
lean_closure_set(v___f_3515_, 4, v___x_3514_);
v___x_3516_ = lean_unsigned_to_nat(2u);
v___x_3517_ = lean_array_get(v___x_3482_, v_args_3512_, v___x_3516_);
v___x_3518_ = 0;
v___x_3519_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_3517_, v___f_3515_, v___x_3518_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_);
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v_a_3520_; lean_object* v_fst_3521_; lean_object* v_snd_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3581_; 
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
lean_inc(v_a_3520_);
lean_dec_ref_known(v___x_3519_, 1);
v_fst_3521_ = lean_ctor_get(v_a_3520_, 0);
v_snd_3522_ = lean_ctor_get(v_a_3520_, 1);
v_isSharedCheck_3581_ = !lean_is_exclusive(v_a_3520_);
if (v_isSharedCheck_3581_ == 0)
{
v___x_3524_ = v_a_3520_;
v_isShared_3525_ = v_isSharedCheck_3581_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_snd_3522_);
lean_inc(v_fst_3521_);
lean_dec(v_a_3520_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3581_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v_00_u03b1_3526_; lean_object* v_00_u03b2_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; 
v_00_u03b1_3526_ = lean_array_get(v___x_3482_, v_args_3512_, v___x_3513_);
v_00_u03b2_3527_ = lean_array_get(v___x_3482_, v_args_3512_, v___x_3489_);
v___x_3528_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__2));
v___x_3529_ = lean_array_get(v___x_3482_, v_args_3512_, v___x_3494_);
lean_inc_ref(v_x_3471_);
lean_inc(v_a_3508_);
lean_inc_ref(v_k_3474_);
lean_inc(v_00_u03b2_3527_);
lean_inc(v_00_u03b1_3526_);
v___x_3530_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3482_, v___x_3513_, v_00_u03b1_3526_, v_00_u03b2_3527_, v___x_3486_, v_k_3474_, v___x_3516_, v___x_3518_, v___x_3498_, v_a_3508_, v_x_3471_, v___x_3489_, v___x_3528_, v___x_3529_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_);
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v_a_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; 
v_a_3531_ = lean_ctor_get(v___x_3530_, 0);
lean_inc(v_a_3531_);
lean_dec_ref_known(v___x_3530_, 1);
v___x_3532_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__4));
v___x_3533_ = lean_array_get(v___x_3482_, v_args_3512_, v___x_3500_);
lean_dec_ref(v_args_3512_);
lean_inc_ref(v_x_3471_);
lean_inc(v_00_u03b2_3527_);
lean_inc(v_00_u03b1_3526_);
v___x_3534_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3482_, v___x_3513_, v_00_u03b1_3526_, v_00_u03b2_3527_, v___x_3486_, v_k_3474_, v___x_3516_, v___x_3518_, v___x_3498_, v_a_3508_, v_x_3471_, v___x_3489_, v___x_3532_, v___x_3533_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_);
if (lean_obj_tag(v___x_3534_) == 0)
{
lean_object* v_a_3535_; lean_object* v___x_3536_; 
v_a_3535_ = lean_ctor_get(v___x_3534_, 0);
lean_inc(v_a_3535_);
lean_dec_ref_known(v___x_3534_, 1);
lean_inc(v_00_u03b1_3526_);
v___x_3536_ = l_Lean_Meta_getLevel(v_00_u03b1_3526_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_);
if (lean_obj_tag(v___x_3536_) == 0)
{
lean_object* v_a_3537_; lean_object* v___x_3538_; 
v_a_3537_ = lean_ctor_get(v___x_3536_, 0);
lean_inc(v_a_3537_);
lean_dec_ref_known(v___x_3536_, 1);
lean_inc(v_00_u03b2_3527_);
v___x_3538_ = l_Lean_Meta_getLevel(v_00_u03b2_3527_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_);
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3564_; 
v_a_3539_ = lean_ctor_get(v___x_3538_, 0);
v_isSharedCheck_3564_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3541_ = v___x_3538_;
v_isShared_3542_ = v_isSharedCheck_3564_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___x_3538_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3564_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3546_; 
v___x_3543_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6));
v___x_3544_ = lean_box(0);
if (v_isShared_3525_ == 0)
{
lean_ctor_set_tag(v___x_3524_, 1);
lean_ctor_set(v___x_3524_, 1, v___x_3544_);
lean_ctor_set(v___x_3524_, 0, v_a_3539_);
v___x_3546_ = v___x_3524_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v_a_3539_);
lean_ctor_set(v_reuseFailAlloc_3563_, 1, v___x_3544_);
v___x_3546_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3561_; 
v___x_3547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3547_, 0, v_a_3537_);
lean_ctor_set(v___x_3547_, 1, v___x_3546_);
v___x_3548_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3548_, 0, v_snd_3522_);
lean_ctor_set(v___x_3548_, 1, v___x_3547_);
v___x_3549_ = l_Lean_mkConst(v___x_3543_, v___x_3548_);
v___x_3550_ = lean_unsigned_to_nat(7u);
v___x_3551_ = lean_mk_empty_array_with_capacity(v___x_3550_);
v___x_3552_ = lean_array_push(v___x_3551_, v_00_u03b1_3526_);
v___x_3553_ = lean_array_push(v___x_3552_, v_00_u03b2_3527_);
v___x_3554_ = lean_array_push(v___x_3553_, v_fst_3521_);
v___x_3555_ = lean_array_push(v___x_3554_, v_x_3471_);
v___x_3556_ = lean_array_push(v___x_3555_, v_a_3531_);
v___x_3557_ = lean_array_push(v___x_3556_, v_a_3535_);
v___x_3558_ = lean_array_push(v___x_3557_, v_F_3472_);
v___x_3559_ = l_Lean_mkAppN(v___x_3549_, v___x_3558_);
lean_dec_ref(v___x_3558_);
if (v_isShared_3542_ == 0)
{
lean_ctor_set(v___x_3541_, 0, v___x_3559_);
v___x_3561_ = v___x_3541_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v___x_3559_);
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
lean_object* v_a_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3572_; 
lean_dec(v_a_3537_);
lean_dec(v_a_3535_);
lean_dec(v_a_3531_);
lean_dec(v_00_u03b2_3527_);
lean_dec(v_00_u03b1_3526_);
lean_del_object(v___x_3524_);
lean_dec(v_snd_3522_);
lean_dec(v_fst_3521_);
lean_dec_ref(v_F_3472_);
lean_dec_ref(v_x_3471_);
v_a_3565_ = lean_ctor_get(v___x_3538_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3567_ = v___x_3538_;
v_isShared_3568_ = v_isSharedCheck_3572_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_a_3565_);
lean_dec(v___x_3538_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3572_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v___x_3570_; 
if (v_isShared_3568_ == 0)
{
v___x_3570_ = v___x_3567_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v_a_3565_);
v___x_3570_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
return v___x_3570_;
}
}
}
}
else
{
lean_object* v_a_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3580_; 
lean_dec(v_a_3535_);
lean_dec(v_a_3531_);
lean_dec(v_00_u03b2_3527_);
lean_dec(v_00_u03b1_3526_);
lean_del_object(v___x_3524_);
lean_dec(v_snd_3522_);
lean_dec(v_fst_3521_);
lean_dec_ref(v_F_3472_);
lean_dec_ref(v_x_3471_);
v_a_3573_ = lean_ctor_get(v___x_3536_, 0);
v_isSharedCheck_3580_ = !lean_is_exclusive(v___x_3536_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3575_ = v___x_3536_;
v_isShared_3576_ = v_isSharedCheck_3580_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_a_3573_);
lean_dec(v___x_3536_);
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
}
else
{
lean_dec(v_a_3531_);
lean_dec(v_00_u03b2_3527_);
lean_dec(v_00_u03b1_3526_);
lean_del_object(v___x_3524_);
lean_dec(v_snd_3522_);
lean_dec(v_fst_3521_);
lean_dec_ref(v_F_3472_);
lean_dec_ref(v_x_3471_);
return v___x_3534_;
}
}
else
{
lean_dec(v_00_u03b2_3527_);
lean_dec(v_00_u03b1_3526_);
lean_del_object(v___x_3524_);
lean_dec(v_snd_3522_);
lean_dec(v_fst_3521_);
lean_dec_ref(v_args_3512_);
lean_dec(v_a_3508_);
lean_dec_ref(v_k_3474_);
lean_dec_ref(v_F_3472_);
lean_dec_ref(v_x_3471_);
return v___x_3530_;
}
}
}
else
{
lean_object* v_a_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3589_; 
lean_dec_ref(v_args_3512_);
lean_dec(v_a_3508_);
lean_dec_ref(v_k_3474_);
lean_dec_ref(v_F_3472_);
lean_dec_ref(v_x_3471_);
v_a_3582_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3589_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3589_ == 0)
{
v___x_3584_ = v___x_3519_;
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_a_3582_);
lean_dec(v___x_3519_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___x_3587_; 
if (v_isShared_3585_ == 0)
{
v___x_3587_ = v___x_3584_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_a_3582_);
v___x_3587_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
return v___x_3587_;
}
}
}
}
else
{
lean_object* v_a_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3597_; 
lean_dec(v___x_3487_);
lean_dec_ref(v_k_3474_);
lean_dec_ref(v_val_3473_);
lean_dec_ref(v_F_3472_);
lean_dec_ref(v_x_3471_);
v_a_3590_ = lean_ctor_get(v___x_3507_, 0);
v_isSharedCheck_3597_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3592_ = v___x_3507_;
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_a_3590_);
lean_dec(v___x_3507_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3595_; 
if (v_isShared_3593_ == 0)
{
v___x_3595_ = v___x_3592_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_a_3590_);
v___x_3595_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
return v___x_3595_;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1(lean_object* v___x_3602_, lean_object* v_body_3603_, lean_object* v_k_3604_, lean_object* v___x_3605_, uint8_t v___x_3606_, uint8_t v___x_3607_, lean_object* v_FNew_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_){
_start:
{
lean_object* v___x_3616_; 
lean_inc_ref(v_FNew_3608_);
lean_inc_ref(v___x_3602_);
v___x_3616_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v___x_3602_, v_FNew_3608_, v_body_3603_, v_k_3604_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_);
if (lean_obj_tag(v___x_3616_) == 0)
{
lean_object* v_a_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; uint8_t v___x_3621_; lean_object* v___x_3622_; 
v_a_3617_ = lean_ctor_get(v___x_3616_, 0);
lean_inc(v_a_3617_);
lean_dec_ref_known(v___x_3616_, 1);
v___x_3618_ = lean_mk_empty_array_with_capacity(v___x_3605_);
v___x_3619_ = lean_array_push(v___x_3618_, v___x_3602_);
v___x_3620_ = lean_array_push(v___x_3619_, v_FNew_3608_);
v___x_3621_ = 1;
v___x_3622_ = l_Lean_Meta_mkLambdaFVars(v___x_3620_, v_a_3617_, v___x_3606_, v___x_3607_, v___x_3606_, v___x_3607_, v___x_3621_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_);
lean_dec_ref(v___x_3620_);
return v___x_3622_;
}
else
{
lean_dec_ref(v_FNew_3608_);
lean_dec_ref(v___x_3602_);
return v___x_3616_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1___boxed(lean_object* v___x_3623_, lean_object* v_body_3624_, lean_object* v_k_3625_, lean_object* v___x_3626_, lean_object* v___x_3627_, lean_object* v___x_3628_, lean_object* v_FNew_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_){
_start:
{
uint8_t v___x_6490__boxed_3637_; uint8_t v___x_6491__boxed_3638_; lean_object* v_res_3639_; 
v___x_6490__boxed_3637_ = lean_unbox(v___x_3627_);
v___x_6491__boxed_3638_ = lean_unbox(v___x_3628_);
v_res_3639_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1(v___x_3623_, v_body_3624_, v_k_3625_, v___x_3626_, v___x_6490__boxed_3637_, v___x_6491__boxed_3638_, v_FNew_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
lean_dec(v___y_3631_);
lean_dec_ref(v___y_3630_);
lean_dec(v___x_3626_);
return v_res_3639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2(lean_object* v___x_3640_, lean_object* v___x_3641_, lean_object* v_00_u03b1_3642_, lean_object* v_00_u03b2_3643_, lean_object* v___x_3644_, lean_object* v_ctorName_3645_, lean_object* v_k_3646_, lean_object* v___x_3647_, uint8_t v___x_3648_, uint8_t v___x_3649_, lean_object* v_a_3650_, lean_object* v_x_3651_, lean_object* v_xs_3652_, lean_object* v_body_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_){
_start:
{
lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; 
v___x_3661_ = lean_array_get_borrowed(v___x_3640_, v_xs_3652_, v___x_3641_);
v___x_3662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3662_, 0, v_00_u03b1_3642_);
v___x_3663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3663_, 0, v_00_u03b2_3643_);
lean_inc(v___x_3661_);
v___x_3664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3661_);
v___x_3665_ = lean_mk_empty_array_with_capacity(v___x_3644_);
v___x_3666_ = lean_array_push(v___x_3665_, v___x_3662_);
v___x_3667_ = lean_array_push(v___x_3666_, v___x_3663_);
v___x_3668_ = lean_array_push(v___x_3667_, v___x_3664_);
v___x_3669_ = l_Lean_Meta_mkAppOptM(v_ctorName_3645_, v___x_3668_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_);
if (lean_obj_tag(v___x_3669_) == 0)
{
lean_object* v_a_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___f_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; 
v_a_3670_ = lean_ctor_get(v___x_3669_, 0);
lean_inc(v_a_3670_);
lean_dec_ref_known(v___x_3669_, 1);
v___x_3671_ = lean_box(v___x_3648_);
v___x_3672_ = lean_box(v___x_3649_);
lean_inc(v___x_3661_);
v___f_3673_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1___boxed), 14, 6);
lean_closure_set(v___f_3673_, 0, v___x_3661_);
lean_closure_set(v___f_3673_, 1, v_body_3653_);
lean_closure_set(v___f_3673_, 2, v_k_3646_);
lean_closure_set(v___f_3673_, 3, v___x_3647_);
lean_closure_set(v___f_3673_, 4, v___x_3671_);
lean_closure_set(v___f_3673_, 5, v___x_3672_);
v___x_3674_ = l_Lean_LocalDecl_type(v_a_3650_);
v___x_3675_ = l_Lean_Expr_replaceFVar(v___x_3674_, v_x_3651_, v_a_3670_);
lean_dec(v_a_3670_);
lean_dec_ref(v___x_3674_);
v___x_3676_ = l_Lean_LocalDecl_userName(v_a_3650_);
v___x_3677_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v___x_3676_, v___x_3675_, v___f_3673_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_);
return v___x_3677_;
}
else
{
lean_dec_ref(v_body_3653_);
lean_dec_ref(v_x_3651_);
lean_dec(v___x_3647_);
lean_dec_ref(v_k_3646_);
return v___x_3669_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2___boxed(lean_object** _args){
lean_object* v___x_3678_ = _args[0];
lean_object* v___x_3679_ = _args[1];
lean_object* v_00_u03b1_3680_ = _args[2];
lean_object* v_00_u03b2_3681_ = _args[3];
lean_object* v___x_3682_ = _args[4];
lean_object* v_ctorName_3683_ = _args[5];
lean_object* v_k_3684_ = _args[6];
lean_object* v___x_3685_ = _args[7];
lean_object* v___x_3686_ = _args[8];
lean_object* v___x_3687_ = _args[9];
lean_object* v_a_3688_ = _args[10];
lean_object* v_x_3689_ = _args[11];
lean_object* v_xs_3690_ = _args[12];
lean_object* v_body_3691_ = _args[13];
lean_object* v___y_3692_ = _args[14];
lean_object* v___y_3693_ = _args[15];
lean_object* v___y_3694_ = _args[16];
lean_object* v___y_3695_ = _args[17];
lean_object* v___y_3696_ = _args[18];
lean_object* v___y_3697_ = _args[19];
lean_object* v___y_3698_ = _args[20];
_start:
{
uint8_t v___x_6511__boxed_3699_; uint8_t v___x_6512__boxed_3700_; lean_object* v_res_3701_; 
v___x_6511__boxed_3699_ = lean_unbox(v___x_3686_);
v___x_6512__boxed_3700_ = lean_unbox(v___x_3687_);
v_res_3701_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2(v___x_3678_, v___x_3679_, v_00_u03b1_3680_, v_00_u03b2_3681_, v___x_3682_, v_ctorName_3683_, v_k_3684_, v___x_3685_, v___x_6511__boxed_3699_, v___x_6512__boxed_3700_, v_a_3688_, v_x_3689_, v_xs_3690_, v_body_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_);
lean_dec(v___y_3697_);
lean_dec_ref(v___y_3696_);
lean_dec(v___y_3695_);
lean_dec_ref(v___y_3694_);
lean_dec(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec_ref(v_xs_3690_);
lean_dec_ref(v_a_3688_);
lean_dec(v___x_3682_);
lean_dec(v___x_3679_);
lean_dec_ref(v___x_3678_);
return v_res_3701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(lean_object* v___x_3702_, lean_object* v___x_3703_, lean_object* v_00_u03b1_3704_, lean_object* v_00_u03b2_3705_, lean_object* v___x_3706_, lean_object* v_k_3707_, lean_object* v___x_3708_, uint8_t v___x_3709_, uint8_t v___x_3710_, lean_object* v_a_3711_, lean_object* v_x_3712_, lean_object* v___x_3713_, lean_object* v_ctorName_3714_, lean_object* v_minor_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_){
_start:
{
lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___f_3725_; lean_object* v___x_3726_; 
v___x_3723_ = lean_box(v___x_3709_);
v___x_3724_ = lean_box(v___x_3710_);
v___f_3725_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2___boxed), 21, 12);
lean_closure_set(v___f_3725_, 0, v___x_3702_);
lean_closure_set(v___f_3725_, 1, v___x_3703_);
lean_closure_set(v___f_3725_, 2, v_00_u03b1_3704_);
lean_closure_set(v___f_3725_, 3, v_00_u03b2_3705_);
lean_closure_set(v___f_3725_, 4, v___x_3706_);
lean_closure_set(v___f_3725_, 5, v_ctorName_3714_);
lean_closure_set(v___f_3725_, 6, v_k_3707_);
lean_closure_set(v___f_3725_, 7, v___x_3708_);
lean_closure_set(v___f_3725_, 8, v___x_3723_);
lean_closure_set(v___f_3725_, 9, v___x_3724_);
lean_closure_set(v___f_3725_, 10, v_a_3711_);
lean_closure_set(v___f_3725_, 11, v_x_3712_);
v___x_3726_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_minor_3715_, v___x_3713_, v___f_3725_, v___x_3709_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_);
return v___x_3726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3___boxed(lean_object** _args){
lean_object* v___x_3727_ = _args[0];
lean_object* v___x_3728_ = _args[1];
lean_object* v_00_u03b1_3729_ = _args[2];
lean_object* v_00_u03b2_3730_ = _args[3];
lean_object* v___x_3731_ = _args[4];
lean_object* v_k_3732_ = _args[5];
lean_object* v___x_3733_ = _args[6];
lean_object* v___x_3734_ = _args[7];
lean_object* v___x_3735_ = _args[8];
lean_object* v_a_3736_ = _args[9];
lean_object* v_x_3737_ = _args[10];
lean_object* v___x_3738_ = _args[11];
lean_object* v_ctorName_3739_ = _args[12];
lean_object* v_minor_3740_ = _args[13];
lean_object* v___y_3741_ = _args[14];
lean_object* v___y_3742_ = _args[15];
lean_object* v___y_3743_ = _args[16];
lean_object* v___y_3744_ = _args[17];
lean_object* v___y_3745_ = _args[18];
lean_object* v___y_3746_ = _args[19];
lean_object* v___y_3747_ = _args[20];
_start:
{
uint8_t v___x_6475__boxed_3748_; uint8_t v___x_6476__boxed_3749_; lean_object* v_res_3750_; 
v___x_6475__boxed_3748_ = lean_unbox(v___x_3734_);
v___x_6476__boxed_3749_ = lean_unbox(v___x_3735_);
v_res_3750_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3727_, v___x_3728_, v_00_u03b1_3729_, v_00_u03b2_3730_, v___x_3731_, v_k_3732_, v___x_3733_, v___x_6475__boxed_3748_, v___x_6476__boxed_3749_, v_a_3736_, v_x_3737_, v___x_3738_, v_ctorName_3739_, v_minor_3740_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_);
lean_dec(v___y_3746_);
lean_dec_ref(v___y_3745_);
lean_dec(v___y_3744_);
lean_dec_ref(v___y_3743_);
lean_dec(v___y_3742_);
lean_dec_ref(v___y_3741_);
return v_res_3750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___boxed(lean_object* v_x_3751_, lean_object* v_F_3752_, lean_object* v_val_3753_, lean_object* v_k_3754_, lean_object* v_a_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_){
_start:
{
lean_object* v_res_3762_; 
v_res_3762_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v_x_3751_, v_F_3752_, v_val_3753_, v_k_3754_, v_a_3755_, v_a_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_);
lean_dec(v_a_3760_);
lean_dec_ref(v_a_3759_);
lean_dec(v_a_3758_);
lean_dec_ref(v_a_3757_);
lean_dec(v_a_3756_);
lean_dec_ref(v_a_3755_);
return v_res_3762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1(lean_object* v_00_u03b1_3763_, lean_object* v_name_3764_, uint8_t v_bi_3765_, lean_object* v_type_3766_, lean_object* v_k_3767_, uint8_t v_kind_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_){
_start:
{
lean_object* v___x_3776_; 
v___x_3776_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(v_name_3764_, v_bi_3765_, v_type_3766_, v_k_3767_, v_kind_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_);
return v___x_3776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___boxed(lean_object* v_00_u03b1_3777_, lean_object* v_name_3778_, lean_object* v_bi_3779_, lean_object* v_type_3780_, lean_object* v_k_3781_, lean_object* v_kind_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_){
_start:
{
uint8_t v_bi_boxed_3790_; uint8_t v_kind_boxed_3791_; lean_object* v_res_3792_; 
v_bi_boxed_3790_ = lean_unbox(v_bi_3779_);
v_kind_boxed_3791_ = lean_unbox(v_kind_3782_);
v_res_3792_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1(v_00_u03b1_3777_, v_name_3778_, v_bi_boxed_3790_, v_type_3780_, v_k_3781_, v_kind_boxed_3791_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_);
lean_dec(v___y_3788_);
lean_dec_ref(v___y_3787_);
lean_dec(v___y_3786_);
lean_dec_ref(v___y_3785_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3783_);
return v_res_3792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1(lean_object* v_00_u03b1_3793_, lean_object* v_name_3794_, lean_object* v_type_3795_, lean_object* v_k_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_){
_start:
{
lean_object* v___x_3804_; 
v___x_3804_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_name_3794_, v_type_3795_, v_k_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_);
return v___x_3804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___boxed(lean_object* v_00_u03b1_3805_, lean_object* v_name_3806_, lean_object* v_type_3807_, lean_object* v_k_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_){
_start:
{
lean_object* v_res_3816_; 
v_res_3816_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1(v_00_u03b1_3805_, v_name_3806_, v_type_3807_, v_k_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_);
lean_dec(v___y_3814_);
lean_dec_ref(v___y_3813_);
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3811_);
lean_dec(v___y_3810_);
lean_dec_ref(v___y_3809_);
return v_res_3816_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3817_; 
v___x_3817_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return v___x_3817_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(lean_object* v_msg_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_){
_start:
{
lean_object* v___x_3826_; lean_object* v___x_3331__overap_3827_; lean_object* v___x_3828_; 
v___x_3826_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0, &l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0);
v___x_3331__overap_3827_ = lean_panic_fn_borrowed(v___x_3826_, v_msg_3818_);
lean_inc(v___y_3824_);
lean_inc_ref(v___y_3823_);
lean_inc(v___y_3822_);
lean_inc_ref(v___y_3821_);
lean_inc(v___y_3820_);
lean_inc_ref(v___y_3819_);
v___x_3828_ = lean_apply_7(v___x_3331__overap_3827_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, lean_box(0));
return v___x_3828_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___boxed(lean_object* v_msg_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_){
_start:
{
lean_object* v_res_3837_; 
v_res_3837_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(v_msg_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
return v_res_3837_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3(void){
_start:
{
lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; 
v___x_3841_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__2));
v___x_3842_ = lean_unsigned_to_nat(49u);
v___x_3843_ = lean_unsigned_to_nat(186u);
v___x_3844_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__1));
v___x_3845_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__0));
v___x_3846_ = l_mkPanicMessageWithDecl(v___x_3845_, v___x_3844_, v___x_3843_, v___x_3842_, v___x_3841_);
return v___x_3846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1___boxed(lean_object* v___x_3852_, lean_object* v_a_3853_, lean_object* v_k_3854_, lean_object* v___x_3855_, lean_object* v___x_3856_, lean_object* v___x_3857_, lean_object* v___x_3858_, lean_object* v___x_3859_, lean_object* v_FNew_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_){
_start:
{
uint8_t v___x_3499__boxed_3868_; uint8_t v___x_3500__boxed_3869_; uint8_t v___x_3501__boxed_3870_; lean_object* v_res_3871_; 
v___x_3499__boxed_3868_ = lean_unbox(v___x_3857_);
v___x_3500__boxed_3869_ = lean_unbox(v___x_3858_);
v___x_3501__boxed_3870_ = lean_unbox(v___x_3859_);
v_res_3871_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1(v___x_3852_, v_a_3853_, v_k_3854_, v___x_3855_, v___x_3856_, v___x_3499__boxed_3868_, v___x_3500__boxed_3869_, v___x_3501__boxed_3870_, v_FNew_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_);
lean_dec(v___y_3866_);
lean_dec_ref(v___y_3865_);
lean_dec(v___y_3864_);
lean_dec_ref(v___y_3863_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
lean_dec(v___x_3855_);
return v_res_3871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0(lean_object* v___x_3872_, lean_object* v___x_3873_, lean_object* v___x_3874_, lean_object* v___x_3875_, uint8_t v___x_3876_, uint8_t v___x_3877_, lean_object* v_00_u03b1_3878_, lean_object* v_00_u03b2_3879_, lean_object* v___x_3880_, lean_object* v_k_3881_, lean_object* v___x_3882_, lean_object* v_a_3883_, lean_object* v_x_3884_, lean_object* v_xs_3885_, lean_object* v_body_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_){
_start:
{
lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; uint8_t v___x_3899_; lean_object* v___x_3900_; 
v___x_3894_ = lean_array_get(v___x_3872_, v_xs_3885_, v___x_3873_);
v___x_3895_ = lean_array_get(v___x_3872_, v_xs_3885_, v___x_3874_);
v___x_3896_ = lean_array_get_size(v_xs_3885_);
v___x_3897_ = l_Array_toSubarray___redArg(v_xs_3885_, v___x_3875_, v___x_3896_);
v___x_3898_ = l_Subarray_copy___redArg(v___x_3897_);
v___x_3899_ = 1;
v___x_3900_ = l_Lean_Meta_mkLambdaFVars(v___x_3898_, v_body_3886_, v___x_3876_, v___x_3877_, v___x_3876_, v___x_3877_, v___x_3899_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_);
lean_dec_ref(v___x_3898_);
if (lean_obj_tag(v___x_3900_) == 0)
{
lean_object* v_a_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3927_; 
v_a_3901_ = lean_ctor_get(v___x_3900_, 0);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___x_3900_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3903_ = v___x_3900_;
v_isShared_3904_ = v_isSharedCheck_3927_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_a_3901_);
lean_dec(v___x_3900_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3927_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3905_; lean_object* v___x_3907_; 
v___x_3905_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__2));
if (v_isShared_3904_ == 0)
{
lean_ctor_set_tag(v___x_3903_, 1);
lean_ctor_set(v___x_3903_, 0, v_00_u03b1_3878_);
v___x_3907_ = v___x_3903_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_00_u03b1_3878_);
v___x_3907_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; 
v___x_3908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3908_, 0, v_00_u03b2_3879_);
lean_inc(v___x_3894_);
v___x_3909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3894_);
lean_inc(v___x_3895_);
v___x_3910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3910_, 0, v___x_3895_);
v___x_3911_ = lean_mk_empty_array_with_capacity(v___x_3880_);
v___x_3912_ = lean_array_push(v___x_3911_, v___x_3907_);
v___x_3913_ = lean_array_push(v___x_3912_, v___x_3908_);
v___x_3914_ = lean_array_push(v___x_3913_, v___x_3909_);
v___x_3915_ = lean_array_push(v___x_3914_, v___x_3910_);
v___x_3916_ = l_Lean_Meta_mkAppOptM(v___x_3905_, v___x_3915_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_);
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_object* v_a_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___f_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; 
v_a_3917_ = lean_ctor_get(v___x_3916_, 0);
lean_inc(v_a_3917_);
lean_dec_ref_known(v___x_3916_, 1);
v___x_3918_ = lean_box(v___x_3876_);
v___x_3919_ = lean_box(v___x_3877_);
v___x_3920_ = lean_box(v___x_3899_);
v___f_3921_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1___boxed), 16, 8);
lean_closure_set(v___f_3921_, 0, v___x_3895_);
lean_closure_set(v___f_3921_, 1, v_a_3901_);
lean_closure_set(v___f_3921_, 2, v_k_3881_);
lean_closure_set(v___f_3921_, 3, v___x_3882_);
lean_closure_set(v___f_3921_, 4, v___x_3894_);
lean_closure_set(v___f_3921_, 5, v___x_3918_);
lean_closure_set(v___f_3921_, 6, v___x_3919_);
lean_closure_set(v___f_3921_, 7, v___x_3920_);
v___x_3922_ = l_Lean_LocalDecl_type(v_a_3883_);
v___x_3923_ = l_Lean_Expr_replaceFVar(v___x_3922_, v_x_3884_, v_a_3917_);
lean_dec(v_a_3917_);
lean_dec_ref(v___x_3922_);
v___x_3924_ = l_Lean_LocalDecl_userName(v_a_3883_);
v___x_3925_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v___x_3924_, v___x_3923_, v___f_3921_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_);
return v___x_3925_;
}
else
{
lean_dec(v_a_3901_);
lean_dec(v___x_3895_);
lean_dec(v___x_3894_);
lean_dec_ref(v_x_3884_);
lean_dec(v___x_3882_);
lean_dec_ref(v_k_3881_);
return v___x_3916_;
}
}
}
}
else
{
lean_dec(v___x_3895_);
lean_dec(v___x_3894_);
lean_dec_ref(v_x_3884_);
lean_dec(v___x_3882_);
lean_dec_ref(v_k_3881_);
lean_dec_ref(v_00_u03b2_3879_);
lean_dec_ref(v_00_u03b1_3878_);
return v___x_3900_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___boxed(lean_object** _args){
lean_object* v___x_3928_ = _args[0];
lean_object* v___x_3929_ = _args[1];
lean_object* v___x_3930_ = _args[2];
lean_object* v___x_3931_ = _args[3];
lean_object* v___x_3932_ = _args[4];
lean_object* v___x_3933_ = _args[5];
lean_object* v_00_u03b1_3934_ = _args[6];
lean_object* v_00_u03b2_3935_ = _args[7];
lean_object* v___x_3936_ = _args[8];
lean_object* v_k_3937_ = _args[9];
lean_object* v___x_3938_ = _args[10];
lean_object* v_a_3939_ = _args[11];
lean_object* v_x_3940_ = _args[12];
lean_object* v_xs_3941_ = _args[13];
lean_object* v_body_3942_ = _args[14];
lean_object* v___y_3943_ = _args[15];
lean_object* v___y_3944_ = _args[16];
lean_object* v___y_3945_ = _args[17];
lean_object* v___y_3946_ = _args[18];
lean_object* v___y_3947_ = _args[19];
lean_object* v___y_3948_ = _args[20];
lean_object* v___y_3949_ = _args[21];
_start:
{
uint8_t v___x_3526__boxed_3950_; uint8_t v___x_3527__boxed_3951_; lean_object* v_res_3952_; 
v___x_3526__boxed_3950_ = lean_unbox(v___x_3932_);
v___x_3527__boxed_3951_ = lean_unbox(v___x_3933_);
v_res_3952_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0(v___x_3928_, v___x_3929_, v___x_3930_, v___x_3931_, v___x_3526__boxed_3950_, v___x_3527__boxed_3951_, v_00_u03b1_3934_, v_00_u03b2_3935_, v___x_3936_, v_k_3937_, v___x_3938_, v_a_3939_, v_x_3940_, v_xs_3941_, v_body_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_);
lean_dec(v___y_3948_);
lean_dec_ref(v___y_3947_);
lean_dec(v___y_3946_);
lean_dec_ref(v___y_3945_);
lean_dec(v___y_3944_);
lean_dec_ref(v___y_3943_);
lean_dec_ref(v_a_3939_);
lean_dec(v___x_3936_);
lean_dec(v___x_3930_);
lean_dec(v___x_3929_);
lean_dec_ref(v___x_3928_);
return v_res_3952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(lean_object* v_x_3956_, lean_object* v_F_3957_, lean_object* v_val_3958_, lean_object* v_k_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_){
_start:
{
lean_object* v___y_3968_; lean_object* v___y_3969_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; lean_object* v___y_3973_; lean_object* v___x_3976_; uint8_t v___y_3978_; uint8_t v___x_4069_; 
v___x_3976_ = l_Lean_instInhabitedExpr;
v___x_4069_ = l_Lean_Expr_isFVar(v_x_3956_);
if (v___x_4069_ == 0)
{
v___y_3978_ = v___x_4069_;
goto v___jp_3977_;
}
else
{
lean_object* v___x_4070_; lean_object* v___x_4071_; uint8_t v___x_4072_; 
v___x_4070_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4));
v___x_4071_ = lean_unsigned_to_nat(5u);
v___x_4072_ = l_Lean_Expr_isAppOfArity(v_val_3958_, v___x_4070_, v___x_4071_);
v___y_3978_ = v___x_4072_;
goto v___jp_3977_;
}
v___jp_3967_:
{
lean_object* v___x_3974_; lean_object* v___x_3975_; 
v___x_3974_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3);
v___x_3975_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(v___x_3974_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_);
return v___x_3975_;
}
v___jp_3977_:
{
if (v___y_3978_ == 0)
{
lean_object* v___x_3979_; 
lean_dec_ref(v_x_3956_);
lean_inc(v_a_3965_);
lean_inc_ref(v_a_3964_);
lean_inc(v_a_3963_);
lean_inc_ref(v_a_3962_);
lean_inc(v_a_3961_);
lean_inc_ref(v_a_3960_);
v___x_3979_ = lean_apply_9(v_k_3959_, v_F_3957_, v_val_3958_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_, lean_box(0));
return v___x_3979_;
}
else
{
lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; uint8_t v___x_3986_; 
v___x_3980_ = lean_unsigned_to_nat(3u);
v___x_3981_ = l_Lean_Expr_getAppNumArgs(v_val_3958_);
v___x_3982_ = lean_nat_sub(v___x_3981_, v___x_3980_);
v___x_3983_ = lean_unsigned_to_nat(1u);
v___x_3984_ = lean_nat_sub(v___x_3982_, v___x_3983_);
lean_dec(v___x_3982_);
v___x_3985_ = l_Lean_Expr_getRevArg_x21(v_val_3958_, v___x_3984_);
v___x_3986_ = lean_expr_eqv(v___x_3985_, v_x_3956_);
lean_dec_ref(v___x_3985_);
if (v___x_3986_ == 0)
{
lean_object* v___x_3987_; 
lean_dec(v___x_3981_);
lean_dec_ref(v_x_3956_);
lean_inc(v_a_3965_);
lean_inc_ref(v_a_3964_);
lean_inc(v_a_3963_);
lean_inc_ref(v_a_3962_);
lean_inc(v_a_3961_);
lean_inc_ref(v_a_3960_);
v___x_3987_ = lean_apply_9(v_k_3959_, v_F_3957_, v_val_3958_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_, lean_box(0));
return v___x_3987_;
}
else
{
lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; uint8_t v___x_3992_; 
v___x_3988_ = lean_unsigned_to_nat(4u);
v___x_3989_ = lean_nat_sub(v___x_3981_, v___x_3988_);
v___x_3990_ = lean_nat_sub(v___x_3989_, v___x_3983_);
lean_dec(v___x_3989_);
v___x_3991_ = l_Lean_Expr_getRevArg_x21(v_val_3958_, v___x_3990_);
v___x_3992_ = l_Lean_Expr_isLambda(v___x_3991_);
if (v___x_3992_ == 0)
{
lean_object* v___x_3993_; 
lean_dec_ref(v___x_3991_);
lean_dec(v___x_3981_);
lean_dec_ref(v_x_3956_);
lean_inc(v_a_3965_);
lean_inc_ref(v_a_3964_);
lean_inc(v_a_3963_);
lean_inc_ref(v_a_3962_);
lean_inc(v_a_3961_);
lean_inc_ref(v_a_3960_);
v___x_3993_ = lean_apply_9(v_k_3959_, v_F_3957_, v_val_3958_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_, lean_box(0));
return v___x_3993_;
}
else
{
lean_object* v___x_3994_; uint8_t v___x_3995_; 
v___x_3994_ = l_Lean_Expr_bindingBody_x21(v___x_3991_);
lean_dec_ref(v___x_3991_);
v___x_3995_ = l_Lean_Expr_isLambda(v___x_3994_);
lean_dec_ref(v___x_3994_);
if (v___x_3995_ == 0)
{
lean_object* v___x_3996_; 
lean_dec(v___x_3981_);
lean_dec_ref(v_x_3956_);
lean_inc(v_a_3965_);
lean_inc_ref(v_a_3964_);
lean_inc(v_a_3963_);
lean_inc_ref(v_a_3962_);
lean_inc(v_a_3961_);
lean_inc_ref(v_a_3960_);
v___x_3996_ = lean_apply_9(v_k_3959_, v_F_3957_, v_val_3958_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_, lean_box(0));
return v___x_3996_;
}
else
{
lean_object* v___x_3997_; lean_object* v___x_3998_; 
v___x_3997_ = l_Lean_Expr_getAppFn(v_val_3958_);
v___x_3998_ = l_Lean_Expr_constLevels_x21(v___x_3997_);
lean_dec_ref(v___x_3997_);
if (lean_obj_tag(v___x_3998_) == 1)
{
lean_object* v_tail_3999_; 
v_tail_3999_ = lean_ctor_get(v___x_3998_, 1);
lean_inc(v_tail_3999_);
lean_dec_ref_known(v___x_3998_, 2);
if (lean_obj_tag(v_tail_3999_) == 1)
{
lean_object* v_tail_4000_; 
v_tail_4000_ = lean_ctor_get(v_tail_3999_, 1);
lean_inc(v_tail_4000_);
if (lean_obj_tag(v_tail_4000_) == 1)
{
lean_object* v_tail_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4067_; 
v_tail_4001_ = lean_ctor_get(v_tail_4000_, 1);
v_isSharedCheck_4067_ = !lean_is_exclusive(v_tail_4000_);
if (v_isSharedCheck_4067_ == 0)
{
lean_object* v_unused_4068_; 
v_unused_4068_ = lean_ctor_get(v_tail_4000_, 0);
lean_dec(v_unused_4068_);
v___x_4003_ = v_tail_4000_;
v_isShared_4004_ = v_isSharedCheck_4067_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_tail_4001_);
lean_dec(v_tail_4000_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4067_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
if (lean_obj_tag(v_tail_4001_) == 0)
{
lean_object* v___x_4005_; lean_object* v___x_4006_; 
v___x_4005_ = l_Lean_Expr_fvarId_x21(v_F_3957_);
v___x_4006_ = l_Lean_FVarId_getDecl___redArg(v___x_4005_, v_a_3962_, v_a_3964_, v_a_3965_);
if (lean_obj_tag(v___x_4006_) == 0)
{
lean_object* v_a_4007_; lean_object* v_dummy_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v_args_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___f_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; uint8_t v___x_4017_; lean_object* v___x_4018_; 
v_a_4007_ = lean_ctor_get(v___x_4006_, 0);
lean_inc_n(v_a_4007_, 2);
lean_dec_ref_known(v___x_4006_, 1);
v_dummy_4008_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_3981_);
v___x_4009_ = lean_mk_array(v___x_3981_, v_dummy_4008_);
v___x_4010_ = lean_nat_sub(v___x_3981_, v___x_3983_);
lean_dec(v___x_3981_);
v_args_4011_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_3958_, v___x_4009_, v___x_4010_);
v___x_4012_ = lean_unsigned_to_nat(0u);
v___x_4013_ = lean_box(v___x_3992_);
lean_inc_ref(v_x_3956_);
v___f_4014_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed), 14, 5);
lean_closure_set(v___f_4014_, 0, v_a_4007_);
lean_closure_set(v___f_4014_, 1, v___x_3976_);
lean_closure_set(v___f_4014_, 2, v___x_4012_);
lean_closure_set(v___f_4014_, 3, v_x_3956_);
lean_closure_set(v___f_4014_, 4, v___x_4013_);
v___x_4015_ = lean_unsigned_to_nat(2u);
v___x_4016_ = lean_array_get(v___x_3976_, v_args_4011_, v___x_4015_);
v___x_4017_ = 0;
v___x_4018_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_4016_, v___f_4014_, v___x_4017_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_);
if (lean_obj_tag(v___x_4018_) == 0)
{
lean_object* v_a_4019_; lean_object* v_fst_4020_; lean_object* v_snd_4021_; lean_object* v_00_u03b1_4022_; lean_object* v_00_u03b2_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___f_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; 
v_a_4019_ = lean_ctor_get(v___x_4018_, 0);
lean_inc(v_a_4019_);
lean_dec_ref_known(v___x_4018_, 1);
v_fst_4020_ = lean_ctor_get(v_a_4019_, 0);
lean_inc(v_fst_4020_);
v_snd_4021_ = lean_ctor_get(v_a_4019_, 1);
lean_inc(v_snd_4021_);
lean_dec(v_a_4019_);
v_00_u03b1_4022_ = lean_array_get(v___x_3976_, v_args_4011_, v___x_4012_);
v_00_u03b2_4023_ = lean_array_get(v___x_3976_, v_args_4011_, v___x_3983_);
v___x_4024_ = lean_box(v___x_4017_);
v___x_4025_ = lean_box(v___x_3992_);
lean_inc_ref(v_x_3956_);
lean_inc(v_00_u03b2_4023_);
lean_inc(v_00_u03b1_4022_);
v___f_4026_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___boxed), 22, 13);
lean_closure_set(v___f_4026_, 0, v___x_3976_);
lean_closure_set(v___f_4026_, 1, v___x_4012_);
lean_closure_set(v___f_4026_, 2, v___x_3983_);
lean_closure_set(v___f_4026_, 3, v___x_4015_);
lean_closure_set(v___f_4026_, 4, v___x_4024_);
lean_closure_set(v___f_4026_, 5, v___x_4025_);
lean_closure_set(v___f_4026_, 6, v_00_u03b1_4022_);
lean_closure_set(v___f_4026_, 7, v_00_u03b2_4023_);
lean_closure_set(v___f_4026_, 8, v___x_3988_);
lean_closure_set(v___f_4026_, 9, v_k_3959_);
lean_closure_set(v___f_4026_, 10, v___x_3980_);
lean_closure_set(v___f_4026_, 11, v_a_4007_);
lean_closure_set(v___f_4026_, 12, v_x_3956_);
v___x_4027_ = lean_array_get(v___x_3976_, v_args_4011_, v___x_3988_);
lean_dec_ref(v_args_4011_);
v___x_4028_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_4027_, v___f_4026_, v___x_4017_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_);
if (lean_obj_tag(v___x_4028_) == 0)
{
lean_object* v_a_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4050_; 
v_a_4029_ = lean_ctor_get(v___x_4028_, 0);
v_isSharedCheck_4050_ = !lean_is_exclusive(v___x_4028_);
if (v_isSharedCheck_4050_ == 0)
{
v___x_4031_ = v___x_4028_;
v_isShared_4032_ = v_isSharedCheck_4050_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_a_4029_);
lean_dec(v___x_4028_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4050_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4033_; lean_object* v___x_4035_; 
v___x_4033_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4));
if (v_isShared_4004_ == 0)
{
lean_ctor_set(v___x_4003_, 1, v_tail_3999_);
lean_ctor_set(v___x_4003_, 0, v_snd_4021_);
v___x_4035_ = v___x_4003_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_snd_4021_);
lean_ctor_set(v_reuseFailAlloc_4049_, 1, v_tail_3999_);
v___x_4035_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4047_; 
v___x_4036_ = l_Lean_mkConst(v___x_4033_, v___x_4035_);
v___x_4037_ = lean_unsigned_to_nat(6u);
v___x_4038_ = lean_mk_empty_array_with_capacity(v___x_4037_);
v___x_4039_ = lean_array_push(v___x_4038_, v_00_u03b1_4022_);
v___x_4040_ = lean_array_push(v___x_4039_, v_00_u03b2_4023_);
v___x_4041_ = lean_array_push(v___x_4040_, v_fst_4020_);
v___x_4042_ = lean_array_push(v___x_4041_, v_x_3956_);
v___x_4043_ = lean_array_push(v___x_4042_, v_a_4029_);
v___x_4044_ = lean_array_push(v___x_4043_, v_F_3957_);
v___x_4045_ = l_Lean_mkAppN(v___x_4036_, v___x_4044_);
lean_dec_ref(v___x_4044_);
if (v_isShared_4032_ == 0)
{
lean_ctor_set(v___x_4031_, 0, v___x_4045_);
v___x_4047_ = v___x_4031_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v___x_4045_);
v___x_4047_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
return v___x_4047_;
}
}
}
}
else
{
lean_dec(v_00_u03b2_4023_);
lean_dec(v_00_u03b1_4022_);
lean_dec(v_snd_4021_);
lean_dec(v_fst_4020_);
lean_del_object(v___x_4003_);
lean_dec_ref_known(v_tail_3999_, 2);
lean_dec_ref(v_F_3957_);
lean_dec_ref(v_x_3956_);
return v___x_4028_;
}
}
else
{
lean_object* v_a_4051_; lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4058_; 
lean_dec_ref(v_args_4011_);
lean_dec(v_a_4007_);
lean_del_object(v___x_4003_);
lean_dec_ref_known(v_tail_3999_, 2);
lean_dec_ref(v_k_3959_);
lean_dec_ref(v_F_3957_);
lean_dec_ref(v_x_3956_);
v_a_4051_ = lean_ctor_get(v___x_4018_, 0);
v_isSharedCheck_4058_ = !lean_is_exclusive(v___x_4018_);
if (v_isSharedCheck_4058_ == 0)
{
v___x_4053_ = v___x_4018_;
v_isShared_4054_ = v_isSharedCheck_4058_;
goto v_resetjp_4052_;
}
else
{
lean_inc(v_a_4051_);
lean_dec(v___x_4018_);
v___x_4053_ = lean_box(0);
v_isShared_4054_ = v_isSharedCheck_4058_;
goto v_resetjp_4052_;
}
v_resetjp_4052_:
{
lean_object* v___x_4056_; 
if (v_isShared_4054_ == 0)
{
v___x_4056_ = v___x_4053_;
goto v_reusejp_4055_;
}
else
{
lean_object* v_reuseFailAlloc_4057_; 
v_reuseFailAlloc_4057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4057_, 0, v_a_4051_);
v___x_4056_ = v_reuseFailAlloc_4057_;
goto v_reusejp_4055_;
}
v_reusejp_4055_:
{
return v___x_4056_;
}
}
}
}
else
{
lean_object* v_a_4059_; lean_object* v___x_4061_; uint8_t v_isShared_4062_; uint8_t v_isSharedCheck_4066_; 
lean_del_object(v___x_4003_);
lean_dec_ref_known(v_tail_3999_, 2);
lean_dec(v___x_3981_);
lean_dec_ref(v_k_3959_);
lean_dec_ref(v_val_3958_);
lean_dec_ref(v_F_3957_);
lean_dec_ref(v_x_3956_);
v_a_4059_ = lean_ctor_get(v___x_4006_, 0);
v_isSharedCheck_4066_ = !lean_is_exclusive(v___x_4006_);
if (v_isSharedCheck_4066_ == 0)
{
v___x_4061_ = v___x_4006_;
v_isShared_4062_ = v_isSharedCheck_4066_;
goto v_resetjp_4060_;
}
else
{
lean_inc(v_a_4059_);
lean_dec(v___x_4006_);
v___x_4061_ = lean_box(0);
v_isShared_4062_ = v_isSharedCheck_4066_;
goto v_resetjp_4060_;
}
v_resetjp_4060_:
{
lean_object* v___x_4064_; 
if (v_isShared_4062_ == 0)
{
v___x_4064_ = v___x_4061_;
goto v_reusejp_4063_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v_a_4059_);
v___x_4064_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4063_;
}
v_reusejp_4063_:
{
return v___x_4064_;
}
}
}
}
else
{
lean_del_object(v___x_4003_);
lean_dec(v_tail_4001_);
lean_dec_ref_known(v_tail_3999_, 2);
lean_dec(v___x_3981_);
lean_dec_ref(v_k_3959_);
lean_dec_ref(v_val_3958_);
lean_dec_ref(v_F_3957_);
lean_dec_ref(v_x_3956_);
v___y_3968_ = v_a_3960_;
v___y_3969_ = v_a_3961_;
v___y_3970_ = v_a_3962_;
v___y_3971_ = v_a_3963_;
v___y_3972_ = v_a_3964_;
v___y_3973_ = v_a_3965_;
goto v___jp_3967_;
}
}
}
else
{
lean_dec(v_tail_4000_);
lean_dec_ref_known(v_tail_3999_, 2);
lean_dec(v___x_3981_);
lean_dec_ref(v_k_3959_);
lean_dec_ref(v_val_3958_);
lean_dec_ref(v_F_3957_);
lean_dec_ref(v_x_3956_);
v___y_3968_ = v_a_3960_;
v___y_3969_ = v_a_3961_;
v___y_3970_ = v_a_3962_;
v___y_3971_ = v_a_3963_;
v___y_3972_ = v_a_3964_;
v___y_3973_ = v_a_3965_;
goto v___jp_3967_;
}
}
else
{
lean_dec(v_tail_3999_);
lean_dec(v___x_3981_);
lean_dec_ref(v_k_3959_);
lean_dec_ref(v_val_3958_);
lean_dec_ref(v_F_3957_);
lean_dec_ref(v_x_3956_);
v___y_3968_ = v_a_3960_;
v___y_3969_ = v_a_3961_;
v___y_3970_ = v_a_3962_;
v___y_3971_ = v_a_3963_;
v___y_3972_ = v_a_3964_;
v___y_3973_ = v_a_3965_;
goto v___jp_3967_;
}
}
else
{
lean_dec(v___x_3998_);
lean_dec(v___x_3981_);
lean_dec_ref(v_k_3959_);
lean_dec_ref(v_val_3958_);
lean_dec_ref(v_F_3957_);
lean_dec_ref(v_x_3956_);
v___y_3968_ = v_a_3960_;
v___y_3969_ = v_a_3961_;
v___y_3970_ = v_a_3962_;
v___y_3971_ = v_a_3963_;
v___y_3972_ = v_a_3964_;
v___y_3973_ = v_a_3965_;
goto v___jp_3967_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1(lean_object* v___x_4073_, lean_object* v_a_4074_, lean_object* v_k_4075_, lean_object* v___x_4076_, lean_object* v___x_4077_, uint8_t v___x_4078_, uint8_t v___x_4079_, uint8_t v___x_4080_, lean_object* v_FNew_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_){
_start:
{
lean_object* v___x_4089_; 
lean_inc_ref(v_FNew_4081_);
lean_inc_ref(v___x_4073_);
v___x_4089_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v___x_4073_, v_FNew_4081_, v_a_4074_, v_k_4075_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_);
if (lean_obj_tag(v___x_4089_) == 0)
{
lean_object* v_a_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; 
v_a_4090_ = lean_ctor_get(v___x_4089_, 0);
lean_inc(v_a_4090_);
lean_dec_ref_known(v___x_4089_, 1);
v___x_4091_ = lean_mk_empty_array_with_capacity(v___x_4076_);
v___x_4092_ = lean_array_push(v___x_4091_, v___x_4077_);
v___x_4093_ = lean_array_push(v___x_4092_, v___x_4073_);
v___x_4094_ = lean_array_push(v___x_4093_, v_FNew_4081_);
v___x_4095_ = l_Lean_Meta_mkLambdaFVars(v___x_4094_, v_a_4090_, v___x_4078_, v___x_4079_, v___x_4078_, v___x_4079_, v___x_4080_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_);
lean_dec_ref(v___x_4094_);
return v___x_4095_;
}
else
{
lean_dec_ref(v_FNew_4081_);
lean_dec_ref(v___x_4077_);
lean_dec_ref(v___x_4073_);
return v___x_4089_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___boxed(lean_object* v_x_4096_, lean_object* v_F_4097_, lean_object* v_val_4098_, lean_object* v_k_4099_, lean_object* v_a_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_){
_start:
{
lean_object* v_res_4107_; 
v_res_4107_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v_x_4096_, v_F_4097_, v_val_4098_, v_k_4099_, v_a_4100_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
lean_dec(v_a_4105_);
lean_dec_ref(v_a_4104_);
lean_dec(v_a_4103_);
lean_dec_ref(v_a_4102_);
lean_dec(v_a_4101_);
lean_dec_ref(v_a_4100_);
return v_res_4107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0(lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_){
_start:
{
lean_object* v___x_4121_; 
v___x_4121_ = l_Lean_Elab_WF_applyCleanWfTactic(v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_);
if (lean_obj_tag(v___x_4121_) == 0)
{
lean_object* v_ref_4122_; uint8_t v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; 
lean_dec_ref_known(v___x_4121_, 1);
v_ref_4122_ = lean_ctor_get(v___y_4118_, 5);
v___x_4123_ = 0;
v___x_4124_ = l_Lean_SourceInfo_fromRef(v_ref_4122_, v___x_4123_);
v___x_4125_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__1));
v___x_4126_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__2));
lean_inc(v___x_4124_);
v___x_4127_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4127_, 0, v___x_4124_);
lean_ctor_set(v___x_4127_, 1, v___x_4126_);
v___x_4128_ = l_Lean_Syntax_node1(v___x_4124_, v___x_4125_, v___x_4127_);
v___x_4129_ = l_Lean_Elab_Tactic_evalTactic(v___x_4128_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_);
return v___x_4129_;
}
else
{
return v___x_4121_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___boxed(lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_){
_start:
{
lean_object* v_res_4139_; 
v_res_4139_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0(v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
lean_dec(v___y_4137_);
lean_dec_ref(v___y_4136_);
lean_dec(v___y_4135_);
lean_dec_ref(v___y_4134_);
lean_dec(v___y_4133_);
lean_dec_ref(v___y_4132_);
lean_dec(v___y_4131_);
lean_dec_ref(v___y_4130_);
return v_res_4139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(lean_object* v_mvarId_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_){
_start:
{
lean_object* v___f_4149_; lean_object* v___x_4150_; 
v___f_4149_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___closed__0));
v___x_4150_ = l_Lean_Elab_Tactic_run(v_mvarId_4141_, v___f_4149_, v_a_4142_, v_a_4143_, v_a_4144_, v_a_4145_, v_a_4146_, v_a_4147_);
if (lean_obj_tag(v___x_4150_) == 0)
{
lean_object* v_a_4151_; lean_object* v___x_4153_; uint8_t v_isShared_4154_; uint8_t v_isSharedCheck_4161_; 
v_a_4151_ = lean_ctor_get(v___x_4150_, 0);
v_isSharedCheck_4161_ = !lean_is_exclusive(v___x_4150_);
if (v_isSharedCheck_4161_ == 0)
{
v___x_4153_ = v___x_4150_;
v_isShared_4154_ = v_isSharedCheck_4161_;
goto v_resetjp_4152_;
}
else
{
lean_inc(v_a_4151_);
lean_dec(v___x_4150_);
v___x_4153_ = lean_box(0);
v_isShared_4154_ = v_isSharedCheck_4161_;
goto v_resetjp_4152_;
}
v_resetjp_4152_:
{
uint8_t v___x_4155_; 
v___x_4155_ = l_List_isEmpty___redArg(v_a_4151_);
if (v___x_4155_ == 0)
{
lean_object* v___x_4156_; 
lean_del_object(v___x_4153_);
v___x_4156_ = l_Lean_Elab_Term_reportUnsolvedGoals(v_a_4151_, v_a_4144_, v_a_4145_, v_a_4146_, v_a_4147_);
return v___x_4156_;
}
else
{
lean_object* v___x_4157_; lean_object* v___x_4159_; 
lean_dec(v_a_4151_);
v___x_4157_ = lean_box(0);
if (v_isShared_4154_ == 0)
{
lean_ctor_set(v___x_4153_, 0, v___x_4157_);
v___x_4159_ = v___x_4153_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v___x_4157_);
v___x_4159_ = v_reuseFailAlloc_4160_;
goto v_reusejp_4158_;
}
v_reusejp_4158_:
{
return v___x_4159_;
}
}
}
}
else
{
lean_object* v_a_4162_; lean_object* v___x_4164_; uint8_t v_isShared_4165_; uint8_t v_isSharedCheck_4169_; 
v_a_4162_ = lean_ctor_get(v___x_4150_, 0);
v_isSharedCheck_4169_ = !lean_is_exclusive(v___x_4150_);
if (v_isSharedCheck_4169_ == 0)
{
v___x_4164_ = v___x_4150_;
v_isShared_4165_ = v_isSharedCheck_4169_;
goto v_resetjp_4163_;
}
else
{
lean_inc(v_a_4162_);
lean_dec(v___x_4150_);
v___x_4164_ = lean_box(0);
v_isShared_4165_ = v_isSharedCheck_4169_;
goto v_resetjp_4163_;
}
v_resetjp_4163_:
{
lean_object* v___x_4167_; 
if (v_isShared_4165_ == 0)
{
v___x_4167_ = v___x_4164_;
goto v_reusejp_4166_;
}
else
{
lean_object* v_reuseFailAlloc_4168_; 
v_reuseFailAlloc_4168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4168_, 0, v_a_4162_);
v___x_4167_ = v_reuseFailAlloc_4168_;
goto v_reusejp_4166_;
}
v_reusejp_4166_:
{
return v___x_4167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___boxed(lean_object* v_mvarId_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_){
_start:
{
lean_object* v_res_4178_; 
v_res_4178_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(v_mvarId_4170_, v_a_4171_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_, v_a_4176_);
lean_dec(v_a_4176_);
lean_dec_ref(v_a_4175_);
lean_dec(v_a_4174_);
lean_dec_ref(v_a_4173_);
lean_dec(v_a_4172_);
lean_dec_ref(v_a_4171_);
return v_res_4178_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(lean_object* v_x_4179_, lean_object* v_x_4180_, lean_object* v_x_4181_, lean_object* v_x_4182_){
_start:
{
lean_object* v_ks_4183_; lean_object* v_vs_4184_; lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4208_; 
v_ks_4183_ = lean_ctor_get(v_x_4179_, 0);
v_vs_4184_ = lean_ctor_get(v_x_4179_, 1);
v_isSharedCheck_4208_ = !lean_is_exclusive(v_x_4179_);
if (v_isSharedCheck_4208_ == 0)
{
v___x_4186_ = v_x_4179_;
v_isShared_4187_ = v_isSharedCheck_4208_;
goto v_resetjp_4185_;
}
else
{
lean_inc(v_vs_4184_);
lean_inc(v_ks_4183_);
lean_dec(v_x_4179_);
v___x_4186_ = lean_box(0);
v_isShared_4187_ = v_isSharedCheck_4208_;
goto v_resetjp_4185_;
}
v_resetjp_4185_:
{
lean_object* v___x_4188_; uint8_t v___x_4189_; 
v___x_4188_ = lean_array_get_size(v_ks_4183_);
v___x_4189_ = lean_nat_dec_lt(v_x_4180_, v___x_4188_);
if (v___x_4189_ == 0)
{
lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4193_; 
lean_dec(v_x_4180_);
v___x_4190_ = lean_array_push(v_ks_4183_, v_x_4181_);
v___x_4191_ = lean_array_push(v_vs_4184_, v_x_4182_);
if (v_isShared_4187_ == 0)
{
lean_ctor_set(v___x_4186_, 1, v___x_4191_);
lean_ctor_set(v___x_4186_, 0, v___x_4190_);
v___x_4193_ = v___x_4186_;
goto v_reusejp_4192_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v___x_4190_);
lean_ctor_set(v_reuseFailAlloc_4194_, 1, v___x_4191_);
v___x_4193_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4192_;
}
v_reusejp_4192_:
{
return v___x_4193_;
}
}
else
{
lean_object* v_k_x27_4195_; uint8_t v___x_4196_; 
v_k_x27_4195_ = lean_array_fget_borrowed(v_ks_4183_, v_x_4180_);
v___x_4196_ = l_Lean_instBEqMVarId_beq(v_x_4181_, v_k_x27_4195_);
if (v___x_4196_ == 0)
{
lean_object* v___x_4198_; 
if (v_isShared_4187_ == 0)
{
v___x_4198_ = v___x_4186_;
goto v_reusejp_4197_;
}
else
{
lean_object* v_reuseFailAlloc_4202_; 
v_reuseFailAlloc_4202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4202_, 0, v_ks_4183_);
lean_ctor_set(v_reuseFailAlloc_4202_, 1, v_vs_4184_);
v___x_4198_ = v_reuseFailAlloc_4202_;
goto v_reusejp_4197_;
}
v_reusejp_4197_:
{
lean_object* v___x_4199_; lean_object* v___x_4200_; 
v___x_4199_ = lean_unsigned_to_nat(1u);
v___x_4200_ = lean_nat_add(v_x_4180_, v___x_4199_);
lean_dec(v_x_4180_);
v_x_4179_ = v___x_4198_;
v_x_4180_ = v___x_4200_;
goto _start;
}
}
else
{
lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4206_; 
v___x_4203_ = lean_array_fset(v_ks_4183_, v_x_4180_, v_x_4181_);
v___x_4204_ = lean_array_fset(v_vs_4184_, v_x_4180_, v_x_4182_);
lean_dec(v_x_4180_);
if (v_isShared_4187_ == 0)
{
lean_ctor_set(v___x_4186_, 1, v___x_4204_);
lean_ctor_set(v___x_4186_, 0, v___x_4203_);
v___x_4206_ = v___x_4186_;
goto v_reusejp_4205_;
}
else
{
lean_object* v_reuseFailAlloc_4207_; 
v_reuseFailAlloc_4207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4207_, 0, v___x_4203_);
lean_ctor_set(v_reuseFailAlloc_4207_, 1, v___x_4204_);
v___x_4206_ = v_reuseFailAlloc_4207_;
goto v_reusejp_4205_;
}
v_reusejp_4205_:
{
return v___x_4206_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_4209_, lean_object* v_k_4210_, lean_object* v_v_4211_){
_start:
{
lean_object* v___x_4212_; lean_object* v___x_4213_; 
v___x_4212_ = lean_unsigned_to_nat(0u);
v___x_4213_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_n_4209_, v___x_4212_, v_k_4210_, v_v_4211_);
return v___x_4213_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4214_; 
v___x_4214_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4214_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(lean_object* v_x_4215_, size_t v_x_4216_, size_t v_x_4217_, lean_object* v_x_4218_, lean_object* v_x_4219_){
_start:
{
if (lean_obj_tag(v_x_4215_) == 0)
{
lean_object* v_es_4220_; size_t v___x_4221_; size_t v___x_4222_; lean_object* v_j_4223_; lean_object* v___x_4224_; uint8_t v___x_4225_; 
v_es_4220_ = lean_ctor_get(v_x_4215_, 0);
v___x_4221_ = ((size_t)31ULL);
v___x_4222_ = lean_usize_land(v_x_4216_, v___x_4221_);
v_j_4223_ = lean_usize_to_nat(v___x_4222_);
v___x_4224_ = lean_array_get_size(v_es_4220_);
v___x_4225_ = lean_nat_dec_lt(v_j_4223_, v___x_4224_);
if (v___x_4225_ == 0)
{
lean_dec(v_j_4223_);
lean_dec(v_x_4219_);
lean_dec(v_x_4218_);
return v_x_4215_;
}
else
{
lean_object* v___x_4227_; uint8_t v_isShared_4228_; uint8_t v_isSharedCheck_4264_; 
lean_inc_ref(v_es_4220_);
v_isSharedCheck_4264_ = !lean_is_exclusive(v_x_4215_);
if (v_isSharedCheck_4264_ == 0)
{
lean_object* v_unused_4265_; 
v_unused_4265_ = lean_ctor_get(v_x_4215_, 0);
lean_dec(v_unused_4265_);
v___x_4227_ = v_x_4215_;
v_isShared_4228_ = v_isSharedCheck_4264_;
goto v_resetjp_4226_;
}
else
{
lean_dec(v_x_4215_);
v___x_4227_ = lean_box(0);
v_isShared_4228_ = v_isSharedCheck_4264_;
goto v_resetjp_4226_;
}
v_resetjp_4226_:
{
lean_object* v_v_4229_; lean_object* v___x_4230_; lean_object* v_xs_x27_4231_; lean_object* v___y_4233_; 
v_v_4229_ = lean_array_fget(v_es_4220_, v_j_4223_);
v___x_4230_ = lean_box(0);
v_xs_x27_4231_ = lean_array_fset(v_es_4220_, v_j_4223_, v___x_4230_);
switch(lean_obj_tag(v_v_4229_))
{
case 0:
{
lean_object* v_key_4238_; lean_object* v_val_4239_; lean_object* v___x_4241_; uint8_t v_isShared_4242_; uint8_t v_isSharedCheck_4249_; 
v_key_4238_ = lean_ctor_get(v_v_4229_, 0);
v_val_4239_ = lean_ctor_get(v_v_4229_, 1);
v_isSharedCheck_4249_ = !lean_is_exclusive(v_v_4229_);
if (v_isSharedCheck_4249_ == 0)
{
v___x_4241_ = v_v_4229_;
v_isShared_4242_ = v_isSharedCheck_4249_;
goto v_resetjp_4240_;
}
else
{
lean_inc(v_val_4239_);
lean_inc(v_key_4238_);
lean_dec(v_v_4229_);
v___x_4241_ = lean_box(0);
v_isShared_4242_ = v_isSharedCheck_4249_;
goto v_resetjp_4240_;
}
v_resetjp_4240_:
{
uint8_t v___x_4243_; 
v___x_4243_ = l_Lean_instBEqMVarId_beq(v_x_4218_, v_key_4238_);
if (v___x_4243_ == 0)
{
lean_object* v___x_4244_; lean_object* v___x_4245_; 
lean_del_object(v___x_4241_);
v___x_4244_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4238_, v_val_4239_, v_x_4218_, v_x_4219_);
v___x_4245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4245_, 0, v___x_4244_);
v___y_4233_ = v___x_4245_;
goto v___jp_4232_;
}
else
{
lean_object* v___x_4247_; 
lean_dec(v_val_4239_);
lean_dec(v_key_4238_);
if (v_isShared_4242_ == 0)
{
lean_ctor_set(v___x_4241_, 1, v_x_4219_);
lean_ctor_set(v___x_4241_, 0, v_x_4218_);
v___x_4247_ = v___x_4241_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v_x_4218_);
lean_ctor_set(v_reuseFailAlloc_4248_, 1, v_x_4219_);
v___x_4247_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
v___y_4233_ = v___x_4247_;
goto v___jp_4232_;
}
}
}
}
case 1:
{
lean_object* v_node_4250_; lean_object* v___x_4252_; uint8_t v_isShared_4253_; uint8_t v_isSharedCheck_4262_; 
v_node_4250_ = lean_ctor_get(v_v_4229_, 0);
v_isSharedCheck_4262_ = !lean_is_exclusive(v_v_4229_);
if (v_isSharedCheck_4262_ == 0)
{
v___x_4252_ = v_v_4229_;
v_isShared_4253_ = v_isSharedCheck_4262_;
goto v_resetjp_4251_;
}
else
{
lean_inc(v_node_4250_);
lean_dec(v_v_4229_);
v___x_4252_ = lean_box(0);
v_isShared_4253_ = v_isSharedCheck_4262_;
goto v_resetjp_4251_;
}
v_resetjp_4251_:
{
size_t v___x_4254_; size_t v___x_4255_; size_t v___x_4256_; size_t v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4260_; 
v___x_4254_ = ((size_t)5ULL);
v___x_4255_ = lean_usize_shift_right(v_x_4216_, v___x_4254_);
v___x_4256_ = ((size_t)1ULL);
v___x_4257_ = lean_usize_add(v_x_4217_, v___x_4256_);
v___x_4258_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_node_4250_, v___x_4255_, v___x_4257_, v_x_4218_, v_x_4219_);
if (v_isShared_4253_ == 0)
{
lean_ctor_set(v___x_4252_, 0, v___x_4258_);
v___x_4260_ = v___x_4252_;
goto v_reusejp_4259_;
}
else
{
lean_object* v_reuseFailAlloc_4261_; 
v_reuseFailAlloc_4261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4261_, 0, v___x_4258_);
v___x_4260_ = v_reuseFailAlloc_4261_;
goto v_reusejp_4259_;
}
v_reusejp_4259_:
{
v___y_4233_ = v___x_4260_;
goto v___jp_4232_;
}
}
}
default: 
{
lean_object* v___x_4263_; 
v___x_4263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4263_, 0, v_x_4218_);
lean_ctor_set(v___x_4263_, 1, v_x_4219_);
v___y_4233_ = v___x_4263_;
goto v___jp_4232_;
}
}
v___jp_4232_:
{
lean_object* v___x_4234_; lean_object* v___x_4236_; 
v___x_4234_ = lean_array_fset(v_xs_x27_4231_, v_j_4223_, v___y_4233_);
lean_dec(v_j_4223_);
if (v_isShared_4228_ == 0)
{
lean_ctor_set(v___x_4227_, 0, v___x_4234_);
v___x_4236_ = v___x_4227_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v___x_4234_);
v___x_4236_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
return v___x_4236_;
}
}
}
}
}
else
{
lean_object* v_ks_4266_; lean_object* v_vs_4267_; lean_object* v___x_4269_; uint8_t v_isShared_4270_; uint8_t v_isSharedCheck_4285_; 
v_ks_4266_ = lean_ctor_get(v_x_4215_, 0);
v_vs_4267_ = lean_ctor_get(v_x_4215_, 1);
v_isSharedCheck_4285_ = !lean_is_exclusive(v_x_4215_);
if (v_isSharedCheck_4285_ == 0)
{
v___x_4269_ = v_x_4215_;
v_isShared_4270_ = v_isSharedCheck_4285_;
goto v_resetjp_4268_;
}
else
{
lean_inc(v_vs_4267_);
lean_inc(v_ks_4266_);
lean_dec(v_x_4215_);
v___x_4269_ = lean_box(0);
v_isShared_4270_ = v_isSharedCheck_4285_;
goto v_resetjp_4268_;
}
v_resetjp_4268_:
{
lean_object* v___x_4272_; 
if (v_isShared_4270_ == 0)
{
v___x_4272_ = v___x_4269_;
goto v_reusejp_4271_;
}
else
{
lean_object* v_reuseFailAlloc_4284_; 
v_reuseFailAlloc_4284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4284_, 0, v_ks_4266_);
lean_ctor_set(v_reuseFailAlloc_4284_, 1, v_vs_4267_);
v___x_4272_ = v_reuseFailAlloc_4284_;
goto v_reusejp_4271_;
}
v_reusejp_4271_:
{
lean_object* v_newNode_4273_; size_t v___x_4274_; uint8_t v___x_4275_; 
v_newNode_4273_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(v___x_4272_, v_x_4218_, v_x_4219_);
v___x_4274_ = ((size_t)7ULL);
v___x_4275_ = lean_usize_dec_le(v___x_4274_, v_x_4217_);
if (v___x_4275_ == 0)
{
lean_object* v___x_4276_; lean_object* v___x_4277_; uint8_t v___x_4278_; 
v___x_4276_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4273_);
v___x_4277_ = lean_unsigned_to_nat(4u);
v___x_4278_ = lean_nat_dec_lt(v___x_4276_, v___x_4277_);
lean_dec(v___x_4276_);
if (v___x_4278_ == 0)
{
lean_object* v_ks_4279_; lean_object* v_vs_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; 
v_ks_4279_ = lean_ctor_get(v_newNode_4273_, 0);
lean_inc_ref(v_ks_4279_);
v_vs_4280_ = lean_ctor_get(v_newNode_4273_, 1);
lean_inc_ref(v_vs_4280_);
lean_dec_ref(v_newNode_4273_);
v___x_4281_ = lean_unsigned_to_nat(0u);
v___x_4282_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_4283_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_x_4217_, v_ks_4279_, v_vs_4280_, v___x_4281_, v___x_4282_);
lean_dec_ref(v_vs_4280_);
lean_dec_ref(v_ks_4279_);
return v___x_4283_;
}
else
{
return v_newNode_4273_;
}
}
else
{
return v_newNode_4273_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_4286_, lean_object* v_keys_4287_, lean_object* v_vals_4288_, lean_object* v_i_4289_, lean_object* v_entries_4290_){
_start:
{
lean_object* v___x_4291_; uint8_t v___x_4292_; 
v___x_4291_ = lean_array_get_size(v_keys_4287_);
v___x_4292_ = lean_nat_dec_lt(v_i_4289_, v___x_4291_);
if (v___x_4292_ == 0)
{
lean_dec(v_i_4289_);
return v_entries_4290_;
}
else
{
lean_object* v_k_4293_; lean_object* v_v_4294_; uint64_t v___x_4295_; size_t v_h_4296_; size_t v___x_4297_; lean_object* v___x_4298_; size_t v___x_4299_; size_t v___x_4300_; size_t v___x_4301_; size_t v_h_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; 
v_k_4293_ = lean_array_fget_borrowed(v_keys_4287_, v_i_4289_);
v_v_4294_ = lean_array_fget_borrowed(v_vals_4288_, v_i_4289_);
v___x_4295_ = l_Lean_instHashableMVarId_hash(v_k_4293_);
v_h_4296_ = lean_uint64_to_usize(v___x_4295_);
v___x_4297_ = ((size_t)5ULL);
v___x_4298_ = lean_unsigned_to_nat(1u);
v___x_4299_ = ((size_t)1ULL);
v___x_4300_ = lean_usize_sub(v_depth_4286_, v___x_4299_);
v___x_4301_ = lean_usize_mul(v___x_4297_, v___x_4300_);
v_h_4302_ = lean_usize_shift_right(v_h_4296_, v___x_4301_);
v___x_4303_ = lean_nat_add(v_i_4289_, v___x_4298_);
lean_dec(v_i_4289_);
lean_inc(v_v_4294_);
lean_inc(v_k_4293_);
v___x_4304_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_entries_4290_, v_h_4302_, v_depth_4286_, v_k_4293_, v_v_4294_);
v_i_4289_ = v___x_4303_;
v_entries_4290_ = v___x_4304_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_4306_, lean_object* v_keys_4307_, lean_object* v_vals_4308_, lean_object* v_i_4309_, lean_object* v_entries_4310_){
_start:
{
size_t v_depth_boxed_4311_; lean_object* v_res_4312_; 
v_depth_boxed_4311_ = lean_unbox_usize(v_depth_4306_);
lean_dec(v_depth_4306_);
v_res_4312_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_4311_, v_keys_4307_, v_vals_4308_, v_i_4309_, v_entries_4310_);
lean_dec_ref(v_vals_4308_);
lean_dec_ref(v_keys_4307_);
return v_res_4312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_4313_, lean_object* v_x_4314_, lean_object* v_x_4315_, lean_object* v_x_4316_, lean_object* v_x_4317_){
_start:
{
size_t v_x_3982__boxed_4318_; size_t v_x_3983__boxed_4319_; lean_object* v_res_4320_; 
v_x_3982__boxed_4318_ = lean_unbox_usize(v_x_4314_);
lean_dec(v_x_4314_);
v_x_3983__boxed_4319_ = lean_unbox_usize(v_x_4315_);
lean_dec(v_x_4315_);
v_res_4320_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4313_, v_x_3982__boxed_4318_, v_x_3983__boxed_4319_, v_x_4316_, v_x_4317_);
return v_res_4320_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(lean_object* v_x_4321_, lean_object* v_x_4322_, lean_object* v_x_4323_){
_start:
{
uint64_t v___x_4324_; size_t v___x_4325_; size_t v___x_4326_; lean_object* v___x_4327_; 
v___x_4324_ = l_Lean_instHashableMVarId_hash(v_x_4322_);
v___x_4325_ = lean_uint64_to_usize(v___x_4324_);
v___x_4326_ = ((size_t)1ULL);
v___x_4327_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4321_, v___x_4325_, v___x_4326_, v_x_4322_, v_x_4323_);
return v___x_4327_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(lean_object* v_mvarId_4328_, lean_object* v_val_4329_, lean_object* v___y_4330_){
_start:
{
lean_object* v___x_4332_; lean_object* v_mctx_4333_; lean_object* v_cache_4334_; lean_object* v_zetaDeltaFVarIds_4335_; lean_object* v_postponed_4336_; lean_object* v_diag_4337_; lean_object* v___x_4339_; uint8_t v_isShared_4340_; uint8_t v_isSharedCheck_4366_; 
v___x_4332_ = lean_st_ref_take(v___y_4330_);
v_mctx_4333_ = lean_ctor_get(v___x_4332_, 0);
v_cache_4334_ = lean_ctor_get(v___x_4332_, 1);
v_zetaDeltaFVarIds_4335_ = lean_ctor_get(v___x_4332_, 2);
v_postponed_4336_ = lean_ctor_get(v___x_4332_, 3);
v_diag_4337_ = lean_ctor_get(v___x_4332_, 4);
v_isSharedCheck_4366_ = !lean_is_exclusive(v___x_4332_);
if (v_isSharedCheck_4366_ == 0)
{
v___x_4339_ = v___x_4332_;
v_isShared_4340_ = v_isSharedCheck_4366_;
goto v_resetjp_4338_;
}
else
{
lean_inc(v_diag_4337_);
lean_inc(v_postponed_4336_);
lean_inc(v_zetaDeltaFVarIds_4335_);
lean_inc(v_cache_4334_);
lean_inc(v_mctx_4333_);
lean_dec(v___x_4332_);
v___x_4339_ = lean_box(0);
v_isShared_4340_ = v_isSharedCheck_4366_;
goto v_resetjp_4338_;
}
v_resetjp_4338_:
{
lean_object* v_depth_4341_; lean_object* v_levelAssignDepth_4342_; lean_object* v_lmvarCounter_4343_; lean_object* v_mvarCounter_4344_; lean_object* v_lDecls_4345_; lean_object* v_decls_4346_; lean_object* v_userNames_4347_; lean_object* v_lAssignment_4348_; lean_object* v_eAssignment_4349_; lean_object* v_dAssignment_4350_; lean_object* v_instanceTypedMVars_4351_; lean_object* v___x_4353_; uint8_t v_isShared_4354_; uint8_t v_isSharedCheck_4365_; 
v_depth_4341_ = lean_ctor_get(v_mctx_4333_, 0);
v_levelAssignDepth_4342_ = lean_ctor_get(v_mctx_4333_, 1);
v_lmvarCounter_4343_ = lean_ctor_get(v_mctx_4333_, 2);
v_mvarCounter_4344_ = lean_ctor_get(v_mctx_4333_, 3);
v_lDecls_4345_ = lean_ctor_get(v_mctx_4333_, 4);
v_decls_4346_ = lean_ctor_get(v_mctx_4333_, 5);
v_userNames_4347_ = lean_ctor_get(v_mctx_4333_, 6);
v_lAssignment_4348_ = lean_ctor_get(v_mctx_4333_, 7);
v_eAssignment_4349_ = lean_ctor_get(v_mctx_4333_, 8);
v_dAssignment_4350_ = lean_ctor_get(v_mctx_4333_, 9);
v_instanceTypedMVars_4351_ = lean_ctor_get(v_mctx_4333_, 10);
v_isSharedCheck_4365_ = !lean_is_exclusive(v_mctx_4333_);
if (v_isSharedCheck_4365_ == 0)
{
v___x_4353_ = v_mctx_4333_;
v_isShared_4354_ = v_isSharedCheck_4365_;
goto v_resetjp_4352_;
}
else
{
lean_inc(v_instanceTypedMVars_4351_);
lean_inc(v_dAssignment_4350_);
lean_inc(v_eAssignment_4349_);
lean_inc(v_lAssignment_4348_);
lean_inc(v_userNames_4347_);
lean_inc(v_decls_4346_);
lean_inc(v_lDecls_4345_);
lean_inc(v_mvarCounter_4344_);
lean_inc(v_lmvarCounter_4343_);
lean_inc(v_levelAssignDepth_4342_);
lean_inc(v_depth_4341_);
lean_dec(v_mctx_4333_);
v___x_4353_ = lean_box(0);
v_isShared_4354_ = v_isSharedCheck_4365_;
goto v_resetjp_4352_;
}
v_resetjp_4352_:
{
lean_object* v___x_4355_; lean_object* v___x_4357_; 
v___x_4355_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(v_eAssignment_4349_, v_mvarId_4328_, v_val_4329_);
if (v_isShared_4354_ == 0)
{
lean_ctor_set(v___x_4353_, 8, v___x_4355_);
v___x_4357_ = v___x_4353_;
goto v_reusejp_4356_;
}
else
{
lean_object* v_reuseFailAlloc_4364_; 
v_reuseFailAlloc_4364_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_4364_, 0, v_depth_4341_);
lean_ctor_set(v_reuseFailAlloc_4364_, 1, v_levelAssignDepth_4342_);
lean_ctor_set(v_reuseFailAlloc_4364_, 2, v_lmvarCounter_4343_);
lean_ctor_set(v_reuseFailAlloc_4364_, 3, v_mvarCounter_4344_);
lean_ctor_set(v_reuseFailAlloc_4364_, 4, v_lDecls_4345_);
lean_ctor_set(v_reuseFailAlloc_4364_, 5, v_decls_4346_);
lean_ctor_set(v_reuseFailAlloc_4364_, 6, v_userNames_4347_);
lean_ctor_set(v_reuseFailAlloc_4364_, 7, v_lAssignment_4348_);
lean_ctor_set(v_reuseFailAlloc_4364_, 8, v___x_4355_);
lean_ctor_set(v_reuseFailAlloc_4364_, 9, v_dAssignment_4350_);
lean_ctor_set(v_reuseFailAlloc_4364_, 10, v_instanceTypedMVars_4351_);
v___x_4357_ = v_reuseFailAlloc_4364_;
goto v_reusejp_4356_;
}
v_reusejp_4356_:
{
lean_object* v___x_4359_; 
if (v_isShared_4340_ == 0)
{
lean_ctor_set(v___x_4339_, 0, v___x_4357_);
v___x_4359_ = v___x_4339_;
goto v_reusejp_4358_;
}
else
{
lean_object* v_reuseFailAlloc_4363_; 
v_reuseFailAlloc_4363_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4363_, 0, v___x_4357_);
lean_ctor_set(v_reuseFailAlloc_4363_, 1, v_cache_4334_);
lean_ctor_set(v_reuseFailAlloc_4363_, 2, v_zetaDeltaFVarIds_4335_);
lean_ctor_set(v_reuseFailAlloc_4363_, 3, v_postponed_4336_);
lean_ctor_set(v_reuseFailAlloc_4363_, 4, v_diag_4337_);
v___x_4359_ = v_reuseFailAlloc_4363_;
goto v_reusejp_4358_;
}
v_reusejp_4358_:
{
lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; 
v___x_4360_ = lean_st_ref_put(v___y_4330_, v___x_4359_);
v___x_4361_ = lean_box(0);
v___x_4362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4362_, 0, v___x_4361_);
return v___x_4362_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg___boxed(lean_object* v_mvarId_4367_, lean_object* v_val_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_){
_start:
{
lean_object* v_res_4371_; 
v_res_4371_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mvarId_4367_, v_val_4368_, v___y_4369_);
lean_dec(v___y_4369_);
return v_res_4371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___lam__0(lean_object* v_mv_u2081_4376_, lean_object* v_mv_u2082_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_){
_start:
{
lean_object* v___x_4386_; 
lean_inc(v_mv_u2081_4376_);
v___x_4386_ = l_Lean_MVarId_getDecl(v_mv_u2081_4376_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_);
if (lean_obj_tag(v___x_4386_) == 0)
{
lean_object* v_a_4387_; lean_object* v___x_4388_; 
v_a_4387_ = lean_ctor_get(v___x_4386_, 0);
lean_inc(v_a_4387_);
lean_dec_ref_known(v___x_4386_, 1);
lean_inc(v_mv_u2082_4377_);
v___x_4388_ = l_Lean_MVarId_getDecl(v_mv_u2082_4377_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_);
if (lean_obj_tag(v___x_4388_) == 0)
{
lean_object* v_a_4389_; lean_object* v_lctx_4390_; lean_object* v_type_4391_; lean_object* v_lctx_4392_; lean_object* v_type_4393_; uint8_t v___x_4394_; 
v_a_4389_ = lean_ctor_get(v___x_4388_, 0);
lean_inc(v_a_4389_);
lean_dec_ref_known(v___x_4388_, 1);
v_lctx_4390_ = lean_ctor_get(v_a_4387_, 1);
lean_inc_ref(v_lctx_4390_);
v_type_4391_ = lean_ctor_get(v_a_4387_, 2);
lean_inc_ref(v_type_4391_);
lean_dec(v_a_4387_);
v_lctx_4392_ = lean_ctor_get(v_a_4389_, 1);
lean_inc_ref(v_lctx_4392_);
v_type_4393_ = lean_ctor_get(v_a_4389_, 2);
lean_inc_ref(v_type_4393_);
lean_dec(v_a_4389_);
v___x_4394_ = lean_expr_eqv(v_type_4391_, v_type_4393_);
lean_dec_ref(v_type_4393_);
lean_dec_ref(v_type_4391_);
if (v___x_4394_ == 0)
{
lean_dec_ref(v_lctx_4392_);
lean_dec_ref(v_lctx_4390_);
lean_dec(v_mv_u2082_4377_);
lean_dec(v_mv_u2081_4376_);
goto v___jp_4383_;
}
else
{
lean_object* v___x_4395_; uint8_t v___x_4396_; 
v___x_4395_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
v___x_4396_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_4390_, v_lctx_4392_, v___x_4395_);
if (v___x_4396_ == 0)
{
uint8_t v___x_4397_; 
v___x_4397_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_4392_, v_lctx_4390_, v___x_4395_);
lean_dec_ref(v_lctx_4390_);
lean_dec_ref(v_lctx_4392_);
if (v___x_4397_ == 0)
{
lean_dec(v_mv_u2082_4377_);
lean_dec(v_mv_u2081_4376_);
goto v___jp_4383_;
}
else
{
lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4401_; uint8_t v_isShared_4402_; uint8_t v_isSharedCheck_4409_; 
v___x_4398_ = l_Lean_Expr_mvar___override(v_mv_u2082_4377_);
v___x_4399_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mv_u2081_4376_, v___x_4398_, v___y_4379_);
v_isSharedCheck_4409_ = !lean_is_exclusive(v___x_4399_);
if (v_isSharedCheck_4409_ == 0)
{
lean_object* v_unused_4410_; 
v_unused_4410_ = lean_ctor_get(v___x_4399_, 0);
lean_dec(v_unused_4410_);
v___x_4401_ = v___x_4399_;
v_isShared_4402_ = v_isSharedCheck_4409_;
goto v_resetjp_4400_;
}
else
{
lean_dec(v___x_4399_);
v___x_4401_ = lean_box(0);
v_isShared_4402_ = v_isSharedCheck_4409_;
goto v_resetjp_4400_;
}
v_resetjp_4400_:
{
lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4407_; 
v___x_4403_ = lean_box(v___x_4396_);
v___x_4404_ = lean_box(v___x_4394_);
v___x_4405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4405_, 0, v___x_4403_);
lean_ctor_set(v___x_4405_, 1, v___x_4404_);
if (v_isShared_4402_ == 0)
{
lean_ctor_set(v___x_4401_, 0, v___x_4405_);
v___x_4407_ = v___x_4401_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v___x_4405_);
v___x_4407_ = v_reuseFailAlloc_4408_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
return v___x_4407_;
}
}
}
}
else
{
lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4414_; uint8_t v_isShared_4415_; uint8_t v_isSharedCheck_4423_; 
lean_dec_ref(v_lctx_4392_);
lean_dec_ref(v_lctx_4390_);
v___x_4411_ = l_Lean_Expr_mvar___override(v_mv_u2081_4376_);
v___x_4412_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mv_u2082_4377_, v___x_4411_, v___y_4379_);
v_isSharedCheck_4423_ = !lean_is_exclusive(v___x_4412_);
if (v_isSharedCheck_4423_ == 0)
{
lean_object* v_unused_4424_; 
v_unused_4424_ = lean_ctor_get(v___x_4412_, 0);
lean_dec(v_unused_4424_);
v___x_4414_ = v___x_4412_;
v_isShared_4415_ = v_isSharedCheck_4423_;
goto v_resetjp_4413_;
}
else
{
lean_dec(v___x_4412_);
v___x_4414_ = lean_box(0);
v_isShared_4415_ = v_isSharedCheck_4423_;
goto v_resetjp_4413_;
}
v_resetjp_4413_:
{
uint8_t v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4421_; 
v___x_4416_ = 0;
v___x_4417_ = lean_box(v___x_4394_);
v___x_4418_ = lean_box(v___x_4416_);
v___x_4419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4419_, 0, v___x_4417_);
lean_ctor_set(v___x_4419_, 1, v___x_4418_);
if (v_isShared_4415_ == 0)
{
lean_ctor_set(v___x_4414_, 0, v___x_4419_);
v___x_4421_ = v___x_4414_;
goto v_reusejp_4420_;
}
else
{
lean_object* v_reuseFailAlloc_4422_; 
v_reuseFailAlloc_4422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4422_, 0, v___x_4419_);
v___x_4421_ = v_reuseFailAlloc_4422_;
goto v_reusejp_4420_;
}
v_reusejp_4420_:
{
return v___x_4421_;
}
}
}
}
}
else
{
lean_object* v_a_4425_; lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4432_; 
lean_dec(v_a_4387_);
lean_dec(v_mv_u2082_4377_);
lean_dec(v_mv_u2081_4376_);
v_a_4425_ = lean_ctor_get(v___x_4388_, 0);
v_isSharedCheck_4432_ = !lean_is_exclusive(v___x_4388_);
if (v_isSharedCheck_4432_ == 0)
{
v___x_4427_ = v___x_4388_;
v_isShared_4428_ = v_isSharedCheck_4432_;
goto v_resetjp_4426_;
}
else
{
lean_inc(v_a_4425_);
lean_dec(v___x_4388_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4432_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
lean_object* v___x_4430_; 
if (v_isShared_4428_ == 0)
{
v___x_4430_ = v___x_4427_;
goto v_reusejp_4429_;
}
else
{
lean_object* v_reuseFailAlloc_4431_; 
v_reuseFailAlloc_4431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4431_, 0, v_a_4425_);
v___x_4430_ = v_reuseFailAlloc_4431_;
goto v_reusejp_4429_;
}
v_reusejp_4429_:
{
return v___x_4430_;
}
}
}
}
else
{
lean_object* v_a_4433_; lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4440_; 
lean_dec(v_mv_u2082_4377_);
lean_dec(v_mv_u2081_4376_);
v_a_4433_ = lean_ctor_get(v___x_4386_, 0);
v_isSharedCheck_4440_ = !lean_is_exclusive(v___x_4386_);
if (v_isSharedCheck_4440_ == 0)
{
v___x_4435_ = v___x_4386_;
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
else
{
lean_inc(v_a_4433_);
lean_dec(v___x_4386_);
v___x_4435_ = lean_box(0);
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
v_resetjp_4434_:
{
lean_object* v___x_4438_; 
if (v_isShared_4436_ == 0)
{
v___x_4438_ = v___x_4435_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v_a_4433_);
v___x_4438_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
return v___x_4438_;
}
}
}
v___jp_4383_:
{
lean_object* v___x_4384_; lean_object* v___x_4385_; 
v___x_4384_ = ((lean_object*)(l_Lean_Elab_WF_assignSubsumed___lam__0___closed__0));
v___x_4385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4385_, 0, v___x_4384_);
return v___x_4385_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___lam__0___boxed(lean_object* v_mv_u2081_4441_, lean_object* v_mv_u2082_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_){
_start:
{
lean_object* v_res_4448_; 
v_res_4448_ = l_Lean_Elab_WF_assignSubsumed___lam__0(v_mv_u2081_4441_, v_mv_u2082_4442_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_);
lean_dec(v___y_4446_);
lean_dec_ref(v___y_4445_);
lean_dec(v___y_4444_);
lean_dec_ref(v___y_4443_);
return v_res_4448_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1(lean_object* v___x_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_){
_start:
{
lean_object* v___x_4455_; 
v___x_4455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4455_, 0, v___x_4449_);
return v___x_4455_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1___boxed(lean_object* v___x_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_){
_start:
{
lean_object* v_res_4462_; 
v_res_4462_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1(v___x_4456_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_);
lean_dec(v___y_4460_);
lean_dec_ref(v___y_4459_);
lean_dec(v___y_4458_);
lean_dec_ref(v___y_4457_);
return v_res_4462_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0(lean_object* v_f_4463_, lean_object* v___x_4464_, lean_object* v___x_4465_, lean_object* v___x_4466_, lean_object* v_a_4467_, uint8_t v___x_4468_, lean_object* v_snd_4469_, lean_object* v_fst_4470_, lean_object* v_next_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_){
_start:
{
lean_object* v___x_4477_; 
v___x_4477_ = lean_apply_7(v_f_4463_, v___x_4464_, v___x_4465_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_, lean_box(0));
if (lean_obj_tag(v___x_4477_) == 0)
{
lean_object* v_a_4478_; lean_object* v___x_4480_; uint8_t v_isShared_4481_; uint8_t v_isSharedCheck_4513_; 
v_a_4478_ = lean_ctor_get(v___x_4477_, 0);
v_isSharedCheck_4513_ = !lean_is_exclusive(v___x_4477_);
if (v_isSharedCheck_4513_ == 0)
{
v___x_4480_ = v___x_4477_;
v_isShared_4481_ = v_isSharedCheck_4513_;
goto v_resetjp_4479_;
}
else
{
lean_inc(v_a_4478_);
lean_dec(v___x_4477_);
v___x_4480_ = lean_box(0);
v_isShared_4481_ = v_isSharedCheck_4513_;
goto v_resetjp_4479_;
}
v_resetjp_4479_:
{
lean_object* v_fst_4482_; lean_object* v_snd_4483_; lean_object* v___x_4485_; uint8_t v_isShared_4486_; uint8_t v_isSharedCheck_4512_; 
v_fst_4482_ = lean_ctor_get(v_a_4478_, 0);
v_snd_4483_ = lean_ctor_get(v_a_4478_, 1);
v_isSharedCheck_4512_ = !lean_is_exclusive(v_a_4478_);
if (v_isSharedCheck_4512_ == 0)
{
v___x_4485_ = v_a_4478_;
v_isShared_4486_ = v_isSharedCheck_4512_;
goto v_resetjp_4484_;
}
else
{
lean_inc(v_snd_4483_);
lean_inc(v_fst_4482_);
lean_dec(v_a_4478_);
v___x_4485_ = lean_box(0);
v_isShared_4486_ = v_isSharedCheck_4512_;
goto v_resetjp_4484_;
}
v_resetjp_4484_:
{
lean_object* v_removed_4488_; lean_object* v_numRemoved_4489_; uint8_t v___x_4508_; 
v___x_4508_ = lean_unbox(v_fst_4482_);
lean_dec(v_fst_4482_);
if (v___x_4508_ == 0)
{
lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; 
v___x_4509_ = lean_nat_add(v_snd_4469_, v___x_4466_);
lean_dec(v_snd_4469_);
v___x_4510_ = lean_box(v___x_4468_);
v___x_4511_ = lean_array_set(v_fst_4470_, v_next_4471_, v___x_4510_);
v_removed_4488_ = v___x_4511_;
v_numRemoved_4489_ = v___x_4509_;
goto v___jp_4487_;
}
else
{
v_removed_4488_ = v_fst_4470_;
v_numRemoved_4489_ = v_snd_4469_;
goto v___jp_4487_;
}
v___jp_4487_:
{
uint8_t v___x_4490_; 
v___x_4490_ = lean_unbox(v_snd_4483_);
lean_dec(v_snd_4483_);
if (v___x_4490_ == 0)
{
lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4495_; 
v___x_4491_ = lean_nat_add(v_numRemoved_4489_, v___x_4466_);
lean_dec(v_numRemoved_4489_);
v___x_4492_ = lean_box(v___x_4468_);
v___x_4493_ = lean_array_set(v_removed_4488_, v_a_4467_, v___x_4492_);
if (v_isShared_4486_ == 0)
{
lean_ctor_set(v___x_4485_, 1, v___x_4491_);
lean_ctor_set(v___x_4485_, 0, v___x_4493_);
v___x_4495_ = v___x_4485_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v___x_4493_);
lean_ctor_set(v_reuseFailAlloc_4500_, 1, v___x_4491_);
v___x_4495_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
lean_object* v___x_4496_; lean_object* v___x_4498_; 
v___x_4496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4496_, 0, v___x_4495_);
if (v_isShared_4481_ == 0)
{
lean_ctor_set(v___x_4480_, 0, v___x_4496_);
v___x_4498_ = v___x_4480_;
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
else
{
lean_object* v___x_4502_; 
if (v_isShared_4486_ == 0)
{
lean_ctor_set(v___x_4485_, 1, v_numRemoved_4489_);
lean_ctor_set(v___x_4485_, 0, v_removed_4488_);
v___x_4502_ = v___x_4485_;
goto v_reusejp_4501_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v_removed_4488_);
lean_ctor_set(v_reuseFailAlloc_4507_, 1, v_numRemoved_4489_);
v___x_4502_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4501_;
}
v_reusejp_4501_:
{
lean_object* v___x_4503_; lean_object* v___x_4505_; 
v___x_4503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4503_, 0, v___x_4502_);
if (v_isShared_4481_ == 0)
{
lean_ctor_set(v___x_4480_, 0, v___x_4503_);
v___x_4505_ = v___x_4480_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4506_; 
v_reuseFailAlloc_4506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v___x_4503_);
v___x_4505_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
return v___x_4505_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4514_; lean_object* v___x_4516_; uint8_t v_isShared_4517_; uint8_t v_isSharedCheck_4521_; 
lean_dec(v_fst_4470_);
lean_dec(v_snd_4469_);
v_a_4514_ = lean_ctor_get(v___x_4477_, 0);
v_isSharedCheck_4521_ = !lean_is_exclusive(v___x_4477_);
if (v_isSharedCheck_4521_ == 0)
{
v___x_4516_ = v___x_4477_;
v_isShared_4517_ = v_isSharedCheck_4521_;
goto v_resetjp_4515_;
}
else
{
lean_inc(v_a_4514_);
lean_dec(v___x_4477_);
v___x_4516_ = lean_box(0);
v_isShared_4517_ = v_isSharedCheck_4521_;
goto v_resetjp_4515_;
}
v_resetjp_4515_:
{
lean_object* v___x_4519_; 
if (v_isShared_4517_ == 0)
{
v___x_4519_ = v___x_4516_;
goto v_reusejp_4518_;
}
else
{
lean_object* v_reuseFailAlloc_4520_; 
v_reuseFailAlloc_4520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4520_, 0, v_a_4514_);
v___x_4519_ = v_reuseFailAlloc_4520_;
goto v_reusejp_4518_;
}
v_reusejp_4518_:
{
return v___x_4519_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_f_4522_, lean_object* v___x_4523_, lean_object* v___x_4524_, lean_object* v___x_4525_, lean_object* v_a_4526_, lean_object* v___x_4527_, lean_object* v_snd_4528_, lean_object* v_fst_4529_, lean_object* v_next_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_){
_start:
{
uint8_t v___x_4355__boxed_4536_; lean_object* v_res_4537_; 
v___x_4355__boxed_4536_ = lean_unbox(v___x_4527_);
v_res_4537_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0(v_f_4522_, v___x_4523_, v___x_4524_, v___x_4525_, v_a_4526_, v___x_4355__boxed_4536_, v_snd_4528_, v_fst_4529_, v_next_4530_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_);
lean_dec(v_next_4530_);
lean_dec(v_a_4526_);
lean_dec(v___x_4525_);
return v_res_4537_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(lean_object* v_upperBound_4538_, lean_object* v_a_4539_, lean_object* v_next_4540_, lean_object* v_f_4541_, lean_object* v_a_4542_, lean_object* v_b_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_){
_start:
{
uint8_t v___x_4549_; 
v___x_4549_ = lean_nat_dec_lt(v_a_4542_, v_upperBound_4538_);
if (v___x_4549_ == 0)
{
lean_object* v___x_4550_; 
lean_dec(v_a_4542_);
lean_dec_ref(v_f_4541_);
lean_dec(v_next_4540_);
v___x_4550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4550_, 0, v_b_4543_);
return v___x_4550_;
}
else
{
lean_object* v_fst_4551_; lean_object* v_snd_4552_; lean_object* v___x_4554_; uint8_t v_isShared_4555_; uint8_t v_isSharedCheck_4599_; 
v_fst_4551_ = lean_ctor_get(v_b_4543_, 0);
v_snd_4552_ = lean_ctor_get(v_b_4543_, 1);
v_isSharedCheck_4599_ = !lean_is_exclusive(v_b_4543_);
if (v_isSharedCheck_4599_ == 0)
{
v___x_4554_ = v_b_4543_;
v_isShared_4555_ = v_isSharedCheck_4599_;
goto v_resetjp_4553_;
}
else
{
lean_inc(v_snd_4552_);
lean_inc(v_fst_4551_);
lean_dec(v_b_4543_);
v___x_4554_ = lean_box(0);
v_isShared_4555_ = v_isSharedCheck_4599_;
goto v_resetjp_4553_;
}
v_resetjp_4553_:
{
lean_object* v___x_4556_; lean_object* v___y_4558_; uint8_t v___y_4581_; uint8_t v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; uint8_t v___x_4594_; 
v___x_4556_ = lean_unsigned_to_nat(1u);
v___x_4591_ = 0;
v___x_4592_ = lean_box(v___x_4591_);
v___x_4593_ = lean_array_get(v___x_4592_, v_fst_4551_, v_next_4540_);
lean_dec(v___x_4592_);
v___x_4594_ = lean_unbox(v___x_4593_);
if (v___x_4594_ == 0)
{
lean_object* v___x_4595_; lean_object* v___x_4596_; uint8_t v___x_4597_; 
lean_dec(v___x_4593_);
v___x_4595_ = lean_box(v___x_4591_);
v___x_4596_ = lean_array_get(v___x_4595_, v_fst_4551_, v_a_4542_);
lean_dec(v___x_4595_);
v___x_4597_ = lean_unbox(v___x_4596_);
lean_dec(v___x_4596_);
v___y_4581_ = v___x_4597_;
goto v___jp_4580_;
}
else
{
uint8_t v___x_4598_; 
v___x_4598_ = lean_unbox(v___x_4593_);
lean_dec(v___x_4593_);
v___y_4581_ = v___x_4598_;
goto v___jp_4580_;
}
v___jp_4557_:
{
lean_object* v___x_4559_; 
lean_inc(v___y_4547_);
lean_inc_ref(v___y_4546_);
lean_inc(v___y_4545_);
lean_inc_ref(v___y_4544_);
v___x_4559_ = lean_apply_5(v___y_4558_, v___y_4544_, v___y_4545_, v___y_4546_, v___y_4547_, lean_box(0));
if (lean_obj_tag(v___x_4559_) == 0)
{
lean_object* v_a_4560_; lean_object* v___x_4562_; uint8_t v_isShared_4563_; uint8_t v_isSharedCheck_4571_; 
v_a_4560_ = lean_ctor_get(v___x_4559_, 0);
v_isSharedCheck_4571_ = !lean_is_exclusive(v___x_4559_);
if (v_isSharedCheck_4571_ == 0)
{
v___x_4562_ = v___x_4559_;
v_isShared_4563_ = v_isSharedCheck_4571_;
goto v_resetjp_4561_;
}
else
{
lean_inc(v_a_4560_);
lean_dec(v___x_4559_);
v___x_4562_ = lean_box(0);
v_isShared_4563_ = v_isSharedCheck_4571_;
goto v_resetjp_4561_;
}
v_resetjp_4561_:
{
if (lean_obj_tag(v_a_4560_) == 0)
{
lean_object* v_a_4564_; lean_object* v___x_4566_; 
lean_dec(v_a_4542_);
lean_dec_ref(v_f_4541_);
lean_dec(v_next_4540_);
v_a_4564_ = lean_ctor_get(v_a_4560_, 0);
lean_inc(v_a_4564_);
lean_dec_ref_known(v_a_4560_, 1);
if (v_isShared_4563_ == 0)
{
lean_ctor_set(v___x_4562_, 0, v_a_4564_);
v___x_4566_ = v___x_4562_;
goto v_reusejp_4565_;
}
else
{
lean_object* v_reuseFailAlloc_4567_; 
v_reuseFailAlloc_4567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4567_, 0, v_a_4564_);
v___x_4566_ = v_reuseFailAlloc_4567_;
goto v_reusejp_4565_;
}
v_reusejp_4565_:
{
return v___x_4566_;
}
}
else
{
lean_object* v_a_4568_; lean_object* v___x_4569_; 
lean_del_object(v___x_4562_);
v_a_4568_ = lean_ctor_get(v_a_4560_, 0);
lean_inc(v_a_4568_);
lean_dec_ref_known(v_a_4560_, 1);
v___x_4569_ = lean_nat_add(v_a_4542_, v___x_4556_);
lean_dec(v_a_4542_);
v_a_4542_ = v___x_4569_;
v_b_4543_ = v_a_4568_;
goto _start;
}
}
}
else
{
lean_object* v_a_4572_; lean_object* v___x_4574_; uint8_t v_isShared_4575_; uint8_t v_isSharedCheck_4579_; 
lean_dec(v_a_4542_);
lean_dec_ref(v_f_4541_);
lean_dec(v_next_4540_);
v_a_4572_ = lean_ctor_get(v___x_4559_, 0);
v_isSharedCheck_4579_ = !lean_is_exclusive(v___x_4559_);
if (v_isSharedCheck_4579_ == 0)
{
v___x_4574_ = v___x_4559_;
v_isShared_4575_ = v_isSharedCheck_4579_;
goto v_resetjp_4573_;
}
else
{
lean_inc(v_a_4572_);
lean_dec(v___x_4559_);
v___x_4574_ = lean_box(0);
v_isShared_4575_ = v_isSharedCheck_4579_;
goto v_resetjp_4573_;
}
v_resetjp_4573_:
{
lean_object* v___x_4577_; 
if (v_isShared_4575_ == 0)
{
v___x_4577_ = v___x_4574_;
goto v_reusejp_4576_;
}
else
{
lean_object* v_reuseFailAlloc_4578_; 
v_reuseFailAlloc_4578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4578_, 0, v_a_4572_);
v___x_4577_ = v_reuseFailAlloc_4578_;
goto v_reusejp_4576_;
}
v_reusejp_4576_:
{
return v___x_4577_;
}
}
}
}
v___jp_4580_:
{
if (v___y_4581_ == 0)
{
lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___f_4585_; 
lean_del_object(v___x_4554_);
v___x_4582_ = lean_array_fget_borrowed(v_a_4539_, v_next_4540_);
v___x_4583_ = lean_array_fget_borrowed(v_a_4539_, v_a_4542_);
v___x_4584_ = lean_box(v___x_4549_);
lean_inc(v_next_4540_);
lean_inc(v_a_4542_);
lean_inc(v___x_4583_);
lean_inc(v___x_4582_);
lean_inc_ref(v_f_4541_);
v___f_4585_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4585_, 0, v_f_4541_);
lean_closure_set(v___f_4585_, 1, v___x_4582_);
lean_closure_set(v___f_4585_, 2, v___x_4583_);
lean_closure_set(v___f_4585_, 3, v___x_4556_);
lean_closure_set(v___f_4585_, 4, v_a_4542_);
lean_closure_set(v___f_4585_, 5, v___x_4584_);
lean_closure_set(v___f_4585_, 6, v_snd_4552_);
lean_closure_set(v___f_4585_, 7, v_fst_4551_);
lean_closure_set(v___f_4585_, 8, v_next_4540_);
v___y_4558_ = v___f_4585_;
goto v___jp_4557_;
}
else
{
lean_object* v___x_4587_; 
if (v_isShared_4555_ == 0)
{
v___x_4587_ = v___x_4554_;
goto v_reusejp_4586_;
}
else
{
lean_object* v_reuseFailAlloc_4590_; 
v_reuseFailAlloc_4590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4590_, 0, v_fst_4551_);
lean_ctor_set(v_reuseFailAlloc_4590_, 1, v_snd_4552_);
v___x_4587_ = v_reuseFailAlloc_4590_;
goto v_reusejp_4586_;
}
v_reusejp_4586_:
{
lean_object* v___x_4588_; lean_object* v___f_4589_; 
v___x_4588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4588_, 0, v___x_4587_);
v___f_4589_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1___boxed), 6, 1);
lean_closure_set(v___f_4589_, 0, v___x_4588_);
v___y_4558_ = v___f_4589_;
goto v___jp_4557_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___boxed(lean_object* v_upperBound_4600_, lean_object* v_a_4601_, lean_object* v_next_4602_, lean_object* v_f_4603_, lean_object* v_a_4604_, lean_object* v_b_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_){
_start:
{
lean_object* v_res_4611_; 
v_res_4611_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v_upperBound_4600_, v_a_4601_, v_next_4602_, v_f_4603_, v_a_4604_, v_b_4605_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_);
lean_dec(v___y_4609_);
lean_dec_ref(v___y_4608_);
lean_dec(v___y_4607_);
lean_dec_ref(v___y_4606_);
lean_dec_ref(v_a_4601_);
lean_dec(v_upperBound_4600_);
return v_res_4611_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(lean_object* v_upperBound_4612_, lean_object* v___x_4613_, lean_object* v_a_4614_, lean_object* v_f_4615_, lean_object* v_a_4616_, lean_object* v_b_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_){
_start:
{
uint8_t v___x_4623_; 
v___x_4623_ = lean_nat_dec_lt(v_a_4616_, v_upperBound_4612_);
if (v___x_4623_ == 0)
{
lean_object* v___x_4624_; 
lean_dec(v_a_4616_);
lean_dec_ref(v_f_4615_);
v___x_4624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4624_, 0, v_b_4617_);
return v___x_4624_;
}
else
{
lean_object* v_fst_4625_; lean_object* v_snd_4626_; lean_object* v___x_4628_; uint8_t v_isShared_4629_; uint8_t v_isSharedCheck_4647_; 
v_fst_4625_ = lean_ctor_get(v_b_4617_, 0);
v_snd_4626_ = lean_ctor_get(v_b_4617_, 1);
v_isSharedCheck_4647_ = !lean_is_exclusive(v_b_4617_);
if (v_isSharedCheck_4647_ == 0)
{
v___x_4628_ = v_b_4617_;
v_isShared_4629_ = v_isSharedCheck_4647_;
goto v_resetjp_4627_;
}
else
{
lean_inc(v_snd_4626_);
lean_inc(v_fst_4625_);
lean_dec(v_b_4617_);
v___x_4628_ = lean_box(0);
v_isShared_4629_ = v_isSharedCheck_4647_;
goto v_resetjp_4627_;
}
v_resetjp_4627_:
{
lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4633_; 
v___x_4630_ = lean_unsigned_to_nat(1u);
v___x_4631_ = lean_nat_add(v_a_4616_, v___x_4630_);
if (v_isShared_4629_ == 0)
{
v___x_4633_ = v___x_4628_;
goto v_reusejp_4632_;
}
else
{
lean_object* v_reuseFailAlloc_4646_; 
v_reuseFailAlloc_4646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4646_, 0, v_fst_4625_);
lean_ctor_set(v_reuseFailAlloc_4646_, 1, v_snd_4626_);
v___x_4633_ = v_reuseFailAlloc_4646_;
goto v_reusejp_4632_;
}
v_reusejp_4632_:
{
lean_object* v___x_4634_; 
lean_inc(v___x_4631_);
lean_inc_ref(v_f_4615_);
v___x_4634_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v___x_4613_, v_a_4614_, v_a_4616_, v_f_4615_, v___x_4631_, v___x_4633_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_);
if (lean_obj_tag(v___x_4634_) == 0)
{
lean_object* v_a_4635_; lean_object* v_fst_4636_; lean_object* v_snd_4637_; lean_object* v___x_4639_; uint8_t v_isShared_4640_; uint8_t v_isSharedCheck_4645_; 
v_a_4635_ = lean_ctor_get(v___x_4634_, 0);
lean_inc(v_a_4635_);
lean_dec_ref_known(v___x_4634_, 1);
v_fst_4636_ = lean_ctor_get(v_a_4635_, 0);
v_snd_4637_ = lean_ctor_get(v_a_4635_, 1);
v_isSharedCheck_4645_ = !lean_is_exclusive(v_a_4635_);
if (v_isSharedCheck_4645_ == 0)
{
v___x_4639_ = v_a_4635_;
v_isShared_4640_ = v_isSharedCheck_4645_;
goto v_resetjp_4638_;
}
else
{
lean_inc(v_snd_4637_);
lean_inc(v_fst_4636_);
lean_dec(v_a_4635_);
v___x_4639_ = lean_box(0);
v_isShared_4640_ = v_isSharedCheck_4645_;
goto v_resetjp_4638_;
}
v_resetjp_4638_:
{
lean_object* v___x_4642_; 
if (v_isShared_4640_ == 0)
{
v___x_4642_ = v___x_4639_;
goto v_reusejp_4641_;
}
else
{
lean_object* v_reuseFailAlloc_4644_; 
v_reuseFailAlloc_4644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4644_, 0, v_fst_4636_);
lean_ctor_set(v_reuseFailAlloc_4644_, 1, v_snd_4637_);
v___x_4642_ = v_reuseFailAlloc_4644_;
goto v_reusejp_4641_;
}
v_reusejp_4641_:
{
v_a_4616_ = v___x_4631_;
v_b_4617_ = v___x_4642_;
goto _start;
}
}
}
else
{
lean_dec(v___x_4631_);
lean_dec_ref(v_f_4615_);
return v___x_4634_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_4648_, lean_object* v___x_4649_, lean_object* v_a_4650_, lean_object* v_f_4651_, lean_object* v_a_4652_, lean_object* v_b_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_){
_start:
{
lean_object* v_res_4659_; 
v_res_4659_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v_upperBound_4648_, v___x_4649_, v_a_4650_, v_f_4651_, v_a_4652_, v_b_4653_, v___y_4654_, v___y_4655_, v___y_4656_, v___y_4657_);
lean_dec(v___y_4657_);
lean_dec_ref(v___y_4656_);
lean_dec(v___y_4655_);
lean_dec_ref(v___y_4654_);
lean_dec_ref(v_a_4650_);
lean_dec(v___x_4649_);
lean_dec(v_upperBound_4648_);
return v_res_4659_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0(lean_object* v___x_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_){
_start:
{
lean_object* v___x_4666_; 
v___x_4666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4666_, 0, v___x_4660_);
return v___x_4666_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed(lean_object* v___x_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_){
_start:
{
lean_object* v_res_4673_; 
v_res_4673_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0(v___x_4667_, v___y_4668_, v___y_4669_, v___y_4670_, v___y_4671_);
lean_dec(v___y_4671_);
lean_dec_ref(v___y_4670_);
lean_dec(v___y_4669_);
lean_dec_ref(v___y_4668_);
return v_res_4673_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(lean_object* v_upperBound_4674_, lean_object* v_removed_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_b_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_){
_start:
{
lean_object* v___y_4685_; uint8_t v___x_4708_; 
v___x_4708_ = lean_nat_dec_lt(v_a_4677_, v_upperBound_4674_);
if (v___x_4708_ == 0)
{
lean_object* v___x_4709_; 
lean_dec(v_a_4677_);
v___x_4709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4709_, 0, v_b_4678_);
return v___x_4709_;
}
else
{
uint8_t v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; uint8_t v___x_4713_; 
v___x_4710_ = 0;
v___x_4711_ = lean_box(v___x_4710_);
v___x_4712_ = lean_array_get(v___x_4711_, v_removed_4675_, v_a_4677_);
lean_dec(v___x_4711_);
v___x_4713_ = lean_unbox(v___x_4712_);
lean_dec(v___x_4712_);
if (v___x_4713_ == 0)
{
lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___f_4717_; 
v___x_4714_ = lean_array_fget_borrowed(v_a_4676_, v_a_4677_);
lean_inc(v___x_4714_);
v___x_4715_ = lean_array_push(v_b_4678_, v___x_4714_);
v___x_4716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4716_, 0, v___x_4715_);
v___f_4717_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4717_, 0, v___x_4716_);
v___y_4685_ = v___f_4717_;
goto v___jp_4684_;
}
else
{
lean_object* v___x_4718_; lean_object* v___f_4719_; 
v___x_4718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4718_, 0, v_b_4678_);
v___f_4719_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4719_, 0, v___x_4718_);
v___y_4685_ = v___f_4719_;
goto v___jp_4684_;
}
}
v___jp_4684_:
{
lean_object* v___x_4686_; 
lean_inc(v___y_4682_);
lean_inc_ref(v___y_4681_);
lean_inc(v___y_4680_);
lean_inc_ref(v___y_4679_);
v___x_4686_ = lean_apply_5(v___y_4685_, v___y_4679_, v___y_4680_, v___y_4681_, v___y_4682_, lean_box(0));
if (lean_obj_tag(v___x_4686_) == 0)
{
lean_object* v_a_4687_; lean_object* v___x_4689_; uint8_t v_isShared_4690_; uint8_t v_isSharedCheck_4699_; 
v_a_4687_ = lean_ctor_get(v___x_4686_, 0);
v_isSharedCheck_4699_ = !lean_is_exclusive(v___x_4686_);
if (v_isSharedCheck_4699_ == 0)
{
v___x_4689_ = v___x_4686_;
v_isShared_4690_ = v_isSharedCheck_4699_;
goto v_resetjp_4688_;
}
else
{
lean_inc(v_a_4687_);
lean_dec(v___x_4686_);
v___x_4689_ = lean_box(0);
v_isShared_4690_ = v_isSharedCheck_4699_;
goto v_resetjp_4688_;
}
v_resetjp_4688_:
{
if (lean_obj_tag(v_a_4687_) == 0)
{
lean_object* v_a_4691_; lean_object* v___x_4693_; 
lean_dec(v_a_4677_);
v_a_4691_ = lean_ctor_get(v_a_4687_, 0);
lean_inc(v_a_4691_);
lean_dec_ref_known(v_a_4687_, 1);
if (v_isShared_4690_ == 0)
{
lean_ctor_set(v___x_4689_, 0, v_a_4691_);
v___x_4693_ = v___x_4689_;
goto v_reusejp_4692_;
}
else
{
lean_object* v_reuseFailAlloc_4694_; 
v_reuseFailAlloc_4694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4694_, 0, v_a_4691_);
v___x_4693_ = v_reuseFailAlloc_4694_;
goto v_reusejp_4692_;
}
v_reusejp_4692_:
{
return v___x_4693_;
}
}
else
{
lean_object* v_a_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; 
lean_del_object(v___x_4689_);
v_a_4695_ = lean_ctor_get(v_a_4687_, 0);
lean_inc(v_a_4695_);
lean_dec_ref_known(v_a_4687_, 1);
v___x_4696_ = lean_unsigned_to_nat(1u);
v___x_4697_ = lean_nat_add(v_a_4677_, v___x_4696_);
lean_dec(v_a_4677_);
v_a_4677_ = v___x_4697_;
v_b_4678_ = v_a_4695_;
goto _start;
}
}
}
else
{
lean_object* v_a_4700_; lean_object* v___x_4702_; uint8_t v_isShared_4703_; uint8_t v_isSharedCheck_4707_; 
lean_dec(v_a_4677_);
v_a_4700_ = lean_ctor_get(v___x_4686_, 0);
v_isSharedCheck_4707_ = !lean_is_exclusive(v___x_4686_);
if (v_isSharedCheck_4707_ == 0)
{
v___x_4702_ = v___x_4686_;
v_isShared_4703_ = v_isSharedCheck_4707_;
goto v_resetjp_4701_;
}
else
{
lean_inc(v_a_4700_);
lean_dec(v___x_4686_);
v___x_4702_ = lean_box(0);
v_isShared_4703_ = v_isSharedCheck_4707_;
goto v_resetjp_4701_;
}
v_resetjp_4701_:
{
lean_object* v___x_4705_; 
if (v_isShared_4703_ == 0)
{
v___x_4705_ = v___x_4702_;
goto v_reusejp_4704_;
}
else
{
lean_object* v_reuseFailAlloc_4706_; 
v_reuseFailAlloc_4706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4706_, 0, v_a_4700_);
v___x_4705_ = v_reuseFailAlloc_4706_;
goto v_reusejp_4704_;
}
v_reusejp_4704_:
{
return v___x_4705_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___boxed(lean_object* v_upperBound_4720_, lean_object* v_removed_4721_, lean_object* v_a_4722_, lean_object* v_a_4723_, lean_object* v_b_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_){
_start:
{
lean_object* v_res_4730_; 
v_res_4730_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v_upperBound_4720_, v_removed_4721_, v_a_4722_, v_a_4723_, v_b_4724_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_);
lean_dec(v___y_4728_);
lean_dec_ref(v___y_4727_);
lean_dec(v___y_4726_);
lean_dec_ref(v___y_4725_);
lean_dec_ref(v_a_4722_);
lean_dec_ref(v_removed_4721_);
lean_dec(v_upperBound_4720_);
return v_res_4730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(lean_object* v_a_4731_, lean_object* v_f_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_){
_start:
{
lean_object* v___x_4738_; uint8_t v___x_4739_; lean_object* v___x_4740_; lean_object* v_removed_4741_; lean_object* v_numRemoved_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; 
v___x_4738_ = lean_array_get_size(v_a_4731_);
v___x_4739_ = 0;
v___x_4740_ = lean_box(v___x_4739_);
v_removed_4741_ = lean_mk_array(v___x_4738_, v___x_4740_);
v_numRemoved_4742_ = lean_unsigned_to_nat(0u);
v___x_4743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4743_, 0, v_removed_4741_);
lean_ctor_set(v___x_4743_, 1, v_numRemoved_4742_);
v___x_4744_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v___x_4738_, v___x_4738_, v_a_4731_, v_f_4732_, v_numRemoved_4742_, v___x_4743_, v___y_4733_, v___y_4734_, v___y_4735_, v___y_4736_);
if (lean_obj_tag(v___x_4744_) == 0)
{
lean_object* v_a_4745_; lean_object* v_fst_4746_; lean_object* v_snd_4747_; lean_object* v_a_x27_4748_; lean_object* v___x_4749_; 
v_a_4745_ = lean_ctor_get(v___x_4744_, 0);
lean_inc(v_a_4745_);
lean_dec_ref_known(v___x_4744_, 1);
v_fst_4746_ = lean_ctor_get(v_a_4745_, 0);
lean_inc(v_fst_4746_);
v_snd_4747_ = lean_ctor_get(v_a_4745_, 1);
lean_inc(v_snd_4747_);
lean_dec(v_a_4745_);
v_a_x27_4748_ = lean_mk_empty_array_with_capacity(v_snd_4747_);
lean_dec(v_snd_4747_);
v___x_4749_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v___x_4738_, v_fst_4746_, v_a_4731_, v_numRemoved_4742_, v_a_x27_4748_, v___y_4733_, v___y_4734_, v___y_4735_, v___y_4736_);
lean_dec(v_fst_4746_);
return v___x_4749_;
}
else
{
lean_object* v_a_4750_; lean_object* v___x_4752_; uint8_t v_isShared_4753_; uint8_t v_isSharedCheck_4757_; 
v_a_4750_ = lean_ctor_get(v___x_4744_, 0);
v_isSharedCheck_4757_ = !lean_is_exclusive(v___x_4744_);
if (v_isSharedCheck_4757_ == 0)
{
v___x_4752_ = v___x_4744_;
v_isShared_4753_ = v_isSharedCheck_4757_;
goto v_resetjp_4751_;
}
else
{
lean_inc(v_a_4750_);
lean_dec(v___x_4744_);
v___x_4752_ = lean_box(0);
v_isShared_4753_ = v_isSharedCheck_4757_;
goto v_resetjp_4751_;
}
v_resetjp_4751_:
{
lean_object* v___x_4755_; 
if (v_isShared_4753_ == 0)
{
v___x_4755_ = v___x_4752_;
goto v_reusejp_4754_;
}
else
{
lean_object* v_reuseFailAlloc_4756_; 
v_reuseFailAlloc_4756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4756_, 0, v_a_4750_);
v___x_4755_ = v_reuseFailAlloc_4756_;
goto v_reusejp_4754_;
}
v_reusejp_4754_:
{
return v___x_4755_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg___boxed(lean_object* v_a_4758_, lean_object* v_f_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_){
_start:
{
lean_object* v_res_4765_; 
v_res_4765_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_a_4758_, v_f_4759_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_);
lean_dec(v___y_4763_);
lean_dec_ref(v___y_4762_);
lean_dec(v___y_4761_);
lean_dec_ref(v___y_4760_);
lean_dec_ref(v_a_4758_);
return v_res_4765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed(lean_object* v_mvars_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_){
_start:
{
lean_object* v___f_4773_; lean_object* v___x_4774_; 
v___f_4773_ = ((lean_object*)(l_Lean_Elab_WF_assignSubsumed___closed__0));
v___x_4774_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_mvars_4767_, v___f_4773_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_);
return v___x_4774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___boxed(lean_object* v_mvars_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_, lean_object* v_a_4779_, lean_object* v_a_4780_){
_start:
{
lean_object* v_res_4781_; 
v_res_4781_ = l_Lean_Elab_WF_assignSubsumed(v_mvars_4775_, v_a_4776_, v_a_4777_, v_a_4778_, v_a_4779_);
lean_dec(v_a_4779_);
lean_dec_ref(v_a_4778_);
lean_dec(v_a_4777_);
lean_dec_ref(v_a_4776_);
lean_dec_ref(v_mvars_4775_);
return v_res_4781_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0(lean_object* v_mvarId_4782_, lean_object* v_val_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_){
_start:
{
lean_object* v___x_4789_; 
v___x_4789_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mvarId_4782_, v_val_4783_, v___y_4785_);
return v___x_4789_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___boxed(lean_object* v_mvarId_4790_, lean_object* v_val_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_){
_start:
{
lean_object* v_res_4797_; 
v_res_4797_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0(v_mvarId_4790_, v_val_4791_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_);
lean_dec(v___y_4795_);
lean_dec_ref(v___y_4794_);
lean_dec(v___y_4793_);
lean_dec_ref(v___y_4792_);
return v_res_4797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1(lean_object* v_00_u03b1_4798_, lean_object* v_a_4799_, lean_object* v_f_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_){
_start:
{
lean_object* v___x_4806_; 
v___x_4806_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_a_4799_, v_f_4800_, v___y_4801_, v___y_4802_, v___y_4803_, v___y_4804_);
return v___x_4806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___boxed(lean_object* v_00_u03b1_4807_, lean_object* v_a_4808_, lean_object* v_f_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_){
_start:
{
lean_object* v_res_4815_; 
v_res_4815_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1(v_00_u03b1_4807_, v_a_4808_, v_f_4809_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_);
lean_dec(v___y_4813_);
lean_dec_ref(v___y_4812_);
lean_dec(v___y_4811_);
lean_dec_ref(v___y_4810_);
lean_dec_ref(v_a_4808_);
return v_res_4815_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0(lean_object* v_00_u03b2_4816_, lean_object* v_x_4817_, lean_object* v_x_4818_, lean_object* v_x_4819_){
_start:
{
lean_object* v___x_4820_; 
v___x_4820_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(v_x_4817_, v_x_4818_, v_x_4819_);
return v___x_4820_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2(lean_object* v_upperBound_4821_, lean_object* v_00_u03b1_4822_, lean_object* v_a_4823_, lean_object* v_next_4824_, lean_object* v_f_4825_, lean_object* v_inst_4826_, lean_object* v_R_4827_, lean_object* v_a_4828_, lean_object* v_b_4829_, lean_object* v_c_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_){
_start:
{
lean_object* v___x_4836_; 
v___x_4836_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v_upperBound_4821_, v_a_4823_, v_next_4824_, v_f_4825_, v_a_4828_, v_b_4829_, v___y_4831_, v___y_4832_, v___y_4833_, v___y_4834_);
return v___x_4836_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___boxed(lean_object* v_upperBound_4837_, lean_object* v_00_u03b1_4838_, lean_object* v_a_4839_, lean_object* v_next_4840_, lean_object* v_f_4841_, lean_object* v_inst_4842_, lean_object* v_R_4843_, lean_object* v_a_4844_, lean_object* v_b_4845_, lean_object* v_c_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_, lean_object* v___y_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_){
_start:
{
lean_object* v_res_4852_; 
v_res_4852_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2(v_upperBound_4837_, v_00_u03b1_4838_, v_a_4839_, v_next_4840_, v_f_4841_, v_inst_4842_, v_R_4843_, v_a_4844_, v_b_4845_, v_c_4846_, v___y_4847_, v___y_4848_, v___y_4849_, v___y_4850_);
lean_dec(v___y_4850_);
lean_dec_ref(v___y_4849_);
lean_dec(v___y_4848_);
lean_dec_ref(v___y_4847_);
lean_dec_ref(v_a_4839_);
lean_dec(v_upperBound_4837_);
return v_res_4852_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3(lean_object* v_00_u03b1_4853_, lean_object* v_upperBound_4854_, lean_object* v_removed_4855_, lean_object* v_a_4856_, lean_object* v_inst_4857_, lean_object* v_R_4858_, lean_object* v_a_4859_, lean_object* v_b_4860_, lean_object* v_c_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_, lean_object* v___y_4865_){
_start:
{
lean_object* v___x_4867_; 
v___x_4867_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v_upperBound_4854_, v_removed_4855_, v_a_4856_, v_a_4859_, v_b_4860_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_);
return v___x_4867_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___boxed(lean_object* v_00_u03b1_4868_, lean_object* v_upperBound_4869_, lean_object* v_removed_4870_, lean_object* v_a_4871_, lean_object* v_inst_4872_, lean_object* v_R_4873_, lean_object* v_a_4874_, lean_object* v_b_4875_, lean_object* v_c_4876_, lean_object* v___y_4877_, lean_object* v___y_4878_, lean_object* v___y_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_){
_start:
{
lean_object* v_res_4882_; 
v_res_4882_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3(v_00_u03b1_4868_, v_upperBound_4869_, v_removed_4870_, v_a_4871_, v_inst_4872_, v_R_4873_, v_a_4874_, v_b_4875_, v_c_4876_, v___y_4877_, v___y_4878_, v___y_4879_, v___y_4880_);
lean_dec(v___y_4880_);
lean_dec_ref(v___y_4879_);
lean_dec(v___y_4878_);
lean_dec_ref(v___y_4877_);
lean_dec_ref(v_a_4871_);
lean_dec_ref(v_removed_4870_);
lean_dec(v_upperBound_4869_);
return v_res_4882_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4(lean_object* v_upperBound_4883_, lean_object* v___x_4884_, lean_object* v_00_u03b1_4885_, lean_object* v_a_4886_, lean_object* v_f_4887_, lean_object* v_inst_4888_, lean_object* v_R_4889_, lean_object* v_a_4890_, lean_object* v_b_4891_, lean_object* v_c_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_, lean_object* v___y_4896_){
_start:
{
lean_object* v___x_4898_; 
v___x_4898_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v_upperBound_4883_, v___x_4884_, v_a_4886_, v_f_4887_, v_a_4890_, v_b_4891_, v___y_4893_, v___y_4894_, v___y_4895_, v___y_4896_);
return v___x_4898_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___boxed(lean_object* v_upperBound_4899_, lean_object* v___x_4900_, lean_object* v_00_u03b1_4901_, lean_object* v_a_4902_, lean_object* v_f_4903_, lean_object* v_inst_4904_, lean_object* v_R_4905_, lean_object* v_a_4906_, lean_object* v_b_4907_, lean_object* v_c_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_){
_start:
{
lean_object* v_res_4914_; 
v_res_4914_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4(v_upperBound_4899_, v___x_4900_, v_00_u03b1_4901_, v_a_4902_, v_f_4903_, v_inst_4904_, v_R_4905_, v_a_4906_, v_b_4907_, v_c_4908_, v___y_4909_, v___y_4910_, v___y_4911_, v___y_4912_);
lean_dec(v___y_4912_);
lean_dec_ref(v___y_4911_);
lean_dec(v___y_4910_);
lean_dec_ref(v___y_4909_);
lean_dec_ref(v_a_4902_);
lean_dec(v___x_4900_);
lean_dec(v_upperBound_4899_);
return v_res_4914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4915_, lean_object* v_x_4916_, size_t v_x_4917_, size_t v_x_4918_, lean_object* v_x_4919_, lean_object* v_x_4920_){
_start:
{
lean_object* v___x_4921_; 
v___x_4921_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4916_, v_x_4917_, v_x_4918_, v_x_4919_, v_x_4920_);
return v___x_4921_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4922_, lean_object* v_x_4923_, lean_object* v_x_4924_, lean_object* v_x_4925_, lean_object* v_x_4926_, lean_object* v_x_4927_){
_start:
{
size_t v_x_4925__boxed_4928_; size_t v_x_4926__boxed_4929_; lean_object* v_res_4930_; 
v_x_4925__boxed_4928_ = lean_unbox_usize(v_x_4924_);
lean_dec(v_x_4924_);
v_x_4926__boxed_4929_ = lean_unbox_usize(v_x_4925_);
lean_dec(v_x_4925_);
v_res_4930_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1(v_00_u03b2_4922_, v_x_4923_, v_x_4925__boxed_4928_, v_x_4926__boxed_4929_, v_x_4926_, v_x_4927_);
return v_res_4930_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_4931_, lean_object* v_n_4932_, lean_object* v_k_4933_, lean_object* v_v_4934_){
_start:
{
lean_object* v___x_4935_; 
v___x_4935_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(v_n_4932_, v_k_4933_, v_v_4934_);
return v___x_4935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_4936_, size_t v_depth_4937_, lean_object* v_keys_4938_, lean_object* v_vals_4939_, lean_object* v_heq_4940_, lean_object* v_i_4941_, lean_object* v_entries_4942_){
_start:
{
lean_object* v___x_4943_; 
v___x_4943_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_4937_, v_keys_4938_, v_vals_4939_, v_i_4941_, v_entries_4942_);
return v___x_4943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_4944_, lean_object* v_depth_4945_, lean_object* v_keys_4946_, lean_object* v_vals_4947_, lean_object* v_heq_4948_, lean_object* v_i_4949_, lean_object* v_entries_4950_){
_start:
{
size_t v_depth_boxed_4951_; lean_object* v_res_4952_; 
v_depth_boxed_4951_ = lean_unbox_usize(v_depth_4945_);
lean_dec(v_depth_4945_);
v_res_4952_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_4944_, v_depth_boxed_4951_, v_keys_4946_, v_vals_4947_, v_heq_4948_, v_i_4949_, v_entries_4950_);
lean_dec_ref(v_vals_4947_);
lean_dec_ref(v_keys_4946_);
return v_res_4952_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_4953_, lean_object* v_x_4954_, lean_object* v_x_4955_, lean_object* v_x_4956_, lean_object* v_x_4957_){
_start:
{
lean_object* v___x_4958_; 
v___x_4958_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_x_4954_, v_x_4955_, v_x_4956_, v_x_4957_);
return v___x_4958_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4960_; lean_object* v___x_4961_; 
v___x_4960_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__0));
v___x_4961_ = l_Lean_stringToMessageData(v___x_4960_);
return v___x_4961_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4963_; lean_object* v___x_4964_; 
v___x_4963_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__2));
v___x_4964_ = l_Lean_stringToMessageData(v___x_4963_);
return v___x_4964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(lean_object* v_argsPacker_4965_, lean_object* v_as_4966_, size_t v_sz_4967_, size_t v_i_4968_, lean_object* v_b_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_){
_start:
{
lean_object* v_a_4976_; uint8_t v___x_4980_; 
v___x_4980_ = lean_usize_dec_lt(v_i_4968_, v_sz_4967_);
if (v___x_4980_ == 0)
{
lean_object* v___x_4981_; 
v___x_4981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4981_, 0, v_b_4969_);
return v___x_4981_;
}
else
{
lean_object* v_a_4982_; lean_object* v___x_4983_; 
v_a_4982_ = lean_array_uget_borrowed(v_as_4966_, v_i_4968_);
lean_inc(v_a_4982_);
v___x_4983_ = l_Lean_MVarId_getType(v_a_4982_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_);
if (lean_obj_tag(v___x_4983_) == 0)
{
lean_object* v_a_4984_; lean_object* v___y_4986_; lean_object* v___y_4987_; lean_object* v___y_4988_; lean_object* v___y_4989_; 
v_a_4984_ = lean_ctor_get(v___x_4983_, 0);
lean_inc(v_a_4984_);
lean_dec_ref_known(v___x_4983_, 1);
if (lean_obj_tag(v_a_4984_) == 10)
{
lean_object* v_expr_5002_; 
v_expr_5002_ = lean_ctor_get(v_a_4984_, 1);
if (lean_obj_tag(v_expr_5002_) == 5)
{
lean_object* v_arg_5003_; lean_object* v___x_5004_; 
lean_inc_ref(v_expr_5002_);
lean_dec_ref_known(v_a_4984_, 2);
v_arg_5003_ = lean_ctor_get(v_expr_5002_, 1);
lean_inc_ref_n(v_arg_5003_, 2);
lean_dec_ref_known(v_expr_5002_, 2);
v___x_5004_ = l_Lean_Meta_ArgsPacker_unpack(v_argsPacker_4965_, v_arg_5003_);
if (lean_obj_tag(v___x_5004_) == 1)
{
lean_object* v_val_5005_; lean_object* v_fst_5006_; lean_object* v___x_5007_; uint8_t v___x_5008_; 
lean_dec_ref(v_arg_5003_);
v_val_5005_ = lean_ctor_get(v___x_5004_, 0);
lean_inc(v_val_5005_);
lean_dec_ref_known(v___x_5004_, 1);
v_fst_5006_ = lean_ctor_get(v_val_5005_, 0);
lean_inc(v_fst_5006_);
lean_dec(v_val_5005_);
v___x_5007_ = lean_array_get_size(v_b_4969_);
v___x_5008_ = lean_nat_dec_lt(v_fst_5006_, v___x_5007_);
if (v___x_5008_ == 0)
{
lean_dec(v_fst_5006_);
v_a_4976_ = v_b_4969_;
goto v___jp_4975_;
}
else
{
lean_object* v_v_5009_; lean_object* v___x_5010_; lean_object* v_xs_x27_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; 
v_v_5009_ = lean_array_fget(v_b_4969_, v_fst_5006_);
v___x_5010_ = lean_box(0);
v_xs_x27_5011_ = lean_array_fset(v_b_4969_, v_fst_5006_, v___x_5010_);
lean_inc(v_a_4982_);
v___x_5012_ = lean_array_push(v_v_5009_, v_a_4982_);
v___x_5013_ = lean_array_fset(v_xs_x27_5011_, v_fst_5006_, v___x_5012_);
lean_dec(v_fst_5006_);
v_a_4976_ = v___x_5013_;
goto v___jp_4975_;
}
}
else
{
lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; 
lean_dec(v___x_5004_);
v___x_5014_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3);
v___x_5015_ = l_Lean_indentExpr(v_arg_5003_);
v___x_5016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5016_, 0, v___x_5014_);
lean_ctor_set(v___x_5016_, 1, v___x_5015_);
v___x_5017_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v___x_5016_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_);
if (lean_obj_tag(v___x_5017_) == 0)
{
lean_dec_ref_known(v___x_5017_, 1);
v_a_4976_ = v_b_4969_;
goto v___jp_4975_;
}
else
{
lean_object* v_a_5018_; lean_object* v___x_5020_; uint8_t v_isShared_5021_; uint8_t v_isSharedCheck_5025_; 
lean_dec_ref(v_b_4969_);
v_a_5018_ = lean_ctor_get(v___x_5017_, 0);
v_isSharedCheck_5025_ = !lean_is_exclusive(v___x_5017_);
if (v_isSharedCheck_5025_ == 0)
{
v___x_5020_ = v___x_5017_;
v_isShared_5021_ = v_isSharedCheck_5025_;
goto v_resetjp_5019_;
}
else
{
lean_inc(v_a_5018_);
lean_dec(v___x_5017_);
v___x_5020_ = lean_box(0);
v_isShared_5021_ = v_isSharedCheck_5025_;
goto v_resetjp_5019_;
}
v_resetjp_5019_:
{
lean_object* v___x_5023_; 
if (v_isShared_5021_ == 0)
{
v___x_5023_ = v___x_5020_;
goto v_reusejp_5022_;
}
else
{
lean_object* v_reuseFailAlloc_5024_; 
v_reuseFailAlloc_5024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5024_, 0, v_a_5018_);
v___x_5023_ = v_reuseFailAlloc_5024_;
goto v_reusejp_5022_;
}
v_reusejp_5022_:
{
return v___x_5023_;
}
}
}
}
}
else
{
v___y_4986_ = v___y_4970_;
v___y_4987_ = v___y_4971_;
v___y_4988_ = v___y_4972_;
v___y_4989_ = v___y_4973_;
goto v___jp_4985_;
}
}
else
{
v___y_4986_ = v___y_4970_;
v___y_4987_ = v___y_4971_;
v___y_4988_ = v___y_4972_;
v___y_4989_ = v___y_4973_;
goto v___jp_4985_;
}
v___jp_4985_:
{
lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; 
v___x_4990_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1);
v___x_4991_ = l_Lean_indentExpr(v_a_4984_);
v___x_4992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4992_, 0, v___x_4990_);
lean_ctor_set(v___x_4992_, 1, v___x_4991_);
v___x_4993_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v___x_4992_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_);
if (lean_obj_tag(v___x_4993_) == 0)
{
lean_dec_ref_known(v___x_4993_, 1);
v_a_4976_ = v_b_4969_;
goto v___jp_4975_;
}
else
{
lean_object* v_a_4994_; lean_object* v___x_4996_; uint8_t v_isShared_4997_; uint8_t v_isSharedCheck_5001_; 
lean_dec_ref(v_b_4969_);
v_a_4994_ = lean_ctor_get(v___x_4993_, 0);
v_isSharedCheck_5001_ = !lean_is_exclusive(v___x_4993_);
if (v_isSharedCheck_5001_ == 0)
{
v___x_4996_ = v___x_4993_;
v_isShared_4997_ = v_isSharedCheck_5001_;
goto v_resetjp_4995_;
}
else
{
lean_inc(v_a_4994_);
lean_dec(v___x_4993_);
v___x_4996_ = lean_box(0);
v_isShared_4997_ = v_isSharedCheck_5001_;
goto v_resetjp_4995_;
}
v_resetjp_4995_:
{
lean_object* v___x_4999_; 
if (v_isShared_4997_ == 0)
{
v___x_4999_ = v___x_4996_;
goto v_reusejp_4998_;
}
else
{
lean_object* v_reuseFailAlloc_5000_; 
v_reuseFailAlloc_5000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5000_, 0, v_a_4994_);
v___x_4999_ = v_reuseFailAlloc_5000_;
goto v_reusejp_4998_;
}
v_reusejp_4998_:
{
return v___x_4999_;
}
}
}
}
}
else
{
lean_object* v_a_5026_; lean_object* v___x_5028_; uint8_t v_isShared_5029_; uint8_t v_isSharedCheck_5033_; 
lean_dec_ref(v_b_4969_);
v_a_5026_ = lean_ctor_get(v___x_4983_, 0);
v_isSharedCheck_5033_ = !lean_is_exclusive(v___x_4983_);
if (v_isSharedCheck_5033_ == 0)
{
v___x_5028_ = v___x_4983_;
v_isShared_5029_ = v_isSharedCheck_5033_;
goto v_resetjp_5027_;
}
else
{
lean_inc(v_a_5026_);
lean_dec(v___x_4983_);
v___x_5028_ = lean_box(0);
v_isShared_5029_ = v_isSharedCheck_5033_;
goto v_resetjp_5027_;
}
v_resetjp_5027_:
{
lean_object* v___x_5031_; 
if (v_isShared_5029_ == 0)
{
v___x_5031_ = v___x_5028_;
goto v_reusejp_5030_;
}
else
{
lean_object* v_reuseFailAlloc_5032_; 
v_reuseFailAlloc_5032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5032_, 0, v_a_5026_);
v___x_5031_ = v_reuseFailAlloc_5032_;
goto v_reusejp_5030_;
}
v_reusejp_5030_:
{
return v___x_5031_;
}
}
}
}
v___jp_4975_:
{
size_t v___x_4977_; size_t v___x_4978_; 
v___x_4977_ = ((size_t)1ULL);
v___x_4978_ = lean_usize_add(v_i_4968_, v___x_4977_);
v_i_4968_ = v___x_4978_;
v_b_4969_ = v_a_4976_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___boxed(lean_object* v_argsPacker_5034_, lean_object* v_as_5035_, lean_object* v_sz_5036_, lean_object* v_i_5037_, lean_object* v_b_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_){
_start:
{
size_t v_sz_boxed_5044_; size_t v_i_boxed_5045_; lean_object* v_res_5046_; 
v_sz_boxed_5044_ = lean_unbox_usize(v_sz_5036_);
lean_dec(v_sz_5036_);
v_i_boxed_5045_ = lean_unbox_usize(v_i_5037_);
lean_dec(v_i_5037_);
v_res_5046_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(v_argsPacker_5034_, v_as_5035_, v_sz_boxed_5044_, v_i_boxed_5045_, v_b_5038_, v___y_5039_, v___y_5040_, v___y_5041_, v___y_5042_);
lean_dec(v___y_5042_);
lean_dec_ref(v___y_5041_);
lean_dec(v___y_5040_);
lean_dec_ref(v___y_5039_);
lean_dec_ref(v_as_5035_);
lean_dec_ref(v_argsPacker_5034_);
return v_res_5046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_groupGoalsByFunction(lean_object* v_argsPacker_5047_, lean_object* v_numFuncs_5048_, lean_object* v_goals_5049_, lean_object* v_a_5050_, lean_object* v_a_5051_, lean_object* v_a_5052_, lean_object* v_a_5053_){
_start:
{
lean_object* v___x_5055_; lean_object* v_r_5056_; size_t v_sz_5057_; size_t v___x_5058_; lean_object* v___x_5059_; 
v___x_5055_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg___closed__0));
v_r_5056_ = lean_mk_array(v_numFuncs_5048_, v___x_5055_);
v_sz_5057_ = lean_array_size(v_goals_5049_);
v___x_5058_ = ((size_t)0ULL);
v___x_5059_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(v_argsPacker_5047_, v_goals_5049_, v_sz_5057_, v___x_5058_, v_r_5056_, v_a_5050_, v_a_5051_, v_a_5052_, v_a_5053_);
return v___x_5059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_groupGoalsByFunction___boxed(lean_object* v_argsPacker_5060_, lean_object* v_numFuncs_5061_, lean_object* v_goals_5062_, lean_object* v_a_5063_, lean_object* v_a_5064_, lean_object* v_a_5065_, lean_object* v_a_5066_, lean_object* v_a_5067_){
_start:
{
lean_object* v_res_5068_; 
v_res_5068_ = l_Lean_Elab_WF_groupGoalsByFunction(v_argsPacker_5060_, v_numFuncs_5061_, v_goals_5062_, v_a_5063_, v_a_5064_, v_a_5065_, v_a_5066_);
lean_dec(v_a_5066_);
lean_dec_ref(v_a_5065_);
lean_dec(v_a_5064_);
lean_dec_ref(v_a_5063_);
lean_dec_ref(v_goals_5062_);
lean_dec_ref(v_argsPacker_5060_);
return v_res_5068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(lean_object* v_t_5069_, lean_object* v___y_5070_){
_start:
{
lean_object* v___x_5072_; lean_object* v_infoState_5073_; uint8_t v_enabled_5074_; 
v___x_5072_ = lean_st_ref_get(v___y_5070_);
v_infoState_5073_ = lean_ctor_get(v___x_5072_, 7);
lean_inc_ref(v_infoState_5073_);
lean_dec(v___x_5072_);
v_enabled_5074_ = lean_ctor_get_uint8(v_infoState_5073_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5073_);
if (v_enabled_5074_ == 0)
{
lean_object* v___x_5075_; lean_object* v___x_5076_; 
lean_dec_ref(v_t_5069_);
v___x_5075_ = lean_box(0);
v___x_5076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5076_, 0, v___x_5075_);
return v___x_5076_;
}
else
{
lean_object* v___x_5077_; lean_object* v_infoState_5078_; lean_object* v_env_5079_; lean_object* v_nextMacroScope_5080_; lean_object* v_ngen_5081_; lean_object* v_auxDeclNGen_5082_; lean_object* v_traceState_5083_; lean_object* v_cache_5084_; lean_object* v_messages_5085_; lean_object* v_snapshotTasks_5086_; lean_object* v___x_5088_; uint8_t v_isShared_5089_; uint8_t v_isSharedCheck_5108_; 
v___x_5077_ = lean_st_ref_take(v___y_5070_);
v_infoState_5078_ = lean_ctor_get(v___x_5077_, 7);
v_env_5079_ = lean_ctor_get(v___x_5077_, 0);
v_nextMacroScope_5080_ = lean_ctor_get(v___x_5077_, 1);
v_ngen_5081_ = lean_ctor_get(v___x_5077_, 2);
v_auxDeclNGen_5082_ = lean_ctor_get(v___x_5077_, 3);
v_traceState_5083_ = lean_ctor_get(v___x_5077_, 4);
v_cache_5084_ = lean_ctor_get(v___x_5077_, 5);
v_messages_5085_ = lean_ctor_get(v___x_5077_, 6);
v_snapshotTasks_5086_ = lean_ctor_get(v___x_5077_, 8);
v_isSharedCheck_5108_ = !lean_is_exclusive(v___x_5077_);
if (v_isSharedCheck_5108_ == 0)
{
v___x_5088_ = v___x_5077_;
v_isShared_5089_ = v_isSharedCheck_5108_;
goto v_resetjp_5087_;
}
else
{
lean_inc(v_snapshotTasks_5086_);
lean_inc(v_infoState_5078_);
lean_inc(v_messages_5085_);
lean_inc(v_cache_5084_);
lean_inc(v_traceState_5083_);
lean_inc(v_auxDeclNGen_5082_);
lean_inc(v_ngen_5081_);
lean_inc(v_nextMacroScope_5080_);
lean_inc(v_env_5079_);
lean_dec(v___x_5077_);
v___x_5088_ = lean_box(0);
v_isShared_5089_ = v_isSharedCheck_5108_;
goto v_resetjp_5087_;
}
v_resetjp_5087_:
{
uint8_t v_enabled_5090_; lean_object* v_assignment_5091_; lean_object* v_lazyAssignment_5092_; lean_object* v_trees_5093_; lean_object* v___x_5095_; uint8_t v_isShared_5096_; uint8_t v_isSharedCheck_5107_; 
v_enabled_5090_ = lean_ctor_get_uint8(v_infoState_5078_, sizeof(void*)*3);
v_assignment_5091_ = lean_ctor_get(v_infoState_5078_, 0);
v_lazyAssignment_5092_ = lean_ctor_get(v_infoState_5078_, 1);
v_trees_5093_ = lean_ctor_get(v_infoState_5078_, 2);
v_isSharedCheck_5107_ = !lean_is_exclusive(v_infoState_5078_);
if (v_isSharedCheck_5107_ == 0)
{
v___x_5095_ = v_infoState_5078_;
v_isShared_5096_ = v_isSharedCheck_5107_;
goto v_resetjp_5094_;
}
else
{
lean_inc(v_trees_5093_);
lean_inc(v_lazyAssignment_5092_);
lean_inc(v_assignment_5091_);
lean_dec(v_infoState_5078_);
v___x_5095_ = lean_box(0);
v_isShared_5096_ = v_isSharedCheck_5107_;
goto v_resetjp_5094_;
}
v_resetjp_5094_:
{
lean_object* v___x_5097_; lean_object* v___x_5099_; 
v___x_5097_ = l_Lean_PersistentArray_push___redArg(v_trees_5093_, v_t_5069_);
if (v_isShared_5096_ == 0)
{
lean_ctor_set(v___x_5095_, 2, v___x_5097_);
v___x_5099_ = v___x_5095_;
goto v_reusejp_5098_;
}
else
{
lean_object* v_reuseFailAlloc_5106_; 
v_reuseFailAlloc_5106_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5106_, 0, v_assignment_5091_);
lean_ctor_set(v_reuseFailAlloc_5106_, 1, v_lazyAssignment_5092_);
lean_ctor_set(v_reuseFailAlloc_5106_, 2, v___x_5097_);
lean_ctor_set_uint8(v_reuseFailAlloc_5106_, sizeof(void*)*3, v_enabled_5090_);
v___x_5099_ = v_reuseFailAlloc_5106_;
goto v_reusejp_5098_;
}
v_reusejp_5098_:
{
lean_object* v___x_5101_; 
if (v_isShared_5089_ == 0)
{
lean_ctor_set(v___x_5088_, 7, v___x_5099_);
v___x_5101_ = v___x_5088_;
goto v_reusejp_5100_;
}
else
{
lean_object* v_reuseFailAlloc_5105_; 
v_reuseFailAlloc_5105_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5105_, 0, v_env_5079_);
lean_ctor_set(v_reuseFailAlloc_5105_, 1, v_nextMacroScope_5080_);
lean_ctor_set(v_reuseFailAlloc_5105_, 2, v_ngen_5081_);
lean_ctor_set(v_reuseFailAlloc_5105_, 3, v_auxDeclNGen_5082_);
lean_ctor_set(v_reuseFailAlloc_5105_, 4, v_traceState_5083_);
lean_ctor_set(v_reuseFailAlloc_5105_, 5, v_cache_5084_);
lean_ctor_set(v_reuseFailAlloc_5105_, 6, v_messages_5085_);
lean_ctor_set(v_reuseFailAlloc_5105_, 7, v___x_5099_);
lean_ctor_set(v_reuseFailAlloc_5105_, 8, v_snapshotTasks_5086_);
v___x_5101_ = v_reuseFailAlloc_5105_;
goto v_reusejp_5100_;
}
v_reusejp_5100_:
{
lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; 
v___x_5102_ = lean_st_ref_put(v___y_5070_, v___x_5101_);
v___x_5103_ = lean_box(0);
v___x_5104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5104_, 0, v___x_5103_);
return v___x_5104_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg___boxed(lean_object* v_t_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_){
_start:
{
lean_object* v_res_5112_; 
v_res_5112_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v_t_5109_, v___y_5110_);
lean_dec(v___y_5110_);
return v_res_5112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0(lean_object* v_t_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_){
_start:
{
lean_object* v___x_5121_; 
v___x_5121_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v_t_5113_, v___y_5119_);
return v___x_5121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___boxed(lean_object* v_t_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_){
_start:
{
lean_object* v_res_5130_; 
v_res_5130_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0(v_t_5122_, v___y_5123_, v___y_5124_, v___y_5125_, v___y_5126_, v___y_5127_, v___y_5128_);
lean_dec(v___y_5128_);
lean_dec_ref(v___y_5127_);
lean_dec(v___y_5126_);
lean_dec_ref(v___y_5125_);
lean_dec(v___y_5124_);
lean_dec_ref(v___y_5123_);
return v_res_5130_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(lean_object* v_e_5131_, lean_object* v___y_5132_){
_start:
{
uint8_t v___x_5134_; 
v___x_5134_ = l_Lean_Expr_hasMVar(v_e_5131_);
if (v___x_5134_ == 0)
{
lean_object* v___x_5135_; 
v___x_5135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5135_, 0, v_e_5131_);
return v___x_5135_;
}
else
{
lean_object* v___x_5136_; lean_object* v_mctx_5137_; lean_object* v___x_5138_; lean_object* v_fst_5139_; lean_object* v_snd_5140_; lean_object* v___x_5141_; lean_object* v_cache_5142_; lean_object* v_zetaDeltaFVarIds_5143_; lean_object* v_postponed_5144_; lean_object* v_diag_5145_; lean_object* v___x_5147_; uint8_t v_isShared_5148_; uint8_t v_isSharedCheck_5154_; 
v___x_5136_ = lean_st_ref_get(v___y_5132_);
v_mctx_5137_ = lean_ctor_get(v___x_5136_, 0);
lean_inc_ref(v_mctx_5137_);
lean_dec(v___x_5136_);
v___x_5138_ = l_Lean_instantiateMVarsCore(v_mctx_5137_, v_e_5131_);
v_fst_5139_ = lean_ctor_get(v___x_5138_, 0);
lean_inc(v_fst_5139_);
v_snd_5140_ = lean_ctor_get(v___x_5138_, 1);
lean_inc(v_snd_5140_);
lean_dec_ref(v___x_5138_);
v___x_5141_ = lean_st_ref_take(v___y_5132_);
v_cache_5142_ = lean_ctor_get(v___x_5141_, 1);
v_zetaDeltaFVarIds_5143_ = lean_ctor_get(v___x_5141_, 2);
v_postponed_5144_ = lean_ctor_get(v___x_5141_, 3);
v_diag_5145_ = lean_ctor_get(v___x_5141_, 4);
v_isSharedCheck_5154_ = !lean_is_exclusive(v___x_5141_);
if (v_isSharedCheck_5154_ == 0)
{
lean_object* v_unused_5155_; 
v_unused_5155_ = lean_ctor_get(v___x_5141_, 0);
lean_dec(v_unused_5155_);
v___x_5147_ = v___x_5141_;
v_isShared_5148_ = v_isSharedCheck_5154_;
goto v_resetjp_5146_;
}
else
{
lean_inc(v_diag_5145_);
lean_inc(v_postponed_5144_);
lean_inc(v_zetaDeltaFVarIds_5143_);
lean_inc(v_cache_5142_);
lean_dec(v___x_5141_);
v___x_5147_ = lean_box(0);
v_isShared_5148_ = v_isSharedCheck_5154_;
goto v_resetjp_5146_;
}
v_resetjp_5146_:
{
lean_object* v___x_5150_; 
if (v_isShared_5148_ == 0)
{
lean_ctor_set(v___x_5147_, 0, v_snd_5140_);
v___x_5150_ = v___x_5147_;
goto v_reusejp_5149_;
}
else
{
lean_object* v_reuseFailAlloc_5153_; 
v_reuseFailAlloc_5153_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5153_, 0, v_snd_5140_);
lean_ctor_set(v_reuseFailAlloc_5153_, 1, v_cache_5142_);
lean_ctor_set(v_reuseFailAlloc_5153_, 2, v_zetaDeltaFVarIds_5143_);
lean_ctor_set(v_reuseFailAlloc_5153_, 3, v_postponed_5144_);
lean_ctor_set(v_reuseFailAlloc_5153_, 4, v_diag_5145_);
v___x_5150_ = v_reuseFailAlloc_5153_;
goto v_reusejp_5149_;
}
v_reusejp_5149_:
{
lean_object* v___x_5151_; lean_object* v___x_5152_; 
v___x_5151_ = lean_st_ref_put(v___y_5132_, v___x_5150_);
v___x_5152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5152_, 0, v_fst_5139_);
return v___x_5152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg___boxed(lean_object* v_e_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_){
_start:
{
lean_object* v_res_5159_; 
v_res_5159_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_e_5156_, v___y_5157_);
lean_dec(v___y_5157_);
return v_res_5159_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7(lean_object* v_e_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_){
_start:
{
lean_object* v___x_5166_; 
v___x_5166_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_e_5160_, v___y_5162_);
return v___x_5166_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___boxed(lean_object* v_e_5167_, lean_object* v___y_5168_, lean_object* v___y_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_){
_start:
{
lean_object* v_res_5173_; 
v_res_5173_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7(v_e_5167_, v___y_5168_, v___y_5169_, v___y_5170_, v___y_5171_);
lean_dec(v___y_5171_);
lean_dec_ref(v___y_5170_);
lean_dec(v___y_5169_);
lean_dec_ref(v___y_5168_);
return v_res_5173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(lean_object* v_as_5174_, size_t v_i_5175_, size_t v_stop_5176_, lean_object* v_b_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_, lean_object* v___y_5180_, lean_object* v___y_5181_, lean_object* v___y_5182_, lean_object* v___y_5183_){
_start:
{
uint8_t v___x_5185_; 
v___x_5185_ = lean_usize_dec_eq(v_i_5175_, v_stop_5176_);
if (v___x_5185_ == 0)
{
lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; 
v___x_5186_ = lean_array_uget_borrowed(v_as_5174_, v_i_5175_);
lean_inc(v___x_5186_);
v___x_5187_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_5187_, 0, v___x_5186_);
v___x_5188_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v___x_5187_, v___y_5183_);
if (lean_obj_tag(v___x_5188_) == 0)
{
lean_object* v_a_5189_; size_t v___x_5190_; size_t v___x_5191_; 
v_a_5189_ = lean_ctor_get(v___x_5188_, 0);
lean_inc(v_a_5189_);
lean_dec_ref_known(v___x_5188_, 1);
v___x_5190_ = ((size_t)1ULL);
v___x_5191_ = lean_usize_add(v_i_5175_, v___x_5190_);
v_i_5175_ = v___x_5191_;
v_b_5177_ = v_a_5189_;
goto _start;
}
else
{
return v___x_5188_;
}
}
else
{
lean_object* v___x_5193_; 
v___x_5193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5193_, 0, v_b_5177_);
return v___x_5193_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4___boxed(lean_object* v_as_5194_, lean_object* v_i_5195_, lean_object* v_stop_5196_, lean_object* v_b_5197_, lean_object* v___y_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_){
_start:
{
size_t v_i_boxed_5205_; size_t v_stop_boxed_5206_; lean_object* v_res_5207_; 
v_i_boxed_5205_ = lean_unbox_usize(v_i_5195_);
lean_dec(v_i_5195_);
v_stop_boxed_5206_ = lean_unbox_usize(v_stop_5196_);
lean_dec(v_stop_5196_);
v_res_5207_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v_as_5194_, v_i_boxed_5205_, v_stop_boxed_5206_, v_b_5197_, v___y_5198_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_, v___y_5203_);
lean_dec(v___y_5203_);
lean_dec_ref(v___y_5202_);
lean_dec(v___y_5201_);
lean_dec_ref(v___y_5200_);
lean_dec(v___y_5199_);
lean_dec_ref(v___y_5198_);
lean_dec_ref(v_as_5194_);
return v_res_5207_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_5208_; lean_object* v___x_5209_; lean_object* v___x_5210_; 
v___x_5208_ = lean_unsigned_to_nat(32u);
v___x_5209_ = lean_mk_empty_array_with_capacity(v___x_5208_);
v___x_5210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5210_, 0, v___x_5209_);
return v___x_5210_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; lean_object* v___x_5216_; 
v___x_5211_ = ((size_t)5ULL);
v___x_5212_ = lean_unsigned_to_nat(0u);
v___x_5213_ = lean_unsigned_to_nat(32u);
v___x_5214_ = lean_mk_empty_array_with_capacity(v___x_5213_);
v___x_5215_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0);
v___x_5216_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5216_, 0, v___x_5215_);
lean_ctor_set(v___x_5216_, 1, v___x_5214_);
lean_ctor_set(v___x_5216_, 2, v___x_5212_);
lean_ctor_set(v___x_5216_, 3, v___x_5212_);
lean_ctor_set_usize(v___x_5216_, 4, v___x_5211_);
return v___x_5216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(lean_object* v___y_5217_){
_start:
{
lean_object* v___x_5219_; lean_object* v_infoState_5220_; lean_object* v_trees_5221_; lean_object* v___x_5222_; lean_object* v_infoState_5223_; lean_object* v_env_5224_; lean_object* v_nextMacroScope_5225_; lean_object* v_ngen_5226_; lean_object* v_auxDeclNGen_5227_; lean_object* v_traceState_5228_; lean_object* v_cache_5229_; lean_object* v_messages_5230_; lean_object* v_snapshotTasks_5231_; lean_object* v___x_5233_; uint8_t v_isShared_5234_; uint8_t v_isSharedCheck_5252_; 
v___x_5219_ = lean_st_ref_get(v___y_5217_);
v_infoState_5220_ = lean_ctor_get(v___x_5219_, 7);
lean_inc_ref(v_infoState_5220_);
lean_dec(v___x_5219_);
v_trees_5221_ = lean_ctor_get(v_infoState_5220_, 2);
lean_inc_ref(v_trees_5221_);
lean_dec_ref(v_infoState_5220_);
v___x_5222_ = lean_st_ref_take(v___y_5217_);
v_infoState_5223_ = lean_ctor_get(v___x_5222_, 7);
v_env_5224_ = lean_ctor_get(v___x_5222_, 0);
v_nextMacroScope_5225_ = lean_ctor_get(v___x_5222_, 1);
v_ngen_5226_ = lean_ctor_get(v___x_5222_, 2);
v_auxDeclNGen_5227_ = lean_ctor_get(v___x_5222_, 3);
v_traceState_5228_ = lean_ctor_get(v___x_5222_, 4);
v_cache_5229_ = lean_ctor_get(v___x_5222_, 5);
v_messages_5230_ = lean_ctor_get(v___x_5222_, 6);
v_snapshotTasks_5231_ = lean_ctor_get(v___x_5222_, 8);
v_isSharedCheck_5252_ = !lean_is_exclusive(v___x_5222_);
if (v_isSharedCheck_5252_ == 0)
{
v___x_5233_ = v___x_5222_;
v_isShared_5234_ = v_isSharedCheck_5252_;
goto v_resetjp_5232_;
}
else
{
lean_inc(v_snapshotTasks_5231_);
lean_inc(v_infoState_5223_);
lean_inc(v_messages_5230_);
lean_inc(v_cache_5229_);
lean_inc(v_traceState_5228_);
lean_inc(v_auxDeclNGen_5227_);
lean_inc(v_ngen_5226_);
lean_inc(v_nextMacroScope_5225_);
lean_inc(v_env_5224_);
lean_dec(v___x_5222_);
v___x_5233_ = lean_box(0);
v_isShared_5234_ = v_isSharedCheck_5252_;
goto v_resetjp_5232_;
}
v_resetjp_5232_:
{
uint8_t v_enabled_5235_; lean_object* v_assignment_5236_; lean_object* v_lazyAssignment_5237_; lean_object* v___x_5239_; uint8_t v_isShared_5240_; uint8_t v_isSharedCheck_5250_; 
v_enabled_5235_ = lean_ctor_get_uint8(v_infoState_5223_, sizeof(void*)*3);
v_assignment_5236_ = lean_ctor_get(v_infoState_5223_, 0);
v_lazyAssignment_5237_ = lean_ctor_get(v_infoState_5223_, 1);
v_isSharedCheck_5250_ = !lean_is_exclusive(v_infoState_5223_);
if (v_isSharedCheck_5250_ == 0)
{
lean_object* v_unused_5251_; 
v_unused_5251_ = lean_ctor_get(v_infoState_5223_, 2);
lean_dec(v_unused_5251_);
v___x_5239_ = v_infoState_5223_;
v_isShared_5240_ = v_isSharedCheck_5250_;
goto v_resetjp_5238_;
}
else
{
lean_inc(v_lazyAssignment_5237_);
lean_inc(v_assignment_5236_);
lean_dec(v_infoState_5223_);
v___x_5239_ = lean_box(0);
v_isShared_5240_ = v_isSharedCheck_5250_;
goto v_resetjp_5238_;
}
v_resetjp_5238_:
{
lean_object* v___x_5241_; lean_object* v___x_5243_; 
v___x_5241_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1);
if (v_isShared_5240_ == 0)
{
lean_ctor_set(v___x_5239_, 2, v___x_5241_);
v___x_5243_ = v___x_5239_;
goto v_reusejp_5242_;
}
else
{
lean_object* v_reuseFailAlloc_5249_; 
v_reuseFailAlloc_5249_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5249_, 0, v_assignment_5236_);
lean_ctor_set(v_reuseFailAlloc_5249_, 1, v_lazyAssignment_5237_);
lean_ctor_set(v_reuseFailAlloc_5249_, 2, v___x_5241_);
lean_ctor_set_uint8(v_reuseFailAlloc_5249_, sizeof(void*)*3, v_enabled_5235_);
v___x_5243_ = v_reuseFailAlloc_5249_;
goto v_reusejp_5242_;
}
v_reusejp_5242_:
{
lean_object* v___x_5245_; 
if (v_isShared_5234_ == 0)
{
lean_ctor_set(v___x_5233_, 7, v___x_5243_);
v___x_5245_ = v___x_5233_;
goto v_reusejp_5244_;
}
else
{
lean_object* v_reuseFailAlloc_5248_; 
v_reuseFailAlloc_5248_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5248_, 0, v_env_5224_);
lean_ctor_set(v_reuseFailAlloc_5248_, 1, v_nextMacroScope_5225_);
lean_ctor_set(v_reuseFailAlloc_5248_, 2, v_ngen_5226_);
lean_ctor_set(v_reuseFailAlloc_5248_, 3, v_auxDeclNGen_5227_);
lean_ctor_set(v_reuseFailAlloc_5248_, 4, v_traceState_5228_);
lean_ctor_set(v_reuseFailAlloc_5248_, 5, v_cache_5229_);
lean_ctor_set(v_reuseFailAlloc_5248_, 6, v_messages_5230_);
lean_ctor_set(v_reuseFailAlloc_5248_, 7, v___x_5243_);
lean_ctor_set(v_reuseFailAlloc_5248_, 8, v_snapshotTasks_5231_);
v___x_5245_ = v_reuseFailAlloc_5248_;
goto v_reusejp_5244_;
}
v_reusejp_5244_:
{
lean_object* v___x_5246_; lean_object* v___x_5247_; 
v___x_5246_ = lean_st_ref_put(v___y_5217_, v___x_5245_);
v___x_5247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5247_, 0, v_trees_5221_);
return v___x_5247_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___boxed(lean_object* v___y_5253_, lean_object* v___y_5254_){
_start:
{
lean_object* v_res_5255_; 
v_res_5255_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_5253_);
lean_dec(v___y_5253_);
return v_res_5255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(lean_object* v___y_5256_, lean_object* v_mkInfoTree_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_, lean_object* v___y_5262_, lean_object* v___y_5263_, lean_object* v___y_5264_, lean_object* v_a_5265_, lean_object* v_a_x3f_5266_){
_start:
{
lean_object* v___x_5268_; lean_object* v_infoState_5269_; lean_object* v_trees_5270_; lean_object* v___x_5271_; 
v___x_5268_ = lean_st_ref_get(v___y_5256_);
v_infoState_5269_ = lean_ctor_get(v___x_5268_, 7);
lean_inc_ref(v_infoState_5269_);
lean_dec(v___x_5268_);
v_trees_5270_ = lean_ctor_get(v_infoState_5269_, 2);
lean_inc_ref(v_trees_5270_);
lean_dec_ref(v_infoState_5269_);
lean_inc(v___y_5256_);
lean_inc_ref(v___y_5264_);
lean_inc(v___y_5263_);
lean_inc_ref(v___y_5262_);
lean_inc(v___y_5261_);
lean_inc_ref(v___y_5260_);
lean_inc(v___y_5259_);
lean_inc_ref(v___y_5258_);
v___x_5271_ = lean_apply_10(v_mkInfoTree_5257_, v_trees_5270_, v___y_5258_, v___y_5259_, v___y_5260_, v___y_5261_, v___y_5262_, v___y_5263_, v___y_5264_, v___y_5256_, lean_box(0));
if (lean_obj_tag(v___x_5271_) == 0)
{
lean_object* v_a_5272_; lean_object* v___x_5274_; uint8_t v_isShared_5275_; uint8_t v_isSharedCheck_5310_; 
v_a_5272_ = lean_ctor_get(v___x_5271_, 0);
v_isSharedCheck_5310_ = !lean_is_exclusive(v___x_5271_);
if (v_isSharedCheck_5310_ == 0)
{
v___x_5274_ = v___x_5271_;
v_isShared_5275_ = v_isSharedCheck_5310_;
goto v_resetjp_5273_;
}
else
{
lean_inc(v_a_5272_);
lean_dec(v___x_5271_);
v___x_5274_ = lean_box(0);
v_isShared_5275_ = v_isSharedCheck_5310_;
goto v_resetjp_5273_;
}
v_resetjp_5273_:
{
lean_object* v___x_5276_; lean_object* v_infoState_5277_; lean_object* v_env_5278_; lean_object* v_nextMacroScope_5279_; lean_object* v_ngen_5280_; lean_object* v_auxDeclNGen_5281_; lean_object* v_traceState_5282_; lean_object* v_cache_5283_; lean_object* v_messages_5284_; lean_object* v_snapshotTasks_5285_; lean_object* v___x_5287_; uint8_t v_isShared_5288_; uint8_t v_isSharedCheck_5309_; 
v___x_5276_ = lean_st_ref_take(v___y_5256_);
v_infoState_5277_ = lean_ctor_get(v___x_5276_, 7);
v_env_5278_ = lean_ctor_get(v___x_5276_, 0);
v_nextMacroScope_5279_ = lean_ctor_get(v___x_5276_, 1);
v_ngen_5280_ = lean_ctor_get(v___x_5276_, 2);
v_auxDeclNGen_5281_ = lean_ctor_get(v___x_5276_, 3);
v_traceState_5282_ = lean_ctor_get(v___x_5276_, 4);
v_cache_5283_ = lean_ctor_get(v___x_5276_, 5);
v_messages_5284_ = lean_ctor_get(v___x_5276_, 6);
v_snapshotTasks_5285_ = lean_ctor_get(v___x_5276_, 8);
v_isSharedCheck_5309_ = !lean_is_exclusive(v___x_5276_);
if (v_isSharedCheck_5309_ == 0)
{
v___x_5287_ = v___x_5276_;
v_isShared_5288_ = v_isSharedCheck_5309_;
goto v_resetjp_5286_;
}
else
{
lean_inc(v_snapshotTasks_5285_);
lean_inc(v_infoState_5277_);
lean_inc(v_messages_5284_);
lean_inc(v_cache_5283_);
lean_inc(v_traceState_5282_);
lean_inc(v_auxDeclNGen_5281_);
lean_inc(v_ngen_5280_);
lean_inc(v_nextMacroScope_5279_);
lean_inc(v_env_5278_);
lean_dec(v___x_5276_);
v___x_5287_ = lean_box(0);
v_isShared_5288_ = v_isSharedCheck_5309_;
goto v_resetjp_5286_;
}
v_resetjp_5286_:
{
uint8_t v_enabled_5289_; lean_object* v_assignment_5290_; lean_object* v_lazyAssignment_5291_; lean_object* v___x_5293_; uint8_t v_isShared_5294_; uint8_t v_isSharedCheck_5307_; 
v_enabled_5289_ = lean_ctor_get_uint8(v_infoState_5277_, sizeof(void*)*3);
v_assignment_5290_ = lean_ctor_get(v_infoState_5277_, 0);
v_lazyAssignment_5291_ = lean_ctor_get(v_infoState_5277_, 1);
v_isSharedCheck_5307_ = !lean_is_exclusive(v_infoState_5277_);
if (v_isSharedCheck_5307_ == 0)
{
lean_object* v_unused_5308_; 
v_unused_5308_ = lean_ctor_get(v_infoState_5277_, 2);
lean_dec(v_unused_5308_);
v___x_5293_ = v_infoState_5277_;
v_isShared_5294_ = v_isSharedCheck_5307_;
goto v_resetjp_5292_;
}
else
{
lean_inc(v_lazyAssignment_5291_);
lean_inc(v_assignment_5290_);
lean_dec(v_infoState_5277_);
v___x_5293_ = lean_box(0);
v_isShared_5294_ = v_isSharedCheck_5307_;
goto v_resetjp_5292_;
}
v_resetjp_5292_:
{
lean_object* v___x_5295_; lean_object* v___x_5297_; 
v___x_5295_ = l_Lean_PersistentArray_push___redArg(v_a_5265_, v_a_5272_);
if (v_isShared_5294_ == 0)
{
lean_ctor_set(v___x_5293_, 2, v___x_5295_);
v___x_5297_ = v___x_5293_;
goto v_reusejp_5296_;
}
else
{
lean_object* v_reuseFailAlloc_5306_; 
v_reuseFailAlloc_5306_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5306_, 0, v_assignment_5290_);
lean_ctor_set(v_reuseFailAlloc_5306_, 1, v_lazyAssignment_5291_);
lean_ctor_set(v_reuseFailAlloc_5306_, 2, v___x_5295_);
lean_ctor_set_uint8(v_reuseFailAlloc_5306_, sizeof(void*)*3, v_enabled_5289_);
v___x_5297_ = v_reuseFailAlloc_5306_;
goto v_reusejp_5296_;
}
v_reusejp_5296_:
{
lean_object* v___x_5299_; 
if (v_isShared_5288_ == 0)
{
lean_ctor_set(v___x_5287_, 7, v___x_5297_);
v___x_5299_ = v___x_5287_;
goto v_reusejp_5298_;
}
else
{
lean_object* v_reuseFailAlloc_5305_; 
v_reuseFailAlloc_5305_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5305_, 0, v_env_5278_);
lean_ctor_set(v_reuseFailAlloc_5305_, 1, v_nextMacroScope_5279_);
lean_ctor_set(v_reuseFailAlloc_5305_, 2, v_ngen_5280_);
lean_ctor_set(v_reuseFailAlloc_5305_, 3, v_auxDeclNGen_5281_);
lean_ctor_set(v_reuseFailAlloc_5305_, 4, v_traceState_5282_);
lean_ctor_set(v_reuseFailAlloc_5305_, 5, v_cache_5283_);
lean_ctor_set(v_reuseFailAlloc_5305_, 6, v_messages_5284_);
lean_ctor_set(v_reuseFailAlloc_5305_, 7, v___x_5297_);
lean_ctor_set(v_reuseFailAlloc_5305_, 8, v_snapshotTasks_5285_);
v___x_5299_ = v_reuseFailAlloc_5305_;
goto v_reusejp_5298_;
}
v_reusejp_5298_:
{
lean_object* v___x_5300_; lean_object* v___x_5301_; lean_object* v___x_5303_; 
v___x_5300_ = lean_st_ref_put(v___y_5256_, v___x_5299_);
v___x_5301_ = lean_box(0);
if (v_isShared_5275_ == 0)
{
lean_ctor_set(v___x_5274_, 0, v___x_5301_);
v___x_5303_ = v___x_5274_;
goto v_reusejp_5302_;
}
else
{
lean_object* v_reuseFailAlloc_5304_; 
v_reuseFailAlloc_5304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5304_, 0, v___x_5301_);
v___x_5303_ = v_reuseFailAlloc_5304_;
goto v_reusejp_5302_;
}
v_reusejp_5302_:
{
return v___x_5303_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5311_; lean_object* v___x_5313_; uint8_t v_isShared_5314_; uint8_t v_isSharedCheck_5318_; 
lean_dec_ref(v_a_5265_);
v_a_5311_ = lean_ctor_get(v___x_5271_, 0);
v_isSharedCheck_5318_ = !lean_is_exclusive(v___x_5271_);
if (v_isSharedCheck_5318_ == 0)
{
v___x_5313_ = v___x_5271_;
v_isShared_5314_ = v_isSharedCheck_5318_;
goto v_resetjp_5312_;
}
else
{
lean_inc(v_a_5311_);
lean_dec(v___x_5271_);
v___x_5313_ = lean_box(0);
v_isShared_5314_ = v_isSharedCheck_5318_;
goto v_resetjp_5312_;
}
v_resetjp_5312_:
{
lean_object* v___x_5316_; 
if (v_isShared_5314_ == 0)
{
v___x_5316_ = v___x_5313_;
goto v_reusejp_5315_;
}
else
{
lean_object* v_reuseFailAlloc_5317_; 
v_reuseFailAlloc_5317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5317_, 0, v_a_5311_);
v___x_5316_ = v_reuseFailAlloc_5317_;
goto v_reusejp_5315_;
}
v_reusejp_5315_:
{
return v___x_5316_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0___boxed(lean_object* v___y_5319_, lean_object* v_mkInfoTree_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_, lean_object* v_a_5328_, lean_object* v_a_x3f_5329_, lean_object* v___y_5330_){
_start:
{
lean_object* v_res_5331_; 
v_res_5331_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5319_, v_mkInfoTree_5320_, v___y_5321_, v___y_5322_, v___y_5323_, v___y_5324_, v___y_5325_, v___y_5326_, v___y_5327_, v_a_5328_, v_a_x3f_5329_);
lean_dec(v_a_x3f_5329_);
lean_dec_ref(v___y_5327_);
lean_dec(v___y_5326_);
lean_dec_ref(v___y_5325_);
lean_dec(v___y_5324_);
lean_dec_ref(v___y_5323_);
lean_dec(v___y_5322_);
lean_dec_ref(v___y_5321_);
lean_dec(v___y_5319_);
return v_res_5331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(lean_object* v_x_5332_, lean_object* v_mkInfoTree_5333_, lean_object* v___y_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_){
_start:
{
lean_object* v___x_5343_; lean_object* v_infoState_5344_; uint8_t v_enabled_5345_; 
v___x_5343_ = lean_st_ref_get(v___y_5341_);
v_infoState_5344_ = lean_ctor_get(v___x_5343_, 7);
lean_inc_ref(v_infoState_5344_);
lean_dec(v___x_5343_);
v_enabled_5345_ = lean_ctor_get_uint8(v_infoState_5344_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5344_);
if (v_enabled_5345_ == 0)
{
lean_object* v___x_5346_; 
lean_dec_ref(v_mkInfoTree_5333_);
lean_inc(v___y_5341_);
lean_inc_ref(v___y_5340_);
lean_inc(v___y_5339_);
lean_inc_ref(v___y_5338_);
lean_inc(v___y_5337_);
lean_inc_ref(v___y_5336_);
lean_inc(v___y_5335_);
lean_inc_ref(v___y_5334_);
v___x_5346_ = lean_apply_9(v_x_5332_, v___y_5334_, v___y_5335_, v___y_5336_, v___y_5337_, v___y_5338_, v___y_5339_, v___y_5340_, v___y_5341_, lean_box(0));
return v___x_5346_;
}
else
{
lean_object* v___x_5347_; lean_object* v_a_5348_; lean_object* v_r_5349_; 
v___x_5347_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_5341_);
v_a_5348_ = lean_ctor_get(v___x_5347_, 0);
lean_inc(v_a_5348_);
lean_dec_ref(v___x_5347_);
lean_inc(v___y_5341_);
lean_inc_ref(v___y_5340_);
lean_inc(v___y_5339_);
lean_inc_ref(v___y_5338_);
lean_inc(v___y_5337_);
lean_inc_ref(v___y_5336_);
lean_inc(v___y_5335_);
lean_inc_ref(v___y_5334_);
v_r_5349_ = lean_apply_9(v_x_5332_, v___y_5334_, v___y_5335_, v___y_5336_, v___y_5337_, v___y_5338_, v___y_5339_, v___y_5340_, v___y_5341_, lean_box(0));
if (lean_obj_tag(v_r_5349_) == 0)
{
lean_object* v_a_5350_; lean_object* v___x_5352_; uint8_t v_isShared_5353_; uint8_t v_isSharedCheck_5374_; 
v_a_5350_ = lean_ctor_get(v_r_5349_, 0);
v_isSharedCheck_5374_ = !lean_is_exclusive(v_r_5349_);
if (v_isSharedCheck_5374_ == 0)
{
v___x_5352_ = v_r_5349_;
v_isShared_5353_ = v_isSharedCheck_5374_;
goto v_resetjp_5351_;
}
else
{
lean_inc(v_a_5350_);
lean_dec(v_r_5349_);
v___x_5352_ = lean_box(0);
v_isShared_5353_ = v_isSharedCheck_5374_;
goto v_resetjp_5351_;
}
v_resetjp_5351_:
{
lean_object* v___x_5355_; 
lean_inc(v_a_5350_);
if (v_isShared_5353_ == 0)
{
lean_ctor_set_tag(v___x_5352_, 1);
v___x_5355_ = v___x_5352_;
goto v_reusejp_5354_;
}
else
{
lean_object* v_reuseFailAlloc_5373_; 
v_reuseFailAlloc_5373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5373_, 0, v_a_5350_);
v___x_5355_ = v_reuseFailAlloc_5373_;
goto v_reusejp_5354_;
}
v_reusejp_5354_:
{
lean_object* v___x_5356_; 
v___x_5356_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5341_, v_mkInfoTree_5333_, v___y_5334_, v___y_5335_, v___y_5336_, v___y_5337_, v___y_5338_, v___y_5339_, v___y_5340_, v_a_5348_, v___x_5355_);
lean_dec_ref(v___x_5355_);
if (lean_obj_tag(v___x_5356_) == 0)
{
lean_object* v___x_5358_; uint8_t v_isShared_5359_; uint8_t v_isSharedCheck_5363_; 
v_isSharedCheck_5363_ = !lean_is_exclusive(v___x_5356_);
if (v_isSharedCheck_5363_ == 0)
{
lean_object* v_unused_5364_; 
v_unused_5364_ = lean_ctor_get(v___x_5356_, 0);
lean_dec(v_unused_5364_);
v___x_5358_ = v___x_5356_;
v_isShared_5359_ = v_isSharedCheck_5363_;
goto v_resetjp_5357_;
}
else
{
lean_dec(v___x_5356_);
v___x_5358_ = lean_box(0);
v_isShared_5359_ = v_isSharedCheck_5363_;
goto v_resetjp_5357_;
}
v_resetjp_5357_:
{
lean_object* v___x_5361_; 
if (v_isShared_5359_ == 0)
{
lean_ctor_set(v___x_5358_, 0, v_a_5350_);
v___x_5361_ = v___x_5358_;
goto v_reusejp_5360_;
}
else
{
lean_object* v_reuseFailAlloc_5362_; 
v_reuseFailAlloc_5362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5362_, 0, v_a_5350_);
v___x_5361_ = v_reuseFailAlloc_5362_;
goto v_reusejp_5360_;
}
v_reusejp_5360_:
{
return v___x_5361_;
}
}
}
else
{
lean_object* v_a_5365_; lean_object* v___x_5367_; uint8_t v_isShared_5368_; uint8_t v_isSharedCheck_5372_; 
lean_dec(v_a_5350_);
v_a_5365_ = lean_ctor_get(v___x_5356_, 0);
v_isSharedCheck_5372_ = !lean_is_exclusive(v___x_5356_);
if (v_isSharedCheck_5372_ == 0)
{
v___x_5367_ = v___x_5356_;
v_isShared_5368_ = v_isSharedCheck_5372_;
goto v_resetjp_5366_;
}
else
{
lean_inc(v_a_5365_);
lean_dec(v___x_5356_);
v___x_5367_ = lean_box(0);
v_isShared_5368_ = v_isSharedCheck_5372_;
goto v_resetjp_5366_;
}
v_resetjp_5366_:
{
lean_object* v___x_5370_; 
if (v_isShared_5368_ == 0)
{
v___x_5370_ = v___x_5367_;
goto v_reusejp_5369_;
}
else
{
lean_object* v_reuseFailAlloc_5371_; 
v_reuseFailAlloc_5371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5371_, 0, v_a_5365_);
v___x_5370_ = v_reuseFailAlloc_5371_;
goto v_reusejp_5369_;
}
v_reusejp_5369_:
{
return v___x_5370_;
}
}
}
}
}
}
else
{
lean_object* v_a_5375_; lean_object* v___x_5376_; lean_object* v___x_5377_; 
v_a_5375_ = lean_ctor_get(v_r_5349_, 0);
lean_inc(v_a_5375_);
lean_dec_ref_known(v_r_5349_, 1);
v___x_5376_ = lean_box(0);
v___x_5377_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5341_, v_mkInfoTree_5333_, v___y_5334_, v___y_5335_, v___y_5336_, v___y_5337_, v___y_5338_, v___y_5339_, v___y_5340_, v_a_5348_, v___x_5376_);
if (lean_obj_tag(v___x_5377_) == 0)
{
lean_object* v___x_5379_; uint8_t v_isShared_5380_; uint8_t v_isSharedCheck_5384_; 
v_isSharedCheck_5384_ = !lean_is_exclusive(v___x_5377_);
if (v_isSharedCheck_5384_ == 0)
{
lean_object* v_unused_5385_; 
v_unused_5385_ = lean_ctor_get(v___x_5377_, 0);
lean_dec(v_unused_5385_);
v___x_5379_ = v___x_5377_;
v_isShared_5380_ = v_isSharedCheck_5384_;
goto v_resetjp_5378_;
}
else
{
lean_dec(v___x_5377_);
v___x_5379_ = lean_box(0);
v_isShared_5380_ = v_isSharedCheck_5384_;
goto v_resetjp_5378_;
}
v_resetjp_5378_:
{
lean_object* v___x_5382_; 
if (v_isShared_5380_ == 0)
{
lean_ctor_set_tag(v___x_5379_, 1);
lean_ctor_set(v___x_5379_, 0, v_a_5375_);
v___x_5382_ = v___x_5379_;
goto v_reusejp_5381_;
}
else
{
lean_object* v_reuseFailAlloc_5383_; 
v_reuseFailAlloc_5383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5383_, 0, v_a_5375_);
v___x_5382_ = v_reuseFailAlloc_5383_;
goto v_reusejp_5381_;
}
v_reusejp_5381_:
{
return v___x_5382_;
}
}
}
else
{
lean_object* v_a_5386_; lean_object* v___x_5388_; uint8_t v_isShared_5389_; uint8_t v_isSharedCheck_5393_; 
lean_dec(v_a_5375_);
v_a_5386_ = lean_ctor_get(v___x_5377_, 0);
v_isSharedCheck_5393_ = !lean_is_exclusive(v___x_5377_);
if (v_isSharedCheck_5393_ == 0)
{
v___x_5388_ = v___x_5377_;
v_isShared_5389_ = v_isSharedCheck_5393_;
goto v_resetjp_5387_;
}
else
{
lean_inc(v_a_5386_);
lean_dec(v___x_5377_);
v___x_5388_ = lean_box(0);
v_isShared_5389_ = v_isSharedCheck_5393_;
goto v_resetjp_5387_;
}
v_resetjp_5387_:
{
lean_object* v___x_5391_; 
if (v_isShared_5389_ == 0)
{
v___x_5391_ = v___x_5388_;
goto v_reusejp_5390_;
}
else
{
lean_object* v_reuseFailAlloc_5392_; 
v_reuseFailAlloc_5392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5392_, 0, v_a_5386_);
v___x_5391_ = v_reuseFailAlloc_5392_;
goto v_reusejp_5390_;
}
v_reusejp_5390_:
{
return v___x_5391_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___boxed(lean_object* v_x_5394_, lean_object* v_mkInfoTree_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_, lean_object* v___y_5398_, lean_object* v___y_5399_, lean_object* v___y_5400_, lean_object* v___y_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_){
_start:
{
lean_object* v_res_5405_; 
v_res_5405_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v_x_5394_, v_mkInfoTree_5395_, v___y_5396_, v___y_5397_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_, v___y_5402_, v___y_5403_);
lean_dec(v___y_5403_);
lean_dec_ref(v___y_5402_);
lean_dec(v___y_5401_);
lean_dec_ref(v___y_5400_);
lean_dec(v___y_5399_);
lean_dec_ref(v___y_5398_);
lean_dec(v___y_5397_);
lean_dec_ref(v___y_5396_);
return v_res_5405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1(lean_object* v_a_5406_, lean_object* v_trees_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_, lean_object* v___y_5411_, lean_object* v___y_5412_, lean_object* v___y_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_){
_start:
{
lean_object* v___x_5417_; 
lean_inc(v___y_5415_);
lean_inc_ref(v___y_5414_);
lean_inc(v___y_5413_);
lean_inc_ref(v___y_5412_);
lean_inc(v___y_5411_);
lean_inc_ref(v___y_5410_);
lean_inc(v___y_5409_);
lean_inc_ref(v___y_5408_);
v___x_5417_ = lean_apply_9(v_a_5406_, v___y_5408_, v___y_5409_, v___y_5410_, v___y_5411_, v___y_5412_, v___y_5413_, v___y_5414_, v___y_5415_, lean_box(0));
if (lean_obj_tag(v___x_5417_) == 0)
{
lean_object* v_a_5418_; lean_object* v___x_5420_; uint8_t v_isShared_5421_; uint8_t v_isSharedCheck_5426_; 
v_a_5418_ = lean_ctor_get(v___x_5417_, 0);
v_isSharedCheck_5426_ = !lean_is_exclusive(v___x_5417_);
if (v_isSharedCheck_5426_ == 0)
{
v___x_5420_ = v___x_5417_;
v_isShared_5421_ = v_isSharedCheck_5426_;
goto v_resetjp_5419_;
}
else
{
lean_inc(v_a_5418_);
lean_dec(v___x_5417_);
v___x_5420_ = lean_box(0);
v_isShared_5421_ = v_isSharedCheck_5426_;
goto v_resetjp_5419_;
}
v_resetjp_5419_:
{
lean_object* v___x_5422_; lean_object* v___x_5424_; 
v___x_5422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5422_, 0, v_a_5418_);
lean_ctor_set(v___x_5422_, 1, v_trees_5407_);
if (v_isShared_5421_ == 0)
{
lean_ctor_set(v___x_5420_, 0, v___x_5422_);
v___x_5424_ = v___x_5420_;
goto v_reusejp_5423_;
}
else
{
lean_object* v_reuseFailAlloc_5425_; 
v_reuseFailAlloc_5425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5425_, 0, v___x_5422_);
v___x_5424_ = v_reuseFailAlloc_5425_;
goto v_reusejp_5423_;
}
v_reusejp_5423_:
{
return v___x_5424_;
}
}
}
else
{
lean_object* v_a_5427_; lean_object* v___x_5429_; uint8_t v_isShared_5430_; uint8_t v_isSharedCheck_5434_; 
lean_dec_ref(v_trees_5407_);
v_a_5427_ = lean_ctor_get(v___x_5417_, 0);
v_isSharedCheck_5434_ = !lean_is_exclusive(v___x_5417_);
if (v_isSharedCheck_5434_ == 0)
{
v___x_5429_ = v___x_5417_;
v_isShared_5430_ = v_isSharedCheck_5434_;
goto v_resetjp_5428_;
}
else
{
lean_inc(v_a_5427_);
lean_dec(v___x_5417_);
v___x_5429_ = lean_box(0);
v_isShared_5430_ = v_isSharedCheck_5434_;
goto v_resetjp_5428_;
}
v_resetjp_5428_:
{
lean_object* v___x_5432_; 
if (v_isShared_5430_ == 0)
{
v___x_5432_ = v___x_5429_;
goto v_reusejp_5431_;
}
else
{
lean_object* v_reuseFailAlloc_5433_; 
v_reuseFailAlloc_5433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5433_, 0, v_a_5427_);
v___x_5432_ = v_reuseFailAlloc_5433_;
goto v_reusejp_5431_;
}
v_reusejp_5431_:
{
return v___x_5432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1___boxed(lean_object* v_a_5435_, lean_object* v_trees_5436_, lean_object* v___y_5437_, lean_object* v___y_5438_, lean_object* v___y_5439_, lean_object* v___y_5440_, lean_object* v___y_5441_, lean_object* v___y_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_){
_start:
{
lean_object* v_res_5446_; 
v_res_5446_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1(v_a_5435_, v_trees_5436_, v___y_5437_, v___y_5438_, v___y_5439_, v___y_5440_, v___y_5441_, v___y_5442_, v___y_5443_, v___y_5444_);
lean_dec(v___y_5444_);
lean_dec_ref(v___y_5443_);
lean_dec(v___y_5442_);
lean_dec_ref(v___y_5441_);
lean_dec(v___y_5440_);
lean_dec_ref(v___y_5439_);
lean_dec(v___y_5438_);
lean_dec_ref(v___y_5437_);
return v_res_5446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2(lean_object* v___x_5447_, lean_object* v_ref_5448_, lean_object* v_tactic_5449_, lean_object* v___y_5450_, lean_object* v___y_5451_, lean_object* v___y_5452_, lean_object* v___y_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_){
_start:
{
lean_object* v___x_5459_; 
v___x_5459_ = l_Lean_Elab_Tactic_setGoals___redArg(v___x_5447_, v___y_5451_);
if (lean_obj_tag(v___x_5459_) == 0)
{
lean_object* v___x_5460_; 
lean_dec_ref_known(v___x_5459_, 1);
v___x_5460_ = l_Lean_Elab_WF_applyCleanWfTactic(v___y_5450_, v___y_5451_, v___y_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_);
if (lean_obj_tag(v___x_5460_) == 0)
{
lean_object* v___x_5461_; 
lean_dec_ref_known(v___x_5460_, 1);
v___x_5461_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v_ref_5448_, v___y_5450_, v___y_5451_, v___y_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_);
if (lean_obj_tag(v___x_5461_) == 0)
{
lean_object* v_a_5462_; lean_object* v___f_5463_; lean_object* v___x_5464_; lean_object* v___x_5465_; 
v_a_5462_ = lean_ctor_get(v___x_5461_, 0);
lean_inc(v_a_5462_);
lean_dec_ref_known(v___x_5461_, 1);
v___f_5463_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1___boxed), 11, 1);
lean_closure_set(v___f_5463_, 0, v_a_5462_);
v___x_5464_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_5464_, 0, v_tactic_5449_);
v___x_5465_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v___x_5464_, v___f_5463_, v___y_5450_, v___y_5451_, v___y_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_);
return v___x_5465_;
}
else
{
lean_object* v_a_5466_; lean_object* v___x_5468_; uint8_t v_isShared_5469_; uint8_t v_isSharedCheck_5473_; 
lean_dec(v_tactic_5449_);
v_a_5466_ = lean_ctor_get(v___x_5461_, 0);
v_isSharedCheck_5473_ = !lean_is_exclusive(v___x_5461_);
if (v_isSharedCheck_5473_ == 0)
{
v___x_5468_ = v___x_5461_;
v_isShared_5469_ = v_isSharedCheck_5473_;
goto v_resetjp_5467_;
}
else
{
lean_inc(v_a_5466_);
lean_dec(v___x_5461_);
v___x_5468_ = lean_box(0);
v_isShared_5469_ = v_isSharedCheck_5473_;
goto v_resetjp_5467_;
}
v_resetjp_5467_:
{
lean_object* v___x_5471_; 
if (v_isShared_5469_ == 0)
{
v___x_5471_ = v___x_5468_;
goto v_reusejp_5470_;
}
else
{
lean_object* v_reuseFailAlloc_5472_; 
v_reuseFailAlloc_5472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5472_, 0, v_a_5466_);
v___x_5471_ = v_reuseFailAlloc_5472_;
goto v_reusejp_5470_;
}
v_reusejp_5470_:
{
return v___x_5471_;
}
}
}
}
else
{
lean_dec(v_tactic_5449_);
lean_dec(v_ref_5448_);
return v___x_5460_;
}
}
else
{
lean_dec(v_tactic_5449_);
lean_dec(v_ref_5448_);
return v___x_5459_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2___boxed(lean_object* v___x_5474_, lean_object* v_ref_5475_, lean_object* v_tactic_5476_, lean_object* v___y_5477_, lean_object* v___y_5478_, lean_object* v___y_5479_, lean_object* v___y_5480_, lean_object* v___y_5481_, lean_object* v___y_5482_, lean_object* v___y_5483_, lean_object* v___y_5484_, lean_object* v___y_5485_){
_start:
{
lean_object* v_res_5486_; 
v_res_5486_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2(v___x_5474_, v_ref_5475_, v_tactic_5476_, v___y_5477_, v___y_5478_, v___y_5479_, v___y_5480_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_);
lean_dec(v___y_5484_);
lean_dec_ref(v___y_5483_);
lean_dec(v___y_5482_);
lean_dec_ref(v___y_5481_);
lean_dec(v___y_5480_);
lean_dec_ref(v___y_5479_);
lean_dec(v___y_5478_);
lean_dec_ref(v___y_5477_);
return v_res_5486_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5487_; lean_object* v___x_5488_; 
v___x_5487_ = lean_box(1);
v___x_5488_ = l_Lean_MessageData_ofFormat(v___x_5487_);
return v___x_5488_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5492_; lean_object* v___x_5493_; 
v___x_5492_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__2));
v___x_5493_ = l_Lean_MessageData_ofFormat(v___x_5492_);
return v___x_5493_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3(lean_object* v_x_5494_, lean_object* v_x_5495_){
_start:
{
if (lean_obj_tag(v_x_5495_) == 0)
{
return v_x_5494_;
}
else
{
lean_object* v_head_5496_; lean_object* v_tail_5497_; lean_object* v___x_5499_; uint8_t v_isShared_5500_; uint8_t v_isSharedCheck_5519_; 
v_head_5496_ = lean_ctor_get(v_x_5495_, 0);
v_tail_5497_ = lean_ctor_get(v_x_5495_, 1);
v_isSharedCheck_5519_ = !lean_is_exclusive(v_x_5495_);
if (v_isSharedCheck_5519_ == 0)
{
v___x_5499_ = v_x_5495_;
v_isShared_5500_ = v_isSharedCheck_5519_;
goto v_resetjp_5498_;
}
else
{
lean_inc(v_tail_5497_);
lean_inc(v_head_5496_);
lean_dec(v_x_5495_);
v___x_5499_ = lean_box(0);
v_isShared_5500_ = v_isSharedCheck_5519_;
goto v_resetjp_5498_;
}
v_resetjp_5498_:
{
lean_object* v_before_5501_; lean_object* v___x_5503_; uint8_t v_isShared_5504_; uint8_t v_isSharedCheck_5517_; 
v_before_5501_ = lean_ctor_get(v_head_5496_, 0);
v_isSharedCheck_5517_ = !lean_is_exclusive(v_head_5496_);
if (v_isSharedCheck_5517_ == 0)
{
lean_object* v_unused_5518_; 
v_unused_5518_ = lean_ctor_get(v_head_5496_, 1);
lean_dec(v_unused_5518_);
v___x_5503_ = v_head_5496_;
v_isShared_5504_ = v_isSharedCheck_5517_;
goto v_resetjp_5502_;
}
else
{
lean_inc(v_before_5501_);
lean_dec(v_head_5496_);
v___x_5503_ = lean_box(0);
v_isShared_5504_ = v_isSharedCheck_5517_;
goto v_resetjp_5502_;
}
v_resetjp_5502_:
{
lean_object* v___x_5505_; lean_object* v___x_5507_; 
v___x_5505_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_5504_ == 0)
{
lean_ctor_set_tag(v___x_5503_, 7);
lean_ctor_set(v___x_5503_, 1, v___x_5505_);
lean_ctor_set(v___x_5503_, 0, v_x_5494_);
v___x_5507_ = v___x_5503_;
goto v_reusejp_5506_;
}
else
{
lean_object* v_reuseFailAlloc_5516_; 
v_reuseFailAlloc_5516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5516_, 0, v_x_5494_);
lean_ctor_set(v_reuseFailAlloc_5516_, 1, v___x_5505_);
v___x_5507_ = v_reuseFailAlloc_5516_;
goto v_reusejp_5506_;
}
v_reusejp_5506_:
{
lean_object* v___x_5508_; lean_object* v___x_5510_; 
v___x_5508_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3);
if (v_isShared_5500_ == 0)
{
lean_ctor_set_tag(v___x_5499_, 7);
lean_ctor_set(v___x_5499_, 1, v___x_5508_);
lean_ctor_set(v___x_5499_, 0, v___x_5507_);
v___x_5510_ = v___x_5499_;
goto v_reusejp_5509_;
}
else
{
lean_object* v_reuseFailAlloc_5515_; 
v_reuseFailAlloc_5515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5515_, 0, v___x_5507_);
lean_ctor_set(v_reuseFailAlloc_5515_, 1, v___x_5508_);
v___x_5510_ = v_reuseFailAlloc_5515_;
goto v_reusejp_5509_;
}
v_reusejp_5509_:
{
lean_object* v___x_5511_; lean_object* v___x_5512_; lean_object* v___x_5513_; 
v___x_5511_ = l_Lean_MessageData_ofSyntax(v_before_5501_);
v___x_5512_ = l_Lean_indentD(v___x_5511_);
v___x_5513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5513_, 0, v___x_5510_);
lean_ctor_set(v___x_5513_, 1, v___x_5512_);
v_x_5494_ = v___x_5513_;
v_x_5495_ = v_tail_5497_;
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
lean_object* v___x_5523_; lean_object* v___x_5524_; 
v___x_5523_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__1));
v___x_5524_ = l_Lean_MessageData_ofFormat(v___x_5523_);
return v___x_5524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(lean_object* v_msgData_5525_, lean_object* v_macroStack_5526_, lean_object* v___y_5527_){
_start:
{
lean_object* v_options_5529_; lean_object* v___x_5530_; uint8_t v___x_5531_; 
v_options_5529_ = lean_ctor_get(v___y_5527_, 2);
v___x_5530_ = l_Lean_Elab_pp_macroStack;
v___x_5531_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v_options_5529_, v___x_5530_);
if (v___x_5531_ == 0)
{
lean_object* v___x_5532_; 
lean_dec(v_macroStack_5526_);
v___x_5532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5532_, 0, v_msgData_5525_);
return v___x_5532_;
}
else
{
if (lean_obj_tag(v_macroStack_5526_) == 0)
{
lean_object* v___x_5533_; 
v___x_5533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5533_, 0, v_msgData_5525_);
return v___x_5533_;
}
else
{
lean_object* v_head_5534_; lean_object* v_after_5535_; lean_object* v___x_5537_; uint8_t v_isShared_5538_; uint8_t v_isSharedCheck_5550_; 
v_head_5534_ = lean_ctor_get(v_macroStack_5526_, 0);
lean_inc(v_head_5534_);
v_after_5535_ = lean_ctor_get(v_head_5534_, 1);
v_isSharedCheck_5550_ = !lean_is_exclusive(v_head_5534_);
if (v_isSharedCheck_5550_ == 0)
{
lean_object* v_unused_5551_; 
v_unused_5551_ = lean_ctor_get(v_head_5534_, 0);
lean_dec(v_unused_5551_);
v___x_5537_ = v_head_5534_;
v_isShared_5538_ = v_isSharedCheck_5550_;
goto v_resetjp_5536_;
}
else
{
lean_inc(v_after_5535_);
lean_dec(v_head_5534_);
v___x_5537_ = lean_box(0);
v_isShared_5538_ = v_isSharedCheck_5550_;
goto v_resetjp_5536_;
}
v_resetjp_5536_:
{
lean_object* v___x_5539_; lean_object* v___x_5541_; 
v___x_5539_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_5538_ == 0)
{
lean_ctor_set_tag(v___x_5537_, 7);
lean_ctor_set(v___x_5537_, 1, v___x_5539_);
lean_ctor_set(v___x_5537_, 0, v_msgData_5525_);
v___x_5541_ = v___x_5537_;
goto v_reusejp_5540_;
}
else
{
lean_object* v_reuseFailAlloc_5549_; 
v_reuseFailAlloc_5549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5549_, 0, v_msgData_5525_);
lean_ctor_set(v_reuseFailAlloc_5549_, 1, v___x_5539_);
v___x_5541_ = v_reuseFailAlloc_5549_;
goto v_reusejp_5540_;
}
v_reusejp_5540_:
{
lean_object* v___x_5542_; lean_object* v___x_5543_; lean_object* v___x_5544_; lean_object* v___x_5545_; lean_object* v_msgData_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; 
v___x_5542_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2);
v___x_5543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5543_, 0, v___x_5541_);
lean_ctor_set(v___x_5543_, 1, v___x_5542_);
v___x_5544_ = l_Lean_MessageData_ofSyntax(v_after_5535_);
v___x_5545_ = l_Lean_indentD(v___x_5544_);
v_msgData_5546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_5546_, 0, v___x_5543_);
lean_ctor_set(v_msgData_5546_, 1, v___x_5545_);
v___x_5547_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3(v_msgData_5546_, v_macroStack_5526_);
v___x_5548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5548_, 0, v___x_5547_);
return v___x_5548_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_5552_, lean_object* v_macroStack_5553_, lean_object* v___y_5554_, lean_object* v___y_5555_){
_start:
{
lean_object* v_res_5556_; 
v_res_5556_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_msgData_5552_, v_macroStack_5553_, v___y_5554_);
lean_dec_ref(v___y_5554_);
return v_res_5556_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(lean_object* v_msg_5557_, lean_object* v___y_5558_, lean_object* v___y_5559_, lean_object* v___y_5560_, lean_object* v___y_5561_, lean_object* v___y_5562_, lean_object* v___y_5563_){
_start:
{
lean_object* v_ref_5565_; lean_object* v___x_5566_; lean_object* v_a_5567_; lean_object* v_macroStack_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; lean_object* v_a_5571_; lean_object* v___x_5573_; uint8_t v_isShared_5574_; uint8_t v_isSharedCheck_5579_; 
v_ref_5565_ = lean_ctor_get(v___y_5562_, 5);
v___x_5566_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_5557_, v___y_5560_, v___y_5561_, v___y_5562_, v___y_5563_);
v_a_5567_ = lean_ctor_get(v___x_5566_, 0);
lean_inc(v_a_5567_);
lean_dec_ref(v___x_5566_);
v_macroStack_5568_ = lean_ctor_get(v___y_5558_, 1);
v___x_5569_ = l_Lean_Elab_getBetterRef(v_ref_5565_, v_macroStack_5568_);
lean_inc(v_macroStack_5568_);
v___x_5570_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_a_5567_, v_macroStack_5568_, v___y_5562_);
v_a_5571_ = lean_ctor_get(v___x_5570_, 0);
v_isSharedCheck_5579_ = !lean_is_exclusive(v___x_5570_);
if (v_isSharedCheck_5579_ == 0)
{
v___x_5573_ = v___x_5570_;
v_isShared_5574_ = v_isSharedCheck_5579_;
goto v_resetjp_5572_;
}
else
{
lean_inc(v_a_5571_);
lean_dec(v___x_5570_);
v___x_5573_ = lean_box(0);
v_isShared_5574_ = v_isSharedCheck_5579_;
goto v_resetjp_5572_;
}
v_resetjp_5572_:
{
lean_object* v___x_5575_; lean_object* v___x_5577_; 
v___x_5575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5575_, 0, v___x_5569_);
lean_ctor_set(v___x_5575_, 1, v_a_5571_);
if (v_isShared_5574_ == 0)
{
lean_ctor_set_tag(v___x_5573_, 1);
lean_ctor_set(v___x_5573_, 0, v___x_5575_);
v___x_5577_ = v___x_5573_;
goto v_reusejp_5576_;
}
else
{
lean_object* v_reuseFailAlloc_5578_; 
v_reuseFailAlloc_5578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5578_, 0, v___x_5575_);
v___x_5577_ = v_reuseFailAlloc_5578_;
goto v_reusejp_5576_;
}
v_reusejp_5576_:
{
return v___x_5577_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg___boxed(lean_object* v_msg_5580_, lean_object* v___y_5581_, lean_object* v___y_5582_, lean_object* v___y_5583_, lean_object* v___y_5584_, lean_object* v___y_5585_, lean_object* v___y_5586_, lean_object* v___y_5587_){
_start:
{
lean_object* v_res_5588_; 
v_res_5588_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v_msg_5580_, v___y_5581_, v___y_5582_, v___y_5583_, v___y_5584_, v___y_5585_, v___y_5586_);
lean_dec(v___y_5586_);
lean_dec_ref(v___y_5585_);
lean_dec(v___y_5584_);
lean_dec_ref(v___y_5583_);
lean_dec(v___y_5582_);
lean_dec_ref(v___y_5581_);
return v_res_5588_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1(void){
_start:
{
lean_object* v___x_5590_; lean_object* v___x_5591_; 
v___x_5590_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__0));
v___x_5591_ = l_Lean_stringToMessageData(v___x_5590_);
return v___x_5591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(lean_object* v_as_5592_, size_t v_sz_5593_, size_t v_i_5594_, lean_object* v_b_5595_, lean_object* v___y_5596_, lean_object* v___y_5597_, lean_object* v___y_5598_, lean_object* v___y_5599_, lean_object* v___y_5600_, lean_object* v___y_5601_){
_start:
{
lean_object* v_a_5604_; uint8_t v___x_5608_; 
v___x_5608_ = lean_usize_dec_lt(v_i_5594_, v_sz_5593_);
if (v___x_5608_ == 0)
{
lean_object* v___x_5609_; 
v___x_5609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5609_, 0, v_b_5595_);
return v___x_5609_;
}
else
{
lean_object* v_a_5610_; lean_object* v___x_5611_; 
v_a_5610_ = lean_array_uget_borrowed(v_as_5592_, v_i_5594_);
lean_inc(v_a_5610_);
v___x_5611_ = l_Lean_MVarId_getType(v_a_5610_, v___y_5598_, v___y_5599_, v___y_5600_, v___y_5601_);
if (lean_obj_tag(v___x_5611_) == 0)
{
lean_object* v_a_5612_; lean_object* v___x_5613_; 
v_a_5612_ = lean_ctor_get(v___x_5611_, 0);
lean_inc(v_a_5612_);
lean_dec_ref_known(v___x_5611_, 1);
lean_inc(v_a_5610_);
v___x_5613_ = l_Lean_MVarId_getType(v_a_5610_, v___y_5598_, v___y_5599_, v___y_5600_, v___y_5601_);
if (lean_obj_tag(v___x_5613_) == 0)
{
lean_object* v_a_5614_; lean_object* v___x_5615_; lean_object* v___x_5616_; 
v_a_5614_ = lean_ctor_get(v___x_5613_, 0);
lean_inc(v_a_5614_);
lean_dec_ref_known(v___x_5613_, 1);
v___x_5615_ = lean_box(0);
v___x_5616_ = l_Lean_getRecAppSyntax_x3f(v_a_5614_);
lean_dec(v_a_5614_);
if (lean_obj_tag(v___x_5616_) == 1)
{
lean_object* v_val_5617_; lean_object* v___x_5618_; lean_object* v___x_5619_; 
v_val_5617_ = lean_ctor_get(v___x_5616_, 0);
lean_inc(v_val_5617_);
lean_dec_ref_known(v___x_5616_, 1);
v___x_5618_ = l_Lean_Expr_mdataExpr_x21(v_a_5612_);
lean_dec(v_a_5612_);
lean_inc(v_a_5610_);
v___x_5619_ = l_Lean_MVarId_setType___redArg(v_a_5610_, v___x_5618_, v___y_5599_);
if (lean_obj_tag(v___x_5619_) == 0)
{
lean_object* v_fileName_5620_; lean_object* v_fileMap_5621_; lean_object* v_options_5622_; lean_object* v_currRecDepth_5623_; lean_object* v_maxRecDepth_5624_; lean_object* v_ref_5625_; lean_object* v_currNamespace_5626_; lean_object* v_openDecls_5627_; lean_object* v_initHeartbeats_5628_; lean_object* v_maxHeartbeats_5629_; lean_object* v_quotContext_5630_; lean_object* v_currMacroScope_5631_; uint8_t v_diag_5632_; lean_object* v_cancelTk_x3f_5633_; uint8_t v_suppressElabErrors_5634_; lean_object* v_inheritedTraceOptions_5635_; lean_object* v_ref_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; 
lean_dec_ref_known(v___x_5619_, 1);
v_fileName_5620_ = lean_ctor_get(v___y_5600_, 0);
v_fileMap_5621_ = lean_ctor_get(v___y_5600_, 1);
v_options_5622_ = lean_ctor_get(v___y_5600_, 2);
v_currRecDepth_5623_ = lean_ctor_get(v___y_5600_, 3);
v_maxRecDepth_5624_ = lean_ctor_get(v___y_5600_, 4);
v_ref_5625_ = lean_ctor_get(v___y_5600_, 5);
v_currNamespace_5626_ = lean_ctor_get(v___y_5600_, 6);
v_openDecls_5627_ = lean_ctor_get(v___y_5600_, 7);
v_initHeartbeats_5628_ = lean_ctor_get(v___y_5600_, 8);
v_maxHeartbeats_5629_ = lean_ctor_get(v___y_5600_, 9);
v_quotContext_5630_ = lean_ctor_get(v___y_5600_, 10);
v_currMacroScope_5631_ = lean_ctor_get(v___y_5600_, 11);
v_diag_5632_ = lean_ctor_get_uint8(v___y_5600_, sizeof(void*)*14);
v_cancelTk_x3f_5633_ = lean_ctor_get(v___y_5600_, 12);
v_suppressElabErrors_5634_ = lean_ctor_get_uint8(v___y_5600_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5635_ = lean_ctor_get(v___y_5600_, 13);
v_ref_5636_ = l_Lean_replaceRef(v_val_5617_, v_ref_5625_);
lean_dec(v_val_5617_);
lean_inc_ref(v_inheritedTraceOptions_5635_);
lean_inc(v_cancelTk_x3f_5633_);
lean_inc(v_currMacroScope_5631_);
lean_inc(v_quotContext_5630_);
lean_inc(v_maxHeartbeats_5629_);
lean_inc(v_initHeartbeats_5628_);
lean_inc(v_openDecls_5627_);
lean_inc(v_currNamespace_5626_);
lean_inc(v_maxRecDepth_5624_);
lean_inc(v_currRecDepth_5623_);
lean_inc_ref(v_options_5622_);
lean_inc_ref(v_fileMap_5621_);
lean_inc_ref(v_fileName_5620_);
v___x_5637_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5637_, 0, v_fileName_5620_);
lean_ctor_set(v___x_5637_, 1, v_fileMap_5621_);
lean_ctor_set(v___x_5637_, 2, v_options_5622_);
lean_ctor_set(v___x_5637_, 3, v_currRecDepth_5623_);
lean_ctor_set(v___x_5637_, 4, v_maxRecDepth_5624_);
lean_ctor_set(v___x_5637_, 5, v_ref_5636_);
lean_ctor_set(v___x_5637_, 6, v_currNamespace_5626_);
lean_ctor_set(v___x_5637_, 7, v_openDecls_5627_);
lean_ctor_set(v___x_5637_, 8, v_initHeartbeats_5628_);
lean_ctor_set(v___x_5637_, 9, v_maxHeartbeats_5629_);
lean_ctor_set(v___x_5637_, 10, v_quotContext_5630_);
lean_ctor_set(v___x_5637_, 11, v_currMacroScope_5631_);
lean_ctor_set(v___x_5637_, 12, v_cancelTk_x3f_5633_);
lean_ctor_set(v___x_5637_, 13, v_inheritedTraceOptions_5635_);
lean_ctor_set_uint8(v___x_5637_, sizeof(void*)*14, v_diag_5632_);
lean_ctor_set_uint8(v___x_5637_, sizeof(void*)*14 + 1, v_suppressElabErrors_5634_);
lean_inc(v_a_5610_);
v___x_5638_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(v_a_5610_, v___y_5596_, v___y_5597_, v___y_5598_, v___y_5599_, v___x_5637_, v___y_5601_);
lean_dec_ref_known(v___x_5637_, 14);
if (lean_obj_tag(v___x_5638_) == 0)
{
lean_dec_ref_known(v___x_5638_, 1);
v_a_5604_ = v___x_5615_;
goto v___jp_5603_;
}
else
{
return v___x_5638_;
}
}
else
{
lean_dec(v_val_5617_);
return v___x_5619_;
}
}
else
{
lean_object* v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; 
lean_dec(v___x_5616_);
v___x_5639_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1);
v___x_5640_ = l_Lean_indentExpr(v_a_5612_);
v___x_5641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5641_, 0, v___x_5639_);
lean_ctor_set(v___x_5641_, 1, v___x_5640_);
v___x_5642_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v___x_5641_, v___y_5596_, v___y_5597_, v___y_5598_, v___y_5599_, v___y_5600_, v___y_5601_);
if (lean_obj_tag(v___x_5642_) == 0)
{
lean_dec_ref_known(v___x_5642_, 1);
v_a_5604_ = v___x_5615_;
goto v___jp_5603_;
}
else
{
return v___x_5642_;
}
}
}
else
{
lean_object* v_a_5643_; lean_object* v___x_5645_; uint8_t v_isShared_5646_; uint8_t v_isSharedCheck_5650_; 
lean_dec(v_a_5612_);
v_a_5643_ = lean_ctor_get(v___x_5613_, 0);
v_isSharedCheck_5650_ = !lean_is_exclusive(v___x_5613_);
if (v_isSharedCheck_5650_ == 0)
{
v___x_5645_ = v___x_5613_;
v_isShared_5646_ = v_isSharedCheck_5650_;
goto v_resetjp_5644_;
}
else
{
lean_inc(v_a_5643_);
lean_dec(v___x_5613_);
v___x_5645_ = lean_box(0);
v_isShared_5646_ = v_isSharedCheck_5650_;
goto v_resetjp_5644_;
}
v_resetjp_5644_:
{
lean_object* v___x_5648_; 
if (v_isShared_5646_ == 0)
{
v___x_5648_ = v___x_5645_;
goto v_reusejp_5647_;
}
else
{
lean_object* v_reuseFailAlloc_5649_; 
v_reuseFailAlloc_5649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5649_, 0, v_a_5643_);
v___x_5648_ = v_reuseFailAlloc_5649_;
goto v_reusejp_5647_;
}
v_reusejp_5647_:
{
return v___x_5648_;
}
}
}
}
else
{
lean_object* v_a_5651_; lean_object* v___x_5653_; uint8_t v_isShared_5654_; uint8_t v_isSharedCheck_5658_; 
v_a_5651_ = lean_ctor_get(v___x_5611_, 0);
v_isSharedCheck_5658_ = !lean_is_exclusive(v___x_5611_);
if (v_isSharedCheck_5658_ == 0)
{
v___x_5653_ = v___x_5611_;
v_isShared_5654_ = v_isSharedCheck_5658_;
goto v_resetjp_5652_;
}
else
{
lean_inc(v_a_5651_);
lean_dec(v___x_5611_);
v___x_5653_ = lean_box(0);
v_isShared_5654_ = v_isSharedCheck_5658_;
goto v_resetjp_5652_;
}
v_resetjp_5652_:
{
lean_object* v___x_5656_; 
if (v_isShared_5654_ == 0)
{
v___x_5656_ = v___x_5653_;
goto v_reusejp_5655_;
}
else
{
lean_object* v_reuseFailAlloc_5657_; 
v_reuseFailAlloc_5657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5657_, 0, v_a_5651_);
v___x_5656_ = v_reuseFailAlloc_5657_;
goto v_reusejp_5655_;
}
v_reusejp_5655_:
{
return v___x_5656_;
}
}
}
}
v___jp_5603_:
{
size_t v___x_5605_; size_t v___x_5606_; 
v___x_5605_ = ((size_t)1ULL);
v___x_5606_ = lean_usize_add(v_i_5594_, v___x_5605_);
v_i_5594_ = v___x_5606_;
v_b_5595_ = v_a_5604_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___boxed(lean_object* v_as_5659_, lean_object* v_sz_5660_, lean_object* v_i_5661_, lean_object* v_b_5662_, lean_object* v___y_5663_, lean_object* v___y_5664_, lean_object* v___y_5665_, lean_object* v___y_5666_, lean_object* v___y_5667_, lean_object* v___y_5668_, lean_object* v___y_5669_){
_start:
{
size_t v_sz_boxed_5670_; size_t v_i_boxed_5671_; lean_object* v_res_5672_; 
v_sz_boxed_5670_ = lean_unbox_usize(v_sz_5660_);
lean_dec(v_sz_5660_);
v_i_boxed_5671_ = lean_unbox_usize(v_i_5661_);
lean_dec(v_i_5661_);
v_res_5672_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(v_as_5659_, v_sz_boxed_5670_, v_i_boxed_5671_, v_b_5662_, v___y_5663_, v___y_5664_, v___y_5665_, v___y_5666_, v___y_5667_, v___y_5668_);
lean_dec(v___y_5668_);
lean_dec_ref(v___y_5667_);
lean_dec(v___y_5666_);
lean_dec_ref(v___y_5665_);
lean_dec(v___y_5664_);
lean_dec_ref(v___y_5663_);
lean_dec_ref(v_as_5659_);
return v_res_5672_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(lean_object* v_as_5673_, size_t v_i_5674_, size_t v_stop_5675_, lean_object* v_b_5676_, lean_object* v___y_5677_, lean_object* v___y_5678_, lean_object* v___y_5679_, lean_object* v___y_5680_){
_start:
{
uint8_t v___x_5682_; 
v___x_5682_ = lean_usize_dec_eq(v_i_5674_, v_stop_5675_);
if (v___x_5682_ == 0)
{
lean_object* v___x_5683_; lean_object* v___x_5684_; 
v___x_5683_ = lean_array_uget_borrowed(v_as_5673_, v_i_5674_);
lean_inc(v___x_5683_);
v___x_5684_ = l_Lean_MVarId_getType(v___x_5683_, v___y_5677_, v___y_5678_, v___y_5679_, v___y_5680_);
if (lean_obj_tag(v___x_5684_) == 0)
{
lean_object* v_a_5685_; lean_object* v___x_5686_; lean_object* v___x_5687_; 
v_a_5685_ = lean_ctor_get(v___x_5684_, 0);
lean_inc(v_a_5685_);
lean_dec_ref_known(v___x_5684_, 1);
v___x_5686_ = l_Lean_Expr_mdataExpr_x21(v_a_5685_);
lean_dec(v_a_5685_);
lean_inc(v___x_5683_);
v___x_5687_ = l_Lean_MVarId_setType___redArg(v___x_5683_, v___x_5686_, v___y_5678_);
if (lean_obj_tag(v___x_5687_) == 0)
{
lean_object* v_a_5688_; size_t v___x_5689_; size_t v___x_5690_; 
v_a_5688_ = lean_ctor_get(v___x_5687_, 0);
lean_inc(v_a_5688_);
lean_dec_ref_known(v___x_5687_, 1);
v___x_5689_ = ((size_t)1ULL);
v___x_5690_ = lean_usize_add(v_i_5674_, v___x_5689_);
v_i_5674_ = v___x_5690_;
v_b_5676_ = v_a_5688_;
goto _start;
}
else
{
return v___x_5687_;
}
}
else
{
lean_object* v_a_5692_; lean_object* v___x_5694_; uint8_t v_isShared_5695_; uint8_t v_isSharedCheck_5699_; 
v_a_5692_ = lean_ctor_get(v___x_5684_, 0);
v_isSharedCheck_5699_ = !lean_is_exclusive(v___x_5684_);
if (v_isSharedCheck_5699_ == 0)
{
v___x_5694_ = v___x_5684_;
v_isShared_5695_ = v_isSharedCheck_5699_;
goto v_resetjp_5693_;
}
else
{
lean_inc(v_a_5692_);
lean_dec(v___x_5684_);
v___x_5694_ = lean_box(0);
v_isShared_5695_ = v_isSharedCheck_5699_;
goto v_resetjp_5693_;
}
v_resetjp_5693_:
{
lean_object* v___x_5697_; 
if (v_isShared_5695_ == 0)
{
v___x_5697_ = v___x_5694_;
goto v_reusejp_5696_;
}
else
{
lean_object* v_reuseFailAlloc_5698_; 
v_reuseFailAlloc_5698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5698_, 0, v_a_5692_);
v___x_5697_ = v_reuseFailAlloc_5698_;
goto v_reusejp_5696_;
}
v_reusejp_5696_:
{
return v___x_5697_;
}
}
}
}
else
{
lean_object* v___x_5700_; 
v___x_5700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5700_, 0, v_b_5676_);
return v___x_5700_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg___boxed(lean_object* v_as_5701_, lean_object* v_i_5702_, lean_object* v_stop_5703_, lean_object* v_b_5704_, lean_object* v___y_5705_, lean_object* v___y_5706_, lean_object* v___y_5707_, lean_object* v___y_5708_, lean_object* v___y_5709_){
_start:
{
size_t v_i_boxed_5710_; size_t v_stop_boxed_5711_; lean_object* v_res_5712_; 
v_i_boxed_5710_ = lean_unbox_usize(v_i_5702_);
lean_dec(v_i_5702_);
v_stop_boxed_5711_ = lean_unbox_usize(v_stop_5703_);
lean_dec(v_stop_5703_);
v_res_5712_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v_as_5701_, v_i_boxed_5710_, v_stop_boxed_5711_, v_b_5704_, v___y_5705_, v___y_5706_, v___y_5707_, v___y_5708_);
lean_dec(v___y_5708_);
lean_dec_ref(v___y_5707_);
lean_dec(v___y_5706_);
lean_dec_ref(v___y_5705_);
lean_dec_ref(v_as_5701_);
return v_res_5712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3(lean_object* v___x_5713_, lean_object* v___x_5714_, lean_object* v___x_5715_, lean_object* v___y_5716_, lean_object* v___y_5717_, lean_object* v___y_5718_, lean_object* v___y_5719_, lean_object* v___y_5720_, lean_object* v___y_5721_){
_start:
{
if (lean_obj_tag(v___x_5713_) == 0)
{
lean_object* v___x_5723_; size_t v_sz_5724_; size_t v___x_5725_; lean_object* v___x_5726_; 
v___x_5723_ = lean_box(0);
v_sz_5724_ = lean_array_size(v___x_5714_);
v___x_5725_ = ((size_t)0ULL);
v___x_5726_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(v___x_5714_, v_sz_5724_, v___x_5725_, v___x_5723_, v___y_5716_, v___y_5717_, v___y_5718_, v___y_5719_, v___y_5720_, v___y_5721_);
lean_dec_ref(v___x_5714_);
if (lean_obj_tag(v___x_5726_) == 0)
{
lean_object* v___x_5728_; uint8_t v_isShared_5729_; uint8_t v_isSharedCheck_5733_; 
v_isSharedCheck_5733_ = !lean_is_exclusive(v___x_5726_);
if (v_isSharedCheck_5733_ == 0)
{
lean_object* v_unused_5734_; 
v_unused_5734_ = lean_ctor_get(v___x_5726_, 0);
lean_dec(v_unused_5734_);
v___x_5728_ = v___x_5726_;
v_isShared_5729_ = v_isSharedCheck_5733_;
goto v_resetjp_5727_;
}
else
{
lean_dec(v___x_5726_);
v___x_5728_ = lean_box(0);
v_isShared_5729_ = v_isSharedCheck_5733_;
goto v_resetjp_5727_;
}
v_resetjp_5727_:
{
lean_object* v___x_5731_; 
if (v_isShared_5729_ == 0)
{
lean_ctor_set(v___x_5728_, 0, v___x_5723_);
v___x_5731_ = v___x_5728_;
goto v_reusejp_5730_;
}
else
{
lean_object* v_reuseFailAlloc_5732_; 
v_reuseFailAlloc_5732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5732_, 0, v___x_5723_);
v___x_5731_ = v_reuseFailAlloc_5732_;
goto v_reusejp_5730_;
}
v_reusejp_5730_:
{
return v___x_5731_;
}
}
}
else
{
return v___x_5726_;
}
}
else
{
lean_object* v_val_5735_; lean_object* v___x_5737_; uint8_t v_isShared_5738_; uint8_t v_isSharedCheck_5813_; 
v_val_5735_ = lean_ctor_get(v___x_5713_, 0);
v_isSharedCheck_5813_ = !lean_is_exclusive(v___x_5713_);
if (v_isSharedCheck_5813_ == 0)
{
v___x_5737_ = v___x_5713_;
v_isShared_5738_ = v_isSharedCheck_5813_;
goto v_resetjp_5736_;
}
else
{
lean_inc(v_val_5735_);
lean_dec(v___x_5713_);
v___x_5737_ = lean_box(0);
v_isShared_5738_ = v_isSharedCheck_5813_;
goto v_resetjp_5736_;
}
v_resetjp_5736_:
{
lean_object* v_ref_5739_; lean_object* v_tactic_5740_; lean_object* v_fileName_5741_; lean_object* v_fileMap_5742_; lean_object* v_options_5743_; lean_object* v_currRecDepth_5744_; lean_object* v_maxRecDepth_5745_; lean_object* v_ref_5746_; lean_object* v_currNamespace_5747_; lean_object* v_openDecls_5748_; lean_object* v_initHeartbeats_5749_; lean_object* v_maxHeartbeats_5750_; lean_object* v_quotContext_5751_; lean_object* v_currMacroScope_5752_; uint8_t v_diag_5753_; lean_object* v_cancelTk_x3f_5754_; uint8_t v_suppressElabErrors_5755_; lean_object* v_inheritedTraceOptions_5756_; lean_object* v___x_5757_; lean_object* v___x_5758_; lean_object* v_ref_5759_; lean_object* v___x_5760_; lean_object* v___y_5786_; lean_object* v___y_5803_; uint8_t v___x_5804_; 
v_ref_5739_ = lean_ctor_get(v_val_5735_, 0);
lean_inc(v_ref_5739_);
v_tactic_5740_ = lean_ctor_get(v_val_5735_, 1);
lean_inc(v_tactic_5740_);
lean_dec(v_val_5735_);
v_fileName_5741_ = lean_ctor_get(v___y_5720_, 0);
v_fileMap_5742_ = lean_ctor_get(v___y_5720_, 1);
v_options_5743_ = lean_ctor_get(v___y_5720_, 2);
v_currRecDepth_5744_ = lean_ctor_get(v___y_5720_, 3);
v_maxRecDepth_5745_ = lean_ctor_get(v___y_5720_, 4);
v_ref_5746_ = lean_ctor_get(v___y_5720_, 5);
v_currNamespace_5747_ = lean_ctor_get(v___y_5720_, 6);
v_openDecls_5748_ = lean_ctor_get(v___y_5720_, 7);
v_initHeartbeats_5749_ = lean_ctor_get(v___y_5720_, 8);
v_maxHeartbeats_5750_ = lean_ctor_get(v___y_5720_, 9);
v_quotContext_5751_ = lean_ctor_get(v___y_5720_, 10);
v_currMacroScope_5752_ = lean_ctor_get(v___y_5720_, 11);
v_diag_5753_ = lean_ctor_get_uint8(v___y_5720_, sizeof(void*)*14);
v_cancelTk_x3f_5754_ = lean_ctor_get(v___y_5720_, 12);
v_suppressElabErrors_5755_ = lean_ctor_get_uint8(v___y_5720_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5756_ = lean_ctor_get(v___y_5720_, 13);
v___x_5757_ = lean_unsigned_to_nat(0u);
v___x_5758_ = lean_array_get_size(v___x_5714_);
v_ref_5759_ = l_Lean_replaceRef(v_ref_5739_, v_ref_5746_);
lean_inc_ref(v_inheritedTraceOptions_5756_);
lean_inc(v_cancelTk_x3f_5754_);
lean_inc(v_currMacroScope_5752_);
lean_inc(v_quotContext_5751_);
lean_inc(v_maxHeartbeats_5750_);
lean_inc(v_initHeartbeats_5749_);
lean_inc(v_openDecls_5748_);
lean_inc(v_currNamespace_5747_);
lean_inc(v_maxRecDepth_5745_);
lean_inc(v_currRecDepth_5744_);
lean_inc_ref(v_options_5743_);
lean_inc_ref(v_fileMap_5742_);
lean_inc_ref(v_fileName_5741_);
v___x_5760_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5760_, 0, v_fileName_5741_);
lean_ctor_set(v___x_5760_, 1, v_fileMap_5742_);
lean_ctor_set(v___x_5760_, 2, v_options_5743_);
lean_ctor_set(v___x_5760_, 3, v_currRecDepth_5744_);
lean_ctor_set(v___x_5760_, 4, v_maxRecDepth_5745_);
lean_ctor_set(v___x_5760_, 5, v_ref_5759_);
lean_ctor_set(v___x_5760_, 6, v_currNamespace_5747_);
lean_ctor_set(v___x_5760_, 7, v_openDecls_5748_);
lean_ctor_set(v___x_5760_, 8, v_initHeartbeats_5749_);
lean_ctor_set(v___x_5760_, 9, v_maxHeartbeats_5750_);
lean_ctor_set(v___x_5760_, 10, v_quotContext_5751_);
lean_ctor_set(v___x_5760_, 11, v_currMacroScope_5752_);
lean_ctor_set(v___x_5760_, 12, v_cancelTk_x3f_5754_);
lean_ctor_set(v___x_5760_, 13, v_inheritedTraceOptions_5756_);
lean_ctor_set_uint8(v___x_5760_, sizeof(void*)*14, v_diag_5753_);
lean_ctor_set_uint8(v___x_5760_, sizeof(void*)*14 + 1, v_suppressElabErrors_5755_);
v___x_5804_ = lean_nat_dec_lt(v___x_5757_, v___x_5758_);
if (v___x_5804_ == 0)
{
goto v___jp_5787_;
}
else
{
lean_object* v___x_5805_; uint8_t v___x_5806_; 
v___x_5805_ = lean_box(0);
v___x_5806_ = lean_nat_dec_le(v___x_5758_, v___x_5758_);
if (v___x_5806_ == 0)
{
if (v___x_5804_ == 0)
{
goto v___jp_5787_;
}
else
{
size_t v___x_5807_; size_t v___x_5808_; lean_object* v___x_5809_; 
v___x_5807_ = ((size_t)0ULL);
v___x_5808_ = lean_usize_of_nat(v___x_5758_);
v___x_5809_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v___x_5714_, v___x_5807_, v___x_5808_, v___x_5805_, v___y_5718_, v___y_5719_, v___x_5760_, v___y_5721_);
v___y_5803_ = v___x_5809_;
goto v___jp_5802_;
}
}
else
{
size_t v___x_5810_; size_t v___x_5811_; lean_object* v___x_5812_; 
v___x_5810_ = ((size_t)0ULL);
v___x_5811_ = lean_usize_of_nat(v___x_5758_);
v___x_5812_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v___x_5714_, v___x_5810_, v___x_5811_, v___x_5805_, v___y_5718_, v___y_5719_, v___x_5760_, v___y_5721_);
v___y_5803_ = v___x_5812_;
goto v___jp_5802_;
}
}
v___jp_5761_:
{
lean_object* v___x_5762_; lean_object* v___x_5763_; lean_object* v___f_5764_; lean_object* v___x_5765_; 
v___x_5762_ = lean_array_get(v___x_5715_, v___x_5714_, v___x_5757_);
v___x_5763_ = lean_array_to_list(v___x_5714_);
v___f_5764_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2___boxed), 12, 3);
lean_closure_set(v___f_5764_, 0, v___x_5763_);
lean_closure_set(v___f_5764_, 1, v_ref_5739_);
lean_closure_set(v___f_5764_, 2, v_tactic_5740_);
v___x_5765_ = l_Lean_Elab_Tactic_run(v___x_5762_, v___f_5764_, v___y_5716_, v___y_5717_, v___y_5718_, v___y_5719_, v___x_5760_, v___y_5721_);
if (lean_obj_tag(v___x_5765_) == 0)
{
lean_object* v_a_5766_; lean_object* v___x_5768_; uint8_t v_isShared_5769_; uint8_t v_isSharedCheck_5776_; 
v_a_5766_ = lean_ctor_get(v___x_5765_, 0);
v_isSharedCheck_5776_ = !lean_is_exclusive(v___x_5765_);
if (v_isSharedCheck_5776_ == 0)
{
v___x_5768_ = v___x_5765_;
v_isShared_5769_ = v_isSharedCheck_5776_;
goto v_resetjp_5767_;
}
else
{
lean_inc(v_a_5766_);
lean_dec(v___x_5765_);
v___x_5768_ = lean_box(0);
v_isShared_5769_ = v_isSharedCheck_5776_;
goto v_resetjp_5767_;
}
v_resetjp_5767_:
{
uint8_t v___x_5770_; 
v___x_5770_ = l_List_isEmpty___redArg(v_a_5766_);
if (v___x_5770_ == 0)
{
lean_object* v___x_5771_; 
lean_del_object(v___x_5768_);
v___x_5771_ = l_Lean_Elab_Term_reportUnsolvedGoals(v_a_5766_, v___y_5718_, v___y_5719_, v___x_5760_, v___y_5721_);
lean_dec_ref_known(v___x_5760_, 14);
return v___x_5771_;
}
else
{
lean_object* v___x_5772_; lean_object* v___x_5774_; 
lean_dec(v_a_5766_);
lean_dec_ref_known(v___x_5760_, 14);
v___x_5772_ = lean_box(0);
if (v_isShared_5769_ == 0)
{
lean_ctor_set(v___x_5768_, 0, v___x_5772_);
v___x_5774_ = v___x_5768_;
goto v_reusejp_5773_;
}
else
{
lean_object* v_reuseFailAlloc_5775_; 
v_reuseFailAlloc_5775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5775_, 0, v___x_5772_);
v___x_5774_ = v_reuseFailAlloc_5775_;
goto v_reusejp_5773_;
}
v_reusejp_5773_:
{
return v___x_5774_;
}
}
}
}
else
{
lean_object* v_a_5777_; lean_object* v___x_5779_; uint8_t v_isShared_5780_; uint8_t v_isSharedCheck_5784_; 
lean_dec_ref_known(v___x_5760_, 14);
v_a_5777_ = lean_ctor_get(v___x_5765_, 0);
v_isSharedCheck_5784_ = !lean_is_exclusive(v___x_5765_);
if (v_isSharedCheck_5784_ == 0)
{
v___x_5779_ = v___x_5765_;
v_isShared_5780_ = v_isSharedCheck_5784_;
goto v_resetjp_5778_;
}
else
{
lean_inc(v_a_5777_);
lean_dec(v___x_5765_);
v___x_5779_ = lean_box(0);
v_isShared_5780_ = v_isSharedCheck_5784_;
goto v_resetjp_5778_;
}
v_resetjp_5778_:
{
lean_object* v___x_5782_; 
if (v_isShared_5780_ == 0)
{
v___x_5782_ = v___x_5779_;
goto v_reusejp_5781_;
}
else
{
lean_object* v_reuseFailAlloc_5783_; 
v_reuseFailAlloc_5783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5783_, 0, v_a_5777_);
v___x_5782_ = v_reuseFailAlloc_5783_;
goto v_reusejp_5781_;
}
v_reusejp_5781_:
{
return v___x_5782_;
}
}
}
}
v___jp_5785_:
{
if (lean_obj_tag(v___y_5786_) == 0)
{
lean_dec_ref_known(v___y_5786_, 1);
goto v___jp_5761_;
}
else
{
lean_dec_ref_known(v___x_5760_, 14);
lean_dec(v_tactic_5740_);
lean_dec(v_ref_5739_);
lean_dec_ref(v___x_5714_);
return v___y_5786_;
}
}
v___jp_5787_:
{
uint8_t v___x_5788_; 
v___x_5788_ = lean_nat_dec_eq(v___x_5758_, v___x_5757_);
if (v___x_5788_ == 0)
{
uint8_t v___x_5789_; 
lean_del_object(v___x_5737_);
v___x_5789_ = lean_nat_dec_lt(v___x_5757_, v___x_5758_);
if (v___x_5789_ == 0)
{
goto v___jp_5761_;
}
else
{
lean_object* v___x_5790_; uint8_t v___x_5791_; 
v___x_5790_ = lean_box(0);
v___x_5791_ = lean_nat_dec_le(v___x_5758_, v___x_5758_);
if (v___x_5791_ == 0)
{
if (v___x_5789_ == 0)
{
goto v___jp_5761_;
}
else
{
size_t v___x_5792_; size_t v___x_5793_; lean_object* v___x_5794_; 
v___x_5792_ = ((size_t)0ULL);
v___x_5793_ = lean_usize_of_nat(v___x_5758_);
v___x_5794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v___x_5714_, v___x_5792_, v___x_5793_, v___x_5790_, v___y_5716_, v___y_5717_, v___y_5718_, v___y_5719_, v___x_5760_, v___y_5721_);
v___y_5786_ = v___x_5794_;
goto v___jp_5785_;
}
}
else
{
size_t v___x_5795_; size_t v___x_5796_; lean_object* v___x_5797_; 
v___x_5795_ = ((size_t)0ULL);
v___x_5796_ = lean_usize_of_nat(v___x_5758_);
v___x_5797_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v___x_5714_, v___x_5795_, v___x_5796_, v___x_5790_, v___y_5716_, v___y_5717_, v___y_5718_, v___y_5719_, v___x_5760_, v___y_5721_);
v___y_5786_ = v___x_5797_;
goto v___jp_5785_;
}
}
}
else
{
lean_object* v___x_5798_; lean_object* v___x_5800_; 
lean_dec_ref_known(v___x_5760_, 14);
lean_dec(v_tactic_5740_);
lean_dec(v_ref_5739_);
lean_dec_ref(v___x_5714_);
v___x_5798_ = lean_box(0);
if (v_isShared_5738_ == 0)
{
lean_ctor_set_tag(v___x_5737_, 0);
lean_ctor_set(v___x_5737_, 0, v___x_5798_);
v___x_5800_ = v___x_5737_;
goto v_reusejp_5799_;
}
else
{
lean_object* v_reuseFailAlloc_5801_; 
v_reuseFailAlloc_5801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5801_, 0, v___x_5798_);
v___x_5800_ = v_reuseFailAlloc_5801_;
goto v_reusejp_5799_;
}
v_reusejp_5799_:
{
return v___x_5800_;
}
}
}
v___jp_5802_:
{
if (lean_obj_tag(v___y_5803_) == 0)
{
lean_dec_ref_known(v___y_5803_, 1);
goto v___jp_5787_;
}
else
{
lean_dec_ref_known(v___x_5760_, 14);
lean_dec(v_tactic_5740_);
lean_dec(v_ref_5739_);
lean_del_object(v___x_5737_);
lean_dec_ref(v___x_5714_);
return v___y_5803_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3___boxed(lean_object* v___x_5814_, lean_object* v___x_5815_, lean_object* v___x_5816_, lean_object* v___y_5817_, lean_object* v___y_5818_, lean_object* v___y_5819_, lean_object* v___y_5820_, lean_object* v___y_5821_, lean_object* v___y_5822_, lean_object* v___y_5823_){
_start:
{
lean_object* v_res_5824_; 
v_res_5824_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3(v___x_5814_, v___x_5815_, v___x_5816_, v___y_5817_, v___y_5818_, v___y_5819_, v___y_5820_, v___y_5821_, v___y_5822_);
lean_dec(v___y_5822_);
lean_dec_ref(v___y_5821_);
lean_dec(v___y_5820_);
lean_dec_ref(v___y_5819_);
lean_dec(v___y_5818_);
lean_dec_ref(v___y_5817_);
lean_dec(v___x_5816_);
return v_res_5824_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0(lean_object* v_x_5825_){
_start:
{
uint8_t v___x_5826_; 
v___x_5826_ = 0;
return v___x_5826_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0___boxed(lean_object* v_x_5827_){
_start:
{
uint8_t v_res_5828_; lean_object* v_r_5829_; 
v_res_5828_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0(v_x_5827_);
lean_dec(v_x_5827_);
v_r_5829_ = lean_box(v_res_5828_);
return v_r_5829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(lean_object* v_as_5836_, size_t v_sz_5837_, size_t v_i_5838_, lean_object* v_b_5839_, lean_object* v___y_5840_, lean_object* v___y_5841_, lean_object* v___y_5842_, lean_object* v___y_5843_){
_start:
{
uint8_t v___x_5845_; 
v___x_5845_ = lean_usize_dec_lt(v_i_5838_, v_sz_5837_);
if (v___x_5845_ == 0)
{
lean_object* v___x_5846_; 
v___x_5846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5846_, 0, v_b_5839_);
return v___x_5846_;
}
else
{
lean_object* v_snd_5847_; lean_object* v_fst_5848_; lean_object* v___x_5850_; uint8_t v_isShared_5851_; uint8_t v_isSharedCheck_5920_; 
v_snd_5847_ = lean_ctor_get(v_b_5839_, 1);
v_fst_5848_ = lean_ctor_get(v_b_5839_, 0);
v_isSharedCheck_5920_ = !lean_is_exclusive(v_b_5839_);
if (v_isSharedCheck_5920_ == 0)
{
v___x_5850_ = v_b_5839_;
v_isShared_5851_ = v_isSharedCheck_5920_;
goto v_resetjp_5849_;
}
else
{
lean_inc(v_snd_5847_);
lean_inc(v_fst_5848_);
lean_dec(v_b_5839_);
v___x_5850_ = lean_box(0);
v_isShared_5851_ = v_isSharedCheck_5920_;
goto v_resetjp_5849_;
}
v_resetjp_5849_:
{
lean_object* v_array_5852_; lean_object* v_start_5853_; lean_object* v_stop_5854_; uint8_t v___x_5855_; 
v_array_5852_ = lean_ctor_get(v_snd_5847_, 0);
v_start_5853_ = lean_ctor_get(v_snd_5847_, 1);
v_stop_5854_ = lean_ctor_get(v_snd_5847_, 2);
v___x_5855_ = lean_nat_dec_lt(v_start_5853_, v_stop_5854_);
if (v___x_5855_ == 0)
{
lean_object* v___x_5857_; 
if (v_isShared_5851_ == 0)
{
v___x_5857_ = v___x_5850_;
goto v_reusejp_5856_;
}
else
{
lean_object* v_reuseFailAlloc_5859_; 
v_reuseFailAlloc_5859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5859_, 0, v_fst_5848_);
lean_ctor_set(v_reuseFailAlloc_5859_, 1, v_snd_5847_);
v___x_5857_ = v_reuseFailAlloc_5859_;
goto v_reusejp_5856_;
}
v_reusejp_5856_:
{
lean_object* v___x_5858_; 
v___x_5858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5858_, 0, v___x_5857_);
return v___x_5858_;
}
}
else
{
lean_object* v___x_5861_; uint8_t v_isShared_5862_; uint8_t v_isSharedCheck_5916_; 
lean_inc(v_stop_5854_);
lean_inc(v_start_5853_);
lean_inc_ref(v_array_5852_);
v_isSharedCheck_5916_ = !lean_is_exclusive(v_snd_5847_);
if (v_isSharedCheck_5916_ == 0)
{
lean_object* v_unused_5917_; lean_object* v_unused_5918_; lean_object* v_unused_5919_; 
v_unused_5917_ = lean_ctor_get(v_snd_5847_, 2);
lean_dec(v_unused_5917_);
v_unused_5918_ = lean_ctor_get(v_snd_5847_, 1);
lean_dec(v_unused_5918_);
v_unused_5919_ = lean_ctor_get(v_snd_5847_, 0);
lean_dec(v_unused_5919_);
v___x_5861_ = v_snd_5847_;
v_isShared_5862_ = v_isSharedCheck_5916_;
goto v_resetjp_5860_;
}
else
{
lean_dec(v_snd_5847_);
v___x_5861_ = lean_box(0);
v_isShared_5862_ = v_isSharedCheck_5916_;
goto v_resetjp_5860_;
}
v_resetjp_5860_:
{
lean_object* v_array_5863_; lean_object* v_start_5864_; lean_object* v_stop_5865_; lean_object* v___x_5866_; lean_object* v___x_5867_; lean_object* v___x_5868_; lean_object* v___x_5870_; 
v_array_5863_ = lean_ctor_get(v_fst_5848_, 0);
v_start_5864_ = lean_ctor_get(v_fst_5848_, 1);
v_stop_5865_ = lean_ctor_get(v_fst_5848_, 2);
v___x_5866_ = lean_array_fget(v_array_5852_, v_start_5853_);
v___x_5867_ = lean_unsigned_to_nat(1u);
v___x_5868_ = lean_nat_add(v_start_5853_, v___x_5867_);
lean_dec(v_start_5853_);
if (v_isShared_5862_ == 0)
{
lean_ctor_set(v___x_5861_, 1, v___x_5868_);
v___x_5870_ = v___x_5861_;
goto v_reusejp_5869_;
}
else
{
lean_object* v_reuseFailAlloc_5915_; 
v_reuseFailAlloc_5915_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5915_, 0, v_array_5852_);
lean_ctor_set(v_reuseFailAlloc_5915_, 1, v___x_5868_);
lean_ctor_set(v_reuseFailAlloc_5915_, 2, v_stop_5854_);
v___x_5870_ = v_reuseFailAlloc_5915_;
goto v_reusejp_5869_;
}
v_reusejp_5869_:
{
uint8_t v___x_5871_; 
v___x_5871_ = lean_nat_dec_lt(v_start_5864_, v_stop_5865_);
if (v___x_5871_ == 0)
{
lean_object* v___x_5873_; 
lean_dec(v___x_5866_);
if (v_isShared_5851_ == 0)
{
lean_ctor_set(v___x_5850_, 1, v___x_5870_);
v___x_5873_ = v___x_5850_;
goto v_reusejp_5872_;
}
else
{
lean_object* v_reuseFailAlloc_5875_; 
v_reuseFailAlloc_5875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5875_, 0, v_fst_5848_);
lean_ctor_set(v_reuseFailAlloc_5875_, 1, v___x_5870_);
v___x_5873_ = v_reuseFailAlloc_5875_;
goto v_reusejp_5872_;
}
v_reusejp_5872_:
{
lean_object* v___x_5874_; 
v___x_5874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5874_, 0, v___x_5873_);
return v___x_5874_;
}
}
else
{
lean_object* v___x_5877_; uint8_t v_isShared_5878_; uint8_t v_isSharedCheck_5911_; 
lean_inc(v_stop_5865_);
lean_inc(v_start_5864_);
lean_inc_ref(v_array_5863_);
v_isSharedCheck_5911_ = !lean_is_exclusive(v_fst_5848_);
if (v_isSharedCheck_5911_ == 0)
{
lean_object* v_unused_5912_; lean_object* v_unused_5913_; lean_object* v_unused_5914_; 
v_unused_5912_ = lean_ctor_get(v_fst_5848_, 2);
lean_dec(v_unused_5912_);
v_unused_5913_ = lean_ctor_get(v_fst_5848_, 1);
lean_dec(v_unused_5913_);
v_unused_5914_ = lean_ctor_get(v_fst_5848_, 0);
lean_dec(v_unused_5914_);
v___x_5877_ = v_fst_5848_;
v_isShared_5878_ = v_isSharedCheck_5911_;
goto v_resetjp_5876_;
}
else
{
lean_dec(v_fst_5848_);
v___x_5877_ = lean_box(0);
v_isShared_5878_ = v_isSharedCheck_5911_;
goto v_resetjp_5876_;
}
v_resetjp_5876_:
{
lean_object* v___f_5879_; lean_object* v___x_5880_; lean_object* v_a_5881_; lean_object* v___x_5882_; lean_object* v___y_5883_; lean_object* v___x_5884_; lean_object* v___x_5885_; lean_object* v___x_5886_; lean_object* v___x_5887_; uint8_t v___x_5888_; lean_object* v___x_5889_; lean_object* v___x_5890_; lean_object* v___x_5891_; lean_object* v___x_5892_; 
v___f_5879_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__0));
v___x_5880_ = lean_box(0);
v_a_5881_ = lean_array_uget_borrowed(v_as_5836_, v_i_5838_);
v___x_5882_ = lean_array_fget_borrowed(v_array_5863_, v_start_5864_);
lean_inc(v___x_5882_);
v___y_5883_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3___boxed), 10, 3);
lean_closure_set(v___y_5883_, 0, v___x_5866_);
lean_closure_set(v___y_5883_, 1, v___x_5882_);
lean_closure_set(v___y_5883_, 2, v___x_5880_);
lean_inc(v_a_5881_);
v___x_5884_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withDeclName___boxed), 10, 3);
lean_closure_set(v___x_5884_, 0, lean_box(0));
lean_closure_set(v___x_5884_, 1, v_a_5881_);
lean_closure_set(v___x_5884_, 2, v___y_5883_);
v___x_5885_ = lean_box(0);
v___x_5886_ = lean_box(0);
v___x_5887_ = lean_box(1);
v___x_5888_ = 0;
v___x_5889_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__1));
v___x_5890_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_5890_, 0, v___x_5885_);
lean_ctor_set(v___x_5890_, 1, v___x_5886_);
lean_ctor_set(v___x_5890_, 2, v___x_5885_);
lean_ctor_set(v___x_5890_, 3, v___f_5879_);
lean_ctor_set(v___x_5890_, 4, v___x_5887_);
lean_ctor_set(v___x_5890_, 5, v___x_5887_);
lean_ctor_set(v___x_5890_, 6, v___x_5885_);
lean_ctor_set(v___x_5890_, 7, v___x_5889_);
lean_ctor_set_uint8(v___x_5890_, sizeof(void*)*8, v___x_5871_);
lean_ctor_set_uint8(v___x_5890_, sizeof(void*)*8 + 1, v___x_5871_);
lean_ctor_set_uint8(v___x_5890_, sizeof(void*)*8 + 2, v___x_5871_);
lean_ctor_set_uint8(v___x_5890_, sizeof(void*)*8 + 3, v___x_5871_);
lean_ctor_set_uint8(v___x_5890_, sizeof(void*)*8 + 4, v___x_5888_);
lean_ctor_set_uint8(v___x_5890_, sizeof(void*)*8 + 5, v___x_5888_);
lean_ctor_set_uint8(v___x_5890_, sizeof(void*)*8 + 6, v___x_5888_);
lean_ctor_set_uint8(v___x_5890_, sizeof(void*)*8 + 7, v___x_5888_);
lean_ctor_set_uint8(v___x_5890_, sizeof(void*)*8 + 8, v___x_5871_);
lean_ctor_set_uint8(v___x_5890_, sizeof(void*)*8 + 9, v___x_5888_);
lean_ctor_set_uint8(v___x_5890_, sizeof(void*)*8 + 10, v___x_5871_);
v___x_5891_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__2));
v___x_5892_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_5884_, v___x_5890_, v___x_5891_, v___y_5840_, v___y_5841_, v___y_5842_, v___y_5843_);
if (lean_obj_tag(v___x_5892_) == 0)
{
lean_object* v___x_5893_; lean_object* v___x_5895_; 
lean_dec_ref_known(v___x_5892_, 1);
v___x_5893_ = lean_nat_add(v_start_5864_, v___x_5867_);
lean_dec(v_start_5864_);
if (v_isShared_5878_ == 0)
{
lean_ctor_set(v___x_5877_, 1, v___x_5893_);
v___x_5895_ = v___x_5877_;
goto v_reusejp_5894_;
}
else
{
lean_object* v_reuseFailAlloc_5902_; 
v_reuseFailAlloc_5902_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5902_, 0, v_array_5863_);
lean_ctor_set(v_reuseFailAlloc_5902_, 1, v___x_5893_);
lean_ctor_set(v_reuseFailAlloc_5902_, 2, v_stop_5865_);
v___x_5895_ = v_reuseFailAlloc_5902_;
goto v_reusejp_5894_;
}
v_reusejp_5894_:
{
lean_object* v___x_5897_; 
if (v_isShared_5851_ == 0)
{
lean_ctor_set(v___x_5850_, 1, v___x_5870_);
lean_ctor_set(v___x_5850_, 0, v___x_5895_);
v___x_5897_ = v___x_5850_;
goto v_reusejp_5896_;
}
else
{
lean_object* v_reuseFailAlloc_5901_; 
v_reuseFailAlloc_5901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5901_, 0, v___x_5895_);
lean_ctor_set(v_reuseFailAlloc_5901_, 1, v___x_5870_);
v___x_5897_ = v_reuseFailAlloc_5901_;
goto v_reusejp_5896_;
}
v_reusejp_5896_:
{
size_t v___x_5898_; size_t v___x_5899_; 
v___x_5898_ = ((size_t)1ULL);
v___x_5899_ = lean_usize_add(v_i_5838_, v___x_5898_);
v_i_5838_ = v___x_5899_;
v_b_5839_ = v___x_5897_;
goto _start;
}
}
}
else
{
lean_object* v_a_5903_; lean_object* v___x_5905_; uint8_t v_isShared_5906_; uint8_t v_isSharedCheck_5910_; 
lean_del_object(v___x_5877_);
lean_dec_ref(v___x_5870_);
lean_dec(v_stop_5865_);
lean_dec(v_start_5864_);
lean_dec_ref(v_array_5863_);
lean_del_object(v___x_5850_);
v_a_5903_ = lean_ctor_get(v___x_5892_, 0);
v_isSharedCheck_5910_ = !lean_is_exclusive(v___x_5892_);
if (v_isSharedCheck_5910_ == 0)
{
v___x_5905_ = v___x_5892_;
v_isShared_5906_ = v_isSharedCheck_5910_;
goto v_resetjp_5904_;
}
else
{
lean_inc(v_a_5903_);
lean_dec(v___x_5892_);
v___x_5905_ = lean_box(0);
v_isShared_5906_ = v_isSharedCheck_5910_;
goto v_resetjp_5904_;
}
v_resetjp_5904_:
{
lean_object* v___x_5908_; 
if (v_isShared_5906_ == 0)
{
v___x_5908_ = v___x_5905_;
goto v_reusejp_5907_;
}
else
{
lean_object* v_reuseFailAlloc_5909_; 
v_reuseFailAlloc_5909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5909_, 0, v_a_5903_);
v___x_5908_ = v_reuseFailAlloc_5909_;
goto v_reusejp_5907_;
}
v_reusejp_5907_:
{
return v___x_5908_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___boxed(lean_object* v_as_5921_, lean_object* v_sz_5922_, lean_object* v_i_5923_, lean_object* v_b_5924_, lean_object* v___y_5925_, lean_object* v___y_5926_, lean_object* v___y_5927_, lean_object* v___y_5928_, lean_object* v___y_5929_){
_start:
{
size_t v_sz_boxed_5930_; size_t v_i_boxed_5931_; lean_object* v_res_5932_; 
v_sz_boxed_5930_ = lean_unbox_usize(v_sz_5922_);
lean_dec(v_sz_5922_);
v_i_boxed_5931_ = lean_unbox_usize(v_i_5923_);
lean_dec(v_i_5923_);
v_res_5932_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(v_as_5921_, v_sz_boxed_5930_, v_i_boxed_5931_, v_b_5924_, v___y_5925_, v___y_5926_, v___y_5927_, v___y_5928_);
lean_dec(v___y_5928_);
lean_dec_ref(v___y_5927_);
lean_dec(v___y_5926_);
lean_dec_ref(v___y_5925_);
lean_dec_ref(v_as_5921_);
return v_res_5932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___lam__0(lean_object* v_value_5933_, lean_object* v_decrTactics_5934_, lean_object* v_argsPacker_5935_, lean_object* v_funNames_5936_, lean_object* v___y_5937_, lean_object* v___y_5938_, lean_object* v___y_5939_, lean_object* v___y_5940_){
_start:
{
lean_object* v___x_5942_; 
lean_inc_ref(v_value_5933_);
v___x_5942_ = l_Lean_Meta_getMVarsNoDelayed(v_value_5933_, v___y_5937_, v___y_5938_, v___y_5939_, v___y_5940_);
if (lean_obj_tag(v___x_5942_) == 0)
{
lean_object* v_a_5943_; lean_object* v___x_5944_; 
v_a_5943_ = lean_ctor_get(v___x_5942_, 0);
lean_inc(v_a_5943_);
lean_dec_ref_known(v___x_5942_, 1);
v___x_5944_ = l_Lean_Elab_WF_assignSubsumed(v_a_5943_, v___y_5937_, v___y_5938_, v___y_5939_, v___y_5940_);
lean_dec(v_a_5943_);
if (lean_obj_tag(v___x_5944_) == 0)
{
lean_object* v_a_5945_; lean_object* v___x_5946_; lean_object* v___x_5947_; 
v_a_5945_ = lean_ctor_get(v___x_5944_, 0);
lean_inc(v_a_5945_);
lean_dec_ref_known(v___x_5944_, 1);
v___x_5946_ = lean_array_get_size(v_decrTactics_5934_);
v___x_5947_ = l_Lean_Elab_WF_groupGoalsByFunction(v_argsPacker_5935_, v___x_5946_, v_a_5945_, v___y_5937_, v___y_5938_, v___y_5939_, v___y_5940_);
lean_dec(v_a_5945_);
if (lean_obj_tag(v___x_5947_) == 0)
{
lean_object* v_a_5948_; lean_object* v___x_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; lean_object* v___x_5952_; lean_object* v___x_5953_; size_t v_sz_5954_; size_t v___x_5955_; lean_object* v___x_5956_; 
v_a_5948_ = lean_ctor_get(v___x_5947_, 0);
lean_inc(v_a_5948_);
lean_dec_ref_known(v___x_5947_, 1);
v___x_5949_ = lean_unsigned_to_nat(0u);
v___x_5950_ = lean_array_get_size(v_a_5948_);
v___x_5951_ = l_Array_toSubarray___redArg(v_a_5948_, v___x_5949_, v___x_5950_);
v___x_5952_ = l_Array_toSubarray___redArg(v_decrTactics_5934_, v___x_5949_, v___x_5946_);
v___x_5953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5953_, 0, v___x_5951_);
lean_ctor_set(v___x_5953_, 1, v___x_5952_);
v_sz_5954_ = lean_array_size(v_funNames_5936_);
v___x_5955_ = ((size_t)0ULL);
v___x_5956_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(v_funNames_5936_, v_sz_5954_, v___x_5955_, v___x_5953_, v___y_5937_, v___y_5938_, v___y_5939_, v___y_5940_);
if (lean_obj_tag(v___x_5956_) == 0)
{
lean_object* v___x_5957_; 
lean_dec_ref_known(v___x_5956_, 1);
v___x_5957_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_value_5933_, v___y_5938_);
return v___x_5957_;
}
else
{
lean_object* v_a_5958_; lean_object* v___x_5960_; uint8_t v_isShared_5961_; uint8_t v_isSharedCheck_5965_; 
lean_dec_ref(v_value_5933_);
v_a_5958_ = lean_ctor_get(v___x_5956_, 0);
v_isSharedCheck_5965_ = !lean_is_exclusive(v___x_5956_);
if (v_isSharedCheck_5965_ == 0)
{
v___x_5960_ = v___x_5956_;
v_isShared_5961_ = v_isSharedCheck_5965_;
goto v_resetjp_5959_;
}
else
{
lean_inc(v_a_5958_);
lean_dec(v___x_5956_);
v___x_5960_ = lean_box(0);
v_isShared_5961_ = v_isSharedCheck_5965_;
goto v_resetjp_5959_;
}
v_resetjp_5959_:
{
lean_object* v___x_5963_; 
if (v_isShared_5961_ == 0)
{
v___x_5963_ = v___x_5960_;
goto v_reusejp_5962_;
}
else
{
lean_object* v_reuseFailAlloc_5964_; 
v_reuseFailAlloc_5964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5964_, 0, v_a_5958_);
v___x_5963_ = v_reuseFailAlloc_5964_;
goto v_reusejp_5962_;
}
v_reusejp_5962_:
{
return v___x_5963_;
}
}
}
}
else
{
lean_object* v_a_5966_; lean_object* v___x_5968_; uint8_t v_isShared_5969_; uint8_t v_isSharedCheck_5973_; 
lean_dec_ref(v_decrTactics_5934_);
lean_dec_ref(v_value_5933_);
v_a_5966_ = lean_ctor_get(v___x_5947_, 0);
v_isSharedCheck_5973_ = !lean_is_exclusive(v___x_5947_);
if (v_isSharedCheck_5973_ == 0)
{
v___x_5968_ = v___x_5947_;
v_isShared_5969_ = v_isSharedCheck_5973_;
goto v_resetjp_5967_;
}
else
{
lean_inc(v_a_5966_);
lean_dec(v___x_5947_);
v___x_5968_ = lean_box(0);
v_isShared_5969_ = v_isSharedCheck_5973_;
goto v_resetjp_5967_;
}
v_resetjp_5967_:
{
lean_object* v___x_5971_; 
if (v_isShared_5969_ == 0)
{
v___x_5971_ = v___x_5968_;
goto v_reusejp_5970_;
}
else
{
lean_object* v_reuseFailAlloc_5972_; 
v_reuseFailAlloc_5972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5972_, 0, v_a_5966_);
v___x_5971_ = v_reuseFailAlloc_5972_;
goto v_reusejp_5970_;
}
v_reusejp_5970_:
{
return v___x_5971_;
}
}
}
}
else
{
lean_object* v_a_5974_; lean_object* v___x_5976_; uint8_t v_isShared_5977_; uint8_t v_isSharedCheck_5981_; 
lean_dec_ref(v_decrTactics_5934_);
lean_dec_ref(v_value_5933_);
v_a_5974_ = lean_ctor_get(v___x_5944_, 0);
v_isSharedCheck_5981_ = !lean_is_exclusive(v___x_5944_);
if (v_isSharedCheck_5981_ == 0)
{
v___x_5976_ = v___x_5944_;
v_isShared_5977_ = v_isSharedCheck_5981_;
goto v_resetjp_5975_;
}
else
{
lean_inc(v_a_5974_);
lean_dec(v___x_5944_);
v___x_5976_ = lean_box(0);
v_isShared_5977_ = v_isSharedCheck_5981_;
goto v_resetjp_5975_;
}
v_resetjp_5975_:
{
lean_object* v___x_5979_; 
if (v_isShared_5977_ == 0)
{
v___x_5979_ = v___x_5976_;
goto v_reusejp_5978_;
}
else
{
lean_object* v_reuseFailAlloc_5980_; 
v_reuseFailAlloc_5980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5980_, 0, v_a_5974_);
v___x_5979_ = v_reuseFailAlloc_5980_;
goto v_reusejp_5978_;
}
v_reusejp_5978_:
{
return v___x_5979_;
}
}
}
}
else
{
lean_object* v_a_5982_; lean_object* v___x_5984_; uint8_t v_isShared_5985_; uint8_t v_isSharedCheck_5989_; 
lean_dec_ref(v_decrTactics_5934_);
lean_dec_ref(v_value_5933_);
v_a_5982_ = lean_ctor_get(v___x_5942_, 0);
v_isSharedCheck_5989_ = !lean_is_exclusive(v___x_5942_);
if (v_isSharedCheck_5989_ == 0)
{
v___x_5984_ = v___x_5942_;
v_isShared_5985_ = v_isSharedCheck_5989_;
goto v_resetjp_5983_;
}
else
{
lean_inc(v_a_5982_);
lean_dec(v___x_5942_);
v___x_5984_ = lean_box(0);
v_isShared_5985_ = v_isSharedCheck_5989_;
goto v_resetjp_5983_;
}
v_resetjp_5983_:
{
lean_object* v___x_5987_; 
if (v_isShared_5985_ == 0)
{
v___x_5987_ = v___x_5984_;
goto v_reusejp_5986_;
}
else
{
lean_object* v_reuseFailAlloc_5988_; 
v_reuseFailAlloc_5988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5988_, 0, v_a_5982_);
v___x_5987_ = v_reuseFailAlloc_5988_;
goto v_reusejp_5986_;
}
v_reusejp_5986_:
{
return v___x_5987_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___lam__0___boxed(lean_object* v_value_5990_, lean_object* v_decrTactics_5991_, lean_object* v_argsPacker_5992_, lean_object* v_funNames_5993_, lean_object* v___y_5994_, lean_object* v___y_5995_, lean_object* v___y_5996_, lean_object* v___y_5997_, lean_object* v___y_5998_){
_start:
{
lean_object* v_res_5999_; 
v_res_5999_ = l_Lean_Elab_WF_solveDecreasingGoals___lam__0(v_value_5990_, v_decrTactics_5991_, v_argsPacker_5992_, v_funNames_5993_, v___y_5994_, v___y_5995_, v___y_5996_, v___y_5997_);
lean_dec(v___y_5997_);
lean_dec_ref(v___y_5996_);
lean_dec(v___y_5995_);
lean_dec_ref(v___y_5994_);
lean_dec_ref(v_funNames_5993_);
lean_dec_ref(v_argsPacker_5992_);
return v_res_5999_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(lean_object* v___y_6000_, uint8_t v_isExporting_6001_, lean_object* v___x_6002_, lean_object* v___y_6003_, lean_object* v___x_6004_, lean_object* v_a_x3f_6005_){
_start:
{
lean_object* v___x_6007_; lean_object* v_env_6008_; lean_object* v_nextMacroScope_6009_; lean_object* v_ngen_6010_; lean_object* v_auxDeclNGen_6011_; lean_object* v_traceState_6012_; lean_object* v_messages_6013_; lean_object* v_infoState_6014_; lean_object* v_snapshotTasks_6015_; lean_object* v___x_6017_; uint8_t v_isShared_6018_; uint8_t v_isSharedCheck_6040_; 
v___x_6007_ = lean_st_ref_take(v___y_6000_);
v_env_6008_ = lean_ctor_get(v___x_6007_, 0);
v_nextMacroScope_6009_ = lean_ctor_get(v___x_6007_, 1);
v_ngen_6010_ = lean_ctor_get(v___x_6007_, 2);
v_auxDeclNGen_6011_ = lean_ctor_get(v___x_6007_, 3);
v_traceState_6012_ = lean_ctor_get(v___x_6007_, 4);
v_messages_6013_ = lean_ctor_get(v___x_6007_, 6);
v_infoState_6014_ = lean_ctor_get(v___x_6007_, 7);
v_snapshotTasks_6015_ = lean_ctor_get(v___x_6007_, 8);
v_isSharedCheck_6040_ = !lean_is_exclusive(v___x_6007_);
if (v_isSharedCheck_6040_ == 0)
{
lean_object* v_unused_6041_; 
v_unused_6041_ = lean_ctor_get(v___x_6007_, 5);
lean_dec(v_unused_6041_);
v___x_6017_ = v___x_6007_;
v_isShared_6018_ = v_isSharedCheck_6040_;
goto v_resetjp_6016_;
}
else
{
lean_inc(v_snapshotTasks_6015_);
lean_inc(v_infoState_6014_);
lean_inc(v_messages_6013_);
lean_inc(v_traceState_6012_);
lean_inc(v_auxDeclNGen_6011_);
lean_inc(v_ngen_6010_);
lean_inc(v_nextMacroScope_6009_);
lean_inc(v_env_6008_);
lean_dec(v___x_6007_);
v___x_6017_ = lean_box(0);
v_isShared_6018_ = v_isSharedCheck_6040_;
goto v_resetjp_6016_;
}
v_resetjp_6016_:
{
lean_object* v___x_6019_; lean_object* v___x_6021_; 
v___x_6019_ = l_Lean_Environment_setExporting(v_env_6008_, v_isExporting_6001_);
if (v_isShared_6018_ == 0)
{
lean_ctor_set(v___x_6017_, 5, v___x_6002_);
lean_ctor_set(v___x_6017_, 0, v___x_6019_);
v___x_6021_ = v___x_6017_;
goto v_reusejp_6020_;
}
else
{
lean_object* v_reuseFailAlloc_6039_; 
v_reuseFailAlloc_6039_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6039_, 0, v___x_6019_);
lean_ctor_set(v_reuseFailAlloc_6039_, 1, v_nextMacroScope_6009_);
lean_ctor_set(v_reuseFailAlloc_6039_, 2, v_ngen_6010_);
lean_ctor_set(v_reuseFailAlloc_6039_, 3, v_auxDeclNGen_6011_);
lean_ctor_set(v_reuseFailAlloc_6039_, 4, v_traceState_6012_);
lean_ctor_set(v_reuseFailAlloc_6039_, 5, v___x_6002_);
lean_ctor_set(v_reuseFailAlloc_6039_, 6, v_messages_6013_);
lean_ctor_set(v_reuseFailAlloc_6039_, 7, v_infoState_6014_);
lean_ctor_set(v_reuseFailAlloc_6039_, 8, v_snapshotTasks_6015_);
v___x_6021_ = v_reuseFailAlloc_6039_;
goto v_reusejp_6020_;
}
v_reusejp_6020_:
{
lean_object* v___x_6022_; lean_object* v___x_6023_; lean_object* v_mctx_6024_; lean_object* v_zetaDeltaFVarIds_6025_; lean_object* v_postponed_6026_; lean_object* v_diag_6027_; lean_object* v___x_6029_; uint8_t v_isShared_6030_; uint8_t v_isSharedCheck_6037_; 
v___x_6022_ = lean_st_ref_put(v___y_6000_, v___x_6021_);
v___x_6023_ = lean_st_ref_take(v___y_6003_);
v_mctx_6024_ = lean_ctor_get(v___x_6023_, 0);
v_zetaDeltaFVarIds_6025_ = lean_ctor_get(v___x_6023_, 2);
v_postponed_6026_ = lean_ctor_get(v___x_6023_, 3);
v_diag_6027_ = lean_ctor_get(v___x_6023_, 4);
v_isSharedCheck_6037_ = !lean_is_exclusive(v___x_6023_);
if (v_isSharedCheck_6037_ == 0)
{
lean_object* v_unused_6038_; 
v_unused_6038_ = lean_ctor_get(v___x_6023_, 1);
lean_dec(v_unused_6038_);
v___x_6029_ = v___x_6023_;
v_isShared_6030_ = v_isSharedCheck_6037_;
goto v_resetjp_6028_;
}
else
{
lean_inc(v_diag_6027_);
lean_inc(v_postponed_6026_);
lean_inc(v_zetaDeltaFVarIds_6025_);
lean_inc(v_mctx_6024_);
lean_dec(v___x_6023_);
v___x_6029_ = lean_box(0);
v_isShared_6030_ = v_isSharedCheck_6037_;
goto v_resetjp_6028_;
}
v_resetjp_6028_:
{
lean_object* v___x_6032_; 
if (v_isShared_6030_ == 0)
{
lean_ctor_set(v___x_6029_, 1, v___x_6004_);
v___x_6032_ = v___x_6029_;
goto v_reusejp_6031_;
}
else
{
lean_object* v_reuseFailAlloc_6036_; 
v_reuseFailAlloc_6036_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6036_, 0, v_mctx_6024_);
lean_ctor_set(v_reuseFailAlloc_6036_, 1, v___x_6004_);
lean_ctor_set(v_reuseFailAlloc_6036_, 2, v_zetaDeltaFVarIds_6025_);
lean_ctor_set(v_reuseFailAlloc_6036_, 3, v_postponed_6026_);
lean_ctor_set(v_reuseFailAlloc_6036_, 4, v_diag_6027_);
v___x_6032_ = v_reuseFailAlloc_6036_;
goto v_reusejp_6031_;
}
v_reusejp_6031_:
{
lean_object* v___x_6033_; lean_object* v___x_6034_; lean_object* v___x_6035_; 
v___x_6033_ = lean_st_ref_put(v___y_6003_, v___x_6032_);
v___x_6034_ = lean_box(0);
v___x_6035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6035_, 0, v___x_6034_);
return v___x_6035_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0___boxed(lean_object* v___y_6042_, lean_object* v_isExporting_6043_, lean_object* v___x_6044_, lean_object* v___y_6045_, lean_object* v___x_6046_, lean_object* v_a_x3f_6047_, lean_object* v___y_6048_){
_start:
{
uint8_t v_isExporting_boxed_6049_; lean_object* v_res_6050_; 
v_isExporting_boxed_6049_ = lean_unbox(v_isExporting_6043_);
v_res_6050_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6042_, v_isExporting_boxed_6049_, v___x_6044_, v___y_6045_, v___x_6046_, v_a_x3f_6047_);
lean_dec(v_a_x3f_6047_);
lean_dec(v___y_6045_);
lean_dec(v___y_6042_);
return v_res_6050_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_6051_; 
v___x_6051_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_6051_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_6052_; lean_object* v___x_6053_; 
v___x_6052_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__0);
v___x_6053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6053_, 0, v___x_6052_);
return v___x_6053_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_6054_; lean_object* v___x_6055_; 
v___x_6054_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1);
v___x_6055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6055_, 0, v___x_6054_);
lean_ctor_set(v___x_6055_, 1, v___x_6054_);
return v___x_6055_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_6056_; lean_object* v___x_6057_; 
v___x_6056_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__1);
v___x_6057_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6057_, 0, v___x_6056_);
lean_ctor_set(v___x_6057_, 1, v___x_6056_);
lean_ctor_set(v___x_6057_, 2, v___x_6056_);
lean_ctor_set(v___x_6057_, 3, v___x_6056_);
lean_ctor_set(v___x_6057_, 4, v___x_6056_);
lean_ctor_set(v___x_6057_, 5, v___x_6056_);
return v___x_6057_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(lean_object* v_x_6058_, uint8_t v_isExporting_6059_, lean_object* v___y_6060_, lean_object* v___y_6061_, lean_object* v___y_6062_, lean_object* v___y_6063_){
_start:
{
lean_object* v___x_6065_; lean_object* v_env_6066_; lean_object* v___x_6067_; uint8_t v_isModule_6068_; 
v___x_6065_ = lean_st_ref_get(v___y_6063_);
v_env_6066_ = lean_ctor_get(v___x_6065_, 0);
lean_inc_ref(v_env_6066_);
lean_dec(v___x_6065_);
v___x_6067_ = l_Lean_Environment_header(v_env_6066_);
v_isModule_6068_ = lean_ctor_get_uint8(v___x_6067_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_6067_);
if (v_isModule_6068_ == 0)
{
lean_object* v___x_6069_; 
lean_dec_ref(v_env_6066_);
lean_inc(v___y_6063_);
lean_inc_ref(v___y_6062_);
lean_inc(v___y_6061_);
lean_inc_ref(v___y_6060_);
v___x_6069_ = lean_apply_5(v_x_6058_, v___y_6060_, v___y_6061_, v___y_6062_, v___y_6063_, lean_box(0));
return v___x_6069_;
}
else
{
uint8_t v_isExporting_6070_; 
v_isExporting_6070_ = lean_ctor_get_uint8(v_env_6066_, sizeof(void*)*8);
lean_dec_ref(v_env_6066_);
if (v_isExporting_6059_ == 0)
{
if (v_isExporting_6070_ == 0)
{
lean_object* v___x_6136_; 
lean_inc(v___y_6063_);
lean_inc_ref(v___y_6062_);
lean_inc(v___y_6061_);
lean_inc_ref(v___y_6060_);
v___x_6136_ = lean_apply_5(v_x_6058_, v___y_6060_, v___y_6061_, v___y_6062_, v___y_6063_, lean_box(0));
return v___x_6136_;
}
else
{
goto v___jp_6071_;
}
}
else
{
if (v_isExporting_6070_ == 0)
{
goto v___jp_6071_;
}
else
{
lean_object* v___x_6137_; 
lean_inc(v___y_6063_);
lean_inc_ref(v___y_6062_);
lean_inc(v___y_6061_);
lean_inc_ref(v___y_6060_);
v___x_6137_ = lean_apply_5(v_x_6058_, v___y_6060_, v___y_6061_, v___y_6062_, v___y_6063_, lean_box(0));
return v___x_6137_;
}
}
v___jp_6071_:
{
lean_object* v___x_6072_; lean_object* v_env_6073_; lean_object* v_nextMacroScope_6074_; lean_object* v_ngen_6075_; lean_object* v_auxDeclNGen_6076_; lean_object* v_traceState_6077_; lean_object* v_messages_6078_; lean_object* v_infoState_6079_; lean_object* v_snapshotTasks_6080_; lean_object* v___x_6082_; uint8_t v_isShared_6083_; uint8_t v_isSharedCheck_6134_; 
v___x_6072_ = lean_st_ref_take(v___y_6063_);
v_env_6073_ = lean_ctor_get(v___x_6072_, 0);
v_nextMacroScope_6074_ = lean_ctor_get(v___x_6072_, 1);
v_ngen_6075_ = lean_ctor_get(v___x_6072_, 2);
v_auxDeclNGen_6076_ = lean_ctor_get(v___x_6072_, 3);
v_traceState_6077_ = lean_ctor_get(v___x_6072_, 4);
v_messages_6078_ = lean_ctor_get(v___x_6072_, 6);
v_infoState_6079_ = lean_ctor_get(v___x_6072_, 7);
v_snapshotTasks_6080_ = lean_ctor_get(v___x_6072_, 8);
v_isSharedCheck_6134_ = !lean_is_exclusive(v___x_6072_);
if (v_isSharedCheck_6134_ == 0)
{
lean_object* v_unused_6135_; 
v_unused_6135_ = lean_ctor_get(v___x_6072_, 5);
lean_dec(v_unused_6135_);
v___x_6082_ = v___x_6072_;
v_isShared_6083_ = v_isSharedCheck_6134_;
goto v_resetjp_6081_;
}
else
{
lean_inc(v_snapshotTasks_6080_);
lean_inc(v_infoState_6079_);
lean_inc(v_messages_6078_);
lean_inc(v_traceState_6077_);
lean_inc(v_auxDeclNGen_6076_);
lean_inc(v_ngen_6075_);
lean_inc(v_nextMacroScope_6074_);
lean_inc(v_env_6073_);
lean_dec(v___x_6072_);
v___x_6082_ = lean_box(0);
v_isShared_6083_ = v_isSharedCheck_6134_;
goto v_resetjp_6081_;
}
v_resetjp_6081_:
{
lean_object* v___x_6084_; lean_object* v___x_6085_; lean_object* v___x_6087_; 
v___x_6084_ = l_Lean_Environment_setExporting(v_env_6073_, v_isExporting_6059_);
v___x_6085_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2);
if (v_isShared_6083_ == 0)
{
lean_ctor_set(v___x_6082_, 5, v___x_6085_);
lean_ctor_set(v___x_6082_, 0, v___x_6084_);
v___x_6087_ = v___x_6082_;
goto v_reusejp_6086_;
}
else
{
lean_object* v_reuseFailAlloc_6133_; 
v_reuseFailAlloc_6133_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6133_, 0, v___x_6084_);
lean_ctor_set(v_reuseFailAlloc_6133_, 1, v_nextMacroScope_6074_);
lean_ctor_set(v_reuseFailAlloc_6133_, 2, v_ngen_6075_);
lean_ctor_set(v_reuseFailAlloc_6133_, 3, v_auxDeclNGen_6076_);
lean_ctor_set(v_reuseFailAlloc_6133_, 4, v_traceState_6077_);
lean_ctor_set(v_reuseFailAlloc_6133_, 5, v___x_6085_);
lean_ctor_set(v_reuseFailAlloc_6133_, 6, v_messages_6078_);
lean_ctor_set(v_reuseFailAlloc_6133_, 7, v_infoState_6079_);
lean_ctor_set(v_reuseFailAlloc_6133_, 8, v_snapshotTasks_6080_);
v___x_6087_ = v_reuseFailAlloc_6133_;
goto v_reusejp_6086_;
}
v_reusejp_6086_:
{
lean_object* v___x_6088_; lean_object* v___x_6089_; lean_object* v_mctx_6090_; lean_object* v_zetaDeltaFVarIds_6091_; lean_object* v_postponed_6092_; lean_object* v_diag_6093_; lean_object* v___x_6095_; uint8_t v_isShared_6096_; uint8_t v_isSharedCheck_6131_; 
v___x_6088_ = lean_st_ref_put(v___y_6063_, v___x_6087_);
v___x_6089_ = lean_st_ref_take(v___y_6061_);
v_mctx_6090_ = lean_ctor_get(v___x_6089_, 0);
v_zetaDeltaFVarIds_6091_ = lean_ctor_get(v___x_6089_, 2);
v_postponed_6092_ = lean_ctor_get(v___x_6089_, 3);
v_diag_6093_ = lean_ctor_get(v___x_6089_, 4);
v_isSharedCheck_6131_ = !lean_is_exclusive(v___x_6089_);
if (v_isSharedCheck_6131_ == 0)
{
lean_object* v_unused_6132_; 
v_unused_6132_ = lean_ctor_get(v___x_6089_, 1);
lean_dec(v_unused_6132_);
v___x_6095_ = v___x_6089_;
v_isShared_6096_ = v_isSharedCheck_6131_;
goto v_resetjp_6094_;
}
else
{
lean_inc(v_diag_6093_);
lean_inc(v_postponed_6092_);
lean_inc(v_zetaDeltaFVarIds_6091_);
lean_inc(v_mctx_6090_);
lean_dec(v___x_6089_);
v___x_6095_ = lean_box(0);
v_isShared_6096_ = v_isSharedCheck_6131_;
goto v_resetjp_6094_;
}
v_resetjp_6094_:
{
lean_object* v___x_6097_; lean_object* v___x_6099_; 
v___x_6097_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3);
if (v_isShared_6096_ == 0)
{
lean_ctor_set(v___x_6095_, 1, v___x_6097_);
v___x_6099_ = v___x_6095_;
goto v_reusejp_6098_;
}
else
{
lean_object* v_reuseFailAlloc_6130_; 
v_reuseFailAlloc_6130_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6130_, 0, v_mctx_6090_);
lean_ctor_set(v_reuseFailAlloc_6130_, 1, v___x_6097_);
lean_ctor_set(v_reuseFailAlloc_6130_, 2, v_zetaDeltaFVarIds_6091_);
lean_ctor_set(v_reuseFailAlloc_6130_, 3, v_postponed_6092_);
lean_ctor_set(v_reuseFailAlloc_6130_, 4, v_diag_6093_);
v___x_6099_ = v_reuseFailAlloc_6130_;
goto v_reusejp_6098_;
}
v_reusejp_6098_:
{
lean_object* v___x_6100_; lean_object* v_r_6101_; 
v___x_6100_ = lean_st_ref_put(v___y_6061_, v___x_6099_);
lean_inc(v___y_6063_);
lean_inc_ref(v___y_6062_);
lean_inc(v___y_6061_);
lean_inc_ref(v___y_6060_);
v_r_6101_ = lean_apply_5(v_x_6058_, v___y_6060_, v___y_6061_, v___y_6062_, v___y_6063_, lean_box(0));
if (lean_obj_tag(v_r_6101_) == 0)
{
lean_object* v_a_6102_; lean_object* v___x_6104_; uint8_t v_isShared_6105_; uint8_t v_isSharedCheck_6118_; 
v_a_6102_ = lean_ctor_get(v_r_6101_, 0);
v_isSharedCheck_6118_ = !lean_is_exclusive(v_r_6101_);
if (v_isSharedCheck_6118_ == 0)
{
v___x_6104_ = v_r_6101_;
v_isShared_6105_ = v_isSharedCheck_6118_;
goto v_resetjp_6103_;
}
else
{
lean_inc(v_a_6102_);
lean_dec(v_r_6101_);
v___x_6104_ = lean_box(0);
v_isShared_6105_ = v_isSharedCheck_6118_;
goto v_resetjp_6103_;
}
v_resetjp_6103_:
{
lean_object* v___x_6107_; 
lean_inc(v_a_6102_);
if (v_isShared_6105_ == 0)
{
lean_ctor_set_tag(v___x_6104_, 1);
v___x_6107_ = v___x_6104_;
goto v_reusejp_6106_;
}
else
{
lean_object* v_reuseFailAlloc_6117_; 
v_reuseFailAlloc_6117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6117_, 0, v_a_6102_);
v___x_6107_ = v_reuseFailAlloc_6117_;
goto v_reusejp_6106_;
}
v_reusejp_6106_:
{
lean_object* v___x_6108_; lean_object* v___x_6110_; uint8_t v_isShared_6111_; uint8_t v_isSharedCheck_6115_; 
v___x_6108_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6063_, v_isExporting_6070_, v___x_6085_, v___y_6061_, v___x_6097_, v___x_6107_);
lean_dec_ref(v___x_6107_);
v_isSharedCheck_6115_ = !lean_is_exclusive(v___x_6108_);
if (v_isSharedCheck_6115_ == 0)
{
lean_object* v_unused_6116_; 
v_unused_6116_ = lean_ctor_get(v___x_6108_, 0);
lean_dec(v_unused_6116_);
v___x_6110_ = v___x_6108_;
v_isShared_6111_ = v_isSharedCheck_6115_;
goto v_resetjp_6109_;
}
else
{
lean_dec(v___x_6108_);
v___x_6110_ = lean_box(0);
v_isShared_6111_ = v_isSharedCheck_6115_;
goto v_resetjp_6109_;
}
v_resetjp_6109_:
{
lean_object* v___x_6113_; 
if (v_isShared_6111_ == 0)
{
lean_ctor_set(v___x_6110_, 0, v_a_6102_);
v___x_6113_ = v___x_6110_;
goto v_reusejp_6112_;
}
else
{
lean_object* v_reuseFailAlloc_6114_; 
v_reuseFailAlloc_6114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6114_, 0, v_a_6102_);
v___x_6113_ = v_reuseFailAlloc_6114_;
goto v_reusejp_6112_;
}
v_reusejp_6112_:
{
return v___x_6113_;
}
}
}
}
}
else
{
lean_object* v_a_6119_; lean_object* v___x_6120_; lean_object* v___x_6121_; lean_object* v___x_6123_; uint8_t v_isShared_6124_; uint8_t v_isSharedCheck_6128_; 
v_a_6119_ = lean_ctor_get(v_r_6101_, 0);
lean_inc(v_a_6119_);
lean_dec_ref_known(v_r_6101_, 1);
v___x_6120_ = lean_box(0);
v___x_6121_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6063_, v_isExporting_6070_, v___x_6085_, v___y_6061_, v___x_6097_, v___x_6120_);
v_isSharedCheck_6128_ = !lean_is_exclusive(v___x_6121_);
if (v_isSharedCheck_6128_ == 0)
{
lean_object* v_unused_6129_; 
v_unused_6129_ = lean_ctor_get(v___x_6121_, 0);
lean_dec(v_unused_6129_);
v___x_6123_ = v___x_6121_;
v_isShared_6124_ = v_isSharedCheck_6128_;
goto v_resetjp_6122_;
}
else
{
lean_dec(v___x_6121_);
v___x_6123_ = lean_box(0);
v_isShared_6124_ = v_isSharedCheck_6128_;
goto v_resetjp_6122_;
}
v_resetjp_6122_:
{
lean_object* v___x_6126_; 
if (v_isShared_6124_ == 0)
{
lean_ctor_set_tag(v___x_6123_, 1);
lean_ctor_set(v___x_6123_, 0, v_a_6119_);
v___x_6126_ = v___x_6123_;
goto v_reusejp_6125_;
}
else
{
lean_object* v_reuseFailAlloc_6127_; 
v_reuseFailAlloc_6127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6127_, 0, v_a_6119_);
v___x_6126_ = v_reuseFailAlloc_6127_;
goto v_reusejp_6125_;
}
v_reusejp_6125_:
{
return v___x_6126_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___boxed(lean_object* v_x_6138_, lean_object* v_isExporting_6139_, lean_object* v___y_6140_, lean_object* v___y_6141_, lean_object* v___y_6142_, lean_object* v___y_6143_, lean_object* v___y_6144_){
_start:
{
uint8_t v_isExporting_boxed_6145_; lean_object* v_res_6146_; 
v_isExporting_boxed_6145_ = lean_unbox(v_isExporting_6139_);
v_res_6146_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6138_, v_isExporting_boxed_6145_, v___y_6140_, v___y_6141_, v___y_6142_, v___y_6143_);
lean_dec(v___y_6143_);
lean_dec_ref(v___y_6142_);
lean_dec(v___y_6141_);
lean_dec_ref(v___y_6140_);
return v_res_6146_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(lean_object* v_x_6147_, uint8_t v_when_6148_, lean_object* v___y_6149_, lean_object* v___y_6150_, lean_object* v___y_6151_, lean_object* v___y_6152_){
_start:
{
if (v_when_6148_ == 0)
{
lean_object* v___x_6154_; 
lean_inc(v___y_6152_);
lean_inc_ref(v___y_6151_);
lean_inc(v___y_6150_);
lean_inc_ref(v___y_6149_);
v___x_6154_ = lean_apply_5(v_x_6147_, v___y_6149_, v___y_6150_, v___y_6151_, v___y_6152_, lean_box(0));
return v___x_6154_;
}
else
{
uint8_t v___x_6155_; lean_object* v___x_6156_; 
v___x_6155_ = 0;
v___x_6156_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6147_, v___x_6155_, v___y_6149_, v___y_6150_, v___y_6151_, v___y_6152_);
return v___x_6156_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg___boxed(lean_object* v_x_6157_, lean_object* v_when_6158_, lean_object* v___y_6159_, lean_object* v___y_6160_, lean_object* v___y_6161_, lean_object* v___y_6162_, lean_object* v___y_6163_){
_start:
{
uint8_t v_when_boxed_6164_; lean_object* v_res_6165_; 
v_when_boxed_6164_ = lean_unbox(v_when_6158_);
v_res_6165_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v_x_6157_, v_when_boxed_6164_, v___y_6159_, v___y_6160_, v___y_6161_, v___y_6162_);
lean_dec(v___y_6162_);
lean_dec_ref(v___y_6161_);
lean_dec(v___y_6160_);
lean_dec_ref(v___y_6159_);
return v_res_6165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals(lean_object* v_funNames_6166_, lean_object* v_argsPacker_6167_, lean_object* v_decrTactics_6168_, lean_object* v_value_6169_, lean_object* v_a_6170_, lean_object* v_a_6171_, lean_object* v_a_6172_, lean_object* v_a_6173_){
_start:
{
lean_object* v___f_6175_; uint8_t v___x_6176_; lean_object* v___x_6177_; 
v___f_6175_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_solveDecreasingGoals___lam__0___boxed), 9, 4);
lean_closure_set(v___f_6175_, 0, v_value_6169_);
lean_closure_set(v___f_6175_, 1, v_decrTactics_6168_);
lean_closure_set(v___f_6175_, 2, v_argsPacker_6167_);
lean_closure_set(v___f_6175_, 3, v_funNames_6166_);
v___x_6176_ = 1;
v___x_6177_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v___f_6175_, v___x_6176_, v_a_6170_, v_a_6171_, v_a_6172_, v_a_6173_);
return v___x_6177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_solveDecreasingGoals___boxed(lean_object* v_funNames_6178_, lean_object* v_argsPacker_6179_, lean_object* v_decrTactics_6180_, lean_object* v_value_6181_, lean_object* v_a_6182_, lean_object* v_a_6183_, lean_object* v_a_6184_, lean_object* v_a_6185_, lean_object* v_a_6186_){
_start:
{
lean_object* v_res_6187_; 
v_res_6187_ = l_Lean_Elab_WF_solveDecreasingGoals(v_funNames_6178_, v_argsPacker_6179_, v_decrTactics_6180_, v_value_6181_, v_a_6182_, v_a_6183_, v_a_6184_, v_a_6185_);
lean_dec(v_a_6185_);
lean_dec_ref(v_a_6184_);
lean_dec(v_a_6183_);
lean_dec_ref(v_a_6182_);
return v_res_6187_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1(lean_object* v_00_u03b1_6188_, lean_object* v_msg_6189_, lean_object* v___y_6190_, lean_object* v___y_6191_, lean_object* v___y_6192_, lean_object* v___y_6193_, lean_object* v___y_6194_, lean_object* v___y_6195_){
_start:
{
lean_object* v___x_6197_; 
v___x_6197_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v_msg_6189_, v___y_6190_, v___y_6191_, v___y_6192_, v___y_6193_, v___y_6194_, v___y_6195_);
return v___x_6197_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___boxed(lean_object* v_00_u03b1_6198_, lean_object* v_msg_6199_, lean_object* v___y_6200_, lean_object* v___y_6201_, lean_object* v___y_6202_, lean_object* v___y_6203_, lean_object* v___y_6204_, lean_object* v___y_6205_, lean_object* v___y_6206_){
_start:
{
lean_object* v_res_6207_; 
v_res_6207_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1(v_00_u03b1_6198_, v_msg_6199_, v___y_6200_, v___y_6201_, v___y_6202_, v___y_6203_, v___y_6204_, v___y_6205_);
lean_dec(v___y_6205_);
lean_dec_ref(v___y_6204_);
lean_dec(v___y_6203_);
lean_dec_ref(v___y_6202_);
lean_dec(v___y_6201_);
lean_dec_ref(v___y_6200_);
return v_res_6207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4(lean_object* v___y_6208_, lean_object* v___y_6209_, lean_object* v___y_6210_, lean_object* v___y_6211_, lean_object* v___y_6212_, lean_object* v___y_6213_, lean_object* v___y_6214_, lean_object* v___y_6215_){
_start:
{
lean_object* v___x_6217_; 
v___x_6217_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_6215_);
return v___x_6217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___boxed(lean_object* v___y_6218_, lean_object* v___y_6219_, lean_object* v___y_6220_, lean_object* v___y_6221_, lean_object* v___y_6222_, lean_object* v___y_6223_, lean_object* v___y_6224_, lean_object* v___y_6225_, lean_object* v___y_6226_){
_start:
{
lean_object* v_res_6227_; 
v_res_6227_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4(v___y_6218_, v___y_6219_, v___y_6220_, v___y_6221_, v___y_6222_, v___y_6223_, v___y_6224_, v___y_6225_);
lean_dec(v___y_6225_);
lean_dec_ref(v___y_6224_);
lean_dec(v___y_6223_);
lean_dec_ref(v___y_6222_);
lean_dec(v___y_6221_);
lean_dec_ref(v___y_6220_);
lean_dec(v___y_6219_);
lean_dec_ref(v___y_6218_);
return v_res_6227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3(lean_object* v_00_u03b1_6228_, lean_object* v_x_6229_, lean_object* v_mkInfoTree_6230_, lean_object* v___y_6231_, lean_object* v___y_6232_, lean_object* v___y_6233_, lean_object* v___y_6234_, lean_object* v___y_6235_, lean_object* v___y_6236_, lean_object* v___y_6237_, lean_object* v___y_6238_){
_start:
{
lean_object* v___x_6240_; 
v___x_6240_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v_x_6229_, v_mkInfoTree_6230_, v___y_6231_, v___y_6232_, v___y_6233_, v___y_6234_, v___y_6235_, v___y_6236_, v___y_6237_, v___y_6238_);
return v___x_6240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___boxed(lean_object* v_00_u03b1_6241_, lean_object* v_x_6242_, lean_object* v_mkInfoTree_6243_, lean_object* v___y_6244_, lean_object* v___y_6245_, lean_object* v___y_6246_, lean_object* v___y_6247_, lean_object* v___y_6248_, lean_object* v___y_6249_, lean_object* v___y_6250_, lean_object* v___y_6251_, lean_object* v___y_6252_){
_start:
{
lean_object* v_res_6253_; 
v_res_6253_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3(v_00_u03b1_6241_, v_x_6242_, v_mkInfoTree_6243_, v___y_6244_, v___y_6245_, v___y_6246_, v___y_6247_, v___y_6248_, v___y_6249_, v___y_6250_, v___y_6251_);
lean_dec(v___y_6251_);
lean_dec_ref(v___y_6250_);
lean_dec(v___y_6249_);
lean_dec_ref(v___y_6248_);
lean_dec(v___y_6247_);
lean_dec_ref(v___y_6246_);
lean_dec(v___y_6245_);
lean_dec_ref(v___y_6244_);
return v_res_6253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5(lean_object* v_as_6254_, size_t v_i_6255_, size_t v_stop_6256_, lean_object* v_b_6257_, lean_object* v___y_6258_, lean_object* v___y_6259_, lean_object* v___y_6260_, lean_object* v___y_6261_, lean_object* v___y_6262_, lean_object* v___y_6263_){
_start:
{
lean_object* v___x_6265_; 
v___x_6265_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v_as_6254_, v_i_6255_, v_stop_6256_, v_b_6257_, v___y_6260_, v___y_6261_, v___y_6262_, v___y_6263_);
return v___x_6265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___boxed(lean_object* v_as_6266_, lean_object* v_i_6267_, lean_object* v_stop_6268_, lean_object* v_b_6269_, lean_object* v___y_6270_, lean_object* v___y_6271_, lean_object* v___y_6272_, lean_object* v___y_6273_, lean_object* v___y_6274_, lean_object* v___y_6275_, lean_object* v___y_6276_){
_start:
{
size_t v_i_boxed_6277_; size_t v_stop_boxed_6278_; lean_object* v_res_6279_; 
v_i_boxed_6277_ = lean_unbox_usize(v_i_6267_);
lean_dec(v_i_6267_);
v_stop_boxed_6278_ = lean_unbox_usize(v_stop_6268_);
lean_dec(v_stop_6268_);
v_res_6279_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5(v_as_6266_, v_i_boxed_6277_, v_stop_boxed_6278_, v_b_6269_, v___y_6270_, v___y_6271_, v___y_6272_, v___y_6273_, v___y_6274_, v___y_6275_);
lean_dec(v___y_6275_);
lean_dec_ref(v___y_6274_);
lean_dec(v___y_6273_);
lean_dec_ref(v___y_6272_);
lean_dec(v___y_6271_);
lean_dec_ref(v___y_6270_);
lean_dec_ref(v_as_6266_);
return v_res_6279_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10(lean_object* v_00_u03b1_6280_, lean_object* v_x_6281_, uint8_t v_isExporting_6282_, lean_object* v___y_6283_, lean_object* v___y_6284_, lean_object* v___y_6285_, lean_object* v___y_6286_){
_start:
{
lean_object* v___x_6288_; 
v___x_6288_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg(v_x_6281_, v_isExporting_6282_, v___y_6283_, v___y_6284_, v___y_6285_, v___y_6286_);
return v___x_6288_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___boxed(lean_object* v_00_u03b1_6289_, lean_object* v_x_6290_, lean_object* v_isExporting_6291_, lean_object* v___y_6292_, lean_object* v___y_6293_, lean_object* v___y_6294_, lean_object* v___y_6295_, lean_object* v___y_6296_){
_start:
{
uint8_t v_isExporting_boxed_6297_; lean_object* v_res_6298_; 
v_isExporting_boxed_6297_ = lean_unbox(v_isExporting_6291_);
v_res_6298_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10(v_00_u03b1_6289_, v_x_6290_, v_isExporting_boxed_6297_, v___y_6292_, v___y_6293_, v___y_6294_, v___y_6295_);
lean_dec(v___y_6295_);
lean_dec_ref(v___y_6294_);
lean_dec(v___y_6293_);
lean_dec_ref(v___y_6292_);
return v_res_6298_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8(lean_object* v_00_u03b1_6299_, lean_object* v_x_6300_, uint8_t v_when_6301_, lean_object* v___y_6302_, lean_object* v___y_6303_, lean_object* v___y_6304_, lean_object* v___y_6305_){
_start:
{
lean_object* v___x_6307_; 
v___x_6307_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___redArg(v_x_6300_, v_when_6301_, v___y_6302_, v___y_6303_, v___y_6304_, v___y_6305_);
return v___x_6307_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8___boxed(lean_object* v_00_u03b1_6308_, lean_object* v_x_6309_, lean_object* v_when_6310_, lean_object* v___y_6311_, lean_object* v___y_6312_, lean_object* v___y_6313_, lean_object* v___y_6314_, lean_object* v___y_6315_){
_start:
{
uint8_t v_when_boxed_6316_; lean_object* v_res_6317_; 
v_when_boxed_6316_ = lean_unbox(v_when_6310_);
v_res_6317_ = l_Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8(v_00_u03b1_6308_, v_x_6309_, v_when_boxed_6316_, v___y_6311_, v___y_6312_, v___y_6313_, v___y_6314_);
lean_dec(v___y_6314_);
lean_dec_ref(v___y_6313_);
lean_dec(v___y_6312_);
lean_dec_ref(v___y_6311_);
return v_res_6317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1(lean_object* v_msgData_6318_, lean_object* v_macroStack_6319_, lean_object* v___y_6320_, lean_object* v___y_6321_, lean_object* v___y_6322_, lean_object* v___y_6323_, lean_object* v___y_6324_, lean_object* v___y_6325_){
_start:
{
lean_object* v___x_6327_; 
v___x_6327_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_msgData_6318_, v_macroStack_6319_, v___y_6324_);
return v___x_6327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___boxed(lean_object* v_msgData_6328_, lean_object* v_macroStack_6329_, lean_object* v___y_6330_, lean_object* v___y_6331_, lean_object* v___y_6332_, lean_object* v___y_6333_, lean_object* v___y_6334_, lean_object* v___y_6335_, lean_object* v___y_6336_){
_start:
{
lean_object* v_res_6337_; 
v_res_6337_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1(v_msgData_6328_, v_macroStack_6329_, v___y_6330_, v___y_6331_, v___y_6332_, v___y_6333_, v___y_6334_, v___y_6335_);
lean_dec(v___y_6335_);
lean_dec_ref(v___y_6334_);
lean_dec(v___y_6333_);
lean_dec_ref(v___y_6332_);
lean_dec(v___y_6331_);
lean_dec_ref(v___y_6330_);
return v_res_6337_;
}
}
static lean_object* _init_l_Lean_Elab_WF_isNatLtWF___closed__4(void){
_start:
{
lean_object* v___x_6344_; lean_object* v___x_6345_; lean_object* v___x_6346_; 
v___x_6344_ = lean_box(0);
v___x_6345_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__3));
v___x_6346_ = l_Lean_mkConst(v___x_6345_, v___x_6344_);
return v___x_6346_;
}
}
static lean_object* _init_l_Lean_Elab_WF_isNatLtWF___closed__7(void){
_start:
{
lean_object* v___x_6351_; lean_object* v___x_6352_; lean_object* v___x_6353_; 
v___x_6351_ = lean_box(0);
v___x_6352_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__6));
v___x_6353_ = l_Lean_mkConst(v___x_6352_, v___x_6351_);
return v___x_6353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isNatLtWF(lean_object* v_wfRel_6354_, lean_object* v_a_6355_, lean_object* v_a_6356_, lean_object* v_a_6357_, lean_object* v_a_6358_){
_start:
{
lean_object* v___x_6360_; 
v___x_6360_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_wfRel_6354_, v_a_6356_);
if (lean_obj_tag(v___x_6360_) == 0)
{
lean_object* v_a_6361_; lean_object* v___x_6363_; uint8_t v_isShared_6364_; uint8_t v_isSharedCheck_6428_; 
v_a_6361_ = lean_ctor_get(v___x_6360_, 0);
v_isSharedCheck_6428_ = !lean_is_exclusive(v___x_6360_);
if (v_isSharedCheck_6428_ == 0)
{
v___x_6363_ = v___x_6360_;
v_isShared_6364_ = v_isSharedCheck_6428_;
goto v_resetjp_6362_;
}
else
{
lean_inc(v_a_6361_);
lean_dec(v___x_6360_);
v___x_6363_ = lean_box(0);
v_isShared_6364_ = v_isSharedCheck_6428_;
goto v_resetjp_6362_;
}
v_resetjp_6362_:
{
lean_object* v___x_6370_; uint8_t v___x_6371_; 
v___x_6370_ = l_Lean_Expr_cleanupAnnotations(v_a_6361_);
v___x_6371_ = l_Lean_Expr_isApp(v___x_6370_);
if (v___x_6371_ == 0)
{
lean_dec_ref(v___x_6370_);
goto v___jp_6365_;
}
else
{
lean_object* v_arg_6372_; lean_object* v___x_6373_; uint8_t v___x_6374_; 
v_arg_6372_ = lean_ctor_get(v___x_6370_, 1);
lean_inc_ref(v_arg_6372_);
v___x_6373_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6370_);
v___x_6374_ = l_Lean_Expr_isApp(v___x_6373_);
if (v___x_6374_ == 0)
{
lean_dec_ref(v___x_6373_);
lean_dec_ref(v_arg_6372_);
goto v___jp_6365_;
}
else
{
lean_object* v_arg_6375_; lean_object* v___x_6376_; uint8_t v___x_6377_; 
v_arg_6375_ = lean_ctor_get(v___x_6373_, 1);
lean_inc_ref(v_arg_6375_);
v___x_6376_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6373_);
v___x_6377_ = l_Lean_Expr_isApp(v___x_6376_);
if (v___x_6377_ == 0)
{
lean_dec_ref(v___x_6376_);
lean_dec_ref(v_arg_6375_);
lean_dec_ref(v_arg_6372_);
goto v___jp_6365_;
}
else
{
lean_object* v_arg_6378_; lean_object* v___x_6379_; uint8_t v___x_6380_; 
v_arg_6378_ = lean_ctor_get(v___x_6376_, 1);
lean_inc_ref(v_arg_6378_);
v___x_6379_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6376_);
v___x_6380_ = l_Lean_Expr_isApp(v___x_6379_);
if (v___x_6380_ == 0)
{
lean_dec_ref(v___x_6379_);
lean_dec_ref(v_arg_6378_);
lean_dec_ref(v_arg_6375_);
lean_dec_ref(v_arg_6372_);
goto v___jp_6365_;
}
else
{
lean_object* v___x_6381_; lean_object* v___x_6382_; uint8_t v___x_6383_; 
v___x_6381_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6379_);
v___x_6382_ = ((lean_object*)(l_Lean_Elab_WF_isNatLtWF___closed__1));
v___x_6383_ = l_Lean_Expr_isConstOf(v___x_6381_, v___x_6382_);
lean_dec_ref(v___x_6381_);
if (v___x_6383_ == 0)
{
lean_dec_ref(v_arg_6378_);
lean_dec_ref(v_arg_6375_);
lean_dec_ref(v_arg_6372_);
goto v___jp_6365_;
}
else
{
lean_object* v___x_6384_; lean_object* v___x_6385_; 
lean_del_object(v___x_6363_);
v___x_6384_ = lean_obj_once(&l_Lean_Elab_WF_isNatLtWF___closed__4, &l_Lean_Elab_WF_isNatLtWF___closed__4_once, _init_l_Lean_Elab_WF_isNatLtWF___closed__4);
v___x_6385_ = l_Lean_Meta_isExprDefEq(v_arg_6378_, v___x_6384_, v_a_6355_, v_a_6356_, v_a_6357_, v_a_6358_);
if (lean_obj_tag(v___x_6385_) == 0)
{
lean_object* v_a_6386_; lean_object* v___x_6388_; uint8_t v_isShared_6389_; uint8_t v_isSharedCheck_6419_; 
v_a_6386_ = lean_ctor_get(v___x_6385_, 0);
v_isSharedCheck_6419_ = !lean_is_exclusive(v___x_6385_);
if (v_isSharedCheck_6419_ == 0)
{
v___x_6388_ = v___x_6385_;
v_isShared_6389_ = v_isSharedCheck_6419_;
goto v_resetjp_6387_;
}
else
{
lean_inc(v_a_6386_);
lean_dec(v___x_6385_);
v___x_6388_ = lean_box(0);
v_isShared_6389_ = v_isSharedCheck_6419_;
goto v_resetjp_6387_;
}
v_resetjp_6387_:
{
uint8_t v___x_6390_; 
v___x_6390_ = lean_unbox(v_a_6386_);
lean_dec(v_a_6386_);
if (v___x_6390_ == 0)
{
lean_object* v___x_6391_; lean_object* v___x_6393_; 
lean_dec_ref(v_arg_6375_);
lean_dec_ref(v_arg_6372_);
v___x_6391_ = lean_box(0);
if (v_isShared_6389_ == 0)
{
lean_ctor_set(v___x_6388_, 0, v___x_6391_);
v___x_6393_ = v___x_6388_;
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
else
{
lean_object* v___x_6395_; lean_object* v___x_6396_; 
lean_del_object(v___x_6388_);
v___x_6395_ = lean_obj_once(&l_Lean_Elab_WF_isNatLtWF___closed__7, &l_Lean_Elab_WF_isNatLtWF___closed__7_once, _init_l_Lean_Elab_WF_isNatLtWF___closed__7);
v___x_6396_ = l_Lean_Meta_isExprDefEq(v_arg_6372_, v___x_6395_, v_a_6355_, v_a_6356_, v_a_6357_, v_a_6358_);
if (lean_obj_tag(v___x_6396_) == 0)
{
lean_object* v_a_6397_; lean_object* v___x_6399_; uint8_t v_isShared_6400_; uint8_t v_isSharedCheck_6410_; 
v_a_6397_ = lean_ctor_get(v___x_6396_, 0);
v_isSharedCheck_6410_ = !lean_is_exclusive(v___x_6396_);
if (v_isSharedCheck_6410_ == 0)
{
v___x_6399_ = v___x_6396_;
v_isShared_6400_ = v_isSharedCheck_6410_;
goto v_resetjp_6398_;
}
else
{
lean_inc(v_a_6397_);
lean_dec(v___x_6396_);
v___x_6399_ = lean_box(0);
v_isShared_6400_ = v_isSharedCheck_6410_;
goto v_resetjp_6398_;
}
v_resetjp_6398_:
{
uint8_t v___x_6401_; 
v___x_6401_ = lean_unbox(v_a_6397_);
lean_dec(v_a_6397_);
if (v___x_6401_ == 0)
{
lean_object* v___x_6402_; lean_object* v___x_6404_; 
lean_dec_ref(v_arg_6375_);
v___x_6402_ = lean_box(0);
if (v_isShared_6400_ == 0)
{
lean_ctor_set(v___x_6399_, 0, v___x_6402_);
v___x_6404_ = v___x_6399_;
goto v_reusejp_6403_;
}
else
{
lean_object* v_reuseFailAlloc_6405_; 
v_reuseFailAlloc_6405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6405_, 0, v___x_6402_);
v___x_6404_ = v_reuseFailAlloc_6405_;
goto v_reusejp_6403_;
}
v_reusejp_6403_:
{
return v___x_6404_;
}
}
else
{
lean_object* v___x_6406_; lean_object* v___x_6408_; 
v___x_6406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6406_, 0, v_arg_6375_);
if (v_isShared_6400_ == 0)
{
lean_ctor_set(v___x_6399_, 0, v___x_6406_);
v___x_6408_ = v___x_6399_;
goto v_reusejp_6407_;
}
else
{
lean_object* v_reuseFailAlloc_6409_; 
v_reuseFailAlloc_6409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6409_, 0, v___x_6406_);
v___x_6408_ = v_reuseFailAlloc_6409_;
goto v_reusejp_6407_;
}
v_reusejp_6407_:
{
return v___x_6408_;
}
}
}
}
else
{
lean_object* v_a_6411_; lean_object* v___x_6413_; uint8_t v_isShared_6414_; uint8_t v_isSharedCheck_6418_; 
lean_dec_ref(v_arg_6375_);
v_a_6411_ = lean_ctor_get(v___x_6396_, 0);
v_isSharedCheck_6418_ = !lean_is_exclusive(v___x_6396_);
if (v_isSharedCheck_6418_ == 0)
{
v___x_6413_ = v___x_6396_;
v_isShared_6414_ = v_isSharedCheck_6418_;
goto v_resetjp_6412_;
}
else
{
lean_inc(v_a_6411_);
lean_dec(v___x_6396_);
v___x_6413_ = lean_box(0);
v_isShared_6414_ = v_isSharedCheck_6418_;
goto v_resetjp_6412_;
}
v_resetjp_6412_:
{
lean_object* v___x_6416_; 
if (v_isShared_6414_ == 0)
{
v___x_6416_ = v___x_6413_;
goto v_reusejp_6415_;
}
else
{
lean_object* v_reuseFailAlloc_6417_; 
v_reuseFailAlloc_6417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6417_, 0, v_a_6411_);
v___x_6416_ = v_reuseFailAlloc_6417_;
goto v_reusejp_6415_;
}
v_reusejp_6415_:
{
return v___x_6416_;
}
}
}
}
}
}
else
{
lean_object* v_a_6420_; lean_object* v___x_6422_; uint8_t v_isShared_6423_; uint8_t v_isSharedCheck_6427_; 
lean_dec_ref(v_arg_6375_);
lean_dec_ref(v_arg_6372_);
v_a_6420_ = lean_ctor_get(v___x_6385_, 0);
v_isSharedCheck_6427_ = !lean_is_exclusive(v___x_6385_);
if (v_isSharedCheck_6427_ == 0)
{
v___x_6422_ = v___x_6385_;
v_isShared_6423_ = v_isSharedCheck_6427_;
goto v_resetjp_6421_;
}
else
{
lean_inc(v_a_6420_);
lean_dec(v___x_6385_);
v___x_6422_ = lean_box(0);
v_isShared_6423_ = v_isSharedCheck_6427_;
goto v_resetjp_6421_;
}
v_resetjp_6421_:
{
lean_object* v___x_6425_; 
if (v_isShared_6423_ == 0)
{
v___x_6425_ = v___x_6422_;
goto v_reusejp_6424_;
}
else
{
lean_object* v_reuseFailAlloc_6426_; 
v_reuseFailAlloc_6426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6426_, 0, v_a_6420_);
v___x_6425_ = v_reuseFailAlloc_6426_;
goto v_reusejp_6424_;
}
v_reusejp_6424_:
{
return v___x_6425_;
}
}
}
}
}
}
}
}
v___jp_6365_:
{
lean_object* v___x_6366_; lean_object* v___x_6368_; 
v___x_6366_ = lean_box(0);
if (v_isShared_6364_ == 0)
{
lean_ctor_set(v___x_6363_, 0, v___x_6366_);
v___x_6368_ = v___x_6363_;
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
lean_object* v_a_6429_; lean_object* v___x_6431_; uint8_t v_isShared_6432_; uint8_t v_isSharedCheck_6436_; 
v_a_6429_ = lean_ctor_get(v___x_6360_, 0);
v_isSharedCheck_6436_ = !lean_is_exclusive(v___x_6360_);
if (v_isSharedCheck_6436_ == 0)
{
v___x_6431_ = v___x_6360_;
v_isShared_6432_ = v_isSharedCheck_6436_;
goto v_resetjp_6430_;
}
else
{
lean_inc(v_a_6429_);
lean_dec(v___x_6360_);
v___x_6431_ = lean_box(0);
v_isShared_6432_ = v_isSharedCheck_6436_;
goto v_resetjp_6430_;
}
v_resetjp_6430_:
{
lean_object* v___x_6434_; 
if (v_isShared_6432_ == 0)
{
v___x_6434_ = v___x_6431_;
goto v_reusejp_6433_;
}
else
{
lean_object* v_reuseFailAlloc_6435_; 
v_reuseFailAlloc_6435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6435_, 0, v_a_6429_);
v___x_6434_ = v_reuseFailAlloc_6435_;
goto v_reusejp_6433_;
}
v_reusejp_6433_:
{
return v___x_6434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isNatLtWF___boxed(lean_object* v_wfRel_6437_, lean_object* v_a_6438_, lean_object* v_a_6439_, lean_object* v_a_6440_, lean_object* v_a_6441_, lean_object* v_a_6442_){
_start:
{
lean_object* v_res_6443_; 
v_res_6443_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_6437_, v_a_6438_, v_a_6439_, v_a_6440_, v_a_6441_);
lean_dec(v_a_6441_);
lean_dec_ref(v_a_6440_);
lean_dec(v_a_6439_);
lean_dec_ref(v_a_6438_);
return v_res_6443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(lean_object* v_type_6444_, lean_object* v_maxFVars_x3f_6445_, lean_object* v_k_6446_, uint8_t v_cleanupAnnotations_6447_, uint8_t v_whnfType_6448_, lean_object* v___y_6449_, lean_object* v___y_6450_, lean_object* v___y_6451_, lean_object* v___y_6452_, lean_object* v___y_6453_, lean_object* v___y_6454_){
_start:
{
lean_object* v___f_6456_; lean_object* v___x_6457_; 
lean_inc(v___y_6450_);
lean_inc_ref(v___y_6449_);
v___f_6456_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_6456_, 0, v_k_6446_);
lean_closure_set(v___f_6456_, 1, v___y_6449_);
lean_closure_set(v___f_6456_, 2, v___y_6450_);
v___x_6457_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_6444_, v_maxFVars_x3f_6445_, v___f_6456_, v_cleanupAnnotations_6447_, v_whnfType_6448_, v___y_6451_, v___y_6452_, v___y_6453_, v___y_6454_);
if (lean_obj_tag(v___x_6457_) == 0)
{
return v___x_6457_;
}
else
{
lean_object* v_a_6458_; lean_object* v___x_6460_; uint8_t v_isShared_6461_; uint8_t v_isSharedCheck_6465_; 
v_a_6458_ = lean_ctor_get(v___x_6457_, 0);
v_isSharedCheck_6465_ = !lean_is_exclusive(v___x_6457_);
if (v_isSharedCheck_6465_ == 0)
{
v___x_6460_ = v___x_6457_;
v_isShared_6461_ = v_isSharedCheck_6465_;
goto v_resetjp_6459_;
}
else
{
lean_inc(v_a_6458_);
lean_dec(v___x_6457_);
v___x_6460_ = lean_box(0);
v_isShared_6461_ = v_isSharedCheck_6465_;
goto v_resetjp_6459_;
}
v_resetjp_6459_:
{
lean_object* v___x_6463_; 
if (v_isShared_6461_ == 0)
{
v___x_6463_ = v___x_6460_;
goto v_reusejp_6462_;
}
else
{
lean_object* v_reuseFailAlloc_6464_; 
v_reuseFailAlloc_6464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6464_, 0, v_a_6458_);
v___x_6463_ = v_reuseFailAlloc_6464_;
goto v_reusejp_6462_;
}
v_reusejp_6462_:
{
return v___x_6463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg___boxed(lean_object* v_type_6466_, lean_object* v_maxFVars_x3f_6467_, lean_object* v_k_6468_, lean_object* v_cleanupAnnotations_6469_, lean_object* v_whnfType_6470_, lean_object* v___y_6471_, lean_object* v___y_6472_, lean_object* v___y_6473_, lean_object* v___y_6474_, lean_object* v___y_6475_, lean_object* v___y_6476_, lean_object* v___y_6477_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_6478_; uint8_t v_whnfType_boxed_6479_; lean_object* v_res_6480_; 
v_cleanupAnnotations_boxed_6478_ = lean_unbox(v_cleanupAnnotations_6469_);
v_whnfType_boxed_6479_ = lean_unbox(v_whnfType_6470_);
v_res_6480_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_type_6466_, v_maxFVars_x3f_6467_, v_k_6468_, v_cleanupAnnotations_boxed_6478_, v_whnfType_boxed_6479_, v___y_6471_, v___y_6472_, v___y_6473_, v___y_6474_, v___y_6475_, v___y_6476_);
lean_dec(v___y_6476_);
lean_dec_ref(v___y_6475_);
lean_dec(v___y_6474_);
lean_dec_ref(v___y_6473_);
lean_dec(v___y_6472_);
lean_dec_ref(v___y_6471_);
return v_res_6480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0(lean_object* v_00_u03b1_6481_, lean_object* v_type_6482_, lean_object* v_maxFVars_x3f_6483_, lean_object* v_k_6484_, uint8_t v_cleanupAnnotations_6485_, uint8_t v_whnfType_6486_, lean_object* v___y_6487_, lean_object* v___y_6488_, lean_object* v___y_6489_, lean_object* v___y_6490_, lean_object* v___y_6491_, lean_object* v___y_6492_){
_start:
{
lean_object* v___x_6494_; 
v___x_6494_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_type_6482_, v_maxFVars_x3f_6483_, v_k_6484_, v_cleanupAnnotations_6485_, v_whnfType_6486_, v___y_6487_, v___y_6488_, v___y_6489_, v___y_6490_, v___y_6491_, v___y_6492_);
return v___x_6494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___boxed(lean_object* v_00_u03b1_6495_, lean_object* v_type_6496_, lean_object* v_maxFVars_x3f_6497_, lean_object* v_k_6498_, lean_object* v_cleanupAnnotations_6499_, lean_object* v_whnfType_6500_, lean_object* v___y_6501_, lean_object* v___y_6502_, lean_object* v___y_6503_, lean_object* v___y_6504_, lean_object* v___y_6505_, lean_object* v___y_6506_, lean_object* v___y_6507_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_6508_; uint8_t v_whnfType_boxed_6509_; lean_object* v_res_6510_; 
v_cleanupAnnotations_boxed_6508_ = lean_unbox(v_cleanupAnnotations_6499_);
v_whnfType_boxed_6509_ = lean_unbox(v_whnfType_6500_);
v_res_6510_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0(v_00_u03b1_6495_, v_type_6496_, v_maxFVars_x3f_6497_, v_k_6498_, v_cleanupAnnotations_boxed_6508_, v_whnfType_boxed_6509_, v___y_6501_, v___y_6502_, v___y_6503_, v___y_6504_, v___y_6505_, v___y_6506_);
lean_dec(v___y_6506_);
lean_dec_ref(v___y_6505_);
lean_dec(v___y_6504_);
lean_dec_ref(v___y_6503_);
lean_dec(v___y_6502_);
lean_dec_ref(v___y_6501_);
return v_res_6510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(lean_object* v_lctx_6511_, lean_object* v_x_6512_, lean_object* v___y_6513_, lean_object* v___y_6514_, lean_object* v___y_6515_, lean_object* v___y_6516_, lean_object* v___y_6517_, lean_object* v___y_6518_){
_start:
{
lean_object* v_keyedConfig_6520_; uint8_t v_trackZetaDelta_6521_; lean_object* v_zetaDeltaSet_6522_; lean_object* v_localInstances_6523_; lean_object* v_defEqCtx_x3f_6524_; lean_object* v_synthPendingDepth_6525_; lean_object* v_customCanUnfoldPredicate_x3f_6526_; uint8_t v_univApprox_6527_; uint8_t v_inTypeClassResolution_6528_; uint8_t v_cacheInferType_6529_; lean_object* v___x_6530_; lean_object* v___x_6531_; 
v_keyedConfig_6520_ = lean_ctor_get(v___y_6515_, 0);
v_trackZetaDelta_6521_ = lean_ctor_get_uint8(v___y_6515_, sizeof(void*)*7);
v_zetaDeltaSet_6522_ = lean_ctor_get(v___y_6515_, 1);
v_localInstances_6523_ = lean_ctor_get(v___y_6515_, 3);
v_defEqCtx_x3f_6524_ = lean_ctor_get(v___y_6515_, 4);
v_synthPendingDepth_6525_ = lean_ctor_get(v___y_6515_, 5);
v_customCanUnfoldPredicate_x3f_6526_ = lean_ctor_get(v___y_6515_, 6);
v_univApprox_6527_ = lean_ctor_get_uint8(v___y_6515_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_6528_ = lean_ctor_get_uint8(v___y_6515_, sizeof(void*)*7 + 2);
v_cacheInferType_6529_ = lean_ctor_get_uint8(v___y_6515_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_6526_);
lean_inc(v_synthPendingDepth_6525_);
lean_inc(v_defEqCtx_x3f_6524_);
lean_inc_ref(v_localInstances_6523_);
lean_inc(v_zetaDeltaSet_6522_);
lean_inc_ref(v_keyedConfig_6520_);
v___x_6530_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6530_, 0, v_keyedConfig_6520_);
lean_ctor_set(v___x_6530_, 1, v_zetaDeltaSet_6522_);
lean_ctor_set(v___x_6530_, 2, v_lctx_6511_);
lean_ctor_set(v___x_6530_, 3, v_localInstances_6523_);
lean_ctor_set(v___x_6530_, 4, v_defEqCtx_x3f_6524_);
lean_ctor_set(v___x_6530_, 5, v_synthPendingDepth_6525_);
lean_ctor_set(v___x_6530_, 6, v_customCanUnfoldPredicate_x3f_6526_);
lean_ctor_set_uint8(v___x_6530_, sizeof(void*)*7, v_trackZetaDelta_6521_);
lean_ctor_set_uint8(v___x_6530_, sizeof(void*)*7 + 1, v_univApprox_6527_);
lean_ctor_set_uint8(v___x_6530_, sizeof(void*)*7 + 2, v_inTypeClassResolution_6528_);
lean_ctor_set_uint8(v___x_6530_, sizeof(void*)*7 + 3, v_cacheInferType_6529_);
lean_inc(v___y_6518_);
lean_inc_ref(v___y_6517_);
lean_inc(v___y_6516_);
lean_inc(v___y_6514_);
lean_inc_ref(v___y_6513_);
v___x_6531_ = lean_apply_7(v_x_6512_, v___y_6513_, v___y_6514_, v___x_6530_, v___y_6516_, v___y_6517_, v___y_6518_, lean_box(0));
if (lean_obj_tag(v___x_6531_) == 0)
{
lean_object* v_a_6532_; lean_object* v___x_6534_; uint8_t v_isShared_6535_; uint8_t v_isSharedCheck_6539_; 
v_a_6532_ = lean_ctor_get(v___x_6531_, 0);
v_isSharedCheck_6539_ = !lean_is_exclusive(v___x_6531_);
if (v_isSharedCheck_6539_ == 0)
{
v___x_6534_ = v___x_6531_;
v_isShared_6535_ = v_isSharedCheck_6539_;
goto v_resetjp_6533_;
}
else
{
lean_inc(v_a_6532_);
lean_dec(v___x_6531_);
v___x_6534_ = lean_box(0);
v_isShared_6535_ = v_isSharedCheck_6539_;
goto v_resetjp_6533_;
}
v_resetjp_6533_:
{
lean_object* v___x_6537_; 
if (v_isShared_6535_ == 0)
{
v___x_6537_ = v___x_6534_;
goto v_reusejp_6536_;
}
else
{
lean_object* v_reuseFailAlloc_6538_; 
v_reuseFailAlloc_6538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6538_, 0, v_a_6532_);
v___x_6537_ = v_reuseFailAlloc_6538_;
goto v_reusejp_6536_;
}
v_reusejp_6536_:
{
return v___x_6537_;
}
}
}
else
{
return v___x_6531_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg___boxed(lean_object* v_lctx_6540_, lean_object* v_x_6541_, lean_object* v___y_6542_, lean_object* v___y_6543_, lean_object* v___y_6544_, lean_object* v___y_6545_, lean_object* v___y_6546_, lean_object* v___y_6547_, lean_object* v___y_6548_){
_start:
{
lean_object* v_res_6549_; 
v_res_6549_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v_lctx_6540_, v_x_6541_, v___y_6542_, v___y_6543_, v___y_6544_, v___y_6545_, v___y_6546_, v___y_6547_);
lean_dec(v___y_6547_);
lean_dec_ref(v___y_6546_);
lean_dec(v___y_6545_);
lean_dec_ref(v___y_6544_);
lean_dec(v___y_6543_);
lean_dec_ref(v___y_6542_);
return v_res_6549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1(lean_object* v_00_u03b1_6550_, lean_object* v_lctx_6551_, lean_object* v_x_6552_, lean_object* v___y_6553_, lean_object* v___y_6554_, lean_object* v___y_6555_, lean_object* v___y_6556_, lean_object* v___y_6557_, lean_object* v___y_6558_){
_start:
{
lean_object* v___x_6560_; 
v___x_6560_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v_lctx_6551_, v_x_6552_, v___y_6553_, v___y_6554_, v___y_6555_, v___y_6556_, v___y_6557_, v___y_6558_);
return v___x_6560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___boxed(lean_object* v_00_u03b1_6561_, lean_object* v_lctx_6562_, lean_object* v_x_6563_, lean_object* v___y_6564_, lean_object* v___y_6565_, lean_object* v___y_6566_, lean_object* v___y_6567_, lean_object* v___y_6568_, lean_object* v___y_6569_, lean_object* v___y_6570_){
_start:
{
lean_object* v_res_6571_; 
v_res_6571_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1(v_00_u03b1_6561_, v_lctx_6562_, v_x_6563_, v___y_6564_, v___y_6565_, v___y_6566_, v___y_6567_, v___y_6568_, v___y_6569_);
lean_dec(v___y_6569_);
lean_dec_ref(v___y_6568_);
lean_dec(v___y_6567_);
lean_dec_ref(v___y_6566_);
lean_dec(v___y_6565_);
lean_dec_ref(v___y_6564_);
return v_res_6571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__0(lean_object* v___x_6588_, lean_object* v___x_6589_, lean_object* v_wfRel_6590_, lean_object* v_x_6591_, lean_object* v_type_6592_, lean_object* v___y_6593_, lean_object* v___y_6594_, lean_object* v___y_6595_, lean_object* v___y_6596_, lean_object* v___y_6597_, lean_object* v___y_6598_){
_start:
{
lean_object* v___x_6600_; lean_object* v___x_6601_; lean_object* v___x_6602_; lean_object* v___x_6603_; 
v___x_6600_ = lean_unsigned_to_nat(0u);
v___x_6601_ = lean_array_get_borrowed(v___x_6588_, v_x_6591_, v___x_6600_);
v___x_6602_ = l_Lean_Expr_fvarId_x21(v___x_6601_);
v___x_6603_ = l_Lean_FVarId_getUserName___redArg(v___x_6602_, v___y_6595_, v___y_6597_, v___y_6598_);
if (lean_obj_tag(v___x_6603_) == 0)
{
lean_object* v_a_6604_; lean_object* v___x_6605_; 
v_a_6604_ = lean_ctor_get(v___x_6603_, 0);
lean_inc(v_a_6604_);
lean_dec_ref_known(v___x_6603_, 1);
lean_inc(v___y_6598_);
lean_inc_ref(v___y_6597_);
lean_inc(v___y_6596_);
lean_inc_ref(v___y_6595_);
lean_inc(v___x_6601_);
v___x_6605_ = lean_infer_type(v___x_6601_, v___y_6595_, v___y_6596_, v___y_6597_, v___y_6598_);
if (lean_obj_tag(v___x_6605_) == 0)
{
lean_object* v_a_6606_; lean_object* v___x_6607_; 
v_a_6606_ = lean_ctor_get(v___x_6605_, 0);
lean_inc_n(v_a_6606_, 2);
lean_dec_ref_known(v___x_6605_, 1);
v___x_6607_ = l_Lean_Meta_getLevel(v_a_6606_, v___y_6595_, v___y_6596_, v___y_6597_, v___y_6598_);
if (lean_obj_tag(v___x_6607_) == 0)
{
lean_object* v_a_6608_; lean_object* v___x_6609_; 
v_a_6608_ = lean_ctor_get(v___x_6607_, 0);
lean_inc(v_a_6608_);
lean_dec_ref_known(v___x_6607_, 1);
lean_inc_ref(v_type_6592_);
v___x_6609_ = l_Lean_Meta_getLevel(v_type_6592_, v___y_6595_, v___y_6596_, v___y_6597_, v___y_6598_);
if (lean_obj_tag(v___x_6609_) == 0)
{
lean_object* v_a_6610_; lean_object* v___x_6611_; lean_object* v___x_6612_; uint8_t v___x_6613_; uint8_t v___x_6614_; uint8_t v___x_6615_; lean_object* v___x_6616_; 
v_a_6610_ = lean_ctor_get(v___x_6609_, 0);
lean_inc(v_a_6610_);
lean_dec_ref_known(v___x_6609_, 1);
v___x_6611_ = lean_mk_empty_array_with_capacity(v___x_6589_);
lean_inc(v___x_6601_);
lean_inc_ref(v___x_6611_);
v___x_6612_ = lean_array_push(v___x_6611_, v___x_6601_);
v___x_6613_ = 0;
v___x_6614_ = 1;
v___x_6615_ = 1;
v___x_6616_ = l_Lean_Meta_mkLambdaFVars(v___x_6612_, v_type_6592_, v___x_6613_, v___x_6614_, v___x_6613_, v___x_6614_, v___x_6615_, v___y_6595_, v___y_6596_, v___y_6597_, v___y_6598_);
lean_dec_ref(v___x_6612_);
if (lean_obj_tag(v___x_6616_) == 0)
{
lean_object* v_a_6617_; lean_object* v___x_6618_; 
v_a_6617_ = lean_ctor_get(v___x_6616_, 0);
lean_inc(v_a_6617_);
lean_dec_ref_known(v___x_6616_, 1);
lean_inc_ref(v_wfRel_6590_);
v___x_6618_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_6590_, v___y_6595_, v___y_6596_, v___y_6597_, v___y_6598_);
if (lean_obj_tag(v___x_6618_) == 0)
{
lean_object* v_a_6619_; lean_object* v___x_6621_; uint8_t v_isShared_6622_; uint8_t v_isSharedCheck_6663_; 
v_a_6619_ = lean_ctor_get(v___x_6618_, 0);
v_isSharedCheck_6663_ = !lean_is_exclusive(v___x_6618_);
if (v_isSharedCheck_6663_ == 0)
{
v___x_6621_ = v___x_6618_;
v_isShared_6622_ = v_isSharedCheck_6663_;
goto v_resetjp_6620_;
}
else
{
lean_inc(v_a_6619_);
lean_dec(v___x_6618_);
v___x_6621_ = lean_box(0);
v_isShared_6622_ = v_isSharedCheck_6663_;
goto v_resetjp_6620_;
}
v_resetjp_6620_:
{
if (lean_obj_tag(v_a_6619_) == 1)
{
lean_object* v_val_6623_; lean_object* v___x_6624_; lean_object* v___x_6625_; lean_object* v___x_6626_; lean_object* v___x_6627_; lean_object* v___x_6628_; lean_object* v___x_6629_; lean_object* v___x_6630_; lean_object* v___x_6632_; 
lean_dec_ref(v___x_6611_);
lean_dec_ref(v_wfRel_6590_);
lean_dec(v___x_6589_);
v_val_6623_ = lean_ctor_get(v_a_6619_, 0);
lean_inc(v_val_6623_);
lean_dec_ref_known(v_a_6619_, 1);
v___x_6624_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__2));
v___x_6625_ = lean_box(0);
v___x_6626_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6626_, 0, v_a_6610_);
lean_ctor_set(v___x_6626_, 1, v___x_6625_);
v___x_6627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6627_, 0, v_a_6608_);
lean_ctor_set(v___x_6627_, 1, v___x_6626_);
v___x_6628_ = l_Lean_mkConst(v___x_6624_, v___x_6627_);
v___x_6629_ = l_Lean_mkApp3(v___x_6628_, v_a_6606_, v_a_6617_, v_val_6623_);
v___x_6630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6630_, 0, v___x_6629_);
lean_ctor_set(v___x_6630_, 1, v_a_6604_);
if (v_isShared_6622_ == 0)
{
lean_ctor_set(v___x_6621_, 0, v___x_6630_);
v___x_6632_ = v___x_6621_;
goto v_reusejp_6631_;
}
else
{
lean_object* v_reuseFailAlloc_6633_; 
v_reuseFailAlloc_6633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6633_, 0, v___x_6630_);
v___x_6632_ = v_reuseFailAlloc_6633_;
goto v_reusejp_6631_;
}
v_reusejp_6631_:
{
return v___x_6632_;
}
}
else
{
lean_object* v___x_6634_; lean_object* v___x_6635_; lean_object* v___x_6636_; lean_object* v___x_6637_; lean_object* v___x_6638_; lean_object* v___x_6639_; 
lean_del_object(v___x_6621_);
lean_dec(v_a_6619_);
v___x_6634_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__4));
lean_inc_ref(v_wfRel_6590_);
v___x_6635_ = l_Lean_mkProj(v___x_6634_, v___x_6600_, v_wfRel_6590_);
v___x_6636_ = l_Lean_mkProj(v___x_6634_, v___x_6589_, v_wfRel_6590_);
v___x_6637_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__6));
v___x_6638_ = lean_array_push(v___x_6611_, v___x_6636_);
v___x_6639_ = l_Lean_Meta_mkAppM(v___x_6637_, v___x_6638_, v___y_6595_, v___y_6596_, v___y_6597_, v___y_6598_);
if (lean_obj_tag(v___x_6639_) == 0)
{
lean_object* v_a_6640_; lean_object* v___x_6642_; uint8_t v_isShared_6643_; uint8_t v_isSharedCheck_6654_; 
v_a_6640_ = lean_ctor_get(v___x_6639_, 0);
v_isSharedCheck_6654_ = !lean_is_exclusive(v___x_6639_);
if (v_isSharedCheck_6654_ == 0)
{
v___x_6642_ = v___x_6639_;
v_isShared_6643_ = v_isSharedCheck_6654_;
goto v_resetjp_6641_;
}
else
{
lean_inc(v_a_6640_);
lean_dec(v___x_6639_);
v___x_6642_ = lean_box(0);
v_isShared_6643_ = v_isSharedCheck_6654_;
goto v_resetjp_6641_;
}
v_resetjp_6641_:
{
lean_object* v___x_6644_; lean_object* v___x_6645_; lean_object* v___x_6646_; lean_object* v___x_6647_; lean_object* v___x_6648_; lean_object* v___x_6649_; lean_object* v___x_6650_; lean_object* v___x_6652_; 
v___x_6644_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___lam__0___closed__7));
v___x_6645_ = lean_box(0);
v___x_6646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6646_, 0, v_a_6610_);
lean_ctor_set(v___x_6646_, 1, v___x_6645_);
v___x_6647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6647_, 0, v_a_6608_);
lean_ctor_set(v___x_6647_, 1, v___x_6646_);
v___x_6648_ = l_Lean_mkConst(v___x_6644_, v___x_6647_);
v___x_6649_ = l_Lean_mkApp4(v___x_6648_, v_a_6606_, v_a_6617_, v___x_6635_, v_a_6640_);
v___x_6650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6650_, 0, v___x_6649_);
lean_ctor_set(v___x_6650_, 1, v_a_6604_);
if (v_isShared_6643_ == 0)
{
lean_ctor_set(v___x_6642_, 0, v___x_6650_);
v___x_6652_ = v___x_6642_;
goto v_reusejp_6651_;
}
else
{
lean_object* v_reuseFailAlloc_6653_; 
v_reuseFailAlloc_6653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6653_, 0, v___x_6650_);
v___x_6652_ = v_reuseFailAlloc_6653_;
goto v_reusejp_6651_;
}
v_reusejp_6651_:
{
return v___x_6652_;
}
}
}
else
{
lean_object* v_a_6655_; lean_object* v___x_6657_; uint8_t v_isShared_6658_; uint8_t v_isSharedCheck_6662_; 
lean_dec_ref(v___x_6635_);
lean_dec(v_a_6617_);
lean_dec(v_a_6610_);
lean_dec(v_a_6608_);
lean_dec(v_a_6606_);
lean_dec(v_a_6604_);
v_a_6655_ = lean_ctor_get(v___x_6639_, 0);
v_isSharedCheck_6662_ = !lean_is_exclusive(v___x_6639_);
if (v_isSharedCheck_6662_ == 0)
{
v___x_6657_ = v___x_6639_;
v_isShared_6658_ = v_isSharedCheck_6662_;
goto v_resetjp_6656_;
}
else
{
lean_inc(v_a_6655_);
lean_dec(v___x_6639_);
v___x_6657_ = lean_box(0);
v_isShared_6658_ = v_isSharedCheck_6662_;
goto v_resetjp_6656_;
}
v_resetjp_6656_:
{
lean_object* v___x_6660_; 
if (v_isShared_6658_ == 0)
{
v___x_6660_ = v___x_6657_;
goto v_reusejp_6659_;
}
else
{
lean_object* v_reuseFailAlloc_6661_; 
v_reuseFailAlloc_6661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6661_, 0, v_a_6655_);
v___x_6660_ = v_reuseFailAlloc_6661_;
goto v_reusejp_6659_;
}
v_reusejp_6659_:
{
return v___x_6660_;
}
}
}
}
}
}
else
{
lean_object* v_a_6664_; lean_object* v___x_6666_; uint8_t v_isShared_6667_; uint8_t v_isSharedCheck_6671_; 
lean_dec(v_a_6617_);
lean_dec_ref(v___x_6611_);
lean_dec(v_a_6610_);
lean_dec(v_a_6608_);
lean_dec(v_a_6606_);
lean_dec(v_a_6604_);
lean_dec_ref(v_wfRel_6590_);
lean_dec(v___x_6589_);
v_a_6664_ = lean_ctor_get(v___x_6618_, 0);
v_isSharedCheck_6671_ = !lean_is_exclusive(v___x_6618_);
if (v_isSharedCheck_6671_ == 0)
{
v___x_6666_ = v___x_6618_;
v_isShared_6667_ = v_isSharedCheck_6671_;
goto v_resetjp_6665_;
}
else
{
lean_inc(v_a_6664_);
lean_dec(v___x_6618_);
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
else
{
lean_object* v_a_6672_; lean_object* v___x_6674_; uint8_t v_isShared_6675_; uint8_t v_isSharedCheck_6679_; 
lean_dec_ref(v___x_6611_);
lean_dec(v_a_6610_);
lean_dec(v_a_6608_);
lean_dec(v_a_6606_);
lean_dec(v_a_6604_);
lean_dec_ref(v_wfRel_6590_);
lean_dec(v___x_6589_);
v_a_6672_ = lean_ctor_get(v___x_6616_, 0);
v_isSharedCheck_6679_ = !lean_is_exclusive(v___x_6616_);
if (v_isSharedCheck_6679_ == 0)
{
v___x_6674_ = v___x_6616_;
v_isShared_6675_ = v_isSharedCheck_6679_;
goto v_resetjp_6673_;
}
else
{
lean_inc(v_a_6672_);
lean_dec(v___x_6616_);
v___x_6674_ = lean_box(0);
v_isShared_6675_ = v_isSharedCheck_6679_;
goto v_resetjp_6673_;
}
v_resetjp_6673_:
{
lean_object* v___x_6677_; 
if (v_isShared_6675_ == 0)
{
v___x_6677_ = v___x_6674_;
goto v_reusejp_6676_;
}
else
{
lean_object* v_reuseFailAlloc_6678_; 
v_reuseFailAlloc_6678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6678_, 0, v_a_6672_);
v___x_6677_ = v_reuseFailAlloc_6678_;
goto v_reusejp_6676_;
}
v_reusejp_6676_:
{
return v___x_6677_;
}
}
}
}
else
{
lean_object* v_a_6680_; lean_object* v___x_6682_; uint8_t v_isShared_6683_; uint8_t v_isSharedCheck_6687_; 
lean_dec(v_a_6608_);
lean_dec(v_a_6606_);
lean_dec(v_a_6604_);
lean_dec_ref(v_type_6592_);
lean_dec_ref(v_wfRel_6590_);
lean_dec(v___x_6589_);
v_a_6680_ = lean_ctor_get(v___x_6609_, 0);
v_isSharedCheck_6687_ = !lean_is_exclusive(v___x_6609_);
if (v_isSharedCheck_6687_ == 0)
{
v___x_6682_ = v___x_6609_;
v_isShared_6683_ = v_isSharedCheck_6687_;
goto v_resetjp_6681_;
}
else
{
lean_inc(v_a_6680_);
lean_dec(v___x_6609_);
v___x_6682_ = lean_box(0);
v_isShared_6683_ = v_isSharedCheck_6687_;
goto v_resetjp_6681_;
}
v_resetjp_6681_:
{
lean_object* v___x_6685_; 
if (v_isShared_6683_ == 0)
{
v___x_6685_ = v___x_6682_;
goto v_reusejp_6684_;
}
else
{
lean_object* v_reuseFailAlloc_6686_; 
v_reuseFailAlloc_6686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6686_, 0, v_a_6680_);
v___x_6685_ = v_reuseFailAlloc_6686_;
goto v_reusejp_6684_;
}
v_reusejp_6684_:
{
return v___x_6685_;
}
}
}
}
else
{
lean_object* v_a_6688_; lean_object* v___x_6690_; uint8_t v_isShared_6691_; uint8_t v_isSharedCheck_6695_; 
lean_dec(v_a_6606_);
lean_dec(v_a_6604_);
lean_dec_ref(v_type_6592_);
lean_dec_ref(v_wfRel_6590_);
lean_dec(v___x_6589_);
v_a_6688_ = lean_ctor_get(v___x_6607_, 0);
v_isSharedCheck_6695_ = !lean_is_exclusive(v___x_6607_);
if (v_isSharedCheck_6695_ == 0)
{
v___x_6690_ = v___x_6607_;
v_isShared_6691_ = v_isSharedCheck_6695_;
goto v_resetjp_6689_;
}
else
{
lean_inc(v_a_6688_);
lean_dec(v___x_6607_);
v___x_6690_ = lean_box(0);
v_isShared_6691_ = v_isSharedCheck_6695_;
goto v_resetjp_6689_;
}
v_resetjp_6689_:
{
lean_object* v___x_6693_; 
if (v_isShared_6691_ == 0)
{
v___x_6693_ = v___x_6690_;
goto v_reusejp_6692_;
}
else
{
lean_object* v_reuseFailAlloc_6694_; 
v_reuseFailAlloc_6694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6694_, 0, v_a_6688_);
v___x_6693_ = v_reuseFailAlloc_6694_;
goto v_reusejp_6692_;
}
v_reusejp_6692_:
{
return v___x_6693_;
}
}
}
}
else
{
lean_object* v_a_6696_; lean_object* v___x_6698_; uint8_t v_isShared_6699_; uint8_t v_isSharedCheck_6703_; 
lean_dec(v_a_6604_);
lean_dec_ref(v_type_6592_);
lean_dec_ref(v_wfRel_6590_);
lean_dec(v___x_6589_);
v_a_6696_ = lean_ctor_get(v___x_6605_, 0);
v_isSharedCheck_6703_ = !lean_is_exclusive(v___x_6605_);
if (v_isSharedCheck_6703_ == 0)
{
v___x_6698_ = v___x_6605_;
v_isShared_6699_ = v_isSharedCheck_6703_;
goto v_resetjp_6697_;
}
else
{
lean_inc(v_a_6696_);
lean_dec(v___x_6605_);
v___x_6698_ = lean_box(0);
v_isShared_6699_ = v_isSharedCheck_6703_;
goto v_resetjp_6697_;
}
v_resetjp_6697_:
{
lean_object* v___x_6701_; 
if (v_isShared_6699_ == 0)
{
v___x_6701_ = v___x_6698_;
goto v_reusejp_6700_;
}
else
{
lean_object* v_reuseFailAlloc_6702_; 
v_reuseFailAlloc_6702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6702_, 0, v_a_6696_);
v___x_6701_ = v_reuseFailAlloc_6702_;
goto v_reusejp_6700_;
}
v_reusejp_6700_:
{
return v___x_6701_;
}
}
}
}
else
{
lean_object* v_a_6704_; lean_object* v___x_6706_; uint8_t v_isShared_6707_; uint8_t v_isSharedCheck_6711_; 
lean_dec_ref(v_type_6592_);
lean_dec_ref(v_wfRel_6590_);
lean_dec(v___x_6589_);
v_a_6704_ = lean_ctor_get(v___x_6603_, 0);
v_isSharedCheck_6711_ = !lean_is_exclusive(v___x_6603_);
if (v_isSharedCheck_6711_ == 0)
{
v___x_6706_ = v___x_6603_;
v_isShared_6707_ = v_isSharedCheck_6711_;
goto v_resetjp_6705_;
}
else
{
lean_inc(v_a_6704_);
lean_dec(v___x_6603_);
v___x_6706_ = lean_box(0);
v_isShared_6707_ = v_isSharedCheck_6711_;
goto v_resetjp_6705_;
}
v_resetjp_6705_:
{
lean_object* v___x_6709_; 
if (v_isShared_6707_ == 0)
{
v___x_6709_ = v___x_6706_;
goto v_reusejp_6708_;
}
else
{
lean_object* v_reuseFailAlloc_6710_; 
v_reuseFailAlloc_6710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6710_, 0, v_a_6704_);
v___x_6709_ = v_reuseFailAlloc_6710_;
goto v_reusejp_6708_;
}
v_reusejp_6708_:
{
return v___x_6709_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__0___boxed(lean_object* v___x_6712_, lean_object* v___x_6713_, lean_object* v_wfRel_6714_, lean_object* v_x_6715_, lean_object* v_type_6716_, lean_object* v___y_6717_, lean_object* v___y_6718_, lean_object* v___y_6719_, lean_object* v___y_6720_, lean_object* v___y_6721_, lean_object* v___y_6722_, lean_object* v___y_6723_){
_start:
{
lean_object* v_res_6724_; 
v_res_6724_ = l_Lean_Elab_WF_mkFix___lam__0(v___x_6712_, v___x_6713_, v_wfRel_6714_, v_x_6715_, v_type_6716_, v___y_6717_, v___y_6718_, v___y_6719_, v___y_6720_, v___y_6721_, v___y_6722_);
lean_dec(v___y_6722_);
lean_dec_ref(v___y_6721_);
lean_dec(v___y_6720_);
lean_dec_ref(v___y_6719_);
lean_dec(v___y_6718_);
lean_dec_ref(v___y_6717_);
lean_dec_ref(v_x_6715_);
lean_dec_ref(v___x_6712_);
return v_res_6724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__1(lean_object* v_prefixArgs_6725_, lean_object* v_declName_6726_, lean_object* v_x_6727_, lean_object* v_F_6728_, lean_object* v_val_6729_, lean_object* v___y_6730_, lean_object* v___y_6731_, lean_object* v___y_6732_, lean_object* v___y_6733_, lean_object* v___y_6734_, lean_object* v___y_6735_){
_start:
{
lean_object* v___x_6737_; lean_object* v___x_6738_; lean_object* v___x_6739_; 
v___x_6737_ = lean_array_get_size(v_prefixArgs_6725_);
v___x_6738_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___boxed), 11, 2);
lean_closure_set(v___x_6738_, 0, v_declName_6726_);
lean_closure_set(v___x_6738_, 1, v___x_6737_);
v___x_6739_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v_x_6727_, v_F_6728_, v_val_6729_, v___x_6738_, v___y_6730_, v___y_6731_, v___y_6732_, v___y_6733_, v___y_6734_, v___y_6735_);
return v___x_6739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__1___boxed(lean_object* v_prefixArgs_6740_, lean_object* v_declName_6741_, lean_object* v_x_6742_, lean_object* v_F_6743_, lean_object* v_val_6744_, lean_object* v___y_6745_, lean_object* v___y_6746_, lean_object* v___y_6747_, lean_object* v___y_6748_, lean_object* v___y_6749_, lean_object* v___y_6750_, lean_object* v___y_6751_){
_start:
{
lean_object* v_res_6752_; 
v_res_6752_ = l_Lean_Elab_WF_mkFix___lam__1(v_prefixArgs_6740_, v_declName_6741_, v_x_6742_, v_F_6743_, v_val_6744_, v___y_6745_, v___y_6746_, v___y_6747_, v___y_6748_, v___y_6749_, v___y_6750_);
lean_dec(v___y_6750_);
lean_dec_ref(v___y_6749_);
lean_dec(v___y_6748_);
lean_dec_ref(v___y_6747_);
lean_dec(v___y_6746_);
lean_dec_ref(v___y_6745_);
lean_dec_ref(v_prefixArgs_6740_);
return v_res_6752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__2(lean_object* v___x_6753_, lean_object* v___x_6754_, lean_object* v___x_6755_, lean_object* v___f_6756_, lean_object* v_funNames_6757_, lean_object* v_argsPacker_6758_, lean_object* v_decrTactics_6759_, uint8_t v___x_6760_, lean_object* v_fst_6761_, lean_object* v_prefixArgs_6762_, lean_object* v___y_6763_, lean_object* v___y_6764_, lean_object* v___y_6765_, lean_object* v___y_6766_, lean_object* v___y_6767_, lean_object* v___y_6768_){
_start:
{
lean_object* v___x_6770_; 
lean_inc_ref(v___x_6754_);
lean_inc_ref(v___x_6753_);
v___x_6770_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v___x_6753_, v___x_6754_, v___x_6755_, v___f_6756_, v___y_6763_, v___y_6764_, v___y_6765_, v___y_6766_, v___y_6767_, v___y_6768_);
if (lean_obj_tag(v___x_6770_) == 0)
{
lean_object* v_a_6771_; lean_object* v___x_6772_; 
v_a_6771_ = lean_ctor_get(v___x_6770_, 0);
lean_inc(v_a_6771_);
lean_dec_ref_known(v___x_6770_, 1);
v___x_6772_ = l_Lean_Elab_WF_solveDecreasingGoals(v_funNames_6757_, v_argsPacker_6758_, v_decrTactics_6759_, v_a_6771_, v___y_6765_, v___y_6766_, v___y_6767_, v___y_6768_);
if (lean_obj_tag(v___x_6772_) == 0)
{
lean_object* v_a_6773_; lean_object* v___x_6774_; lean_object* v___x_6775_; lean_object* v___x_6776_; lean_object* v___x_6777_; uint8_t v___x_6778_; uint8_t v___x_6779_; lean_object* v___x_6780_; 
v_a_6773_ = lean_ctor_get(v___x_6772_, 0);
lean_inc(v_a_6773_);
lean_dec_ref_known(v___x_6772_, 1);
v___x_6774_ = lean_unsigned_to_nat(2u);
v___x_6775_ = lean_mk_empty_array_with_capacity(v___x_6774_);
v___x_6776_ = lean_array_push(v___x_6775_, v___x_6753_);
v___x_6777_ = lean_array_push(v___x_6776_, v___x_6754_);
v___x_6778_ = 1;
v___x_6779_ = 1;
v___x_6780_ = l_Lean_Meta_mkLambdaFVars(v___x_6777_, v_a_6773_, v___x_6760_, v___x_6778_, v___x_6760_, v___x_6778_, v___x_6779_, v___y_6765_, v___y_6766_, v___y_6767_, v___y_6768_);
lean_dec_ref(v___x_6777_);
if (lean_obj_tag(v___x_6780_) == 0)
{
lean_object* v_a_6781_; lean_object* v___x_6782_; lean_object* v___x_6783_; 
v_a_6781_ = lean_ctor_get(v___x_6780_, 0);
lean_inc(v_a_6781_);
lean_dec_ref_known(v___x_6780_, 1);
v___x_6782_ = l_Lean_Expr_app___override(v_fst_6761_, v_a_6781_);
v___x_6783_ = l_Lean_Meta_mkLambdaFVars(v_prefixArgs_6762_, v___x_6782_, v___x_6760_, v___x_6778_, v___x_6760_, v___x_6778_, v___x_6779_, v___y_6765_, v___y_6766_, v___y_6767_, v___y_6768_);
return v___x_6783_;
}
else
{
lean_dec_ref(v_fst_6761_);
return v___x_6780_;
}
}
else
{
lean_dec_ref(v_fst_6761_);
lean_dec_ref(v___x_6754_);
lean_dec_ref(v___x_6753_);
return v___x_6772_;
}
}
else
{
lean_dec_ref(v_fst_6761_);
lean_dec_ref(v_decrTactics_6759_);
lean_dec_ref(v_argsPacker_6758_);
lean_dec_ref(v_funNames_6757_);
lean_dec_ref(v___x_6754_);
lean_dec_ref(v___x_6753_);
return v___x_6770_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__2___boxed(lean_object** _args){
lean_object* v___x_6784_ = _args[0];
lean_object* v___x_6785_ = _args[1];
lean_object* v___x_6786_ = _args[2];
lean_object* v___f_6787_ = _args[3];
lean_object* v_funNames_6788_ = _args[4];
lean_object* v_argsPacker_6789_ = _args[5];
lean_object* v_decrTactics_6790_ = _args[6];
lean_object* v___x_6791_ = _args[7];
lean_object* v_fst_6792_ = _args[8];
lean_object* v_prefixArgs_6793_ = _args[9];
lean_object* v___y_6794_ = _args[10];
lean_object* v___y_6795_ = _args[11];
lean_object* v___y_6796_ = _args[12];
lean_object* v___y_6797_ = _args[13];
lean_object* v___y_6798_ = _args[14];
lean_object* v___y_6799_ = _args[15];
lean_object* v___y_6800_ = _args[16];
_start:
{
uint8_t v___x_5938__boxed_6801_; lean_object* v_res_6802_; 
v___x_5938__boxed_6801_ = lean_unbox(v___x_6791_);
v_res_6802_ = l_Lean_Elab_WF_mkFix___lam__2(v___x_6784_, v___x_6785_, v___x_6786_, v___f_6787_, v_funNames_6788_, v_argsPacker_6789_, v_decrTactics_6790_, v___x_5938__boxed_6801_, v_fst_6792_, v_prefixArgs_6793_, v___y_6794_, v___y_6795_, v___y_6796_, v___y_6797_, v___y_6798_, v___y_6799_);
lean_dec(v___y_6799_);
lean_dec_ref(v___y_6798_);
lean_dec(v___y_6797_);
lean_dec_ref(v___y_6796_);
lean_dec(v___y_6795_);
lean_dec_ref(v___y_6794_);
lean_dec_ref(v_prefixArgs_6793_);
return v_res_6802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__3(lean_object* v___x_6803_, lean_object* v_snd_6804_, lean_object* v___x_6805_, lean_object* v_prefixArgs_6806_, lean_object* v_value_6807_, lean_object* v___f_6808_, lean_object* v_funNames_6809_, lean_object* v_argsPacker_6810_, lean_object* v_decrTactics_6811_, uint8_t v___x_6812_, lean_object* v_fst_6813_, lean_object* v_xs_6814_, lean_object* v_x_6815_, lean_object* v___y_6816_, lean_object* v___y_6817_, lean_object* v___y_6818_, lean_object* v___y_6819_, lean_object* v___y_6820_, lean_object* v___y_6821_){
_start:
{
lean_object* v_lctx_6823_; lean_object* v___x_6824_; lean_object* v___x_6825_; lean_object* v___x_6826_; lean_object* v___x_6827_; lean_object* v___x_6828_; lean_object* v___x_6829_; lean_object* v___x_6830_; lean_object* v___x_6831_; lean_object* v___f_6832_; lean_object* v___x_6833_; 
v_lctx_6823_ = lean_ctor_get(v___y_6818_, 2);
v___x_6824_ = lean_unsigned_to_nat(0u);
v___x_6825_ = lean_array_get_borrowed(v___x_6803_, v_xs_6814_, v___x_6824_);
v___x_6826_ = l_Lean_Expr_fvarId_x21(v___x_6825_);
lean_inc_ref(v_lctx_6823_);
v___x_6827_ = l_Lean_LocalContext_setUserName(v_lctx_6823_, v___x_6826_, v_snd_6804_);
v___x_6828_ = lean_array_get_borrowed(v___x_6803_, v_xs_6814_, v___x_6805_);
lean_inc_n(v___x_6825_, 2);
lean_inc_ref(v_prefixArgs_6806_);
v___x_6829_ = lean_array_push(v_prefixArgs_6806_, v___x_6825_);
v___x_6830_ = l_Lean_Expr_beta(v_value_6807_, v___x_6829_);
v___x_6831_ = lean_box(v___x_6812_);
lean_inc(v___x_6828_);
v___f_6832_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__2___boxed), 17, 10);
lean_closure_set(v___f_6832_, 0, v___x_6825_);
lean_closure_set(v___f_6832_, 1, v___x_6828_);
lean_closure_set(v___f_6832_, 2, v___x_6830_);
lean_closure_set(v___f_6832_, 3, v___f_6808_);
lean_closure_set(v___f_6832_, 4, v_funNames_6809_);
lean_closure_set(v___f_6832_, 5, v_argsPacker_6810_);
lean_closure_set(v___f_6832_, 6, v_decrTactics_6811_);
lean_closure_set(v___f_6832_, 7, v___x_6831_);
lean_closure_set(v___f_6832_, 8, v_fst_6813_);
lean_closure_set(v___f_6832_, 9, v_prefixArgs_6806_);
v___x_6833_ = l_Lean_Meta_withLCtx_x27___at___00Lean_Elab_WF_mkFix_spec__1___redArg(v___x_6827_, v___f_6832_, v___y_6816_, v___y_6817_, v___y_6818_, v___y_6819_, v___y_6820_, v___y_6821_);
return v___x_6833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___lam__3___boxed(lean_object** _args){
lean_object* v___x_6834_ = _args[0];
lean_object* v_snd_6835_ = _args[1];
lean_object* v___x_6836_ = _args[2];
lean_object* v_prefixArgs_6837_ = _args[3];
lean_object* v_value_6838_ = _args[4];
lean_object* v___f_6839_ = _args[5];
lean_object* v_funNames_6840_ = _args[6];
lean_object* v_argsPacker_6841_ = _args[7];
lean_object* v_decrTactics_6842_ = _args[8];
lean_object* v___x_6843_ = _args[9];
lean_object* v_fst_6844_ = _args[10];
lean_object* v_xs_6845_ = _args[11];
lean_object* v_x_6846_ = _args[12];
lean_object* v___y_6847_ = _args[13];
lean_object* v___y_6848_ = _args[14];
lean_object* v___y_6849_ = _args[15];
lean_object* v___y_6850_ = _args[16];
lean_object* v___y_6851_ = _args[17];
lean_object* v___y_6852_ = _args[18];
lean_object* v___y_6853_ = _args[19];
_start:
{
uint8_t v___x_6008__boxed_6854_; lean_object* v_res_6855_; 
v___x_6008__boxed_6854_ = lean_unbox(v___x_6843_);
v_res_6855_ = l_Lean_Elab_WF_mkFix___lam__3(v___x_6834_, v_snd_6835_, v___x_6836_, v_prefixArgs_6837_, v_value_6838_, v___f_6839_, v_funNames_6840_, v_argsPacker_6841_, v_decrTactics_6842_, v___x_6008__boxed_6854_, v_fst_6844_, v_xs_6845_, v_x_6846_, v___y_6847_, v___y_6848_, v___y_6849_, v___y_6850_, v___y_6851_, v___y_6852_);
lean_dec(v___y_6852_);
lean_dec_ref(v___y_6851_);
lean_dec(v___y_6850_);
lean_dec_ref(v___y_6849_);
lean_dec(v___y_6848_);
lean_dec_ref(v___y_6847_);
lean_dec_ref(v_x_6846_);
lean_dec_ref(v_xs_6845_);
lean_dec(v___x_6836_);
lean_dec_ref(v___x_6834_);
return v_res_6855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix(lean_object* v_preDef_6860_, lean_object* v_prefixArgs_6861_, lean_object* v_argsPacker_6862_, lean_object* v_wfRel_6863_, lean_object* v_funNames_6864_, lean_object* v_decrTactics_6865_, lean_object* v_a_6866_, lean_object* v_a_6867_, lean_object* v_a_6868_, lean_object* v_a_6869_, lean_object* v_a_6870_, lean_object* v_a_6871_){
_start:
{
lean_object* v_declName_6873_; lean_object* v_type_6874_; lean_object* v_value_6875_; lean_object* v___x_6876_; 
v_declName_6873_ = lean_ctor_get(v_preDef_6860_, 3);
lean_inc(v_declName_6873_);
v_type_6874_ = lean_ctor_get(v_preDef_6860_, 6);
lean_inc_ref(v_type_6874_);
v_value_6875_ = lean_ctor_get(v_preDef_6860_, 7);
lean_inc_ref(v_value_6875_);
lean_dec_ref(v_preDef_6860_);
v___x_6876_ = l_Lean_Meta_instantiateForall(v_type_6874_, v_prefixArgs_6861_, v_a_6868_, v_a_6869_, v_a_6870_, v_a_6871_);
if (lean_obj_tag(v___x_6876_) == 0)
{
lean_object* v_a_6877_; lean_object* v___x_6878_; lean_object* v___x_6879_; lean_object* v___f_6880_; lean_object* v___x_6881_; uint8_t v___x_6882_; lean_object* v___x_6883_; 
v_a_6877_ = lean_ctor_get(v___x_6876_, 0);
lean_inc(v_a_6877_);
lean_dec_ref_known(v___x_6876_, 1);
v___x_6878_ = l_Lean_instInhabitedExpr;
v___x_6879_ = lean_unsigned_to_nat(1u);
v___f_6880_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__0___boxed), 12, 3);
lean_closure_set(v___f_6880_, 0, v___x_6878_);
lean_closure_set(v___f_6880_, 1, v___x_6879_);
lean_closure_set(v___f_6880_, 2, v_wfRel_6863_);
v___x_6881_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___closed__0));
v___x_6882_ = 0;
v___x_6883_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v_a_6877_, v___x_6881_, v___f_6880_, v___x_6882_, v___x_6882_, v_a_6866_, v_a_6867_, v_a_6868_, v_a_6869_, v_a_6870_, v_a_6871_);
if (lean_obj_tag(v___x_6883_) == 0)
{
lean_object* v_a_6884_; lean_object* v_fst_6885_; lean_object* v_snd_6886_; lean_object* v___x_6887_; 
v_a_6884_ = lean_ctor_get(v___x_6883_, 0);
lean_inc(v_a_6884_);
lean_dec_ref_known(v___x_6883_, 1);
v_fst_6885_ = lean_ctor_get(v_a_6884_, 0);
lean_inc_n(v_fst_6885_, 2);
v_snd_6886_ = lean_ctor_get(v_a_6884_, 1);
lean_inc(v_snd_6886_);
lean_dec(v_a_6884_);
lean_inc(v_a_6871_);
lean_inc_ref(v_a_6870_);
lean_inc(v_a_6869_);
lean_inc_ref(v_a_6868_);
v___x_6887_ = lean_infer_type(v_fst_6885_, v_a_6868_, v_a_6869_, v_a_6870_, v_a_6871_);
if (lean_obj_tag(v___x_6887_) == 0)
{
lean_object* v_a_6888_; lean_object* v___x_6889_; 
v_a_6888_ = lean_ctor_get(v___x_6887_, 0);
lean_inc(v_a_6888_);
lean_dec_ref_known(v___x_6887_, 1);
lean_inc(v_a_6871_);
lean_inc_ref(v_a_6870_);
lean_inc(v_a_6869_);
lean_inc_ref(v_a_6868_);
v___x_6889_ = lean_whnf(v_a_6888_, v_a_6868_, v_a_6869_, v_a_6870_, v_a_6871_);
if (lean_obj_tag(v___x_6889_) == 0)
{
lean_object* v_a_6890_; lean_object* v___f_6891_; lean_object* v___x_6892_; lean_object* v___f_6893_; lean_object* v___x_6894_; lean_object* v___x_6895_; lean_object* v___x_6896_; 
v_a_6890_ = lean_ctor_get(v___x_6889_, 0);
lean_inc(v_a_6890_);
lean_dec_ref_known(v___x_6889_, 1);
lean_inc_ref(v_prefixArgs_6861_);
v___f_6891_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__1___boxed), 12, 2);
lean_closure_set(v___f_6891_, 0, v_prefixArgs_6861_);
lean_closure_set(v___f_6891_, 1, v_declName_6873_);
v___x_6892_ = lean_box(v___x_6882_);
v___f_6893_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkFix___lam__3___boxed), 20, 11);
lean_closure_set(v___f_6893_, 0, v___x_6878_);
lean_closure_set(v___f_6893_, 1, v_snd_6886_);
lean_closure_set(v___f_6893_, 2, v___x_6879_);
lean_closure_set(v___f_6893_, 3, v_prefixArgs_6861_);
lean_closure_set(v___f_6893_, 4, v_value_6875_);
lean_closure_set(v___f_6893_, 5, v___f_6891_);
lean_closure_set(v___f_6893_, 6, v_funNames_6864_);
lean_closure_set(v___f_6893_, 7, v_argsPacker_6862_);
lean_closure_set(v___f_6893_, 8, v_decrTactics_6865_);
lean_closure_set(v___f_6893_, 9, v___x_6892_);
lean_closure_set(v___f_6893_, 10, v_fst_6885_);
v___x_6894_ = l_Lean_Expr_bindingDomain_x21(v_a_6890_);
lean_dec(v_a_6890_);
v___x_6895_ = ((lean_object*)(l_Lean_Elab_WF_mkFix___closed__1));
v___x_6896_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_WF_mkFix_spec__0___redArg(v___x_6894_, v___x_6895_, v___f_6893_, v___x_6882_, v___x_6882_, v_a_6866_, v_a_6867_, v_a_6868_, v_a_6869_, v_a_6870_, v_a_6871_);
return v___x_6896_;
}
else
{
lean_dec(v_snd_6886_);
lean_dec(v_fst_6885_);
lean_dec_ref(v_value_6875_);
lean_dec(v_declName_6873_);
lean_dec_ref(v_decrTactics_6865_);
lean_dec_ref(v_funNames_6864_);
lean_dec_ref(v_argsPacker_6862_);
lean_dec_ref(v_prefixArgs_6861_);
return v___x_6889_;
}
}
else
{
lean_dec(v_snd_6886_);
lean_dec(v_fst_6885_);
lean_dec_ref(v_value_6875_);
lean_dec(v_declName_6873_);
lean_dec_ref(v_decrTactics_6865_);
lean_dec_ref(v_funNames_6864_);
lean_dec_ref(v_argsPacker_6862_);
lean_dec_ref(v_prefixArgs_6861_);
return v___x_6887_;
}
}
else
{
lean_object* v_a_6897_; lean_object* v___x_6899_; uint8_t v_isShared_6900_; uint8_t v_isSharedCheck_6904_; 
lean_dec_ref(v_value_6875_);
lean_dec(v_declName_6873_);
lean_dec_ref(v_decrTactics_6865_);
lean_dec_ref(v_funNames_6864_);
lean_dec_ref(v_argsPacker_6862_);
lean_dec_ref(v_prefixArgs_6861_);
v_a_6897_ = lean_ctor_get(v___x_6883_, 0);
v_isSharedCheck_6904_ = !lean_is_exclusive(v___x_6883_);
if (v_isSharedCheck_6904_ == 0)
{
v___x_6899_ = v___x_6883_;
v_isShared_6900_ = v_isSharedCheck_6904_;
goto v_resetjp_6898_;
}
else
{
lean_inc(v_a_6897_);
lean_dec(v___x_6883_);
v___x_6899_ = lean_box(0);
v_isShared_6900_ = v_isSharedCheck_6904_;
goto v_resetjp_6898_;
}
v_resetjp_6898_:
{
lean_object* v___x_6902_; 
if (v_isShared_6900_ == 0)
{
v___x_6902_ = v___x_6899_;
goto v_reusejp_6901_;
}
else
{
lean_object* v_reuseFailAlloc_6903_; 
v_reuseFailAlloc_6903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6903_, 0, v_a_6897_);
v___x_6902_ = v_reuseFailAlloc_6903_;
goto v_reusejp_6901_;
}
v_reusejp_6901_:
{
return v___x_6902_;
}
}
}
}
else
{
lean_dec_ref(v_value_6875_);
lean_dec(v_declName_6873_);
lean_dec_ref(v_decrTactics_6865_);
lean_dec_ref(v_funNames_6864_);
lean_dec_ref(v_wfRel_6863_);
lean_dec_ref(v_argsPacker_6862_);
lean_dec_ref(v_prefixArgs_6861_);
return v___x_6876_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkFix___boxed(lean_object* v_preDef_6905_, lean_object* v_prefixArgs_6906_, lean_object* v_argsPacker_6907_, lean_object* v_wfRel_6908_, lean_object* v_funNames_6909_, lean_object* v_decrTactics_6910_, lean_object* v_a_6911_, lean_object* v_a_6912_, lean_object* v_a_6913_, lean_object* v_a_6914_, lean_object* v_a_6915_, lean_object* v_a_6916_, lean_object* v_a_6917_){
_start:
{
lean_object* v_res_6918_; 
v_res_6918_ = l_Lean_Elab_WF_mkFix(v_preDef_6905_, v_prefixArgs_6906_, v_argsPacker_6907_, v_wfRel_6908_, v_funNames_6909_, v_decrTactics_6910_, v_a_6911_, v_a_6912_, v_a_6913_, v_a_6914_, v_a_6915_, v_a_6916_);
lean_dec(v_a_6916_);
lean_dec_ref(v_a_6915_);
lean_dec(v_a_6914_);
lean_dec_ref(v_a_6913_);
lean_dec(v_a_6912_);
lean_dec_ref(v_a_6911_);
return v_res_6918_;
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
