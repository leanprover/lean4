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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
v___x_280_ = lean_st_ref_set(v_a_271_, v_snd_279_);
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
v___x_360_ = lean_st_ref_set(v___y_321_, v___x_359_);
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
v___x_671_ = lean_alloc_ctor(0, 10, 0);
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
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_56835__overap_1076_; lean_object* v___x_1077_; 
v___x_1072_ = l_StateRefT_x27_instMonad___redArg(v___x_1071_);
v___x_1073_ = l_StateRefT_x27_instMonad___redArg(v___x_1072_);
v___x_1074_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_1075_ = l_instInhabitedOfMonad___redArg(v___x_1073_, v___x_1074_);
v___x_56835__overap_1076_ = lean_panic_fn_borrowed(v___x_1075_, v_msg_989_);
lean_dec(v___x_1075_);
lean_inc(v___y_997_);
lean_inc_ref(v___y_996_);
lean_inc(v___y_995_);
lean_inc_ref(v___y_994_);
lean_inc(v___y_993_);
lean_inc_ref(v___y_992_);
lean_inc(v___y_991_);
lean_inc(v___y_990_);
v___x_1077_ = lean_apply_9(v___x_56835__overap_1076_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, lean_box(0));
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
lean_object* v_declName_1207_; lean_object* v_us_1208_; lean_object* v___x_1209_; lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1364_; 
v_declName_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc_n(v_declName_1207_, 2);
v_us_1208_ = lean_ctor_get(v___x_1206_, 1);
lean_inc(v_us_1208_);
lean_dec_ref_known(v___x_1206_, 2);
v___x_1209_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(v_declName_1207_, v___y_1198_);
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1212_ = v___x_1209_;
v_isShared_1213_ = v_isSharedCheck_1364_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1209_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1364_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
if (lean_obj_tag(v_a_1210_) == 1)
{
lean_object* v_val_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1256_; 
v_val_1214_ = lean_ctor_get(v_a_1210_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v_a_1210_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1216_ = v_a_1210_;
v_isShared_1217_ = v_isSharedCheck_1256_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_val_1214_);
lean_dec(v_a_1210_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1256_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v_dummy_1218_; lean_object* v_nargs_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v_args_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; uint8_t v___x_1226_; 
v_dummy_1218_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
v_nargs_1219_ = l_Lean_Expr_getAppNumArgs(v_e_1189_);
lean_inc(v_nargs_1219_);
v___x_1220_ = lean_mk_array(v_nargs_1219_, v_dummy_1218_);
v___x_1221_ = lean_unsigned_to_nat(1u);
v___x_1222_ = lean_nat_sub(v_nargs_1219_, v___x_1221_);
lean_dec(v_nargs_1219_);
v_args_1223_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1189_, v___x_1220_, v___x_1222_);
v___x_1224_ = lean_array_get_size(v_args_1223_);
v___x_1225_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_1214_);
v___x_1226_ = lean_nat_dec_lt(v___x_1224_, v___x_1225_);
lean_dec(v___x_1225_);
if (v___x_1226_ == 0)
{
lean_object* v_numParams_1227_; lean_object* v_numDiscrs_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1247_; 
v_numParams_1227_ = lean_ctor_get(v_val_1214_, 0);
v_numDiscrs_1228_ = lean_ctor_get(v_val_1214_, 1);
v___x_1229_ = lean_array_mk(v_us_1208_);
v___x_1230_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1227_);
v___x_1231_ = l_Array_extract___redArg(v_args_1223_, v___x_1230_, v_numParams_1227_);
v___x_1232_ = l_Lean_instInhabitedExpr;
v___x_1233_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_1214_);
v___x_1234_ = lean_array_get(v___x_1232_, v_args_1223_, v___x_1233_);
lean_dec(v___x_1233_);
v___x_1235_ = lean_nat_add(v_numParams_1227_, v___x_1221_);
v___x_1236_ = lean_nat_add(v___x_1235_, v_numDiscrs_1228_);
lean_inc(v___x_1236_);
lean_inc_ref_n(v_args_1223_, 2);
v___x_1237_ = l_Array_toSubarray___redArg(v_args_1223_, v___x_1235_, v___x_1236_);
v___x_1238_ = l_Subarray_copy___redArg(v___x_1237_);
v___x_1239_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1214_);
v___x_1240_ = lean_nat_add(v___x_1236_, v___x_1239_);
lean_dec(v___x_1239_);
lean_inc(v___x_1240_);
v___x_1241_ = l_Array_toSubarray___redArg(v_args_1223_, v___x_1236_, v___x_1240_);
v___x_1242_ = l_Subarray_copy___redArg(v___x_1241_);
v___x_1243_ = l_Array_toSubarray___redArg(v_args_1223_, v___x_1240_, v___x_1224_);
v___x_1244_ = l_Subarray_copy___redArg(v___x_1243_);
v___x_1245_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1245_, 0, v_val_1214_);
lean_ctor_set(v___x_1245_, 1, v_declName_1207_);
lean_ctor_set(v___x_1245_, 2, v___x_1229_);
lean_ctor_set(v___x_1245_, 3, v___x_1231_);
lean_ctor_set(v___x_1245_, 4, v___x_1234_);
lean_ctor_set(v___x_1245_, 5, v___x_1238_);
lean_ctor_set(v___x_1245_, 6, v___x_1242_);
lean_ctor_set(v___x_1245_, 7, v___x_1244_);
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 0, v___x_1245_);
v___x_1247_ = v___x_1216_;
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
lean_dec_ref(v_args_1223_);
lean_del_object(v___x_1216_);
lean_dec(v_val_1214_);
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
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1355_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1264_ = v___x_1261_;
v_isShared_1265_ = v_isSharedCheck_1355_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1261_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1355_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
if (lean_obj_tag(v_a_1262_) == 5)
{
lean_object* v_val_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1350_; 
v_val_1266_ = lean_ctor_get(v_a_1262_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v_a_1262_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1268_ = v_a_1262_;
v_isShared_1269_ = v_isSharedCheck_1350_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_val_1266_);
lean_dec(v_a_1262_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1350_;
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
lean_object* v___x_1291_; lean_object* v_params_1292_; lean_object* v___x_1293_; lean_object* v_motive_1294_; lean_object* v_discrs_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v_discrInfos_1298_; lean_object* v_alts_1299_; lean_object* v___y_1301_; lean_object* v___y_1302_; lean_object* v_lower_1341_; lean_object* v_upper_1342_; uint8_t v___x_1349_; 
lean_del_object(v___x_1264_);
v___x_1291_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1271_);
lean_inc_ref_n(v_args_1279_, 3);
v_params_1292_ = l_Array_toSubarray___redArg(v_args_1279_, v___x_1291_, v_numParams_1271_);
v___x_1293_ = l_Lean_instInhabitedExpr;
v_motive_1294_ = lean_array_get(v___x_1293_, v_args_1279_, v_numParams_1271_);
lean_dec(v_numParams_1271_);
lean_inc(v___x_1282_);
v_discrs_1295_ = l_Array_toSubarray___redArg(v_args_1279_, v___x_1280_, v___x_1282_);
v___x_1296_ = lean_nat_add(v_numIndices_1272_, v___x_1277_);
lean_dec(v_numIndices_1272_);
v___x_1297_ = lean_box(0);
v_discrInfos_1298_ = lean_mk_array(v___x_1296_, v___x_1297_);
lean_inc(v___x_1284_);
v_alts_1299_ = l_Array_toSubarray___redArg(v_args_1279_, v___x_1282_, v___x_1284_);
v___x_1349_ = lean_nat_dec_le(v___x_1284_, v___x_1291_);
if (v___x_1349_ == 0)
{
v_lower_1341_ = v___x_1284_;
v_upper_1342_ = v___x_1285_;
goto v___jp_1340_;
}
else
{
lean_dec(v___x_1284_);
v_lower_1341_ = v___x_1291_;
v_upper_1342_ = v___x_1285_;
goto v___jp_1340_;
}
v___jp_1300_:
{
lean_object* v___x_1303_; size_t v_sz_1304_; size_t v___x_1305_; lean_object* v___x_1306_; 
v___x_1303_ = lean_array_mk(v_ctors_1273_);
v_sz_1304_ = lean_array_size(v___x_1303_);
v___x_1305_ = ((size_t)0ULL);
v___x_1306_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__21(v_sz_1304_, v___x_1305_, v___x_1303_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1331_; 
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1309_ = v___x_1306_;
v_isShared_1310_ = v_isSharedCheck_1331_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1306_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1331_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v_start_1311_; lean_object* v_stop_1312_; lean_object* v_start_1313_; lean_object* v_stop_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1326_; 
v_start_1311_ = lean_ctor_get(v_params_1292_, 1);
lean_inc(v_start_1311_);
v_stop_1312_ = lean_ctor_get(v_params_1292_, 2);
lean_inc(v_stop_1312_);
v_start_1313_ = lean_ctor_get(v_discrs_1295_, 1);
lean_inc(v_start_1313_);
v_stop_1314_ = lean_ctor_get(v_discrs_1295_, 2);
lean_inc(v_stop_1314_);
v___x_1315_ = lean_nat_sub(v_stop_1312_, v_start_1311_);
lean_dec(v_start_1311_);
lean_dec(v_stop_1312_);
v___x_1316_ = lean_nat_sub(v_stop_1314_, v_start_1313_);
lean_dec(v_start_1313_);
lean_dec(v_stop_1314_);
v___x_1317_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__2);
v___x_1318_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1315_);
lean_ctor_set(v___x_1318_, 1, v___x_1316_);
lean_ctor_set(v___x_1318_, 2, v_a_1307_);
lean_ctor_set(v___x_1318_, 3, v___y_1302_);
lean_ctor_set(v___x_1318_, 4, v_discrInfos_1298_);
lean_ctor_set(v___x_1318_, 5, v___x_1317_);
v___x_1319_ = lean_array_mk(v_us_1208_);
v___x_1320_ = l_Subarray_copy___redArg(v_params_1292_);
v___x_1321_ = l_Subarray_copy___redArg(v_discrs_1295_);
v___x_1322_ = l_Subarray_copy___redArg(v_alts_1299_);
v___x_1323_ = l_Subarray_copy___redArg(v___y_1301_);
v___x_1324_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1318_);
lean_ctor_set(v___x_1324_, 1, v_declName_1207_);
lean_ctor_set(v___x_1324_, 2, v___x_1319_);
lean_ctor_set(v___x_1324_, 3, v___x_1320_);
lean_ctor_set(v___x_1324_, 4, v_motive_1294_);
lean_ctor_set(v___x_1324_, 5, v___x_1321_);
lean_ctor_set(v___x_1324_, 6, v___x_1322_);
lean_ctor_set(v___x_1324_, 7, v___x_1323_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set_tag(v___x_1268_, 1);
lean_ctor_set(v___x_1268_, 0, v___x_1324_);
v___x_1326_ = v___x_1268_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v___x_1324_);
v___x_1326_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
lean_object* v___x_1328_; 
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 0, v___x_1326_);
v___x_1328_ = v___x_1309_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1326_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
}
else
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec_ref(v_alts_1299_);
lean_dec_ref(v_discrInfos_1298_);
lean_dec_ref(v_discrs_1295_);
lean_dec(v_motive_1294_);
lean_dec_ref(v_params_1292_);
lean_del_object(v___x_1268_);
lean_dec(v_us_1208_);
lean_dec(v_declName_1207_);
v_a_1332_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1334_ = v___x_1306_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1306_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_a_1332_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
v___jp_1340_:
{
lean_object* v_levelParams_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; uint8_t v___x_1347_; 
v_levelParams_1343_ = lean_ctor_get(v_toConstantVal_1270_, 1);
lean_inc(v_levelParams_1343_);
lean_dec_ref(v_toConstantVal_1270_);
v___x_1344_ = l_Array_toSubarray___redArg(v_args_1279_, v_lower_1341_, v_upper_1342_);
v___x_1345_ = l_List_lengthTR___redArg(v_levelParams_1343_);
lean_dec(v_levelParams_1343_);
v___x_1346_ = l_List_lengthTR___redArg(v_us_1208_);
v___x_1347_ = lean_nat_dec_eq(v___x_1345_, v___x_1346_);
lean_dec(v___x_1346_);
lean_dec(v___x_1345_);
if (v___x_1347_ == 0)
{
lean_object* v___x_1348_; 
v___x_1348_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__3));
v___y_1301_ = v___x_1344_;
v___y_1302_ = v___x_1348_;
goto v___jp_1300_;
}
else
{
v___y_1301_ = v___x_1344_;
v___y_1302_ = v___x_1297_;
goto v___jp_1300_;
}
}
}
}
}
else
{
lean_object* v___x_1351_; lean_object* v___x_1353_; 
lean_dec(v_a_1262_);
lean_dec(v_us_1208_);
lean_dec(v_declName_1207_);
lean_dec_ref(v_e_1189_);
v___x_1351_ = lean_box(0);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 0, v___x_1351_);
v___x_1353_ = v___x_1264_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1351_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
}
else
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1363_; 
lean_dec(v_us_1208_);
lean_dec(v_declName_1207_);
lean_dec_ref(v_e_1189_);
v_a_1356_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1358_ = v___x_1261_;
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1261_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___boxed(lean_object* v_e_1365_, lean_object* v_alsoCasesOn_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
uint8_t v_alsoCasesOn_boxed_1376_; lean_object* v_res_1377_; 
v_alsoCasesOn_boxed_1376_ = lean_unbox(v_alsoCasesOn_1366_);
v_res_1377_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(v_e_1365_, v_alsoCasesOn_boxed_1376_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec(v___y_1367_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0(lean_object* v_k_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v_b_1383_, lean_object* v_c_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
lean_object* v___x_1390_; 
lean_inc(v___y_1388_);
lean_inc_ref(v___y_1387_);
lean_inc(v___y_1386_);
lean_inc_ref(v___y_1385_);
lean_inc(v___y_1382_);
lean_inc_ref(v___y_1381_);
lean_inc(v___y_1380_);
lean_inc(v___y_1379_);
v___x_1390_ = lean_apply_11(v_k_1378_, v_b_1383_, v_c_1384_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, lean_box(0));
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0___boxed(lean_object* v_k_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v_b_1396_, lean_object* v_c_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0(v_k_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v_b_1396_, v_c_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec(v___y_1392_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(lean_object* v_e_1404_, lean_object* v_maxFVars_1405_, lean_object* v_k_1406_, uint8_t v_cleanupAnnotations_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v___f_1417_; uint8_t v___x_1418_; uint8_t v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
lean_inc(v___y_1411_);
lean_inc_ref(v___y_1410_);
lean_inc(v___y_1409_);
lean_inc(v___y_1408_);
v___f_1417_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1417_, 0, v_k_1406_);
lean_closure_set(v___f_1417_, 1, v___y_1408_);
lean_closure_set(v___f_1417_, 2, v___y_1409_);
lean_closure_set(v___f_1417_, 3, v___y_1410_);
lean_closure_set(v___f_1417_, 4, v___y_1411_);
v___x_1418_ = 1;
v___x_1419_ = 0;
v___x_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1420_, 0, v_maxFVars_1405_);
v___x_1421_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1404_, v___x_1418_, v___x_1419_, v___x_1418_, v___x_1419_, v___x_1420_, v___f_1417_, v_cleanupAnnotations_1407_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
lean_dec_ref_known(v___x_1420_, 1);
if (lean_obj_tag(v___x_1421_) == 0)
{
return v___x_1421_;
}
else
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1424_ = v___x_1421_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1421_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1422_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg___boxed(lean_object* v_e_1430_, lean_object* v_maxFVars_1431_, lean_object* v_k_1432_, lean_object* v_cleanupAnnotations_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1443_; lean_object* v_res_1444_; 
v_cleanupAnnotations_boxed_1443_ = lean_unbox(v_cleanupAnnotations_1433_);
v_res_1444_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(v_e_1430_, v_maxFVars_1431_, v_k_1432_, v_cleanupAnnotations_boxed_1443_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v___y_1435_);
lean_dec(v___y_1434_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0(lean_object* v_k_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v_b_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v___x_1456_; 
lean_inc(v___y_1454_);
lean_inc_ref(v___y_1453_);
lean_inc(v___y_1452_);
lean_inc_ref(v___y_1451_);
lean_inc(v___y_1449_);
lean_inc_ref(v___y_1448_);
lean_inc(v___y_1447_);
lean_inc(v___y_1446_);
v___x_1456_ = lean_apply_10(v_k_1445_, v_b_1450_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, lean_box(0));
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0___boxed(lean_object* v_k_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v_b_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0(v_k_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v_b_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec(v___y_1458_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(lean_object* v_name_1469_, lean_object* v_type_1470_, lean_object* v_val_1471_, lean_object* v_k_1472_, uint8_t v_nondep_1473_, uint8_t v_kind_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v___f_1484_; lean_object* v___x_1485_; 
lean_inc(v___y_1478_);
lean_inc_ref(v___y_1477_);
lean_inc(v___y_1476_);
lean_inc(v___y_1475_);
v___f_1484_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1484_, 0, v_k_1472_);
lean_closure_set(v___f_1484_, 1, v___y_1475_);
lean_closure_set(v___f_1484_, 2, v___y_1476_);
lean_closure_set(v___f_1484_, 3, v___y_1477_);
lean_closure_set(v___f_1484_, 4, v___y_1478_);
v___x_1485_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1469_, v_type_1470_, v_val_1471_, v___f_1484_, v_nondep_1473_, v_kind_1474_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
if (lean_obj_tag(v___x_1485_) == 0)
{
return v___x_1485_;
}
else
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1493_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1488_ = v___x_1485_;
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1485_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1491_; 
if (v_isShared_1489_ == 0)
{
v___x_1491_ = v___x_1488_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_a_1486_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg___boxed(lean_object* v_name_1494_, lean_object* v_type_1495_, lean_object* v_val_1496_, lean_object* v_k_1497_, lean_object* v_nondep_1498_, lean_object* v_kind_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
uint8_t v_nondep_boxed_1509_; uint8_t v_kind_boxed_1510_; lean_object* v_res_1511_; 
v_nondep_boxed_1509_ = lean_unbox(v_nondep_1498_);
v_kind_boxed_1510_ = lean_unbox(v_kind_1499_);
v_res_1511_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(v_name_1494_, v_type_1495_, v_val_1496_, v_k_1497_, v_nondep_boxed_1509_, v_kind_boxed_1510_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1501_);
lean_dec(v___y_1500_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0(lean_object* v_k_1512_, uint8_t v_usedLetOnly_1513_, lean_object* v_x_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v___x_1524_; 
lean_inc(v___y_1522_);
lean_inc_ref(v___y_1521_);
lean_inc(v___y_1520_);
lean_inc_ref(v___y_1519_);
lean_inc(v___y_1518_);
lean_inc_ref(v___y_1517_);
lean_inc(v___y_1516_);
lean_inc(v___y_1515_);
lean_inc_ref(v_x_1514_);
v___x_1524_ = lean_apply_10(v_k_1512_, v_x_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, lean_box(0));
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; uint8_t v___x_1529_; uint8_t v___x_1530_; lean_object* v___x_1531_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1525_);
lean_dec_ref_known(v___x_1524_, 1);
v___x_1526_ = lean_unsigned_to_nat(1u);
v___x_1527_ = lean_mk_empty_array_with_capacity(v___x_1526_);
v___x_1528_ = lean_array_push(v___x_1527_, v_x_1514_);
v___x_1529_ = 0;
v___x_1530_ = 1;
v___x_1531_ = l_Lean_Meta_mkLetFVars(v___x_1528_, v_a_1525_, v_usedLetOnly_1513_, v___x_1529_, v___x_1530_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
lean_dec_ref(v___x_1528_);
return v___x_1531_;
}
else
{
lean_dec_ref(v_x_1514_);
return v___x_1524_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0___boxed(lean_object* v_k_1532_, lean_object* v_usedLetOnly_1533_, lean_object* v_x_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
uint8_t v_usedLetOnly_boxed_1544_; lean_object* v_res_1545_; 
v_usedLetOnly_boxed_1544_ = lean_unbox(v_usedLetOnly_1533_);
v_res_1545_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0(v_k_1532_, v_usedLetOnly_boxed_1544_, v_x_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v___y_1536_);
lean_dec(v___y_1535_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(lean_object* v_name_1546_, lean_object* v_type_1547_, lean_object* v_val_1548_, lean_object* v_k_1549_, uint8_t v_nondep_1550_, uint8_t v_kind_1551_, uint8_t v_usedLetOnly_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v___x_1562_; lean_object* v___f_1563_; lean_object* v___x_1564_; 
v___x_1562_ = lean_box(v_usedLetOnly_1552_);
v___f_1563_ = lean_alloc_closure((void*)(l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___lam__0___boxed), 12, 2);
lean_closure_set(v___f_1563_, 0, v_k_1549_);
lean_closure_set(v___f_1563_, 1, v___x_1562_);
v___x_1564_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(v_name_1546_, v_type_1547_, v_val_1548_, v___f_1563_, v_nondep_1550_, v_kind_1551_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11___boxed(lean_object* v_name_1565_, lean_object* v_type_1566_, lean_object* v_val_1567_, lean_object* v_k_1568_, lean_object* v_nondep_1569_, lean_object* v_kind_1570_, lean_object* v_usedLetOnly_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
uint8_t v_nondep_boxed_1581_; uint8_t v_kind_boxed_1582_; uint8_t v_usedLetOnly_boxed_1583_; lean_object* v_res_1584_; 
v_nondep_boxed_1581_ = lean_unbox(v_nondep_1569_);
v_kind_boxed_1582_ = lean_unbox(v_kind_1570_);
v_usedLetOnly_boxed_1583_ = lean_unbox(v_usedLetOnly_1571_);
v_res_1584_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(v_name_1565_, v_type_1566_, v_val_1567_, v_k_1568_, v_nondep_boxed_1581_, v_kind_boxed_1582_, v_usedLetOnly_boxed_1583_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec(v___y_1572_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(lean_object* v_name_1585_, uint8_t v_bi_1586_, lean_object* v_type_1587_, lean_object* v_k_1588_, uint8_t v_kind_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v___f_1599_; lean_object* v___x_1600_; 
lean_inc(v___y_1593_);
lean_inc_ref(v___y_1592_);
lean_inc(v___y_1591_);
lean_inc(v___y_1590_);
v___f_1599_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1599_, 0, v_k_1588_);
lean_closure_set(v___f_1599_, 1, v___y_1590_);
lean_closure_set(v___f_1599_, 2, v___y_1591_);
lean_closure_set(v___f_1599_, 3, v___y_1592_);
lean_closure_set(v___f_1599_, 4, v___y_1593_);
v___x_1600_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1585_, v_bi_1586_, v_type_1587_, v___f_1599_, v_kind_1589_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
if (lean_obj_tag(v___x_1600_) == 0)
{
return v___x_1600_;
}
else
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1600_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1600_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1601_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg___boxed(lean_object* v_name_1609_, lean_object* v_bi_1610_, lean_object* v_type_1611_, lean_object* v_k_1612_, lean_object* v_kind_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
uint8_t v_bi_boxed_1623_; uint8_t v_kind_boxed_1624_; lean_object* v_res_1625_; 
v_bi_boxed_1623_ = lean_unbox(v_bi_1610_);
v_kind_boxed_1624_ = lean_unbox(v_kind_1613_);
v_res_1625_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_name_1609_, v_bi_boxed_1623_, v_type_1611_, v_k_1612_, v_kind_boxed_1624_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec(v___y_1614_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0(lean_object* v_k_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v___x_1636_; 
lean_inc(v___y_1630_);
lean_inc_ref(v___y_1629_);
lean_inc(v___y_1628_);
lean_inc(v___y_1627_);
v___x_1636_ = lean_apply_9(v_k_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, lean_box(0));
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0___boxed(lean_object* v_k_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0(v_k_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec(v___y_1638_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(lean_object* v_k_1648_, uint8_t v_allowLevelAssignments_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v___f_1659_; lean_object* v___x_1660_; 
lean_inc(v___y_1653_);
lean_inc_ref(v___y_1652_);
lean_inc(v___y_1651_);
lean_inc(v___y_1650_);
v___f_1659_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1659_, 0, v_k_1648_);
lean_closure_set(v___f_1659_, 1, v___y_1650_);
lean_closure_set(v___f_1659_, 2, v___y_1651_);
lean_closure_set(v___f_1659_, 3, v___y_1652_);
lean_closure_set(v___f_1659_, 4, v___y_1653_);
v___x_1660_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1649_, v___f_1659_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
if (lean_obj_tag(v___x_1660_) == 0)
{
return v___x_1660_;
}
else
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1660_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1660_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg___boxed(lean_object* v_k_1669_, lean_object* v_allowLevelAssignments_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1680_; lean_object* v_res_1681_; 
v_allowLevelAssignments_boxed_1680_ = lean_unbox(v_allowLevelAssignments_1670_);
v_res_1681_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v_k_1669_, v_allowLevelAssignments_boxed_1680_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec(v___y_1671_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(lean_object* v_a_1682_, lean_object* v_x_1683_){
_start:
{
if (lean_obj_tag(v_x_1683_) == 0)
{
lean_object* v___x_1684_; 
v___x_1684_ = lean_box(0);
return v___x_1684_;
}
else
{
lean_object* v_key_1685_; lean_object* v_value_1686_; lean_object* v_tail_1687_; uint8_t v___x_1688_; 
v_key_1685_ = lean_ctor_get(v_x_1683_, 0);
v_value_1686_ = lean_ctor_get(v_x_1683_, 1);
v_tail_1687_ = lean_ctor_get(v_x_1683_, 2);
v___x_1688_ = lean_expr_eqv(v_key_1685_, v_a_1682_);
if (v___x_1688_ == 0)
{
v_x_1683_ = v_tail_1687_;
goto _start;
}
else
{
lean_object* v___x_1690_; 
lean_inc(v_value_1686_);
v___x_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1690_, 0, v_value_1686_);
return v___x_1690_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg___boxed(lean_object* v_a_1691_, lean_object* v_x_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(v_a_1691_, v_x_1692_);
lean_dec(v_x_1692_);
lean_dec_ref(v_a_1691_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(lean_object* v_m_1694_, lean_object* v_a_1695_){
_start:
{
lean_object* v_buckets_1696_; lean_object* v___x_1697_; uint64_t v___x_1698_; uint64_t v___x_1699_; uint64_t v___x_1700_; uint64_t v_fold_1701_; uint64_t v___x_1702_; uint64_t v___x_1703_; uint64_t v___x_1704_; size_t v___x_1705_; size_t v___x_1706_; size_t v___x_1707_; size_t v___x_1708_; size_t v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
v_buckets_1696_ = lean_ctor_get(v_m_1694_, 1);
v___x_1697_ = lean_array_get_size(v_buckets_1696_);
v___x_1698_ = l_Lean_Expr_hash(v_a_1695_);
v___x_1699_ = 32ULL;
v___x_1700_ = lean_uint64_shift_right(v___x_1698_, v___x_1699_);
v_fold_1701_ = lean_uint64_xor(v___x_1698_, v___x_1700_);
v___x_1702_ = 16ULL;
v___x_1703_ = lean_uint64_shift_right(v_fold_1701_, v___x_1702_);
v___x_1704_ = lean_uint64_xor(v_fold_1701_, v___x_1703_);
v___x_1705_ = lean_uint64_to_usize(v___x_1704_);
v___x_1706_ = lean_usize_of_nat(v___x_1697_);
v___x_1707_ = ((size_t)1ULL);
v___x_1708_ = lean_usize_sub(v___x_1706_, v___x_1707_);
v___x_1709_ = lean_usize_land(v___x_1705_, v___x_1708_);
v___x_1710_ = lean_array_uget_borrowed(v_buckets_1696_, v___x_1709_);
v___x_1711_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(v_a_1695_, v___x_1710_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg___boxed(lean_object* v_m_1712_, lean_object* v_a_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v_m_1712_, v_a_1713_);
lean_dec_ref(v_a_1713_);
lean_dec_ref(v_m_1712_);
return v_res_1714_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(lean_object* v_opts_1715_, lean_object* v_opt_1716_){
_start:
{
lean_object* v_name_1717_; lean_object* v_defValue_1718_; lean_object* v_map_1719_; lean_object* v___x_1720_; 
v_name_1717_ = lean_ctor_get(v_opt_1716_, 0);
v_defValue_1718_ = lean_ctor_get(v_opt_1716_, 1);
v_map_1719_ = lean_ctor_get(v_opts_1715_, 0);
v___x_1720_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1719_, v_name_1717_);
if (lean_obj_tag(v___x_1720_) == 0)
{
uint8_t v___x_1721_; 
v___x_1721_ = lean_unbox(v_defValue_1718_);
return v___x_1721_;
}
else
{
lean_object* v_val_1722_; 
v_val_1722_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_val_1722_);
lean_dec_ref_known(v___x_1720_, 1);
if (lean_obj_tag(v_val_1722_) == 1)
{
uint8_t v_v_1723_; 
v_v_1723_ = lean_ctor_get_uint8(v_val_1722_, 0);
lean_dec_ref_known(v_val_1722_, 0);
return v_v_1723_;
}
else
{
uint8_t v___x_1724_; 
lean_dec(v_val_1722_);
v___x_1724_ = lean_unbox(v_defValue_1718_);
return v___x_1724_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5___boxed(lean_object* v_opts_1725_, lean_object* v_opt_1726_){
_start:
{
uint8_t v_res_1727_; lean_object* v_r_1728_; 
v_res_1727_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v_opts_1725_, v_opt_1726_);
lean_dec_ref(v_opt_1726_);
lean_dec_ref(v_opts_1725_);
v_r_1728_ = lean_box(v_res_1727_);
return v_r_1728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(lean_object* v_a_1729_, lean_object* v_b_1730_){
_start:
{
lean_object* v_array_1731_; lean_object* v_start_1732_; lean_object* v_stop_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1746_; 
v_array_1731_ = lean_ctor_get(v_a_1729_, 0);
v_start_1732_ = lean_ctor_get(v_a_1729_, 1);
v_stop_1733_ = lean_ctor_get(v_a_1729_, 2);
v_isSharedCheck_1746_ = !lean_is_exclusive(v_a_1729_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1735_ = v_a_1729_;
v_isShared_1736_ = v_isSharedCheck_1746_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_stop_1733_);
lean_inc(v_start_1732_);
lean_inc(v_array_1731_);
lean_dec(v_a_1729_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1746_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
uint8_t v___x_1737_; 
v___x_1737_ = lean_nat_dec_lt(v_start_1732_, v_stop_1733_);
if (v___x_1737_ == 0)
{
lean_del_object(v___x_1735_);
lean_dec(v_stop_1733_);
lean_dec(v_start_1732_);
lean_dec_ref(v_array_1731_);
return v_b_1730_;
}
else
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1741_; 
v___x_1738_ = lean_unsigned_to_nat(1u);
v___x_1739_ = lean_nat_add(v_start_1732_, v___x_1738_);
lean_inc_ref(v_array_1731_);
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 1, v___x_1739_);
v___x_1741_ = v___x_1735_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_array_1731_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v___x_1739_);
lean_ctor_set(v_reuseFailAlloc_1745_, 2, v_stop_1733_);
v___x_1741_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1742_ = lean_array_fget(v_array_1731_, v_start_1732_);
lean_dec(v_start_1732_);
lean_dec_ref(v_array_1731_);
v___x_1743_ = lean_array_push(v_b_1730_, v___x_1742_);
v_a_1729_ = v___x_1741_;
v_b_1730_ = v___x_1743_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0(lean_object* v_body_1747_, lean_object* v_recFnName_1748_, lean_object* v_fixedPrefixSize_1749_, lean_object* v_F_1750_, lean_object* v_x_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = lean_expr_instantiate1(v_body_1747_, v_x_1751_);
v___x_1762_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1748_, v_fixedPrefixSize_1749_, v_F_1750_, v___x_1761_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; uint8_t v___x_1767_; uint8_t v___x_1768_; uint8_t v___x_1769_; lean_object* v___x_1770_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
lean_inc(v_a_1763_);
lean_dec_ref_known(v___x_1762_, 1);
v___x_1764_ = lean_unsigned_to_nat(1u);
v___x_1765_ = lean_mk_empty_array_with_capacity(v___x_1764_);
v___x_1766_ = lean_array_push(v___x_1765_, v_x_1751_);
v___x_1767_ = 0;
v___x_1768_ = 1;
v___x_1769_ = 1;
v___x_1770_ = l_Lean_Meta_mkLambdaFVars(v___x_1766_, v_a_1763_, v___x_1767_, v___x_1768_, v___x_1767_, v___x_1768_, v___x_1769_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_);
lean_dec_ref(v___x_1766_);
return v___x_1770_;
}
else
{
lean_dec_ref(v_x_1751_);
return v___x_1762_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0___boxed(lean_object* v_body_1771_, lean_object* v_recFnName_1772_, lean_object* v_fixedPrefixSize_1773_, lean_object* v_F_1774_, lean_object* v_x_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0(v_body_1771_, v_recFnName_1772_, v_fixedPrefixSize_1773_, v_F_1774_, v_x_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec(v___y_1776_);
lean_dec_ref(v_body_1771_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1(lean_object* v_body_1786_, lean_object* v_recFnName_1787_, lean_object* v_fixedPrefixSize_1788_, lean_object* v_F_1789_, lean_object* v_x_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1800_ = lean_expr_instantiate1(v_body_1786_, v_x_1790_);
v___x_1801_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1787_, v_fixedPrefixSize_1788_, v_F_1789_, v___x_1800_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_a_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; uint8_t v___x_1806_; uint8_t v___x_1807_; uint8_t v___x_1808_; lean_object* v___x_1809_; 
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
lean_inc(v_a_1802_);
lean_dec_ref_known(v___x_1801_, 1);
v___x_1803_ = lean_unsigned_to_nat(1u);
v___x_1804_ = lean_mk_empty_array_with_capacity(v___x_1803_);
v___x_1805_ = lean_array_push(v___x_1804_, v_x_1790_);
v___x_1806_ = 0;
v___x_1807_ = 1;
v___x_1808_ = 1;
v___x_1809_ = l_Lean_Meta_mkForallFVars(v___x_1805_, v_a_1802_, v___x_1806_, v___x_1807_, v___x_1807_, v___x_1808_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
lean_dec_ref(v___x_1805_);
return v___x_1809_;
}
else
{
lean_dec_ref(v_x_1790_);
return v___x_1801_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1___boxed(lean_object* v_body_1810_, lean_object* v_recFnName_1811_, lean_object* v_fixedPrefixSize_1812_, lean_object* v_F_1813_, lean_object* v_x_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1(v_body_1810_, v_recFnName_1811_, v_fixedPrefixSize_1812_, v_F_1813_, v_x_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v_body_1810_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2___boxed(lean_object* v_body_1825_, lean_object* v_recFnName_1826_, lean_object* v_fixedPrefixSize_1827_, lean_object* v_F_1828_, lean_object* v_x_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2(v_body_1825_, v_recFnName_1826_, v_fixedPrefixSize_1827_, v_F_1828_, v_x_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v_x_1829_);
lean_dec_ref(v_body_1825_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(lean_object* v_recFnName_1842_, lean_object* v_fixedPrefixSize_1843_, lean_object* v_F_1844_, size_t v_sz_1845_, size_t v_i_1846_, lean_object* v_bs_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
uint8_t v___x_1857_; 
v___x_1857_ = lean_usize_dec_lt(v_i_1846_, v_sz_1845_);
if (v___x_1857_ == 0)
{
lean_object* v___x_1858_; 
lean_dec_ref(v_F_1844_);
lean_dec(v_fixedPrefixSize_1843_);
lean_dec(v_recFnName_1842_);
v___x_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1858_, 0, v_bs_1847_);
return v___x_1858_;
}
else
{
lean_object* v_v_1859_; lean_object* v___x_1860_; 
v_v_1859_ = lean_array_uget_borrowed(v_bs_1847_, v_i_1846_);
lean_inc(v_v_1859_);
lean_inc_ref(v_F_1844_);
lean_inc(v_fixedPrefixSize_1843_);
lean_inc(v_recFnName_1842_);
v___x_1860_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1842_, v_fixedPrefixSize_1843_, v_F_1844_, v_v_1859_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v___x_1862_; lean_object* v_bs_x27_1863_; size_t v___x_1864_; size_t v___x_1865_; lean_object* v___x_1866_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
lean_inc(v_a_1861_);
lean_dec_ref_known(v___x_1860_, 1);
v___x_1862_ = lean_unsigned_to_nat(0u);
v_bs_x27_1863_ = lean_array_uset(v_bs_1847_, v_i_1846_, v___x_1862_);
v___x_1864_ = ((size_t)1ULL);
v___x_1865_ = lean_usize_add(v_i_1846_, v___x_1864_);
v___x_1866_ = lean_array_uset(v_bs_x27_1863_, v_i_1846_, v_a_1861_);
v_i_1846_ = v___x_1865_;
v_bs_1847_ = v___x_1866_;
goto _start;
}
else
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
lean_dec_ref(v_bs_1847_);
lean_dec_ref(v_F_1844_);
lean_dec(v_fixedPrefixSize_1843_);
lean_dec(v_recFnName_1842_);
v_a_1868_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1860_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1860_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4(void){
_start:
{
lean_object* v_cls_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v_cls_1883_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_1884_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__3));
v___x_1885_ = l_Lean_Name_append(v___x_1884_, v_cls_1883_);
return v___x_1885_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6(void){
_start:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1887_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__5));
v___x_1888_ = l_Lean_stringToMessageData(v___x_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(lean_object* v_recFnName_1889_, lean_object* v_fixedPrefixSize_1890_, lean_object* v_F_1891_, lean_object* v_e_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_){
_start:
{
lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; uint8_t v___x_1917_; 
v___x_1914_ = l_Lean_Expr_getAppNumArgs(v_e_1892_);
v___x_1915_ = lean_unsigned_to_nat(1u);
v___x_1916_ = lean_nat_add(v_fixedPrefixSize_1890_, v___x_1915_);
v___x_1917_ = lean_nat_dec_lt(v___x_1914_, v___x_1916_);
if (v___x_1917_ == 0)
{
lean_object* v_dummy_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v_args_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v_dummy_1918_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_1914_);
v___x_1919_ = lean_mk_array(v___x_1914_, v_dummy_1918_);
v___x_1920_ = lean_nat_sub(v___x_1914_, v___x_1915_);
lean_dec(v___x_1914_);
v_args_1921_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1892_, v___x_1919_, v___x_1920_);
v___x_1922_ = l_Lean_instInhabitedExpr;
v___x_1923_ = lean_array_get(v___x_1922_, v_args_1921_, v_fixedPrefixSize_1890_);
lean_inc_ref(v_F_1891_);
lean_inc(v_fixedPrefixSize_1890_);
lean_inc(v_recFnName_1889_);
v___x_1924_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1889_, v_fixedPrefixSize_1890_, v_F_1891_, v___x_1923_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_a_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc(v_a_1925_);
lean_dec_ref_known(v___x_1924_, 1);
lean_inc_ref(v_F_1891_);
v___x_1926_ = l_Lean_Expr_app___override(v_F_1891_, v_a_1925_);
lean_inc(v_a_1900_);
lean_inc_ref(v_a_1899_);
lean_inc(v_a_1898_);
lean_inc_ref(v_a_1897_);
lean_inc_ref(v___x_1926_);
v___x_1927_ = lean_infer_type(v___x_1926_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1929_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref_known(v___x_1927_, 1);
lean_inc(v_a_1900_);
lean_inc_ref(v_a_1899_);
lean_inc(v_a_1898_);
lean_inc_ref(v_a_1897_);
v___x_1929_ = lean_whnf(v_a_1928_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_a_1930_);
lean_dec_ref_known(v___x_1929_, 1);
v___x_1931_ = l_Lean_Expr_bindingDomain_x21(v_a_1930_);
lean_dec(v_a_1930_);
v___x_1932_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg(v___x_1931_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v___x_1934_; lean_object* v_lower_1936_; lean_object* v_upper_1937_; lean_object* v___x_1961_; lean_object* v___x_1962_; uint8_t v___x_1963_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
lean_dec_ref_known(v___x_1932_, 1);
v___x_1934_ = l_Lean_Expr_app___override(v___x_1926_, v_a_1933_);
v___x_1961_ = lean_unsigned_to_nat(0u);
v___x_1962_ = lean_array_get_size(v_args_1921_);
v___x_1963_ = lean_nat_dec_le(v___x_1916_, v___x_1961_);
if (v___x_1963_ == 0)
{
v_lower_1936_ = v___x_1916_;
v_upper_1937_ = v___x_1962_;
goto v___jp_1935_;
}
else
{
lean_dec(v___x_1916_);
v_lower_1936_ = v___x_1961_;
v_upper_1937_ = v___x_1962_;
goto v___jp_1935_;
}
v___jp_1935_:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; size_t v_sz_1941_; size_t v___x_1942_; lean_object* v___x_1943_; 
v___x_1938_ = l_Array_toSubarray___redArg(v_args_1921_, v_lower_1936_, v_upper_1937_);
v___x_1939_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
v___x_1940_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(v___x_1938_, v___x_1939_);
v_sz_1941_ = lean_array_size(v___x_1940_);
v___x_1942_ = ((size_t)0ULL);
v___x_1943_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_1889_, v_fixedPrefixSize_1890_, v_F_1891_, v_sz_1941_, v___x_1942_, v___x_1940_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1952_; 
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1946_ = v___x_1943_;
v_isShared_1947_ = v_isSharedCheck_1952_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1943_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1952_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1948_; lean_object* v___x_1950_; 
v___x_1948_ = l_Lean_mkAppN(v___x_1934_, v_a_1944_);
lean_dec(v_a_1944_);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 0, v___x_1948_);
v___x_1950_ = v___x_1946_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v___x_1948_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
else
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
lean_dec_ref(v___x_1934_);
v_a_1953_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1955_ = v___x_1943_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1943_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1958_; 
if (v_isShared_1956_ == 0)
{
v___x_1958_ = v___x_1955_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_a_1953_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1926_);
lean_dec_ref(v_args_1921_);
lean_dec(v___x_1916_);
lean_dec_ref(v_F_1891_);
lean_dec(v_fixedPrefixSize_1890_);
lean_dec(v_recFnName_1889_);
return v___x_1932_;
}
}
else
{
lean_dec_ref(v___x_1926_);
lean_dec_ref(v_args_1921_);
lean_dec(v___x_1916_);
lean_dec_ref(v_F_1891_);
lean_dec(v_fixedPrefixSize_1890_);
lean_dec(v_recFnName_1889_);
return v___x_1929_;
}
}
else
{
lean_dec_ref(v___x_1926_);
lean_dec_ref(v_args_1921_);
lean_dec(v___x_1916_);
lean_dec_ref(v_F_1891_);
lean_dec(v_fixedPrefixSize_1890_);
lean_dec(v_recFnName_1889_);
return v___x_1927_;
}
}
else
{
lean_dec_ref(v_args_1921_);
lean_dec(v___x_1916_);
lean_dec_ref(v_F_1891_);
lean_dec(v_fixedPrefixSize_1890_);
lean_dec(v_recFnName_1889_);
return v___x_1924_;
}
}
else
{
lean_object* v_options_1964_; uint8_t v_hasTrace_1965_; 
lean_dec(v___x_1916_);
lean_dec(v___x_1914_);
v_options_1964_ = lean_ctor_get(v_a_1899_, 2);
v_hasTrace_1965_ = lean_ctor_get_uint8(v_options_1964_, sizeof(void*)*1);
if (v_hasTrace_1965_ == 0)
{
v___y_1903_ = v_a_1893_;
v___y_1904_ = v_a_1894_;
v___y_1905_ = v_a_1895_;
v___y_1906_ = v_a_1896_;
v___y_1907_ = v_a_1897_;
v___y_1908_ = v_a_1898_;
v___y_1909_ = v_a_1899_;
v___y_1910_ = v_a_1900_;
goto v___jp_1902_;
}
else
{
lean_object* v_inheritedTraceOptions_1966_; lean_object* v_cls_1967_; lean_object* v___x_1968_; uint8_t v___x_1969_; 
v_inheritedTraceOptions_1966_ = lean_ctor_get(v_a_1899_, 13);
v_cls_1967_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_1968_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_1969_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1966_, v_options_1964_, v___x_1968_);
if (v___x_1969_ == 0)
{
v___y_1903_ = v_a_1893_;
v___y_1904_ = v_a_1894_;
v___y_1905_ = v_a_1895_;
v___y_1906_ = v_a_1896_;
v___y_1907_ = v_a_1897_;
v___y_1908_ = v_a_1898_;
v___y_1909_ = v_a_1899_;
v___y_1910_ = v_a_1900_;
goto v___jp_1902_;
}
else
{
lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1970_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__6);
lean_inc_ref(v_e_1892_);
v___x_1971_ = l_Lean_indentExpr(v_e_1892_);
v___x_1972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1972_, 0, v___x_1970_);
lean_ctor_set(v___x_1972_, 1, v___x_1971_);
v___x_1973_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(v_cls_1967_, v___x_1972_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_dec_ref_known(v___x_1973_, 1);
v___y_1903_ = v_a_1893_;
v___y_1904_ = v_a_1894_;
v___y_1905_ = v_a_1895_;
v___y_1906_ = v_a_1896_;
v___y_1907_ = v_a_1897_;
v___y_1908_ = v_a_1898_;
v___y_1909_ = v_a_1899_;
v___y_1910_ = v_a_1900_;
goto v___jp_1902_;
}
else
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1981_; 
lean_dec_ref(v_e_1892_);
lean_dec_ref(v_F_1891_);
lean_dec(v_fixedPrefixSize_1890_);
lean_dec(v_recFnName_1889_);
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1976_ = v___x_1973_;
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1973_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1977_ == 0)
{
v___x_1979_ = v___x_1976_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1974_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
}
}
}
v___jp_1902_:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_Lean_Meta_etaExpand(v_e_1892_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v___x_1913_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1912_);
lean_dec_ref_known(v___x_1911_, 1);
v___x_1913_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1889_, v_fixedPrefixSize_1890_, v_F_1891_, v_a_1912_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
return v___x_1913_;
}
else
{
lean_dec_ref(v_F_1891_);
lean_dec(v_fixedPrefixSize_1890_);
lean_dec(v_recFnName_1889_);
return v___x_1911_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(lean_object* v_recFnName_1982_, lean_object* v_fixedPrefixSize_1983_, lean_object* v_F_1984_, lean_object* v_x_1985_, lean_object* v_x_1986_, lean_object* v_x_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
if (lean_obj_tag(v_x_1985_) == 5)
{
lean_object* v_fn_1997_; lean_object* v_arg_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; 
v_fn_1997_ = lean_ctor_get(v_x_1985_, 0);
lean_inc_ref(v_fn_1997_);
v_arg_1998_ = lean_ctor_get(v_x_1985_, 1);
lean_inc_ref(v_arg_1998_);
lean_dec_ref_known(v_x_1985_, 2);
v___x_1999_ = lean_array_set(v_x_1986_, v_x_1987_, v_arg_1998_);
v___x_2000_ = lean_unsigned_to_nat(1u);
v___x_2001_ = lean_nat_sub(v_x_1987_, v___x_2000_);
lean_dec(v_x_1987_);
v_x_1985_ = v_fn_1997_;
v_x_1986_ = v___x_1999_;
v_x_1987_ = v___x_2001_;
goto _start;
}
else
{
lean_object* v___x_2003_; 
lean_dec(v_x_1987_);
lean_inc_ref(v_F_1984_);
lean_inc(v_fixedPrefixSize_1983_);
lean_inc(v_recFnName_1982_);
v___x_2003_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_1982_, v_fixedPrefixSize_1983_, v_F_1984_, v_x_1985_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_a_2004_; size_t v_sz_2005_; size_t v___x_2006_; lean_object* v___x_2007_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_a_2004_);
lean_dec_ref_known(v___x_2003_, 1);
v_sz_2005_ = lean_array_size(v_x_1986_);
v___x_2006_ = ((size_t)0ULL);
v___x_2007_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_1982_, v_fixedPrefixSize_1983_, v_F_1984_, v_sz_2005_, v___x_2006_, v_x_1986_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2016_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2010_ = v___x_2007_;
v_isShared_2011_ = v_isSharedCheck_2016_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_2007_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2016_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2012_; lean_object* v___x_2014_; 
v___x_2012_ = l_Lean_mkAppN(v_a_2004_, v_a_2008_);
lean_dec(v_a_2008_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v___x_2012_);
v___x_2014_ = v___x_2010_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_2012_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
else
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2024_; 
lean_dec(v_a_2004_);
v_a_2017_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2019_ = v___x_2007_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2007_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2017_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
else
{
lean_dec_ref(v_x_1986_);
lean_dec_ref(v_F_1984_);
lean_dec(v_fixedPrefixSize_1983_);
lean_dec(v_recFnName_1982_);
return v___x_2003_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(lean_object* v_recFnName_2025_, lean_object* v_fixedPrefixSize_2026_, lean_object* v_F_2027_, lean_object* v_e_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_){
_start:
{
uint8_t v___x_2038_; 
v___x_2038_ = l_Lean_Expr_isAppOf(v_e_2028_, v_recFnName_2025_);
if (v___x_2038_ == 0)
{
lean_object* v_dummy_2039_; lean_object* v_nargs_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
v_dummy_2039_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
v_nargs_2040_ = l_Lean_Expr_getAppNumArgs(v_e_2028_);
lean_inc(v_nargs_2040_);
v___x_2041_ = lean_mk_array(v_nargs_2040_, v_dummy_2039_);
v___x_2042_ = lean_unsigned_to_nat(1u);
v___x_2043_ = lean_nat_sub(v_nargs_2040_, v___x_2042_);
lean_dec(v_nargs_2040_);
v___x_2044_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(v_recFnName_2025_, v_fixedPrefixSize_2026_, v_F_2027_, v_e_2028_, v___x_2041_, v___x_2043_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_);
return v___x_2044_;
}
else
{
lean_object* v___x_2045_; 
v___x_2045_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2025_, v_fixedPrefixSize_2026_, v_F_2027_, v_e_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_);
return v___x_2045_;
}
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2047_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__0));
v___x_2048_ = l_Lean_stringToMessageData(v___x_2047_);
return v___x_2048_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2050_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__2));
v___x_2051_ = l_Lean_stringToMessageData(v___x_2050_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0(lean_object* v___x_2052_, lean_object* v_b_2053_, lean_object* v_recFnName_2054_, lean_object* v_fixedPrefixSize_2055_, uint8_t v___x_2056_, lean_object* v___x_2057_, lean_object* v_a_2058_, lean_object* v_e_2059_, lean_object* v_xs_2060_, lean_object* v_altBody_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v___x_2078_; uint8_t v___x_2079_; 
v___x_2078_ = lean_array_get_size(v_xs_2060_);
v___x_2079_ = lean_nat_dec_eq(v___x_2078_, v___x_2057_);
if (v___x_2079_ == 0)
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2095_; 
lean_dec_ref(v_altBody_2061_);
lean_dec(v_fixedPrefixSize_2055_);
lean_dec(v_recFnName_2054_);
v___x_2080_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__1);
v___x_2081_ = l_Lean_indentExpr(v_a_2058_);
v___x_2082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2080_);
lean_ctor_set(v___x_2082_, 1, v___x_2081_);
v___x_2083_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___closed__3);
v___x_2084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2082_);
lean_ctor_set(v___x_2084_, 1, v___x_2083_);
v___x_2085_ = l_Lean_indentExpr(v_e_2059_);
v___x_2086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2084_);
lean_ctor_set(v___x_2086_, 1, v___x_2085_);
v___x_2087_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v___x_2086_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2090_ = v___x_2087_;
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2087_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2093_; 
if (v_isShared_2091_ == 0)
{
v___x_2093_ = v___x_2090_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_a_2088_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
else
{
lean_dec_ref(v_e_2059_);
lean_dec_ref(v_a_2058_);
goto v___jp_2071_;
}
v___jp_2071_:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2072_ = lean_array_get_borrowed(v___x_2052_, v_xs_2060_, v_b_2053_);
lean_inc(v___x_2072_);
v___x_2073_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2054_, v_fixedPrefixSize_2055_, v___x_2072_, v_altBody_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v_a_2074_; uint8_t v___x_2075_; uint8_t v___x_2076_; lean_object* v___x_2077_; 
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_a_2074_);
lean_dec_ref_known(v___x_2073_, 1);
v___x_2075_ = 0;
v___x_2076_ = 1;
v___x_2077_ = l_Lean_Meta_mkLambdaFVars(v_xs_2060_, v_a_2074_, v___x_2075_, v___x_2056_, v___x_2075_, v___x_2056_, v___x_2076_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
return v___x_2077_;
}
else
{
return v___x_2073_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___boxed(lean_object** _args){
lean_object* v___x_2096_ = _args[0];
lean_object* v_b_2097_ = _args[1];
lean_object* v_recFnName_2098_ = _args[2];
lean_object* v_fixedPrefixSize_2099_ = _args[3];
lean_object* v___x_2100_ = _args[4];
lean_object* v___x_2101_ = _args[5];
lean_object* v_a_2102_ = _args[6];
lean_object* v_e_2103_ = _args[7];
lean_object* v_xs_2104_ = _args[8];
lean_object* v_altBody_2105_ = _args[9];
lean_object* v___y_2106_ = _args[10];
lean_object* v___y_2107_ = _args[11];
lean_object* v___y_2108_ = _args[12];
lean_object* v___y_2109_ = _args[13];
lean_object* v___y_2110_ = _args[14];
lean_object* v___y_2111_ = _args[15];
lean_object* v___y_2112_ = _args[16];
lean_object* v___y_2113_ = _args[17];
lean_object* v___y_2114_ = _args[18];
_start:
{
uint8_t v___x_65230__boxed_2115_; lean_object* v_res_2116_; 
v___x_65230__boxed_2115_ = lean_unbox(v___x_2100_);
v_res_2116_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0(v___x_2096_, v_b_2097_, v_recFnName_2098_, v_fixedPrefixSize_2099_, v___x_65230__boxed_2115_, v___x_2101_, v_a_2102_, v_e_2103_, v_xs_2104_, v_altBody_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec(v___y_2106_);
lean_dec_ref(v_xs_2104_);
lean_dec(v___x_2101_);
lean_dec(v_b_2097_);
lean_dec_ref(v___x_2096_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(lean_object* v_recFnName_2117_, lean_object* v_fixedPrefixSize_2118_, lean_object* v_e_2119_, lean_object* v_as_2120_, lean_object* v_bs_2121_, lean_object* v_i_2122_, lean_object* v_cs_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v___x_2133_; uint8_t v___x_2134_; 
v___x_2133_ = lean_array_get_size(v_as_2120_);
v___x_2134_ = lean_nat_dec_lt(v_i_2122_, v___x_2133_);
if (v___x_2134_ == 0)
{
lean_object* v___x_2135_; 
lean_dec(v_i_2122_);
lean_dec_ref(v_e_2119_);
lean_dec(v_fixedPrefixSize_2118_);
lean_dec(v_recFnName_2117_);
v___x_2135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2135_, 0, v_cs_2123_);
return v___x_2135_;
}
else
{
lean_object* v___x_2136_; uint8_t v___x_2137_; 
v___x_2136_ = lean_array_get_size(v_bs_2121_);
v___x_2137_ = lean_nat_dec_lt(v_i_2122_, v___x_2136_);
if (v___x_2137_ == 0)
{
lean_object* v___x_2138_; 
lean_dec(v_i_2122_);
lean_dec_ref(v_e_2119_);
lean_dec(v_fixedPrefixSize_2118_);
lean_dec(v_recFnName_2117_);
v___x_2138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2138_, 0, v_cs_2123_);
return v___x_2138_;
}
else
{
lean_object* v___x_2139_; lean_object* v_a_2140_; lean_object* v_b_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___f_2145_; uint8_t v___x_2146_; lean_object* v___x_2147_; 
v___x_2139_ = l_Lean_instInhabitedExpr;
v_a_2140_ = lean_array_fget_borrowed(v_as_2120_, v_i_2122_);
v_b_2141_ = lean_array_fget_borrowed(v_bs_2121_, v_i_2122_);
v___x_2142_ = lean_unsigned_to_nat(1u);
v___x_2143_ = lean_nat_add(v_b_2141_, v___x_2142_);
v___x_2144_ = lean_box(v___x_2137_);
lean_inc_ref(v_e_2119_);
lean_inc_n(v_a_2140_, 2);
lean_inc(v___x_2143_);
lean_inc(v_fixedPrefixSize_2118_);
lean_inc(v_recFnName_2117_);
lean_inc(v_b_2141_);
v___f_2145_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___lam__0___boxed), 19, 8);
lean_closure_set(v___f_2145_, 0, v___x_2139_);
lean_closure_set(v___f_2145_, 1, v_b_2141_);
lean_closure_set(v___f_2145_, 2, v_recFnName_2117_);
lean_closure_set(v___f_2145_, 3, v_fixedPrefixSize_2118_);
lean_closure_set(v___f_2145_, 4, v___x_2144_);
lean_closure_set(v___f_2145_, 5, v___x_2143_);
lean_closure_set(v___f_2145_, 6, v_a_2140_);
lean_closure_set(v___f_2145_, 7, v_e_2119_);
v___x_2146_ = 0;
v___x_2147_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(v_a_2140_, v___x_2143_, v___f_2145_, v___x_2146_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v_a_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
lean_inc(v_a_2148_);
lean_dec_ref_known(v___x_2147_, 1);
v___x_2149_ = lean_nat_add(v_i_2122_, v___x_2142_);
lean_dec(v_i_2122_);
v___x_2150_ = lean_array_push(v_cs_2123_, v_a_2148_);
v_i_2122_ = v___x_2149_;
v_cs_2123_ = v___x_2150_;
goto _start;
}
else
{
lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2159_; 
lean_dec_ref(v_cs_2123_);
lean_dec(v_i_2122_);
lean_dec_ref(v_e_2119_);
lean_dec(v_fixedPrefixSize_2118_);
lean_dec(v_recFnName_2117_);
v_a_2152_ = lean_ctor_get(v___x_2147_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2154_ = v___x_2147_;
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___x_2147_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2157_; 
if (v_isShared_2155_ == 0)
{
v___x_2157_ = v___x_2154_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_a_2152_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(lean_object* v_recFnName_2160_, lean_object* v_fixedPrefixSize_2161_, lean_object* v_F_2162_, lean_object* v_e_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_){
_start:
{
switch(lean_obj_tag(v_e_2163_))
{
case 6:
{
lean_object* v_binderName_2173_; lean_object* v_binderType_2174_; lean_object* v_body_2175_; uint8_t v_binderInfo_2176_; lean_object* v___x_2177_; 
v_binderName_2173_ = lean_ctor_get(v_e_2163_, 0);
lean_inc(v_binderName_2173_);
v_binderType_2174_ = lean_ctor_get(v_e_2163_, 1);
lean_inc_ref(v_binderType_2174_);
v_body_2175_ = lean_ctor_get(v_e_2163_, 2);
lean_inc_ref(v_body_2175_);
v_binderInfo_2176_ = lean_ctor_get_uint8(v_e_2163_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2163_, 3);
lean_inc_ref(v_F_2162_);
lean_inc(v_fixedPrefixSize_2161_);
lean_inc(v_recFnName_2160_);
v___x_2177_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2160_, v_fixedPrefixSize_2161_, v_F_2162_, v_binderType_2174_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v___f_2179_; uint8_t v___x_2180_; lean_object* v___x_2181_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_a_2178_);
lean_dec_ref_known(v___x_2177_, 1);
v___f_2179_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__0___boxed), 14, 4);
lean_closure_set(v___f_2179_, 0, v_body_2175_);
lean_closure_set(v___f_2179_, 1, v_recFnName_2160_);
lean_closure_set(v___f_2179_, 2, v_fixedPrefixSize_2161_);
lean_closure_set(v___f_2179_, 3, v_F_2162_);
v___x_2180_ = 0;
v___x_2181_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_binderName_2173_, v_binderInfo_2176_, v_a_2178_, v___f_2179_, v___x_2180_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
return v___x_2181_;
}
else
{
lean_dec_ref(v_body_2175_);
lean_dec(v_binderName_2173_);
lean_dec_ref(v_F_2162_);
lean_dec(v_fixedPrefixSize_2161_);
lean_dec(v_recFnName_2160_);
return v___x_2177_;
}
}
case 7:
{
lean_object* v_binderName_2182_; lean_object* v_binderType_2183_; lean_object* v_body_2184_; uint8_t v_binderInfo_2185_; lean_object* v___x_2186_; 
v_binderName_2182_ = lean_ctor_get(v_e_2163_, 0);
lean_inc(v_binderName_2182_);
v_binderType_2183_ = lean_ctor_get(v_e_2163_, 1);
lean_inc_ref(v_binderType_2183_);
v_body_2184_ = lean_ctor_get(v_e_2163_, 2);
lean_inc_ref(v_body_2184_);
v_binderInfo_2185_ = lean_ctor_get_uint8(v_e_2163_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2163_, 3);
lean_inc_ref(v_F_2162_);
lean_inc(v_fixedPrefixSize_2161_);
lean_inc(v_recFnName_2160_);
v___x_2186_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2160_, v_fixedPrefixSize_2161_, v_F_2162_, v_binderType_2183_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v_a_2187_; lean_object* v___f_2188_; uint8_t v___x_2189_; lean_object* v___x_2190_; 
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
lean_inc(v_a_2187_);
lean_dec_ref_known(v___x_2186_, 1);
v___f_2188_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__1___boxed), 14, 4);
lean_closure_set(v___f_2188_, 0, v_body_2184_);
lean_closure_set(v___f_2188_, 1, v_recFnName_2160_);
lean_closure_set(v___f_2188_, 2, v_fixedPrefixSize_2161_);
lean_closure_set(v___f_2188_, 3, v_F_2162_);
v___x_2189_ = 0;
v___x_2190_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_binderName_2182_, v_binderInfo_2185_, v_a_2187_, v___f_2188_, v___x_2189_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
return v___x_2190_;
}
else
{
lean_dec_ref(v_body_2184_);
lean_dec(v_binderName_2182_);
lean_dec_ref(v_F_2162_);
lean_dec(v_fixedPrefixSize_2161_);
lean_dec(v_recFnName_2160_);
return v___x_2186_;
}
}
case 8:
{
lean_object* v_declName_2191_; lean_object* v_type_2192_; lean_object* v_value_2193_; lean_object* v_body_2194_; uint8_t v_nondep_2195_; lean_object* v___x_2196_; 
v_declName_2191_ = lean_ctor_get(v_e_2163_, 0);
lean_inc(v_declName_2191_);
v_type_2192_ = lean_ctor_get(v_e_2163_, 1);
lean_inc_ref(v_type_2192_);
v_value_2193_ = lean_ctor_get(v_e_2163_, 2);
lean_inc_ref(v_value_2193_);
v_body_2194_ = lean_ctor_get(v_e_2163_, 3);
lean_inc_ref(v_body_2194_);
v_nondep_2195_ = lean_ctor_get_uint8(v_e_2163_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2163_, 4);
lean_inc_ref(v_F_2162_);
lean_inc(v_fixedPrefixSize_2161_);
lean_inc(v_recFnName_2160_);
v___x_2196_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2160_, v_fixedPrefixSize_2161_, v_F_2162_, v_type_2192_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v_a_2197_; lean_object* v___x_2198_; 
v_a_2197_ = lean_ctor_get(v___x_2196_, 0);
lean_inc(v_a_2197_);
lean_dec_ref_known(v___x_2196_, 1);
lean_inc_ref(v_F_2162_);
lean_inc(v_fixedPrefixSize_2161_);
lean_inc(v_recFnName_2160_);
v___x_2198_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2160_, v_fixedPrefixSize_2161_, v_F_2162_, v_value_2193_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; lean_object* v___f_2200_; uint8_t v___x_2201_; uint8_t v___x_2202_; lean_object* v___x_2203_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_a_2199_);
lean_dec_ref_known(v___x_2198_, 1);
v___f_2200_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2___boxed), 14, 4);
lean_closure_set(v___f_2200_, 0, v_body_2194_);
lean_closure_set(v___f_2200_, 1, v_recFnName_2160_);
lean_closure_set(v___f_2200_, 2, v_fixedPrefixSize_2161_);
lean_closure_set(v___f_2200_, 3, v_F_2162_);
v___x_2201_ = 0;
v___x_2202_ = 0;
v___x_2203_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11(v_declName_2191_, v_a_2197_, v_a_2199_, v___f_2200_, v_nondep_2195_, v___x_2201_, v___x_2202_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
return v___x_2203_;
}
else
{
lean_dec(v_a_2197_);
lean_dec_ref(v_body_2194_);
lean_dec(v_declName_2191_);
lean_dec_ref(v_F_2162_);
lean_dec(v_fixedPrefixSize_2161_);
lean_dec(v_recFnName_2160_);
return v___x_2198_;
}
}
else
{
lean_dec_ref(v_body_2194_);
lean_dec_ref(v_value_2193_);
lean_dec(v_declName_2191_);
lean_dec_ref(v_F_2162_);
lean_dec(v_fixedPrefixSize_2161_);
lean_dec(v_recFnName_2160_);
return v___x_2196_;
}
}
case 10:
{
lean_object* v_data_2204_; lean_object* v_expr_2205_; lean_object* v___x_2206_; 
v_data_2204_ = lean_ctor_get(v_e_2163_, 0);
lean_inc(v_data_2204_);
v_expr_2205_ = lean_ctor_get(v_e_2163_, 1);
lean_inc_ref(v_expr_2205_);
v___x_2206_ = l_Lean_getRecAppSyntax_x3f(v_e_2163_);
lean_dec_ref_known(v_e_2163_, 2);
if (lean_obj_tag(v___x_2206_) == 1)
{
lean_object* v_val_2207_; lean_object* v_fileName_2208_; lean_object* v_fileMap_2209_; lean_object* v_options_2210_; lean_object* v_currRecDepth_2211_; lean_object* v_maxRecDepth_2212_; lean_object* v_ref_2213_; lean_object* v_currNamespace_2214_; lean_object* v_openDecls_2215_; lean_object* v_initHeartbeats_2216_; lean_object* v_maxHeartbeats_2217_; lean_object* v_quotContext_2218_; lean_object* v_currMacroScope_2219_; uint8_t v_diag_2220_; lean_object* v_cancelTk_x3f_2221_; uint8_t v_suppressElabErrors_2222_; lean_object* v_inheritedTraceOptions_2223_; lean_object* v_ref_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
lean_dec(v_data_2204_);
v_val_2207_ = lean_ctor_get(v___x_2206_, 0);
lean_inc(v_val_2207_);
lean_dec_ref_known(v___x_2206_, 1);
v_fileName_2208_ = lean_ctor_get(v_a_2170_, 0);
v_fileMap_2209_ = lean_ctor_get(v_a_2170_, 1);
v_options_2210_ = lean_ctor_get(v_a_2170_, 2);
v_currRecDepth_2211_ = lean_ctor_get(v_a_2170_, 3);
v_maxRecDepth_2212_ = lean_ctor_get(v_a_2170_, 4);
v_ref_2213_ = lean_ctor_get(v_a_2170_, 5);
v_currNamespace_2214_ = lean_ctor_get(v_a_2170_, 6);
v_openDecls_2215_ = lean_ctor_get(v_a_2170_, 7);
v_initHeartbeats_2216_ = lean_ctor_get(v_a_2170_, 8);
v_maxHeartbeats_2217_ = lean_ctor_get(v_a_2170_, 9);
v_quotContext_2218_ = lean_ctor_get(v_a_2170_, 10);
v_currMacroScope_2219_ = lean_ctor_get(v_a_2170_, 11);
v_diag_2220_ = lean_ctor_get_uint8(v_a_2170_, sizeof(void*)*14);
v_cancelTk_x3f_2221_ = lean_ctor_get(v_a_2170_, 12);
v_suppressElabErrors_2222_ = lean_ctor_get_uint8(v_a_2170_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2223_ = lean_ctor_get(v_a_2170_, 13);
v_ref_2224_ = l_Lean_replaceRef(v_val_2207_, v_ref_2213_);
lean_dec(v_val_2207_);
lean_inc_ref(v_inheritedTraceOptions_2223_);
lean_inc(v_cancelTk_x3f_2221_);
lean_inc(v_currMacroScope_2219_);
lean_inc(v_quotContext_2218_);
lean_inc(v_maxHeartbeats_2217_);
lean_inc(v_initHeartbeats_2216_);
lean_inc(v_openDecls_2215_);
lean_inc(v_currNamespace_2214_);
lean_inc(v_maxRecDepth_2212_);
lean_inc(v_currRecDepth_2211_);
lean_inc_ref(v_options_2210_);
lean_inc_ref(v_fileMap_2209_);
lean_inc_ref(v_fileName_2208_);
v___x_2225_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2225_, 0, v_fileName_2208_);
lean_ctor_set(v___x_2225_, 1, v_fileMap_2209_);
lean_ctor_set(v___x_2225_, 2, v_options_2210_);
lean_ctor_set(v___x_2225_, 3, v_currRecDepth_2211_);
lean_ctor_set(v___x_2225_, 4, v_maxRecDepth_2212_);
lean_ctor_set(v___x_2225_, 5, v_ref_2224_);
lean_ctor_set(v___x_2225_, 6, v_currNamespace_2214_);
lean_ctor_set(v___x_2225_, 7, v_openDecls_2215_);
lean_ctor_set(v___x_2225_, 8, v_initHeartbeats_2216_);
lean_ctor_set(v___x_2225_, 9, v_maxHeartbeats_2217_);
lean_ctor_set(v___x_2225_, 10, v_quotContext_2218_);
lean_ctor_set(v___x_2225_, 11, v_currMacroScope_2219_);
lean_ctor_set(v___x_2225_, 12, v_cancelTk_x3f_2221_);
lean_ctor_set(v___x_2225_, 13, v_inheritedTraceOptions_2223_);
lean_ctor_set_uint8(v___x_2225_, sizeof(void*)*14, v_diag_2220_);
lean_ctor_set_uint8(v___x_2225_, sizeof(void*)*14 + 1, v_suppressElabErrors_2222_);
v___x_2226_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2160_, v_fixedPrefixSize_2161_, v_F_2162_, v_expr_2205_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v___x_2225_, v_a_2171_);
lean_dec_ref_known(v___x_2225_, 14);
return v___x_2226_;
}
else
{
lean_object* v___x_2227_; 
lean_dec(v___x_2206_);
v___x_2227_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2160_, v_fixedPrefixSize_2161_, v_F_2162_, v_expr_2205_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2236_; 
v_a_2228_ = lean_ctor_get(v___x_2227_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2230_ = v___x_2227_;
v_isShared_2231_ = v_isSharedCheck_2236_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_dec(v___x_2227_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2236_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2232_; lean_object* v___x_2234_; 
v___x_2232_ = l_Lean_mkMData(v_data_2204_, v_a_2228_);
if (v_isShared_2231_ == 0)
{
lean_ctor_set(v___x_2230_, 0, v___x_2232_);
v___x_2234_ = v___x_2230_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2232_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
else
{
lean_dec(v_data_2204_);
return v___x_2227_;
}
}
}
case 11:
{
lean_object* v_typeName_2237_; lean_object* v_idx_2238_; lean_object* v_struct_2239_; lean_object* v___x_2240_; 
v_typeName_2237_ = lean_ctor_get(v_e_2163_, 0);
lean_inc(v_typeName_2237_);
v_idx_2238_ = lean_ctor_get(v_e_2163_, 1);
lean_inc(v_idx_2238_);
v_struct_2239_ = lean_ctor_get(v_e_2163_, 2);
lean_inc_ref(v_struct_2239_);
lean_dec_ref_known(v_e_2163_, 3);
v___x_2240_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2160_, v_fixedPrefixSize_2161_, v_F_2162_, v_struct_2239_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2249_; 
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2243_ = v___x_2240_;
v_isShared_2244_ = v_isSharedCheck_2249_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2240_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2249_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2245_; lean_object* v___x_2247_; 
v___x_2245_ = l_Lean_mkProj(v_typeName_2237_, v_idx_2238_, v_a_2241_);
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 0, v___x_2245_);
v___x_2247_ = v___x_2243_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v___x_2245_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
else
{
lean_dec(v_idx_2238_);
lean_dec(v_typeName_2237_);
return v___x_2240_;
}
}
case 4:
{
uint8_t v___x_2250_; 
v___x_2250_ = l_Lean_Expr_isConstOf(v_e_2163_, v_recFnName_2160_);
if (v___x_2250_ == 0)
{
lean_object* v___x_2251_; 
lean_dec_ref(v_F_2162_);
lean_dec(v_fixedPrefixSize_2161_);
lean_dec(v_recFnName_2160_);
v___x_2251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2251_, 0, v_e_2163_);
return v___x_2251_;
}
else
{
lean_object* v___x_2252_; 
v___x_2252_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2160_, v_fixedPrefixSize_2161_, v_F_2162_, v_e_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
return v___x_2252_;
}
}
case 5:
{
uint8_t v___x_2253_; lean_object* v___x_2254_; 
v___x_2253_ = 1;
lean_inc_ref(v_e_2163_);
v___x_2254_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13(v_e_2163_, v___x_2253_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_object* v_a_2255_; 
v_a_2255_ = lean_ctor_get(v___x_2254_, 0);
lean_inc(v_a_2255_);
lean_dec_ref_known(v___x_2254_, 1);
if (lean_obj_tag(v_a_2255_) == 0)
{
lean_object* v___x_2256_; 
v___x_2256_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2160_, v_fixedPrefixSize_2161_, v_F_2162_, v_e_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
return v___x_2256_;
}
else
{
lean_object* v_val_2257_; lean_object* v___x_2258_; 
v_val_2257_ = lean_ctor_get(v_a_2255_, 0);
lean_inc(v_val_2257_);
lean_dec_ref_known(v_a_2255_, 1);
lean_inc_ref(v_F_2162_);
v___x_2258_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_val_2257_, v_F_2162_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_object* v_a_2259_; 
v_a_2259_ = lean_ctor_get(v___x_2258_, 0);
lean_inc(v_a_2259_);
lean_dec_ref_known(v___x_2258_, 1);
if (lean_obj_tag(v_a_2259_) == 1)
{
lean_object* v_val_2260_; lean_object* v_toMatcherInfo_2261_; lean_object* v_matcherName_2262_; lean_object* v_matcherLevels_2263_; lean_object* v_params_2264_; lean_object* v_motive_2265_; lean_object* v_discrs_2266_; lean_object* v_alts_2267_; lean_object* v_remaining_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v_val_2260_ = lean_ctor_get(v_a_2259_, 0);
lean_inc(v_val_2260_);
lean_dec_ref_known(v_a_2259_, 1);
v_toMatcherInfo_2261_ = lean_ctor_get(v_val_2260_, 0);
lean_inc_ref(v_toMatcherInfo_2261_);
v_matcherName_2262_ = lean_ctor_get(v_val_2260_, 1);
lean_inc(v_matcherName_2262_);
v_matcherLevels_2263_ = lean_ctor_get(v_val_2260_, 2);
lean_inc_ref(v_matcherLevels_2263_);
v_params_2264_ = lean_ctor_get(v_val_2260_, 3);
lean_inc_ref(v_params_2264_);
v_motive_2265_ = lean_ctor_get(v_val_2260_, 4);
lean_inc_ref(v_motive_2265_);
v_discrs_2266_ = lean_ctor_get(v_val_2260_, 5);
lean_inc_ref(v_discrs_2266_);
v_alts_2267_ = lean_ctor_get(v_val_2260_, 6);
lean_inc_ref(v_alts_2267_);
v_remaining_2268_ = lean_ctor_get(v_val_2260_, 7);
lean_inc_ref(v_remaining_2268_);
v___x_2269_ = l_Lean_Meta_MatcherApp_altNumParams(v_val_2260_);
v___x_2270_ = lean_unsigned_to_nat(0u);
v___x_2271_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
lean_inc(v_fixedPrefixSize_2161_);
lean_inc(v_recFnName_2160_);
v___x_2272_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(v_recFnName_2160_, v_fixedPrefixSize_2161_, v_e_2163_, v_alts_2267_, v___x_2269_, v___x_2270_, v___x_2271_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
lean_dec_ref(v___x_2269_);
lean_dec_ref(v_alts_2267_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_object* v_a_2273_; size_t v_sz_2274_; size_t v___x_2275_; lean_object* v___x_2276_; 
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
lean_inc(v_a_2273_);
lean_dec_ref_known(v___x_2272_, 1);
v_sz_2274_ = lean_array_size(v_discrs_2266_);
v___x_2275_ = ((size_t)0ULL);
v___x_2276_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_2160_, v_fixedPrefixSize_2161_, v_F_2162_, v_sz_2274_, v___x_2275_, v_discrs_2266_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2286_; 
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2279_ = v___x_2276_;
v_isShared_2280_ = v_isSharedCheck_2286_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2276_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2286_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2284_; 
v___x_2281_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2281_, 0, v_toMatcherInfo_2261_);
lean_ctor_set(v___x_2281_, 1, v_matcherName_2262_);
lean_ctor_set(v___x_2281_, 2, v_matcherLevels_2263_);
lean_ctor_set(v___x_2281_, 3, v_params_2264_);
lean_ctor_set(v___x_2281_, 4, v_motive_2265_);
lean_ctor_set(v___x_2281_, 5, v_a_2277_);
lean_ctor_set(v___x_2281_, 6, v_a_2273_);
lean_ctor_set(v___x_2281_, 7, v_remaining_2268_);
v___x_2282_ = l_Lean_Meta_MatcherApp_toExpr(v___x_2281_);
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 0, v___x_2282_);
v___x_2284_ = v___x_2279_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v___x_2282_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
}
else
{
lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2294_; 
lean_dec(v_a_2273_);
lean_dec_ref(v_remaining_2268_);
lean_dec_ref(v_motive_2265_);
lean_dec_ref(v_params_2264_);
lean_dec_ref(v_matcherLevels_2263_);
lean_dec(v_matcherName_2262_);
lean_dec_ref(v_toMatcherInfo_2261_);
v_a_2287_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2289_ = v___x_2276_;
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2276_);
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
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2302_; 
lean_dec_ref(v_remaining_2268_);
lean_dec_ref(v_discrs_2266_);
lean_dec_ref(v_motive_2265_);
lean_dec_ref(v_params_2264_);
lean_dec_ref(v_matcherLevels_2263_);
lean_dec(v_matcherName_2262_);
lean_dec_ref(v_toMatcherInfo_2261_);
lean_dec_ref(v_F_2162_);
lean_dec(v_fixedPrefixSize_2161_);
lean_dec(v_recFnName_2160_);
v_a_2295_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2297_ = v___x_2272_;
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___x_2272_);
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
lean_object* v___x_2303_; 
lean_dec(v_a_2259_);
v___x_2303_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2160_, v_fixedPrefixSize_2161_, v_F_2162_, v_e_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
return v___x_2303_;
}
}
else
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2311_; 
lean_dec_ref_known(v_e_2163_, 2);
lean_dec_ref(v_F_2162_);
lean_dec(v_fixedPrefixSize_2161_);
lean_dec(v_recFnName_2160_);
v_a_2304_ = lean_ctor_get(v___x_2258_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2306_ = v___x_2258_;
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2258_);
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
else
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2319_; 
lean_dec_ref_known(v_e_2163_, 2);
lean_dec_ref(v_F_2162_);
lean_dec(v_fixedPrefixSize_2161_);
lean_dec(v_recFnName_2160_);
v_a_2312_ = lean_ctor_get(v___x_2254_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2314_ = v___x_2254_;
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___x_2254_);
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
default: 
{
lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
lean_dec_ref(v_F_2162_);
lean_dec(v_fixedPrefixSize_2161_);
v___x_2320_ = lean_unsigned_to_nat(1u);
v___x_2321_ = lean_mk_empty_array_with_capacity(v___x_2320_);
v___x_2322_ = lean_array_push(v___x_2321_, v_recFnName_2160_);
lean_inc_ref(v_e_2163_);
v___x_2323_ = l_Lean_Elab_ensureNoRecFn(v___x_2322_, v_e_2163_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2330_; 
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2330_ == 0)
{
lean_object* v_unused_2331_; 
v_unused_2331_ = lean_ctor_get(v___x_2323_, 0);
lean_dec(v_unused_2331_);
v___x_2325_ = v___x_2323_;
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
else
{
lean_dec(v___x_2323_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2328_; 
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 0, v_e_2163_);
v___x_2328_ = v___x_2325_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_e_2163_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
else
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
lean_dec_ref(v_e_2163_);
v_a_2332_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2334_ = v___x_2323_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2323_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2337_; 
if (v_isShared_2335_ == 0)
{
v___x_2337_ = v___x_2334_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2332_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(lean_object* v_recFnName_2340_, lean_object* v_fixedPrefixSize_2341_, lean_object* v_F_2342_, lean_object* v_e_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_){
_start:
{
lean_object* v___x_2353_; 
lean_inc_ref(v_e_2343_);
lean_inc(v_recFnName_2340_);
v___x_2353_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_containsRecFn___redArg(v_recFnName_2340_, v_e_2343_, v_a_2344_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2461_; 
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2356_ = v___x_2353_;
v_isShared_2357_ = v_isSharedCheck_2461_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2353_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2461_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
uint8_t v___x_2358_; 
v___x_2358_ = lean_unbox(v_a_2354_);
lean_dec(v_a_2354_);
if (v___x_2358_ == 0)
{
lean_object* v___x_2360_; 
lean_dec_ref(v_F_2342_);
lean_dec(v_fixedPrefixSize_2341_);
lean_dec(v_recFnName_2340_);
if (v_isShared_2357_ == 0)
{
lean_ctor_set(v___x_2356_, 0, v_e_2343_);
v___x_2360_ = v___x_2356_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_e_2343_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
else
{
lean_object* v___x_2362_; uint8_t v___x_2363_; lean_object* v___y_2365_; lean_object* v___y_2366_; lean_object* v___y_2367_; lean_object* v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v___x_2439_; 
lean_del_object(v___x_2356_);
v___x_2362_ = lean_st_ref_get(v_a_2345_);
v___x_2363_ = 0;
v___x_2439_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v___x_2362_, v_e_2343_);
lean_dec(v___x_2362_);
if (lean_obj_tag(v___x_2439_) == 1)
{
lean_object* v_val_2440_; lean_object* v_fst_2441_; lean_object* v_snd_2442_; lean_object* v___x_2443_; 
v_val_2440_ = lean_ctor_get(v___x_2439_, 0);
lean_inc(v_val_2440_);
lean_dec_ref_known(v___x_2439_, 1);
v_fst_2441_ = lean_ctor_get(v_val_2440_, 0);
lean_inc(v_fst_2441_);
v_snd_2442_ = lean_ctor_get(v_val_2440_, 1);
lean_inc(v_snd_2442_);
lean_dec(v_val_2440_);
v___x_2443_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_LCtxId_isValid___redArg(v_snd_2442_, v_a_2348_);
lean_dec(v_snd_2442_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2452_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2446_ = v___x_2443_;
v_isShared_2447_ = v_isSharedCheck_2452_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2443_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2452_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
uint8_t v___x_2448_; 
v___x_2448_ = lean_unbox(v_a_2444_);
lean_dec(v_a_2444_);
if (v___x_2448_ == 0)
{
lean_del_object(v___x_2446_);
lean_dec(v_fst_2441_);
v___y_2365_ = v_a_2344_;
v___y_2366_ = v_a_2345_;
v___y_2367_ = v_a_2346_;
v___y_2368_ = v_a_2347_;
v___y_2369_ = v_a_2348_;
v___y_2370_ = v_a_2349_;
v___y_2371_ = v_a_2350_;
v___y_2372_ = v_a_2351_;
goto v___jp_2364_;
}
else
{
lean_object* v___x_2450_; 
lean_dec_ref(v_e_2343_);
lean_dec_ref(v_F_2342_);
lean_dec(v_fixedPrefixSize_2341_);
lean_dec(v_recFnName_2340_);
if (v_isShared_2447_ == 0)
{
lean_ctor_set(v___x_2446_, 0, v_fst_2441_);
v___x_2450_ = v___x_2446_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_fst_2441_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
}
}
else
{
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2460_; 
lean_dec(v_fst_2441_);
lean_dec_ref(v_e_2343_);
lean_dec_ref(v_F_2342_);
lean_dec(v_fixedPrefixSize_2341_);
lean_dec(v_recFnName_2340_);
v_a_2453_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2455_ = v___x_2443_;
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2443_);
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
}
else
{
lean_dec(v___x_2439_);
v___y_2365_ = v_a_2344_;
v___y_2366_ = v_a_2345_;
v___y_2367_ = v_a_2346_;
v___y_2368_ = v_a_2347_;
v___y_2369_ = v_a_2348_;
v___y_2370_ = v_a_2349_;
v___y_2371_ = v_a_2350_;
v___y_2372_ = v_a_2351_;
goto v___jp_2364_;
}
v___jp_2364_:
{
lean_object* v___x_2373_; 
lean_inc_ref(v_e_2343_);
v___x_2373_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(v_recFnName_2340_, v_fixedPrefixSize_2341_, v_F_2342_, v_e_2343_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_object* v_a_2374_; lean_object* v___x_2375_; 
v_a_2374_ = lean_ctor_get(v___x_2373_, 0);
lean_inc(v_a_2374_);
lean_dec_ref_known(v___x_2373_, 1);
v___x_2375_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId(v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
if (lean_obj_tag(v___x_2375_) == 0)
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2430_; 
v_a_2376_ = lean_ctor_get(v___x_2375_, 0);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2378_ = v___x_2375_;
v_isShared_2379_ = v_isSharedCheck_2430_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2375_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2430_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v_options_2384_; lean_object* v___x_2385_; uint8_t v___x_2386_; 
v___x_2380_ = lean_st_ref_take(v___y_2366_);
lean_inc(v_a_2374_);
v___x_2381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2381_, 0, v_a_2374_);
lean_ctor_set(v___x_2381_, 1, v_a_2376_);
lean_inc_ref(v_e_2343_);
v___x_2382_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4___redArg(v___x_2380_, v_e_2343_, v___x_2381_);
v___x_2383_ = lean_st_ref_set(v___y_2366_, v___x_2382_);
v_options_2384_ = lean_ctor_get(v___y_2371_, 2);
v___x_2385_ = l_Lean_Elab_WF_debug_definition_wf_replaceRecApps;
v___x_2386_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v_options_2384_, v___x_2385_);
if (v___x_2386_ == 0)
{
lean_object* v___x_2388_; 
lean_dec_ref(v_e_2343_);
if (v_isShared_2379_ == 0)
{
lean_ctor_set(v___x_2378_, 0, v_a_2374_);
v___x_2388_ = v___x_2378_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_a_2374_);
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
lean_object* v_keyedConfig_2390_; uint8_t v_trackZetaDelta_2391_; lean_object* v_zetaDeltaSet_2392_; lean_object* v_lctx_2393_; lean_object* v_localInstances_2394_; lean_object* v_defEqCtx_x3f_2395_; lean_object* v_synthPendingDepth_2396_; lean_object* v_customCanUnfoldPredicate_x3f_2397_; uint8_t v_univApprox_2398_; uint8_t v_inTypeClassResolution_2399_; uint8_t v_cacheInferType_2400_; lean_object* v___f_2401_; uint8_t v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
lean_del_object(v___x_2378_);
v_keyedConfig_2390_ = lean_ctor_get(v___y_2369_, 0);
v_trackZetaDelta_2391_ = lean_ctor_get_uint8(v___y_2369_, sizeof(void*)*7);
v_zetaDeltaSet_2392_ = lean_ctor_get(v___y_2369_, 1);
v_lctx_2393_ = lean_ctor_get(v___y_2369_, 2);
v_localInstances_2394_ = lean_ctor_get(v___y_2369_, 3);
v_defEqCtx_x3f_2395_ = lean_ctor_get(v___y_2369_, 4);
v_synthPendingDepth_2396_ = lean_ctor_get(v___y_2369_, 5);
v_customCanUnfoldPredicate_x3f_2397_ = lean_ctor_get(v___y_2369_, 6);
v_univApprox_2398_ = lean_ctor_get_uint8(v___y_2369_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2399_ = lean_ctor_get_uint8(v___y_2369_, sizeof(void*)*7 + 2);
v_cacheInferType_2400_ = lean_ctor_get_uint8(v___y_2369_, sizeof(void*)*7 + 3);
lean_inc(v_a_2374_);
v___f_2401_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___lam__0___boxed), 11, 2);
lean_closure_set(v___f_2401_, 0, v_a_2374_);
lean_closure_set(v___f_2401_, 1, v_e_2343_);
v___x_2402_ = 0;
lean_inc_ref(v_keyedConfig_2390_);
v___x_2403_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2402_, v_keyedConfig_2390_);
lean_inc(v_customCanUnfoldPredicate_x3f_2397_);
lean_inc(v_synthPendingDepth_2396_);
lean_inc(v_defEqCtx_x3f_2395_);
lean_inc_ref(v_localInstances_2394_);
lean_inc_ref(v_lctx_2393_);
lean_inc(v_zetaDeltaSet_2392_);
v___x_2404_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2404_, 0, v___x_2403_);
lean_ctor_set(v___x_2404_, 1, v_zetaDeltaSet_2392_);
lean_ctor_set(v___x_2404_, 2, v_lctx_2393_);
lean_ctor_set(v___x_2404_, 3, v_localInstances_2394_);
lean_ctor_set(v___x_2404_, 4, v_defEqCtx_x3f_2395_);
lean_ctor_set(v___x_2404_, 5, v_synthPendingDepth_2396_);
lean_ctor_set(v___x_2404_, 6, v_customCanUnfoldPredicate_x3f_2397_);
lean_ctor_set_uint8(v___x_2404_, sizeof(void*)*7, v_trackZetaDelta_2391_);
lean_ctor_set_uint8(v___x_2404_, sizeof(void*)*7 + 1, v_univApprox_2398_);
lean_ctor_set_uint8(v___x_2404_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2399_);
lean_ctor_set_uint8(v___x_2404_, sizeof(void*)*7 + 3, v_cacheInferType_2400_);
v___x_2405_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v___f_2401_, v___x_2363_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___x_2404_, v___y_2370_, v___y_2371_, v___y_2372_);
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
lean_ctor_set(v___x_2407_, 0, v_a_2374_);
v___x_2410_ = v___x_2407_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_a_2374_);
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
lean_ctor_set(v___x_2415_, 0, v_a_2374_);
v___x_2418_ = v___x_2415_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_a_2374_);
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
lean_dec(v_a_2374_);
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
}
else
{
lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2438_; 
lean_dec(v_a_2374_);
lean_dec_ref(v_e_2343_);
v_a_2431_ = lean_ctor_get(v___x_2375_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2433_ = v___x_2375_;
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_dec(v___x_2375_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2436_; 
if (v_isShared_2434_ == 0)
{
v___x_2436_ = v___x_2433_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_a_2431_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
}
else
{
lean_dec_ref(v_e_2343_);
return v___x_2373_;
}
}
}
}
}
else
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
lean_dec_ref(v_e_2343_);
lean_dec_ref(v_F_2342_);
lean_dec(v_fixedPrefixSize_2341_);
lean_dec(v_recFnName_2340_);
v_a_2462_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2353_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2353_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2462_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___lam__2(lean_object* v_body_2470_, lean_object* v_recFnName_2471_, lean_object* v_fixedPrefixSize_2472_, lean_object* v_F_2473_, lean_object* v_x_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; 
v___x_2484_ = lean_expr_instantiate1(v_body_2470_, v_x_2474_);
v___x_2485_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2471_, v_fixedPrefixSize_2472_, v_F_2473_, v___x_2484_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
return v___x_2485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp___boxed(lean_object* v_recFnName_2486_, lean_object* v_fixedPrefixSize_2487_, lean_object* v_F_2488_, lean_object* v_e_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp(v_recFnName_2486_, v_fixedPrefixSize_2487_, v_F_2488_, v_e_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_);
lean_dec(v_a_2497_);
lean_dec_ref(v_a_2496_);
lean_dec(v_a_2495_);
lean_dec_ref(v_a_2494_);
lean_dec(v_a_2493_);
lean_dec_ref(v_a_2492_);
lean_dec(v_a_2491_);
lean_dec(v_a_2490_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1___boxed(lean_object* v_recFnName_2500_, lean_object* v_fixedPrefixSize_2501_, lean_object* v_F_2502_, lean_object* v_sz_2503_, lean_object* v_i_2504_, lean_object* v_bs_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_){
_start:
{
size_t v_sz_boxed_2515_; size_t v_i_boxed_2516_; lean_object* v_res_2517_; 
v_sz_boxed_2515_ = lean_unbox_usize(v_sz_2503_);
lean_dec(v_sz_2503_);
v_i_boxed_2516_ = lean_unbox_usize(v_i_2504_);
lean_dec(v_i_2504_);
v_res_2517_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__1(v_recFnName_2500_, v_fixedPrefixSize_2501_, v_F_2502_, v_sz_boxed_2515_, v_i_boxed_2516_, v_bs_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_);
lean_dec(v___y_2513_);
lean_dec_ref(v___y_2512_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
lean_dec(v___y_2509_);
lean_dec_ref(v___y_2508_);
lean_dec(v___y_2507_);
lean_dec(v___y_2506_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16___boxed(lean_object* v_recFnName_2518_, lean_object* v_fixedPrefixSize_2519_, lean_object* v_F_2520_, lean_object* v_x_2521_, lean_object* v_x_2522_, lean_object* v_x_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_){
_start:
{
lean_object* v_res_2533_; 
v_res_2533_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processApp_spec__16(v_recFnName_2518_, v_fixedPrefixSize_2519_, v_F_2520_, v_x_2521_, v_x_2522_, v_x_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
lean_dec(v___y_2525_);
lean_dec(v___y_2524_);
return v_res_2533_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14___boxed(lean_object* v_recFnName_2534_, lean_object* v_fixedPrefixSize_2535_, lean_object* v_e_2536_, lean_object* v_as_2537_, lean_object* v_bs_2538_, lean_object* v_i_2539_, lean_object* v_cs_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_){
_start:
{
lean_object* v_res_2550_; 
v_res_2550_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__14(v_recFnName_2534_, v_fixedPrefixSize_2535_, v_e_2536_, v_as_2537_, v_bs_2538_, v_i_2539_, v_cs_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec(v___y_2542_);
lean_dec(v___y_2541_);
lean_dec_ref(v_bs_2538_);
lean_dec_ref(v_as_2537_);
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop___boxed(lean_object* v_recFnName_2551_, lean_object* v_fixedPrefixSize_2552_, lean_object* v_F_2553_, lean_object* v_e_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_){
_start:
{
lean_object* v_res_2564_; 
v_res_2564_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_2551_, v_fixedPrefixSize_2552_, v_F_2553_, v_e_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___boxed(lean_object* v_recFnName_2565_, lean_object* v_fixedPrefixSize_2566_, lean_object* v_F_2567_, lean_object* v_e_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_){
_start:
{
lean_object* v_res_2578_; 
v_res_2578_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec(v_recFnName_2565_, v_fixedPrefixSize_2566_, v_F_2567_, v_e_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_);
lean_dec(v_a_2576_);
lean_dec_ref(v_a_2575_);
lean_dec(v_a_2574_);
lean_dec_ref(v_a_2573_);
lean_dec(v_a_2572_);
lean_dec_ref(v_a_2571_);
lean_dec(v_a_2570_);
lean_dec(v_a_2569_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo___boxed(lean_object* v_recFnName_2579_, lean_object* v_fixedPrefixSize_2580_, lean_object* v_F_2581_, lean_object* v_e_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo(v_recFnName_2579_, v_fixedPrefixSize_2580_, v_F_2581_, v_e_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_);
lean_dec(v_a_2590_);
lean_dec_ref(v_a_2589_);
lean_dec(v_a_2588_);
lean_dec_ref(v_a_2587_);
lean_dec(v_a_2586_);
lean_dec_ref(v_a_2585_);
lean_dec(v_a_2584_);
lean_dec(v_a_2583_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7(lean_object* v_00_u03b1_2593_, lean_object* v_k_2594_, uint8_t v_allowLevelAssignments_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v___x_2605_; 
v___x_2605_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___redArg(v_k_2594_, v_allowLevelAssignments_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7___boxed(lean_object* v_00_u03b1_2606_, lean_object* v_k_2607_, lean_object* v_allowLevelAssignments_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2618_; lean_object* v_res_2619_; 
v_allowLevelAssignments_boxed_2618_ = lean_unbox(v_allowLevelAssignments_2608_);
v_res_2619_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__7(v_00_u03b1_2606_, v_k_2607_, v_allowLevelAssignments_boxed_2618_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec(v___y_2609_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10(lean_object* v_00_u03b1_2620_, lean_object* v_name_2621_, uint8_t v_bi_2622_, lean_object* v_type_2623_, lean_object* v_k_2624_, uint8_t v_kind_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
lean_object* v___x_2635_; 
v___x_2635_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___redArg(v_name_2621_, v_bi_2622_, v_type_2623_, v_k_2624_, v_kind_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10___boxed(lean_object* v_00_u03b1_2636_, lean_object* v_name_2637_, lean_object* v_bi_2638_, lean_object* v_type_2639_, lean_object* v_k_2640_, lean_object* v_kind_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_){
_start:
{
uint8_t v_bi_boxed_2651_; uint8_t v_kind_boxed_2652_; lean_object* v_res_2653_; 
v_bi_boxed_2651_ = lean_unbox(v_bi_2638_);
v_kind_boxed_2652_ = lean_unbox(v_kind_2641_);
v_res_2653_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__10(v_00_u03b1_2636_, v_name_2637_, v_bi_boxed_2651_, v_type_2639_, v_k_2640_, v_kind_boxed_2652_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
lean_dec(v___y_2643_);
lean_dec(v___y_2642_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(lean_object* v_00_u03b1_2654_, lean_object* v_e_2655_, lean_object* v_maxFVars_2656_, lean_object* v_k_2657_, uint8_t v_cleanupAnnotations_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v___x_2668_; 
v___x_2668_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___redArg(v_e_2655_, v_maxFVars_2656_, v_k_2657_, v_cleanupAnnotations_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
return v___x_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12___boxed(lean_object* v_00_u03b1_2669_, lean_object* v_e_2670_, lean_object* v_maxFVars_2671_, lean_object* v_k_2672_, lean_object* v_cleanupAnnotations_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2683_; lean_object* v_res_2684_; 
v_cleanupAnnotations_boxed_2683_ = lean_unbox(v_cleanupAnnotations_2673_);
v_res_2684_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__12(v_00_u03b1_2669_, v_e_2670_, v_maxFVars_2671_, v_k_2672_, v_cleanupAnnotations_boxed_2683_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec(v___y_2675_);
lean_dec(v___y_2674_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0(lean_object* v_inst_2685_, lean_object* v_R_2686_, lean_object* v_a_2687_, lean_object* v_b_2688_){
_start:
{
lean_object* v___x_2689_; 
v___x_2689_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__0___redArg(v_a_2687_, v_b_2688_);
return v___x_2689_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2(lean_object* v_cls_2690_, lean_object* v_msg_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_){
_start:
{
lean_object* v___x_2701_; 
v___x_2701_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg(v_cls_2690_, v_msg_2691_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___boxed(lean_object* v_cls_2702_, lean_object* v_msg_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2(v_cls_2702_, v_msg_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec(v___y_2705_);
lean_dec(v___y_2704_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4(lean_object* v_00_u03b2_2714_, lean_object* v_m_2715_, lean_object* v_a_2716_, lean_object* v_b_2717_){
_start:
{
lean_object* v___x_2718_; 
v___x_2718_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4___redArg(v_m_2715_, v_a_2716_, v_b_2717_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(lean_object* v_00_u03b1_2719_, lean_object* v_msg_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
lean_object* v___x_2730_; 
v___x_2730_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___redArg(v_msg_2720_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_);
return v___x_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6___boxed(lean_object* v_00_u03b1_2731_, lean_object* v_msg_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
lean_object* v_res_2742_; 
v_res_2742_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__6(v_00_u03b1_2731_, v_msg_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec_ref(v___y_2737_);
lean_dec(v___y_2736_);
lean_dec_ref(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec(v___y_2733_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8(lean_object* v_00_u03b2_2743_, lean_object* v_m_2744_, lean_object* v_a_2745_){
_start:
{
lean_object* v___x_2746_; 
v___x_2746_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___redArg(v_m_2744_, v_a_2745_);
return v___x_2746_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8___boxed(lean_object* v_00_u03b2_2747_, lean_object* v_m_2748_, lean_object* v_a_2749_){
_start:
{
lean_object* v_res_2750_; 
v_res_2750_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8(v_00_u03b2_2747_, v_m_2748_, v_a_2749_);
lean_dec_ref(v_a_2749_);
lean_dec_ref(v_m_2748_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15(lean_object* v_00_u03b1_2751_, lean_object* v_name_2752_, lean_object* v_type_2753_, lean_object* v_val_2754_, lean_object* v_k_2755_, uint8_t v_nondep_2756_, uint8_t v_kind_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_){
_start:
{
lean_object* v___x_2767_; 
v___x_2767_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___redArg(v_name_2752_, v_type_2753_, v_val_2754_, v_k_2755_, v_nondep_2756_, v_kind_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15___boxed(lean_object* v_00_u03b1_2768_, lean_object* v_name_2769_, lean_object* v_type_2770_, lean_object* v_val_2771_, lean_object* v_k_2772_, lean_object* v_nondep_2773_, lean_object* v_kind_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_){
_start:
{
uint8_t v_nondep_boxed_2784_; uint8_t v_kind_boxed_2785_; lean_object* v_res_2786_; 
v_nondep_boxed_2784_ = lean_unbox(v_nondep_2773_);
v_kind_boxed_2785_ = lean_unbox(v_kind_2774_);
v_res_2786_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__11_spec__15(v_00_u03b1_2768_, v_name_2769_, v_type_2770_, v_val_2771_, v_k_2772_, v_nondep_boxed_2784_, v_kind_boxed_2785_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec(v___y_2776_);
lean_dec(v___y_2775_);
return v_res_2786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20(lean_object* v_declName_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_){
_start:
{
lean_object* v___x_2797_; 
v___x_2797_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___redArg(v_declName_2787_, v___y_2795_);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20___boxed(lean_object* v_declName_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__20(v_declName_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec(v___y_2800_);
lean_dec(v___y_2799_);
return v_res_2808_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4(lean_object* v_00_u03b2_2809_, lean_object* v_a_2810_, lean_object* v_x_2811_){
_start:
{
uint8_t v___x_2812_; 
v___x_2812_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___redArg(v_a_2810_, v_x_2811_);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4___boxed(lean_object* v_00_u03b2_2813_, lean_object* v_a_2814_, lean_object* v_x_2815_){
_start:
{
uint8_t v_res_2816_; lean_object* v_r_2817_; 
v_res_2816_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__4(v_00_u03b2_2813_, v_a_2814_, v_x_2815_);
lean_dec(v_x_2815_);
lean_dec_ref(v_a_2814_);
v_r_2817_ = lean_box(v_res_2816_);
return v_r_2817_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5(lean_object* v_00_u03b2_2818_, lean_object* v_data_2819_){
_start:
{
lean_object* v___x_2820_; 
v___x_2820_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5___redArg(v_data_2819_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6(lean_object* v_00_u03b2_2821_, lean_object* v_a_2822_, lean_object* v_b_2823_, lean_object* v_x_2824_){
_start:
{
lean_object* v___x_2825_; 
v___x_2825_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__6___redArg(v_a_2822_, v_b_2823_, v_x_2824_);
return v___x_2825_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11(lean_object* v_00_u03b2_2826_, lean_object* v_a_2827_, lean_object* v_x_2828_){
_start:
{
lean_object* v___x_2829_; 
v___x_2829_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___redArg(v_a_2827_, v_x_2828_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11___boxed(lean_object* v_00_u03b2_2830_, lean_object* v_a_2831_, lean_object* v_x_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__8_spec__11(v_00_u03b2_2830_, v_a_2831_, v_x_2832_);
lean_dec(v_x_2832_);
lean_dec_ref(v_a_2831_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12(lean_object* v_00_u03b2_2834_, lean_object* v_i_2835_, lean_object* v_source_2836_, lean_object* v_target_2837_){
_start:
{
lean_object* v___x_2838_; 
v___x_2838_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12___redArg(v_i_2835_, v_source_2836_, v_target_2837_);
return v___x_2838_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21(lean_object* v_00_u03b1_2839_, lean_object* v_constName_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
lean_object* v___x_2850_; 
v___x_2850_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___redArg(v_constName_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21___boxed(lean_object* v_00_u03b1_2851_, lean_object* v_constName_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_){
_start:
{
lean_object* v_res_2862_; 
v_res_2862_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21(v_00_u03b1_2851_, v_constName_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
lean_dec(v___y_2858_);
lean_dec_ref(v___y_2857_);
lean_dec(v___y_2856_);
lean_dec_ref(v___y_2855_);
lean_dec(v___y_2854_);
lean_dec(v___y_2853_);
return v_res_2862_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12_spec__22(lean_object* v_00_u03b2_2863_, lean_object* v_x_2864_, lean_object* v_x_2865_){
_start:
{
lean_object* v___x_2866_; 
v___x_2866_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__4_spec__5_spec__12_spec__22___redArg(v_x_2864_, v_x_2865_);
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27(lean_object* v_00_u03b1_2867_, lean_object* v_ref_2868_, lean_object* v_constName_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_){
_start:
{
lean_object* v___x_2879_; 
v___x_2879_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___redArg(v_ref_2868_, v_constName_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27___boxed(lean_object* v_00_u03b1_2880_, lean_object* v_ref_2881_, lean_object* v_constName_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27(v_00_u03b1_2880_, v_ref_2881_, v_constName_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec_ref(v___y_2885_);
lean_dec(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec(v_ref_2881_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29(lean_object* v_00_u03b1_2893_, lean_object* v_ref_2894_, lean_object* v_msg_2895_, lean_object* v_declHint_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_){
_start:
{
lean_object* v___x_2906_; 
v___x_2906_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___redArg(v_ref_2894_, v_msg_2895_, v_declHint_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_);
return v___x_2906_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29___boxed(lean_object* v_00_u03b1_2907_, lean_object* v_ref_2908_, lean_object* v_msg_2909_, lean_object* v_declHint_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_){
_start:
{
lean_object* v_res_2920_; 
v_res_2920_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29(v_00_u03b1_2907_, v_ref_2908_, v_msg_2909_, v_declHint_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec(v___y_2911_);
lean_dec(v_ref_2908_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31(lean_object* v_msg_2921_, lean_object* v_declHint_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_){
_start:
{
lean_object* v___x_2932_; 
v___x_2932_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___redArg(v_msg_2921_, v_declHint_2922_, v___y_2930_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31___boxed(lean_object* v_msg_2933_, lean_object* v_declHint_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_){
_start:
{
lean_object* v_res_2944_; 
v_res_2944_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__30_spec__31(v_msg_2933_, v_declHint_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_);
lean_dec(v___y_2942_);
lean_dec_ref(v___y_2941_);
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2939_);
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec(v___y_2936_);
lean_dec(v___y_2935_);
return v_res_2944_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31(lean_object* v_00_u03b1_2945_, lean_object* v_ref_2946_, lean_object* v_msg_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_){
_start:
{
lean_object* v___x_2957_; 
v___x_2957_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___redArg(v_ref_2946_, v_msg_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31___boxed(lean_object* v_00_u03b1_2958_, lean_object* v_ref_2959_, lean_object* v_msg_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_){
_start:
{
lean_object* v_res_2970_; 
v_res_2970_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13_spec__18_spec__21_spec__27_spec__29_spec__31(v_00_u03b1_2958_, v_ref_2959_, v_msg_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v___y_2964_);
lean_dec_ref(v___y_2963_);
lean_dec(v___y_2962_);
lean_dec(v___y_2961_);
lean_dec(v_ref_2959_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(lean_object* v_cls_2971_, lean_object* v_msg_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_){
_start:
{
lean_object* v_ref_2978_; lean_object* v___x_2979_; lean_object* v_a_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_3024_; 
v_ref_2978_ = lean_ctor_get(v___y_2975_, 5);
v___x_2979_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
v_a_2980_ = lean_ctor_get(v___x_2979_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_2982_ = v___x_2979_;
v_isShared_2983_ = v_isSharedCheck_3024_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_a_2980_);
lean_dec(v___x_2979_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_3024_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2984_; lean_object* v_traceState_2985_; lean_object* v_env_2986_; lean_object* v_nextMacroScope_2987_; lean_object* v_ngen_2988_; lean_object* v_auxDeclNGen_2989_; lean_object* v_cache_2990_; lean_object* v_messages_2991_; lean_object* v_infoState_2992_; lean_object* v_snapshotTasks_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3023_; 
v___x_2984_ = lean_st_ref_take(v___y_2976_);
v_traceState_2985_ = lean_ctor_get(v___x_2984_, 4);
v_env_2986_ = lean_ctor_get(v___x_2984_, 0);
v_nextMacroScope_2987_ = lean_ctor_get(v___x_2984_, 1);
v_ngen_2988_ = lean_ctor_get(v___x_2984_, 2);
v_auxDeclNGen_2989_ = lean_ctor_get(v___x_2984_, 3);
v_cache_2990_ = lean_ctor_get(v___x_2984_, 5);
v_messages_2991_ = lean_ctor_get(v___x_2984_, 6);
v_infoState_2992_ = lean_ctor_get(v___x_2984_, 7);
v_snapshotTasks_2993_ = lean_ctor_get(v___x_2984_, 8);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_2984_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_2995_ = v___x_2984_;
v_isShared_2996_ = v_isSharedCheck_3023_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_snapshotTasks_2993_);
lean_inc(v_infoState_2992_);
lean_inc(v_messages_2991_);
lean_inc(v_cache_2990_);
lean_inc(v_traceState_2985_);
lean_inc(v_auxDeclNGen_2989_);
lean_inc(v_ngen_2988_);
lean_inc(v_nextMacroScope_2987_);
lean_inc(v_env_2986_);
lean_dec(v___x_2984_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3023_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
uint64_t v_tid_2997_; lean_object* v_traces_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3022_; 
v_tid_2997_ = lean_ctor_get_uint64(v_traceState_2985_, sizeof(void*)*1);
v_traces_2998_ = lean_ctor_get(v_traceState_2985_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v_traceState_2985_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3000_ = v_traceState_2985_;
v_isShared_3001_ = v_isSharedCheck_3022_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_traces_2998_);
lean_dec(v_traceState_2985_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3022_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3002_; double v___x_3003_; uint8_t v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3012_; 
v___x_3002_ = lean_box(0);
v___x_3003_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__0);
v___x_3004_ = 0;
v___x_3005_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__1));
v___x_3006_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3006_, 0, v_cls_2971_);
lean_ctor_set(v___x_3006_, 1, v___x_3002_);
lean_ctor_set(v___x_3006_, 2, v___x_3005_);
lean_ctor_set_float(v___x_3006_, sizeof(void*)*3, v___x_3003_);
lean_ctor_set_float(v___x_3006_, sizeof(void*)*3 + 8, v___x_3003_);
lean_ctor_set_uint8(v___x_3006_, sizeof(void*)*3 + 16, v___x_3004_);
v___x_3007_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec_spec__2___redArg___closed__2));
v___x_3008_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3006_);
lean_ctor_set(v___x_3008_, 1, v_a_2980_);
lean_ctor_set(v___x_3008_, 2, v___x_3007_);
lean_inc(v_ref_2978_);
v___x_3009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3009_, 0, v_ref_2978_);
lean_ctor_set(v___x_3009_, 1, v___x_3008_);
v___x_3010_ = l_Lean_PersistentArray_push___redArg(v_traces_2998_, v___x_3009_);
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 0, v___x_3010_);
v___x_3012_ = v___x_3000_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v___x_3010_);
lean_ctor_set_uint64(v_reuseFailAlloc_3021_, sizeof(void*)*1, v_tid_2997_);
v___x_3012_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
lean_object* v___x_3014_; 
if (v_isShared_2996_ == 0)
{
lean_ctor_set(v___x_2995_, 4, v___x_3012_);
v___x_3014_ = v___x_2995_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_env_2986_);
lean_ctor_set(v_reuseFailAlloc_3020_, 1, v_nextMacroScope_2987_);
lean_ctor_set(v_reuseFailAlloc_3020_, 2, v_ngen_2988_);
lean_ctor_set(v_reuseFailAlloc_3020_, 3, v_auxDeclNGen_2989_);
lean_ctor_set(v_reuseFailAlloc_3020_, 4, v___x_3012_);
lean_ctor_set(v_reuseFailAlloc_3020_, 5, v_cache_2990_);
lean_ctor_set(v_reuseFailAlloc_3020_, 6, v_messages_2991_);
lean_ctor_set(v_reuseFailAlloc_3020_, 7, v_infoState_2992_);
lean_ctor_set(v_reuseFailAlloc_3020_, 8, v_snapshotTasks_2993_);
v___x_3014_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3018_; 
v___x_3015_ = lean_st_ref_set(v___y_2976_, v___x_3014_);
v___x_3016_ = lean_box(0);
if (v_isShared_2983_ == 0)
{
lean_ctor_set(v___x_2982_, 0, v___x_3016_);
v___x_3018_ = v___x_2982_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v___x_3016_);
v___x_3018_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
return v___x_3018_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg___boxed(lean_object* v_cls_3025_, lean_object* v_msg_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_){
_start:
{
lean_object* v_res_3032_; 
v_res_3032_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3025_, v_msg_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3029_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
return v_res_3032_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0(void){
_start:
{
lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3033_ = lean_box(0);
v___x_3034_ = lean_unsigned_to_nat(16u);
v___x_3035_ = lean_mk_array(v___x_3034_, v___x_3033_);
return v___x_3035_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1(void){
_start:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3036_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__0);
v___x_3037_ = lean_unsigned_to_nat(0u);
v___x_3038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3037_);
lean_ctor_set(v___x_3038_, 1, v___x_3036_);
return v___x_3038_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3(void){
_start:
{
lean_object* v___x_3040_; lean_object* v___x_3041_; 
v___x_3040_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__2));
v___x_3041_ = l_Lean_stringToMessageData(v___x_3040_);
return v___x_3041_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5(void){
_start:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3043_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__4));
v___x_3044_ = l_Lean_stringToMessageData(v___x_3043_);
return v___x_3044_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7(void){
_start:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3046_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__6));
v___x_3047_ = l_Lean_stringToMessageData(v___x_3046_);
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(lean_object* v_recFnName_3048_, lean_object* v_fixedPrefixSize_3049_, lean_object* v_F_3050_, lean_object* v_e_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_){
_start:
{
lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v_options_3080_; uint8_t v_hasTrace_3081_; 
v_options_3080_ = lean_ctor_get(v_a_3056_, 2);
v_hasTrace_3081_ = lean_ctor_get_uint8(v_options_3080_, sizeof(void*)*1);
if (v_hasTrace_3081_ == 0)
{
v___y_3060_ = v_a_3052_;
v___y_3061_ = v_a_3053_;
v___y_3062_ = v_a_3054_;
v___y_3063_ = v_a_3055_;
v___y_3064_ = v_a_3056_;
v___y_3065_ = v_a_3057_;
goto v___jp_3059_;
}
else
{
lean_object* v_inheritedTraceOptions_3082_; lean_object* v_cls_3083_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v_options_3090_; lean_object* v_inheritedTraceOptions_3091_; lean_object* v___y_3092_; lean_object* v___x_3113_; uint8_t v___x_3114_; 
v_inheritedTraceOptions_3082_ = lean_ctor_get(v_a_3056_, 13);
v_cls_3083_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__1));
v___x_3113_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_3114_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3082_, v_options_3080_, v___x_3113_);
if (v___x_3114_ == 0)
{
v___y_3085_ = v_a_3052_;
v___y_3086_ = v_a_3053_;
v___y_3087_ = v_a_3054_;
v___y_3088_ = v_a_3055_;
v___y_3089_ = v_a_3056_;
v_options_3090_ = v_options_3080_;
v_inheritedTraceOptions_3091_ = v_inheritedTraceOptions_3082_;
v___y_3092_ = v_a_3057_;
goto v___jp_3084_;
}
else
{
lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3115_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__7);
lean_inc_ref(v_e_3051_);
v___x_3116_ = l_Lean_indentExpr(v_e_3051_);
v___x_3117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3117_, 0, v___x_3115_);
lean_ctor_set(v___x_3117_, 1, v___x_3116_);
v___x_3118_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3083_, v___x_3117_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_dec_ref_known(v___x_3118_, 1);
v___y_3085_ = v_a_3052_;
v___y_3086_ = v_a_3053_;
v___y_3087_ = v_a_3054_;
v___y_3088_ = v_a_3055_;
v___y_3089_ = v_a_3056_;
v_options_3090_ = v_options_3080_;
v_inheritedTraceOptions_3091_ = v_inheritedTraceOptions_3082_;
v___y_3092_ = v_a_3057_;
goto v___jp_3084_;
}
else
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
lean_dec_ref(v_e_3051_);
lean_dec_ref(v_F_3050_);
lean_dec(v_fixedPrefixSize_3049_);
lean_dec(v_recFnName_3048_);
v_a_3119_ = lean_ctor_get(v___x_3118_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3121_ = v___x_3118_;
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3118_);
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
v___jp_3084_:
{
lean_object* v___x_3093_; uint8_t v___x_3094_; 
v___x_3093_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__4);
v___x_3094_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3091_, v_options_3090_, v___x_3093_);
if (v___x_3094_ == 0)
{
v___y_3060_ = v___y_3085_;
v___y_3061_ = v___y_3086_;
v___y_3062_ = v___y_3087_;
v___y_3063_ = v___y_3088_;
v___y_3064_ = v___y_3089_;
v___y_3065_ = v___y_3092_;
goto v___jp_3059_;
}
else
{
lean_object* v___x_3095_; 
lean_inc(v___y_3092_);
lean_inc_ref(v___y_3089_);
lean_inc(v___y_3088_);
lean_inc_ref(v___y_3087_);
lean_inc_ref(v_F_3050_);
v___x_3095_ = lean_infer_type(v_F_3050_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3092_);
if (lean_obj_tag(v___x_3095_) == 0)
{
lean_object* v_a_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v_a_3096_ = lean_ctor_get(v___x_3095_, 0);
lean_inc(v_a_3096_);
lean_dec_ref_known(v___x_3095_, 1);
v___x_3097_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__3);
lean_inc_ref(v_F_3050_);
v___x_3098_ = l_Lean_MessageData_ofExpr(v_F_3050_);
v___x_3099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3097_);
lean_ctor_set(v___x_3099_, 1, v___x_3098_);
v___x_3100_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__5);
v___x_3101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3101_, 0, v___x_3099_);
lean_ctor_set(v___x_3101_, 1, v___x_3100_);
v___x_3102_ = l_Lean_indentExpr(v_a_3096_);
v___x_3103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3101_);
lean_ctor_set(v___x_3103_, 1, v___x_3102_);
v___x_3104_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3083_, v___x_3103_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3092_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_dec_ref_known(v___x_3104_, 1);
v___y_3060_ = v___y_3085_;
v___y_3061_ = v___y_3086_;
v___y_3062_ = v___y_3087_;
v___y_3063_ = v___y_3088_;
v___y_3064_ = v___y_3089_;
v___y_3065_ = v___y_3092_;
goto v___jp_3059_;
}
else
{
lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3112_; 
lean_dec_ref(v_e_3051_);
lean_dec_ref(v_F_3050_);
lean_dec(v_fixedPrefixSize_3049_);
lean_dec(v_recFnName_3048_);
v_a_3105_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3107_ = v___x_3104_;
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v___x_3104_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3110_; 
if (v_isShared_3108_ == 0)
{
v___x_3110_ = v___x_3107_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_a_3105_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
}
else
{
lean_dec_ref(v_e_3051_);
lean_dec_ref(v_F_3050_);
lean_dec(v_fixedPrefixSize_3049_);
lean_dec(v_recFnName_3048_);
return v___x_3095_;
}
}
}
}
v___jp_3059_:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3066_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___closed__1);
v___x_3067_ = lean_st_mk_ref(v___x_3066_);
v___x_3068_ = lean_st_mk_ref(v___x_3066_);
v___x_3069_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop(v_recFnName_3048_, v_fixedPrefixSize_3049_, v_F_3050_, v_e_3051_, v___x_3068_, v___x_3067_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_);
if (lean_obj_tag(v___x_3069_) == 0)
{
lean_object* v_a_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3079_; 
v_a_3070_ = lean_ctor_get(v___x_3069_, 0);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3072_ = v___x_3069_;
v_isShared_3073_ = v_isSharedCheck_3079_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_a_3070_);
lean_dec(v___x_3069_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3079_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3077_; 
v___x_3074_ = lean_st_ref_get(v___x_3068_);
lean_dec(v___x_3068_);
lean_dec(v___x_3074_);
v___x_3075_ = lean_st_ref_get(v___x_3067_);
lean_dec(v___x_3067_);
lean_dec(v___x_3075_);
if (v_isShared_3073_ == 0)
{
v___x_3077_ = v___x_3072_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_a_3070_);
v___x_3077_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
return v___x_3077_;
}
}
}
else
{
lean_dec(v___x_3068_);
lean_dec(v___x_3067_);
return v___x_3069_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps___boxed(lean_object* v_recFnName_3127_, lean_object* v_fixedPrefixSize_3128_, lean_object* v_F_3129_, lean_object* v_e_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_){
_start:
{
lean_object* v_res_3138_; 
v_res_3138_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps(v_recFnName_3127_, v_fixedPrefixSize_3128_, v_F_3129_, v_e_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_);
lean_dec(v_a_3136_);
lean_dec_ref(v_a_3135_);
lean_dec(v_a_3134_);
lean_dec_ref(v_a_3133_);
lean_dec(v_a_3132_);
lean_dec_ref(v_a_3131_);
return v_res_3138_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0(lean_object* v_cls_3139_, lean_object* v_msg_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_){
_start:
{
lean_object* v___x_3148_; 
v___x_3148_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___redArg(v_cls_3139_, v_msg_3140_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0___boxed(lean_object* v_cls_3149_, lean_object* v_msg_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_){
_start:
{
lean_object* v_res_3158_; 
v_res_3158_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_spec__0(v_cls_3149_, v_msg_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
return v_res_3158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0(lean_object* v_k_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v_b_3162_, lean_object* v_c_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_){
_start:
{
lean_object* v___x_3169_; 
lean_inc(v___y_3167_);
lean_inc_ref(v___y_3166_);
lean_inc(v___y_3165_);
lean_inc_ref(v___y_3164_);
lean_inc(v___y_3161_);
lean_inc_ref(v___y_3160_);
v___x_3169_ = lean_apply_9(v_k_3159_, v_b_3162_, v_c_3163_, v___y_3160_, v___y_3161_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, lean_box(0));
return v___x_3169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed(lean_object* v_k_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v_b_3173_, lean_object* v_c_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
lean_object* v_res_3180_; 
v_res_3180_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0(v_k_3170_, v___y_3171_, v___y_3172_, v_b_3173_, v_c_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
return v_res_3180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(lean_object* v_e_3181_, lean_object* v_k_3182_, uint8_t v_cleanupAnnotations_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
lean_object* v___f_3191_; uint8_t v___x_3192_; uint8_t v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; 
lean_inc(v___y_3185_);
lean_inc_ref(v___y_3184_);
v___f_3191_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3191_, 0, v_k_3182_);
lean_closure_set(v___f_3191_, 1, v___y_3184_);
lean_closure_set(v___f_3191_, 2, v___y_3185_);
v___x_3192_ = 1;
v___x_3193_ = 0;
v___x_3194_ = lean_box(0);
v___x_3195_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3181_, v___x_3192_, v___x_3193_, v___x_3192_, v___x_3193_, v___x_3194_, v___f_3191_, v_cleanupAnnotations_3183_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_);
if (lean_obj_tag(v___x_3195_) == 0)
{
return v___x_3195_;
}
else
{
lean_object* v_a_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3203_; 
v_a_3196_ = lean_ctor_get(v___x_3195_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_3195_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3198_ = v___x_3195_;
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_a_3196_);
lean_dec(v___x_3195_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3201_; 
if (v_isShared_3199_ == 0)
{
v___x_3201_ = v___x_3198_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v_a_3196_);
v___x_3201_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
return v___x_3201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___boxed(lean_object* v_e_3204_, lean_object* v_k_3205_, lean_object* v_cleanupAnnotations_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3214_; lean_object* v_res_3215_; 
v_cleanupAnnotations_boxed_3214_ = lean_unbox(v_cleanupAnnotations_3206_);
v_res_3215_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v_e_3204_, v_k_3205_, v_cleanupAnnotations_boxed_3214_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_);
lean_dec(v___y_3212_);
lean_dec_ref(v___y_3211_);
lean_dec(v___y_3210_);
lean_dec_ref(v___y_3209_);
lean_dec(v___y_3208_);
lean_dec_ref(v___y_3207_);
return v_res_3215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0(lean_object* v_00_u03b1_3216_, lean_object* v_e_3217_, lean_object* v_k_3218_, uint8_t v_cleanupAnnotations_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_){
_start:
{
lean_object* v___x_3227_; 
v___x_3227_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v_e_3217_, v_k_3218_, v_cleanupAnnotations_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
return v___x_3227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___boxed(lean_object* v_00_u03b1_3228_, lean_object* v_e_3229_, lean_object* v_k_3230_, lean_object* v_cleanupAnnotations_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3239_; lean_object* v_res_3240_; 
v_cleanupAnnotations_boxed_3239_ = lean_unbox(v_cleanupAnnotations_3231_);
v_res_3240_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0(v_00_u03b1_3228_, v_e_3229_, v_k_3230_, v_cleanupAnnotations_boxed_3239_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec(v___y_3233_);
lean_dec_ref(v___y_3232_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(lean_object* v_e_3241_, lean_object* v_maxFVars_3242_, lean_object* v_k_3243_, uint8_t v_cleanupAnnotations_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_){
_start:
{
lean_object* v___f_3252_; uint8_t v___x_3253_; uint8_t v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; 
lean_inc(v___y_3246_);
lean_inc_ref(v___y_3245_);
v___f_3252_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3252_, 0, v_k_3243_);
lean_closure_set(v___f_3252_, 1, v___y_3245_);
lean_closure_set(v___f_3252_, 2, v___y_3246_);
v___x_3253_ = 1;
v___x_3254_ = 0;
v___x_3255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3255_, 0, v_maxFVars_3242_);
v___x_3256_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3241_, v___x_3253_, v___x_3254_, v___x_3253_, v___x_3254_, v___x_3255_, v___f_3252_, v_cleanupAnnotations_3244_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_);
lean_dec_ref_known(v___x_3255_, 1);
if (lean_obj_tag(v___x_3256_) == 0)
{
return v___x_3256_;
}
else
{
lean_object* v_a_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3264_; 
v_a_3257_ = lean_ctor_get(v___x_3256_, 0);
v_isSharedCheck_3264_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3259_ = v___x_3256_;
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_a_3257_);
lean_dec(v___x_3256_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
lean_object* v___x_3262_; 
if (v_isShared_3260_ == 0)
{
v___x_3262_ = v___x_3259_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_a_3257_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg___boxed(lean_object* v_e_3265_, lean_object* v_maxFVars_3266_, lean_object* v_k_3267_, lean_object* v_cleanupAnnotations_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3276_; lean_object* v_res_3277_; 
v_cleanupAnnotations_boxed_3276_ = lean_unbox(v_cleanupAnnotations_3268_);
v_res_3277_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_e_3265_, v_maxFVars_3266_, v_k_3267_, v_cleanupAnnotations_boxed_3276_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
return v_res_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2(lean_object* v_00_u03b1_3278_, lean_object* v_e_3279_, lean_object* v_maxFVars_3280_, lean_object* v_k_3281_, uint8_t v_cleanupAnnotations_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
lean_object* v___x_3290_; 
v___x_3290_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_e_3279_, v_maxFVars_3280_, v_k_3281_, v_cleanupAnnotations_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_);
return v___x_3290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___boxed(lean_object* v_00_u03b1_3291_, lean_object* v_e_3292_, lean_object* v_maxFVars_3293_, lean_object* v_k_3294_, lean_object* v_cleanupAnnotations_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3303_; lean_object* v_res_3304_; 
v_cleanupAnnotations_boxed_3303_ = lean_unbox(v_cleanupAnnotations_3295_);
v_res_3304_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2(v_00_u03b1_3291_, v_e_3292_, v_maxFVars_3293_, v_k_3294_, v_cleanupAnnotations_boxed_3303_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_);
lean_dec(v___y_3301_);
lean_dec_ref(v___y_3300_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0(lean_object* v_a_3305_, lean_object* v___x_3306_, lean_object* v___x_3307_, lean_object* v_x_3308_, uint8_t v___x_3309_, lean_object* v_xs_3310_, lean_object* v_type_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_){
_start:
{
lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3319_ = l_Lean_LocalDecl_type(v_a_3305_);
v___x_3320_ = lean_array_get_borrowed(v___x_3306_, v_xs_3310_, v___x_3307_);
v___x_3321_ = l_Lean_Expr_replaceFVar(v___x_3319_, v_x_3308_, v___x_3320_);
lean_dec_ref(v___x_3319_);
v___x_3322_ = l_Lean_mkArrow(v___x_3321_, v_type_3311_, v___y_3316_, v___y_3317_);
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_object* v_a_3323_; uint8_t v___x_3324_; uint8_t v___x_3325_; lean_object* v___x_3326_; 
v_a_3323_ = lean_ctor_get(v___x_3322_, 0);
lean_inc_n(v_a_3323_, 2);
lean_dec_ref_known(v___x_3322_, 1);
v___x_3324_ = 0;
v___x_3325_ = 1;
v___x_3326_ = l_Lean_Meta_mkLambdaFVars(v_xs_3310_, v_a_3323_, v___x_3324_, v___x_3309_, v___x_3324_, v___x_3309_, v___x_3325_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v_a_3327_; lean_object* v___x_3328_; 
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_a_3327_);
lean_dec_ref_known(v___x_3326_, 1);
v___x_3328_ = l_Lean_Meta_getLevel(v_a_3323_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_);
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_object* v_a_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3337_; 
v_a_3329_ = lean_ctor_get(v___x_3328_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3328_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3331_ = v___x_3328_;
v_isShared_3332_ = v_isSharedCheck_3337_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_a_3329_);
lean_dec(v___x_3328_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3337_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3333_; lean_object* v___x_3335_; 
v___x_3333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3333_, 0, v_a_3327_);
lean_ctor_set(v___x_3333_, 1, v_a_3329_);
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 0, v___x_3333_);
v___x_3335_ = v___x_3331_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v___x_3333_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
return v___x_3335_;
}
}
}
else
{
lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3345_; 
lean_dec(v_a_3327_);
v_a_3338_ = lean_ctor_get(v___x_3328_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3328_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3340_ = v___x_3328_;
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3328_);
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
lean_dec(v_a_3323_);
v_a_3346_ = lean_ctor_get(v___x_3326_, 0);
v_isSharedCheck_3353_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3348_ = v___x_3326_;
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_dec(v___x_3326_);
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
else
{
lean_object* v_a_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3361_; 
v_a_3354_ = lean_ctor_get(v___x_3322_, 0);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___x_3322_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3356_ = v___x_3322_;
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_a_3354_);
lean_dec(v___x_3322_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v___x_3359_; 
if (v_isShared_3357_ == 0)
{
v___x_3359_ = v___x_3356_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v_a_3354_);
v___x_3359_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
return v___x_3359_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed(lean_object* v_a_3362_, lean_object* v___x_3363_, lean_object* v___x_3364_, lean_object* v_x_3365_, lean_object* v___x_3366_, lean_object* v_xs_3367_, lean_object* v_type_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
uint8_t v___x_6703__boxed_3376_; lean_object* v_res_3377_; 
v___x_6703__boxed_3376_ = lean_unbox(v___x_3366_);
v_res_3377_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0(v_a_3362_, v___x_3363_, v___x_3364_, v_x_3365_, v___x_6703__boxed_3376_, v_xs_3367_, v_type_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_);
lean_dec(v___y_3374_);
lean_dec_ref(v___y_3373_);
lean_dec(v___y_3372_);
lean_dec_ref(v___y_3371_);
lean_dec(v___y_3370_);
lean_dec_ref(v___y_3369_);
lean_dec_ref(v_xs_3367_);
lean_dec(v___x_3364_);
lean_dec_ref(v___x_3363_);
lean_dec_ref(v_a_3362_);
return v_res_3377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0(lean_object* v_k_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v_b_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_){
_start:
{
lean_object* v___x_3387_; 
lean_inc(v___y_3385_);
lean_inc_ref(v___y_3384_);
lean_inc(v___y_3383_);
lean_inc_ref(v___y_3382_);
lean_inc(v___y_3380_);
lean_inc_ref(v___y_3379_);
v___x_3387_ = lean_apply_8(v_k_3378_, v_b_3381_, v___y_3379_, v___y_3380_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, lean_box(0));
return v___x_3387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_k_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v_b_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_){
_start:
{
lean_object* v_res_3397_; 
v_res_3397_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0(v_k_3388_, v___y_3389_, v___y_3390_, v_b_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
return v_res_3397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(lean_object* v_name_3398_, uint8_t v_bi_3399_, lean_object* v_type_3400_, lean_object* v_k_3401_, uint8_t v_kind_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_){
_start:
{
lean_object* v___f_3410_; lean_object* v___x_3411_; 
lean_inc(v___y_3404_);
lean_inc_ref(v___y_3403_);
v___f_3410_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3410_, 0, v_k_3401_);
lean_closure_set(v___f_3410_, 1, v___y_3403_);
lean_closure_set(v___f_3410_, 2, v___y_3404_);
v___x_3411_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3398_, v_bi_3399_, v_type_3400_, v___f_3410_, v_kind_3402_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_);
if (lean_obj_tag(v___x_3411_) == 0)
{
return v___x_3411_;
}
else
{
lean_object* v_a_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3419_; 
v_a_3412_ = lean_ctor_get(v___x_3411_, 0);
v_isSharedCheck_3419_ = !lean_is_exclusive(v___x_3411_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3414_ = v___x_3411_;
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_a_3412_);
lean_dec(v___x_3411_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3417_; 
if (v_isShared_3415_ == 0)
{
v___x_3417_ = v___x_3414_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_a_3412_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
return v___x_3417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg___boxed(lean_object* v_name_3420_, lean_object* v_bi_3421_, lean_object* v_type_3422_, lean_object* v_k_3423_, lean_object* v_kind_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_){
_start:
{
uint8_t v_bi_boxed_3432_; uint8_t v_kind_boxed_3433_; lean_object* v_res_3434_; 
v_bi_boxed_3432_ = lean_unbox(v_bi_3421_);
v_kind_boxed_3433_ = lean_unbox(v_kind_3424_);
v_res_3434_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(v_name_3420_, v_bi_boxed_3432_, v_type_3422_, v_k_3423_, v_kind_boxed_3433_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
lean_dec(v___y_3430_);
lean_dec_ref(v___y_3429_);
lean_dec(v___y_3428_);
lean_dec_ref(v___y_3427_);
lean_dec(v___y_3426_);
lean_dec_ref(v___y_3425_);
return v_res_3434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(lean_object* v_name_3435_, lean_object* v_type_3436_, lean_object* v_k_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_){
_start:
{
uint8_t v___x_3445_; uint8_t v___x_3446_; lean_object* v___x_3447_; 
v___x_3445_ = 0;
v___x_3446_ = 0;
v___x_3447_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(v_name_3435_, v___x_3445_, v_type_3436_, v_k_3437_, v___x_3446_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_);
return v___x_3447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg___boxed(lean_object* v_name_3448_, lean_object* v_type_3449_, lean_object* v_k_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_){
_start:
{
lean_object* v_res_3458_; 
v_res_3458_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_name_3448_, v_type_3449_, v_k_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
lean_dec(v___y_3456_);
lean_dec_ref(v___y_3455_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec(v___y_3452_);
lean_dec_ref(v___y_3451_);
return v_res_3458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(lean_object* v_x_3472_, lean_object* v_F_3473_, lean_object* v_val_3474_, lean_object* v_k_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_){
_start:
{
uint8_t v___y_3484_; uint8_t v___x_3599_; 
v___x_3599_ = l_Lean_Expr_isFVar(v_x_3472_);
if (v___x_3599_ == 0)
{
v___y_3484_ = v___x_3599_;
goto v___jp_3483_;
}
else
{
lean_object* v___x_3600_; lean_object* v___x_3601_; uint8_t v___x_3602_; 
v___x_3600_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6));
v___x_3601_ = lean_unsigned_to_nat(6u);
v___x_3602_ = l_Lean_Expr_isAppOfArity(v_val_3474_, v___x_3600_, v___x_3601_);
v___y_3484_ = v___x_3602_;
goto v___jp_3483_;
}
v___jp_3483_:
{
if (v___y_3484_ == 0)
{
lean_object* v___x_3485_; 
lean_inc(v_a_3481_);
lean_inc_ref(v_a_3480_);
lean_inc(v_a_3479_);
lean_inc_ref(v_a_3478_);
lean_inc(v_a_3477_);
lean_inc_ref(v_a_3476_);
v___x_3485_ = lean_apply_10(v_k_3475_, v_x_3472_, v_F_3473_, v_val_3474_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, lean_box(0));
return v___x_3485_;
}
else
{
lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; uint8_t v___x_3492_; 
v___x_3486_ = lean_unsigned_to_nat(3u);
v___x_3487_ = l_Lean_Expr_getAppNumArgs(v_val_3474_);
v___x_3488_ = lean_nat_sub(v___x_3487_, v___x_3486_);
v___x_3489_ = lean_unsigned_to_nat(1u);
v___x_3490_ = lean_nat_sub(v___x_3488_, v___x_3489_);
lean_dec(v___x_3488_);
v___x_3491_ = l_Lean_Expr_getRevArg_x21(v_val_3474_, v___x_3490_);
v___x_3492_ = lean_expr_eqv(v___x_3491_, v_x_3472_);
lean_dec_ref(v___x_3491_);
if (v___x_3492_ == 0)
{
lean_object* v___x_3493_; 
lean_dec(v___x_3487_);
lean_inc(v_a_3481_);
lean_inc_ref(v_a_3480_);
lean_inc(v_a_3479_);
lean_inc_ref(v_a_3478_);
lean_inc(v_a_3477_);
lean_inc_ref(v_a_3476_);
v___x_3493_ = lean_apply_10(v_k_3475_, v_x_3472_, v_F_3473_, v_val_3474_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, lean_box(0));
return v___x_3493_;
}
else
{
lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; uint8_t v___x_3498_; 
v___x_3494_ = lean_unsigned_to_nat(4u);
v___x_3495_ = lean_nat_sub(v___x_3487_, v___x_3494_);
v___x_3496_ = lean_nat_sub(v___x_3495_, v___x_3489_);
lean_dec(v___x_3495_);
v___x_3497_ = l_Lean_Expr_getRevArg_x21(v_val_3474_, v___x_3496_);
v___x_3498_ = l_Lean_Expr_isLambda(v___x_3497_);
lean_dec_ref(v___x_3497_);
if (v___x_3498_ == 0)
{
lean_object* v___x_3499_; 
lean_dec(v___x_3487_);
lean_inc(v_a_3481_);
lean_inc_ref(v_a_3480_);
lean_inc(v_a_3479_);
lean_inc_ref(v_a_3478_);
lean_inc(v_a_3477_);
lean_inc_ref(v_a_3476_);
v___x_3499_ = lean_apply_10(v_k_3475_, v_x_3472_, v_F_3473_, v_val_3474_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, lean_box(0));
return v___x_3499_;
}
else
{
lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; uint8_t v___x_3504_; 
v___x_3500_ = lean_unsigned_to_nat(5u);
v___x_3501_ = lean_nat_sub(v___x_3487_, v___x_3500_);
v___x_3502_ = lean_nat_sub(v___x_3501_, v___x_3489_);
lean_dec(v___x_3501_);
v___x_3503_ = l_Lean_Expr_getRevArg_x21(v_val_3474_, v___x_3502_);
v___x_3504_ = l_Lean_Expr_isLambda(v___x_3503_);
lean_dec_ref(v___x_3503_);
if (v___x_3504_ == 0)
{
lean_object* v___x_3505_; 
lean_dec(v___x_3487_);
lean_inc(v_a_3481_);
lean_inc_ref(v_a_3480_);
lean_inc(v_a_3479_);
lean_inc_ref(v_a_3478_);
lean_inc(v_a_3477_);
lean_inc_ref(v_a_3476_);
v___x_3505_ = lean_apply_10(v_k_3475_, v_x_3472_, v_F_3473_, v_val_3474_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, lean_box(0));
return v___x_3505_;
}
else
{
lean_object* v___x_3506_; lean_object* v___x_3507_; 
v___x_3506_ = l_Lean_Expr_fvarId_x21(v_F_3473_);
v___x_3507_ = l_Lean_FVarId_getDecl___redArg(v___x_3506_, v_a_3478_, v_a_3480_, v_a_3481_);
if (lean_obj_tag(v___x_3507_) == 0)
{
lean_object* v_a_3508_; lean_object* v___x_3509_; lean_object* v_dummy_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v_args_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___f_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; uint8_t v___x_3519_; lean_object* v___x_3520_; 
v_a_3508_ = lean_ctor_get(v___x_3507_, 0);
lean_inc_n(v_a_3508_, 2);
lean_dec_ref_known(v___x_3507_, 1);
v___x_3509_ = l_Lean_instInhabitedExpr;
v_dummy_3510_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_3487_);
v___x_3511_ = lean_mk_array(v___x_3487_, v_dummy_3510_);
v___x_3512_ = lean_nat_sub(v___x_3487_, v___x_3489_);
lean_dec(v___x_3487_);
v_args_3513_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_3474_, v___x_3511_, v___x_3512_);
v___x_3514_ = lean_unsigned_to_nat(0u);
v___x_3515_ = lean_box(v___x_3498_);
lean_inc_ref(v_x_3472_);
v___f_3516_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed), 14, 5);
lean_closure_set(v___f_3516_, 0, v_a_3508_);
lean_closure_set(v___f_3516_, 1, v___x_3509_);
lean_closure_set(v___f_3516_, 2, v___x_3514_);
lean_closure_set(v___f_3516_, 3, v_x_3472_);
lean_closure_set(v___f_3516_, 4, v___x_3515_);
v___x_3517_ = lean_unsigned_to_nat(2u);
v___x_3518_ = lean_array_get(v___x_3509_, v_args_3513_, v___x_3517_);
v___x_3519_ = 0;
v___x_3520_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_3518_, v___f_3516_, v___x_3519_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_object* v_a_3521_; lean_object* v_fst_3522_; lean_object* v_snd_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3582_; 
v_a_3521_ = lean_ctor_get(v___x_3520_, 0);
lean_inc(v_a_3521_);
lean_dec_ref_known(v___x_3520_, 1);
v_fst_3522_ = lean_ctor_get(v_a_3521_, 0);
v_snd_3523_ = lean_ctor_get(v_a_3521_, 1);
v_isSharedCheck_3582_ = !lean_is_exclusive(v_a_3521_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3525_ = v_a_3521_;
v_isShared_3526_ = v_isSharedCheck_3582_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_snd_3523_);
lean_inc(v_fst_3522_);
lean_dec(v_a_3521_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3582_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v_00_u03b1_3527_; lean_object* v_00_u03b2_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; 
v_00_u03b1_3527_ = lean_array_get(v___x_3509_, v_args_3513_, v___x_3514_);
v_00_u03b2_3528_ = lean_array_get(v___x_3509_, v_args_3513_, v___x_3489_);
v___x_3529_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__2));
v___x_3530_ = lean_array_get(v___x_3509_, v_args_3513_, v___x_3494_);
lean_inc_ref(v_x_3472_);
lean_inc(v_a_3508_);
lean_inc_ref(v_k_3475_);
lean_inc(v_00_u03b2_3528_);
lean_inc(v_00_u03b1_3527_);
v___x_3531_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3509_, v___x_3514_, v_00_u03b1_3527_, v_00_u03b2_3528_, v___x_3486_, v_k_3475_, v___x_3517_, v___x_3519_, v___x_3498_, v_a_3508_, v_x_3472_, v___x_3489_, v___x_3529_, v___x_3530_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_);
if (lean_obj_tag(v___x_3531_) == 0)
{
lean_object* v_a_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; 
v_a_3532_ = lean_ctor_get(v___x_3531_, 0);
lean_inc(v_a_3532_);
lean_dec_ref_known(v___x_3531_, 1);
v___x_3533_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__4));
v___x_3534_ = lean_array_get(v___x_3509_, v_args_3513_, v___x_3500_);
lean_dec_ref(v_args_3513_);
lean_inc_ref(v_x_3472_);
lean_inc(v_00_u03b2_3528_);
lean_inc(v_00_u03b1_3527_);
v___x_3535_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3509_, v___x_3514_, v_00_u03b1_3527_, v_00_u03b2_3528_, v___x_3486_, v_k_3475_, v___x_3517_, v___x_3519_, v___x_3498_, v_a_3508_, v_x_3472_, v___x_3489_, v___x_3533_, v___x_3534_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_object* v_a_3536_; lean_object* v___x_3537_; 
v_a_3536_ = lean_ctor_get(v___x_3535_, 0);
lean_inc(v_a_3536_);
lean_dec_ref_known(v___x_3535_, 1);
lean_inc(v_00_u03b1_3527_);
v___x_3537_ = l_Lean_Meta_getLevel(v_00_u03b1_3527_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_);
if (lean_obj_tag(v___x_3537_) == 0)
{
lean_object* v_a_3538_; lean_object* v___x_3539_; 
v_a_3538_ = lean_ctor_get(v___x_3537_, 0);
lean_inc(v_a_3538_);
lean_dec_ref_known(v___x_3537_, 1);
lean_inc(v_00_u03b2_3528_);
v___x_3539_ = l_Lean_Meta_getLevel(v_00_u03b2_3528_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_);
if (lean_obj_tag(v___x_3539_) == 0)
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3565_; 
v_a_3540_ = lean_ctor_get(v___x_3539_, 0);
v_isSharedCheck_3565_ = !lean_is_exclusive(v___x_3539_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3542_ = v___x_3539_;
v_isShared_3543_ = v_isSharedCheck_3565_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3539_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3565_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3547_; 
v___x_3544_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___closed__6));
v___x_3545_ = lean_box(0);
if (v_isShared_3526_ == 0)
{
lean_ctor_set_tag(v___x_3525_, 1);
lean_ctor_set(v___x_3525_, 1, v___x_3545_);
lean_ctor_set(v___x_3525_, 0, v_a_3540_);
v___x_3547_ = v___x_3525_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_a_3540_);
lean_ctor_set(v_reuseFailAlloc_3564_, 1, v___x_3545_);
v___x_3547_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3562_; 
v___x_3548_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3548_, 0, v_a_3538_);
lean_ctor_set(v___x_3548_, 1, v___x_3547_);
v___x_3549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3549_, 0, v_snd_3523_);
lean_ctor_set(v___x_3549_, 1, v___x_3548_);
v___x_3550_ = l_Lean_mkConst(v___x_3544_, v___x_3549_);
v___x_3551_ = lean_unsigned_to_nat(7u);
v___x_3552_ = lean_mk_empty_array_with_capacity(v___x_3551_);
v___x_3553_ = lean_array_push(v___x_3552_, v_00_u03b1_3527_);
v___x_3554_ = lean_array_push(v___x_3553_, v_00_u03b2_3528_);
v___x_3555_ = lean_array_push(v___x_3554_, v_fst_3522_);
v___x_3556_ = lean_array_push(v___x_3555_, v_x_3472_);
v___x_3557_ = lean_array_push(v___x_3556_, v_a_3532_);
v___x_3558_ = lean_array_push(v___x_3557_, v_a_3536_);
v___x_3559_ = lean_array_push(v___x_3558_, v_F_3473_);
v___x_3560_ = l_Lean_mkAppN(v___x_3550_, v___x_3559_);
lean_dec_ref(v___x_3559_);
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 0, v___x_3560_);
v___x_3562_ = v___x_3542_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v___x_3560_);
v___x_3562_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
return v___x_3562_;
}
}
}
}
else
{
lean_object* v_a_3566_; lean_object* v___x_3568_; uint8_t v_isShared_3569_; uint8_t v_isSharedCheck_3573_; 
lean_dec(v_a_3538_);
lean_dec(v_a_3536_);
lean_dec(v_a_3532_);
lean_dec(v_00_u03b2_3528_);
lean_dec(v_00_u03b1_3527_);
lean_del_object(v___x_3525_);
lean_dec(v_snd_3523_);
lean_dec(v_fst_3522_);
lean_dec_ref(v_F_3473_);
lean_dec_ref(v_x_3472_);
v_a_3566_ = lean_ctor_get(v___x_3539_, 0);
v_isSharedCheck_3573_ = !lean_is_exclusive(v___x_3539_);
if (v_isSharedCheck_3573_ == 0)
{
v___x_3568_ = v___x_3539_;
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
else
{
lean_inc(v_a_3566_);
lean_dec(v___x_3539_);
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
lean_object* v_a_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3581_; 
lean_dec(v_a_3536_);
lean_dec(v_a_3532_);
lean_dec(v_00_u03b2_3528_);
lean_dec(v_00_u03b1_3527_);
lean_del_object(v___x_3525_);
lean_dec(v_snd_3523_);
lean_dec(v_fst_3522_);
lean_dec_ref(v_F_3473_);
lean_dec_ref(v_x_3472_);
v_a_3574_ = lean_ctor_get(v___x_3537_, 0);
v_isSharedCheck_3581_ = !lean_is_exclusive(v___x_3537_);
if (v_isSharedCheck_3581_ == 0)
{
v___x_3576_ = v___x_3537_;
v_isShared_3577_ = v_isSharedCheck_3581_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_a_3574_);
lean_dec(v___x_3537_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3581_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v___x_3579_; 
if (v_isShared_3577_ == 0)
{
v___x_3579_ = v___x_3576_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v_a_3574_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
return v___x_3579_;
}
}
}
}
else
{
lean_dec(v_a_3532_);
lean_dec(v_00_u03b2_3528_);
lean_dec(v_00_u03b1_3527_);
lean_del_object(v___x_3525_);
lean_dec(v_snd_3523_);
lean_dec(v_fst_3522_);
lean_dec_ref(v_F_3473_);
lean_dec_ref(v_x_3472_);
return v___x_3535_;
}
}
else
{
lean_dec(v_00_u03b2_3528_);
lean_dec(v_00_u03b1_3527_);
lean_del_object(v___x_3525_);
lean_dec(v_snd_3523_);
lean_dec(v_fst_3522_);
lean_dec_ref(v_args_3513_);
lean_dec(v_a_3508_);
lean_dec_ref(v_k_3475_);
lean_dec_ref(v_F_3473_);
lean_dec_ref(v_x_3472_);
return v___x_3531_;
}
}
}
else
{
lean_object* v_a_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3590_; 
lean_dec_ref(v_args_3513_);
lean_dec(v_a_3508_);
lean_dec_ref(v_k_3475_);
lean_dec_ref(v_F_3473_);
lean_dec_ref(v_x_3472_);
v_a_3583_ = lean_ctor_get(v___x_3520_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_3520_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3585_ = v___x_3520_;
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_a_3583_);
lean_dec(v___x_3520_);
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
else
{
lean_object* v_a_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3598_; 
lean_dec(v___x_3487_);
lean_dec_ref(v_k_3475_);
lean_dec_ref(v_val_3474_);
lean_dec_ref(v_F_3473_);
lean_dec_ref(v_x_3472_);
v_a_3591_ = lean_ctor_get(v___x_3507_, 0);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3593_ = v___x_3507_;
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_a_3591_);
lean_dec(v___x_3507_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v___x_3596_; 
if (v_isShared_3594_ == 0)
{
v___x_3596_ = v___x_3593_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_a_3591_);
v___x_3596_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
return v___x_3596_;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1(lean_object* v___x_3603_, lean_object* v_body_3604_, lean_object* v_k_3605_, lean_object* v___x_3606_, uint8_t v___x_3607_, uint8_t v___x_3608_, lean_object* v_FNew_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_){
_start:
{
lean_object* v___x_3617_; 
lean_inc_ref(v_FNew_3609_);
lean_inc_ref(v___x_3603_);
v___x_3617_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v___x_3603_, v_FNew_3609_, v_body_3604_, v_k_3605_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_);
if (lean_obj_tag(v___x_3617_) == 0)
{
lean_object* v_a_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; uint8_t v___x_3622_; lean_object* v___x_3623_; 
v_a_3618_ = lean_ctor_get(v___x_3617_, 0);
lean_inc(v_a_3618_);
lean_dec_ref_known(v___x_3617_, 1);
v___x_3619_ = lean_mk_empty_array_with_capacity(v___x_3606_);
v___x_3620_ = lean_array_push(v___x_3619_, v___x_3603_);
v___x_3621_ = lean_array_push(v___x_3620_, v_FNew_3609_);
v___x_3622_ = 1;
v___x_3623_ = l_Lean_Meta_mkLambdaFVars(v___x_3621_, v_a_3618_, v___x_3607_, v___x_3608_, v___x_3607_, v___x_3608_, v___x_3622_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_);
lean_dec_ref(v___x_3621_);
return v___x_3623_;
}
else
{
lean_dec_ref(v_FNew_3609_);
lean_dec_ref(v___x_3603_);
return v___x_3617_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1___boxed(lean_object* v___x_3624_, lean_object* v_body_3625_, lean_object* v_k_3626_, lean_object* v___x_3627_, lean_object* v___x_3628_, lean_object* v___x_3629_, lean_object* v_FNew_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_){
_start:
{
uint8_t v___x_6949__boxed_3638_; uint8_t v___x_6950__boxed_3639_; lean_object* v_res_3640_; 
v___x_6949__boxed_3638_ = lean_unbox(v___x_3628_);
v___x_6950__boxed_3639_ = lean_unbox(v___x_3629_);
v_res_3640_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1(v___x_3624_, v_body_3625_, v_k_3626_, v___x_3627_, v___x_6949__boxed_3638_, v___x_6950__boxed_3639_, v_FNew_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec(v___y_3634_);
lean_dec_ref(v___y_3633_);
lean_dec(v___y_3632_);
lean_dec_ref(v___y_3631_);
lean_dec(v___x_3627_);
return v_res_3640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2(lean_object* v___x_3641_, lean_object* v___x_3642_, lean_object* v_00_u03b1_3643_, lean_object* v_00_u03b2_3644_, lean_object* v___x_3645_, lean_object* v_ctorName_3646_, lean_object* v_k_3647_, lean_object* v___x_3648_, uint8_t v___x_3649_, uint8_t v___x_3650_, lean_object* v_a_3651_, lean_object* v_x_3652_, lean_object* v_xs_3653_, lean_object* v_body_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_){
_start:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; 
v___x_3662_ = lean_array_get_borrowed(v___x_3641_, v_xs_3653_, v___x_3642_);
v___x_3663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3663_, 0, v_00_u03b1_3643_);
v___x_3664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3664_, 0, v_00_u03b2_3644_);
lean_inc(v___x_3662_);
v___x_3665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3665_, 0, v___x_3662_);
v___x_3666_ = lean_mk_empty_array_with_capacity(v___x_3645_);
v___x_3667_ = lean_array_push(v___x_3666_, v___x_3663_);
v___x_3668_ = lean_array_push(v___x_3667_, v___x_3664_);
v___x_3669_ = lean_array_push(v___x_3668_, v___x_3665_);
v___x_3670_ = l_Lean_Meta_mkAppOptM(v_ctorName_3646_, v___x_3669_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_object* v_a_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___f_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; 
v_a_3671_ = lean_ctor_get(v___x_3670_, 0);
lean_inc(v_a_3671_);
lean_dec_ref_known(v___x_3670_, 1);
v___x_3672_ = lean_box(v___x_3649_);
v___x_3673_ = lean_box(v___x_3650_);
lean_inc(v___x_3662_);
v___f_3674_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__1___boxed), 14, 6);
lean_closure_set(v___f_3674_, 0, v___x_3662_);
lean_closure_set(v___f_3674_, 1, v_body_3654_);
lean_closure_set(v___f_3674_, 2, v_k_3647_);
lean_closure_set(v___f_3674_, 3, v___x_3648_);
lean_closure_set(v___f_3674_, 4, v___x_3672_);
lean_closure_set(v___f_3674_, 5, v___x_3673_);
v___x_3675_ = l_Lean_LocalDecl_type(v_a_3651_);
v___x_3676_ = l_Lean_Expr_replaceFVar(v___x_3675_, v_x_3652_, v_a_3671_);
lean_dec(v_a_3671_);
lean_dec_ref(v___x_3675_);
v___x_3677_ = l_Lean_LocalDecl_userName(v_a_3651_);
v___x_3678_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v___x_3677_, v___x_3676_, v___f_3674_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
return v___x_3678_;
}
else
{
lean_dec_ref(v_body_3654_);
lean_dec_ref(v_x_3652_);
lean_dec(v___x_3648_);
lean_dec_ref(v_k_3647_);
return v___x_3670_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2___boxed(lean_object** _args){
lean_object* v___x_3679_ = _args[0];
lean_object* v___x_3680_ = _args[1];
lean_object* v_00_u03b1_3681_ = _args[2];
lean_object* v_00_u03b2_3682_ = _args[3];
lean_object* v___x_3683_ = _args[4];
lean_object* v_ctorName_3684_ = _args[5];
lean_object* v_k_3685_ = _args[6];
lean_object* v___x_3686_ = _args[7];
lean_object* v___x_3687_ = _args[8];
lean_object* v___x_3688_ = _args[9];
lean_object* v_a_3689_ = _args[10];
lean_object* v_x_3690_ = _args[11];
lean_object* v_xs_3691_ = _args[12];
lean_object* v_body_3692_ = _args[13];
lean_object* v___y_3693_ = _args[14];
lean_object* v___y_3694_ = _args[15];
lean_object* v___y_3695_ = _args[16];
lean_object* v___y_3696_ = _args[17];
lean_object* v___y_3697_ = _args[18];
lean_object* v___y_3698_ = _args[19];
lean_object* v___y_3699_ = _args[20];
_start:
{
uint8_t v___x_6970__boxed_3700_; uint8_t v___x_6971__boxed_3701_; lean_object* v_res_3702_; 
v___x_6970__boxed_3700_ = lean_unbox(v___x_3687_);
v___x_6971__boxed_3701_ = lean_unbox(v___x_3688_);
v_res_3702_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2(v___x_3679_, v___x_3680_, v_00_u03b1_3681_, v_00_u03b2_3682_, v___x_3683_, v_ctorName_3684_, v_k_3685_, v___x_3686_, v___x_6970__boxed_3700_, v___x_6971__boxed_3701_, v_a_3689_, v_x_3690_, v_xs_3691_, v_body_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_);
lean_dec(v___y_3698_);
lean_dec_ref(v___y_3697_);
lean_dec(v___y_3696_);
lean_dec_ref(v___y_3695_);
lean_dec(v___y_3694_);
lean_dec_ref(v___y_3693_);
lean_dec_ref(v_xs_3691_);
lean_dec_ref(v_a_3689_);
lean_dec(v___x_3683_);
lean_dec(v___x_3680_);
lean_dec_ref(v___x_3679_);
return v_res_3702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(lean_object* v___x_3703_, lean_object* v___x_3704_, lean_object* v_00_u03b1_3705_, lean_object* v_00_u03b2_3706_, lean_object* v___x_3707_, lean_object* v_k_3708_, lean_object* v___x_3709_, uint8_t v___x_3710_, uint8_t v___x_3711_, lean_object* v_a_3712_, lean_object* v_x_3713_, lean_object* v___x_3714_, lean_object* v_ctorName_3715_, lean_object* v_minor_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_){
_start:
{
lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___f_3726_; lean_object* v___x_3727_; 
v___x_3724_ = lean_box(v___x_3710_);
v___x_3725_ = lean_box(v___x_3711_);
v___f_3726_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__2___boxed), 21, 12);
lean_closure_set(v___f_3726_, 0, v___x_3703_);
lean_closure_set(v___f_3726_, 1, v___x_3704_);
lean_closure_set(v___f_3726_, 2, v_00_u03b1_3705_);
lean_closure_set(v___f_3726_, 3, v_00_u03b2_3706_);
lean_closure_set(v___f_3726_, 4, v___x_3707_);
lean_closure_set(v___f_3726_, 5, v_ctorName_3715_);
lean_closure_set(v___f_3726_, 6, v_k_3708_);
lean_closure_set(v___f_3726_, 7, v___x_3709_);
lean_closure_set(v___f_3726_, 8, v___x_3724_);
lean_closure_set(v___f_3726_, 9, v___x_3725_);
lean_closure_set(v___f_3726_, 10, v_a_3712_);
lean_closure_set(v___f_3726_, 11, v_x_3713_);
v___x_3727_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__2___redArg(v_minor_3716_, v___x_3714_, v___f_3726_, v___x_3710_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_);
return v___x_3727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3___boxed(lean_object** _args){
lean_object* v___x_3728_ = _args[0];
lean_object* v___x_3729_ = _args[1];
lean_object* v_00_u03b1_3730_ = _args[2];
lean_object* v_00_u03b2_3731_ = _args[3];
lean_object* v___x_3732_ = _args[4];
lean_object* v_k_3733_ = _args[5];
lean_object* v___x_3734_ = _args[6];
lean_object* v___x_3735_ = _args[7];
lean_object* v___x_3736_ = _args[8];
lean_object* v_a_3737_ = _args[9];
lean_object* v_x_3738_ = _args[10];
lean_object* v___x_3739_ = _args[11];
lean_object* v_ctorName_3740_ = _args[12];
lean_object* v_minor_3741_ = _args[13];
lean_object* v___y_3742_ = _args[14];
lean_object* v___y_3743_ = _args[15];
lean_object* v___y_3744_ = _args[16];
lean_object* v___y_3745_ = _args[17];
lean_object* v___y_3746_ = _args[18];
lean_object* v___y_3747_ = _args[19];
lean_object* v___y_3748_ = _args[20];
_start:
{
uint8_t v___x_6934__boxed_3749_; uint8_t v___x_6935__boxed_3750_; lean_object* v_res_3751_; 
v___x_6934__boxed_3749_ = lean_unbox(v___x_3735_);
v___x_6935__boxed_3750_ = lean_unbox(v___x_3736_);
v_res_3751_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__3(v___x_3728_, v___x_3729_, v_00_u03b1_3730_, v_00_u03b2_3731_, v___x_3732_, v_k_3733_, v___x_3734_, v___x_6934__boxed_3749_, v___x_6935__boxed_3750_, v_a_3737_, v_x_3738_, v___x_3739_, v_ctorName_3740_, v_minor_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_);
lean_dec(v___y_3747_);
lean_dec_ref(v___y_3746_);
lean_dec(v___y_3745_);
lean_dec_ref(v___y_3744_);
lean_dec(v___y_3743_);
lean_dec_ref(v___y_3742_);
return v_res_3751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___boxed(lean_object* v_x_3752_, lean_object* v_F_3753_, lean_object* v_val_3754_, lean_object* v_k_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_){
_start:
{
lean_object* v_res_3763_; 
v_res_3763_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn(v_x_3752_, v_F_3753_, v_val_3754_, v_k_3755_, v_a_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_);
lean_dec(v_a_3761_);
lean_dec_ref(v_a_3760_);
lean_dec(v_a_3759_);
lean_dec_ref(v_a_3758_);
lean_dec(v_a_3757_);
lean_dec_ref(v_a_3756_);
return v_res_3763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1(lean_object* v_00_u03b1_3764_, lean_object* v_name_3765_, uint8_t v_bi_3766_, lean_object* v_type_3767_, lean_object* v_k_3768_, uint8_t v_kind_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_){
_start:
{
lean_object* v___x_3777_; 
v___x_3777_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___redArg(v_name_3765_, v_bi_3766_, v_type_3767_, v_k_3768_, v_kind_3769_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_);
return v___x_3777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1___boxed(lean_object* v_00_u03b1_3778_, lean_object* v_name_3779_, lean_object* v_bi_3780_, lean_object* v_type_3781_, lean_object* v_k_3782_, lean_object* v_kind_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_){
_start:
{
uint8_t v_bi_boxed_3791_; uint8_t v_kind_boxed_3792_; lean_object* v_res_3793_; 
v_bi_boxed_3791_ = lean_unbox(v_bi_3780_);
v_kind_boxed_3792_ = lean_unbox(v_kind_3783_);
v_res_3793_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1_spec__1(v_00_u03b1_3778_, v_name_3779_, v_bi_boxed_3791_, v_type_3781_, v_k_3782_, v_kind_boxed_3792_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_);
lean_dec(v___y_3789_);
lean_dec_ref(v___y_3788_);
lean_dec(v___y_3787_);
lean_dec_ref(v___y_3786_);
lean_dec(v___y_3785_);
lean_dec_ref(v___y_3784_);
return v_res_3793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1(lean_object* v_00_u03b1_3794_, lean_object* v_name_3795_, lean_object* v_type_3796_, lean_object* v_k_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_){
_start:
{
lean_object* v___x_3805_; 
v___x_3805_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v_name_3795_, v_type_3796_, v_k_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_);
return v___x_3805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___boxed(lean_object* v_00_u03b1_3806_, lean_object* v_name_3807_, lean_object* v_type_3808_, lean_object* v_k_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_){
_start:
{
lean_object* v_res_3817_; 
v_res_3817_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1(v_00_u03b1_3806_, v_name_3807_, v_type_3808_, v_k_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_);
lean_dec(v___y_3815_);
lean_dec_ref(v___y_3814_);
lean_dec(v___y_3813_);
lean_dec_ref(v___y_3812_);
lean_dec(v___y_3811_);
lean_dec_ref(v___y_3810_);
return v_res_3817_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3818_; 
v___x_3818_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return v___x_3818_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(lean_object* v_msg_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_){
_start:
{
lean_object* v___x_3827_; lean_object* v___x_3874__overap_3828_; lean_object* v___x_3829_; 
v___x_3827_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0, &l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___closed__0);
v___x_3874__overap_3828_ = lean_panic_fn_borrowed(v___x_3827_, v_msg_3819_);
lean_inc(v___y_3825_);
lean_inc_ref(v___y_3824_);
lean_inc(v___y_3823_);
lean_inc_ref(v___y_3822_);
lean_inc(v___y_3821_);
lean_inc_ref(v___y_3820_);
v___x_3829_ = lean_apply_7(v___x_3874__overap_3828_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, lean_box(0));
return v___x_3829_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0___boxed(lean_object* v_msg_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_){
_start:
{
lean_object* v_res_3838_; 
v_res_3838_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(v_msg_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
return v_res_3838_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3(void){
_start:
{
lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; 
v___x_3842_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__2));
v___x_3843_ = lean_unsigned_to_nat(49u);
v___x_3844_ = lean_unsigned_to_nat(186u);
v___x_3845_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__1));
v___x_3846_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__0));
v___x_3847_ = l_mkPanicMessageWithDecl(v___x_3846_, v___x_3845_, v___x_3844_, v___x_3843_, v___x_3842_);
return v___x_3847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1___boxed(lean_object* v___x_3853_, lean_object* v_a_3854_, lean_object* v_k_3855_, lean_object* v___x_3856_, lean_object* v___x_3857_, lean_object* v___x_3858_, lean_object* v___x_3859_, lean_object* v___x_3860_, lean_object* v_FNew_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_){
_start:
{
uint8_t v___x_4042__boxed_3869_; uint8_t v___x_4043__boxed_3870_; uint8_t v___x_4044__boxed_3871_; lean_object* v_res_3872_; 
v___x_4042__boxed_3869_ = lean_unbox(v___x_3858_);
v___x_4043__boxed_3870_ = lean_unbox(v___x_3859_);
v___x_4044__boxed_3871_ = lean_unbox(v___x_3860_);
v_res_3872_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1(v___x_3853_, v_a_3854_, v_k_3855_, v___x_3856_, v___x_3857_, v___x_4042__boxed_3869_, v___x_4043__boxed_3870_, v___x_4044__boxed_3871_, v_FNew_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_);
lean_dec(v___y_3867_);
lean_dec_ref(v___y_3866_);
lean_dec(v___y_3865_);
lean_dec_ref(v___y_3864_);
lean_dec(v___y_3863_);
lean_dec_ref(v___y_3862_);
lean_dec(v___x_3856_);
return v_res_3872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0(lean_object* v___x_3873_, lean_object* v___x_3874_, lean_object* v___x_3875_, lean_object* v___x_3876_, uint8_t v___x_3877_, uint8_t v___x_3878_, lean_object* v_00_u03b1_3879_, lean_object* v_00_u03b2_3880_, lean_object* v___x_3881_, lean_object* v_k_3882_, lean_object* v___x_3883_, lean_object* v_a_3884_, lean_object* v_x_3885_, lean_object* v_xs_3886_, lean_object* v_body_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_){
_start:
{
lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; uint8_t v___x_3900_; lean_object* v___x_3901_; 
v___x_3895_ = lean_array_get(v___x_3873_, v_xs_3886_, v___x_3874_);
v___x_3896_ = lean_array_get(v___x_3873_, v_xs_3886_, v___x_3875_);
v___x_3897_ = lean_array_get_size(v_xs_3886_);
v___x_3898_ = l_Array_toSubarray___redArg(v_xs_3886_, v___x_3876_, v___x_3897_);
v___x_3899_ = l_Subarray_copy___redArg(v___x_3898_);
v___x_3900_ = 1;
v___x_3901_ = l_Lean_Meta_mkLambdaFVars(v___x_3899_, v_body_3887_, v___x_3877_, v___x_3878_, v___x_3877_, v___x_3878_, v___x_3900_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
lean_dec_ref(v___x_3899_);
if (lean_obj_tag(v___x_3901_) == 0)
{
lean_object* v_a_3902_; lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_3928_; 
v_a_3902_ = lean_ctor_get(v___x_3901_, 0);
v_isSharedCheck_3928_ = !lean_is_exclusive(v___x_3901_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3904_ = v___x_3901_;
v_isShared_3905_ = v_isSharedCheck_3928_;
goto v_resetjp_3903_;
}
else
{
lean_inc(v_a_3902_);
lean_dec(v___x_3901_);
v___x_3904_ = lean_box(0);
v_isShared_3905_ = v_isSharedCheck_3928_;
goto v_resetjp_3903_;
}
v_resetjp_3903_:
{
lean_object* v___x_3906_; lean_object* v___x_3908_; 
v___x_3906_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___closed__2));
if (v_isShared_3905_ == 0)
{
lean_ctor_set_tag(v___x_3904_, 1);
lean_ctor_set(v___x_3904_, 0, v_00_u03b1_3879_);
v___x_3908_ = v___x_3904_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_00_u03b1_3879_);
v___x_3908_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; 
v___x_3909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3909_, 0, v_00_u03b2_3880_);
lean_inc(v___x_3895_);
v___x_3910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3910_, 0, v___x_3895_);
lean_inc(v___x_3896_);
v___x_3911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3911_, 0, v___x_3896_);
v___x_3912_ = lean_mk_empty_array_with_capacity(v___x_3881_);
v___x_3913_ = lean_array_push(v___x_3912_, v___x_3908_);
v___x_3914_ = lean_array_push(v___x_3913_, v___x_3909_);
v___x_3915_ = lean_array_push(v___x_3914_, v___x_3910_);
v___x_3916_ = lean_array_push(v___x_3915_, v___x_3911_);
v___x_3917_ = l_Lean_Meta_mkAppOptM(v___x_3906_, v___x_3916_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
if (lean_obj_tag(v___x_3917_) == 0)
{
lean_object* v_a_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___f_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; 
v_a_3918_ = lean_ctor_get(v___x_3917_, 0);
lean_inc(v_a_3918_);
lean_dec_ref_known(v___x_3917_, 1);
v___x_3919_ = lean_box(v___x_3877_);
v___x_3920_ = lean_box(v___x_3878_);
v___x_3921_ = lean_box(v___x_3900_);
v___f_3922_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1___boxed), 16, 8);
lean_closure_set(v___f_3922_, 0, v___x_3896_);
lean_closure_set(v___f_3922_, 1, v_a_3902_);
lean_closure_set(v___f_3922_, 2, v_k_3882_);
lean_closure_set(v___f_3922_, 3, v___x_3883_);
lean_closure_set(v___f_3922_, 4, v___x_3895_);
lean_closure_set(v___f_3922_, 5, v___x_3919_);
lean_closure_set(v___f_3922_, 6, v___x_3920_);
lean_closure_set(v___f_3922_, 7, v___x_3921_);
v___x_3923_ = l_Lean_LocalDecl_type(v_a_3884_);
v___x_3924_ = l_Lean_Expr_replaceFVar(v___x_3923_, v_x_3885_, v_a_3918_);
lean_dec(v_a_3918_);
lean_dec_ref(v___x_3923_);
v___x_3925_ = l_Lean_LocalDecl_userName(v_a_3884_);
v___x_3926_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__1___redArg(v___x_3925_, v___x_3924_, v___f_3922_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_3926_;
}
else
{
lean_dec(v_a_3902_);
lean_dec(v___x_3896_);
lean_dec(v___x_3895_);
lean_dec_ref(v_x_3885_);
lean_dec(v___x_3883_);
lean_dec_ref(v_k_3882_);
return v___x_3917_;
}
}
}
}
else
{
lean_dec(v___x_3896_);
lean_dec(v___x_3895_);
lean_dec_ref(v_x_3885_);
lean_dec(v___x_3883_);
lean_dec_ref(v_k_3882_);
lean_dec_ref(v_00_u03b2_3880_);
lean_dec_ref(v_00_u03b1_3879_);
return v___x_3901_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___boxed(lean_object** _args){
lean_object* v___x_3929_ = _args[0];
lean_object* v___x_3930_ = _args[1];
lean_object* v___x_3931_ = _args[2];
lean_object* v___x_3932_ = _args[3];
lean_object* v___x_3933_ = _args[4];
lean_object* v___x_3934_ = _args[5];
lean_object* v_00_u03b1_3935_ = _args[6];
lean_object* v_00_u03b2_3936_ = _args[7];
lean_object* v___x_3937_ = _args[8];
lean_object* v_k_3938_ = _args[9];
lean_object* v___x_3939_ = _args[10];
lean_object* v_a_3940_ = _args[11];
lean_object* v_x_3941_ = _args[12];
lean_object* v_xs_3942_ = _args[13];
lean_object* v_body_3943_ = _args[14];
lean_object* v___y_3944_ = _args[15];
lean_object* v___y_3945_ = _args[16];
lean_object* v___y_3946_ = _args[17];
lean_object* v___y_3947_ = _args[18];
lean_object* v___y_3948_ = _args[19];
lean_object* v___y_3949_ = _args[20];
lean_object* v___y_3950_ = _args[21];
_start:
{
uint8_t v___x_4069__boxed_3951_; uint8_t v___x_4070__boxed_3952_; lean_object* v_res_3953_; 
v___x_4069__boxed_3951_ = lean_unbox(v___x_3933_);
v___x_4070__boxed_3952_ = lean_unbox(v___x_3934_);
v_res_3953_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0(v___x_3929_, v___x_3930_, v___x_3931_, v___x_3932_, v___x_4069__boxed_3951_, v___x_4070__boxed_3952_, v_00_u03b1_3935_, v_00_u03b2_3936_, v___x_3937_, v_k_3938_, v___x_3939_, v_a_3940_, v_x_3941_, v_xs_3942_, v_body_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
lean_dec(v___y_3945_);
lean_dec_ref(v___y_3944_);
lean_dec_ref(v_a_3940_);
lean_dec(v___x_3937_);
lean_dec(v___x_3931_);
lean_dec(v___x_3930_);
lean_dec_ref(v___x_3929_);
return v_res_3953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(lean_object* v_x_3957_, lean_object* v_F_3958_, lean_object* v_val_3959_, lean_object* v_k_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_){
_start:
{
lean_object* v___y_3969_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; lean_object* v___y_3973_; lean_object* v___y_3974_; uint8_t v___y_3978_; uint8_t v___x_4070_; 
v___x_4070_ = l_Lean_Expr_isFVar(v_x_3957_);
if (v___x_4070_ == 0)
{
v___y_3978_ = v___x_4070_;
goto v___jp_3977_;
}
else
{
lean_object* v___x_4071_; lean_object* v___x_4072_; uint8_t v___x_4073_; 
v___x_4071_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4));
v___x_4072_ = lean_unsigned_to_nat(5u);
v___x_4073_ = l_Lean_Expr_isAppOfArity(v_val_3959_, v___x_4071_, v___x_4072_);
v___y_3978_ = v___x_4073_;
goto v___jp_3977_;
}
v___jp_3968_:
{
lean_object* v___x_3975_; lean_object* v___x_3976_; 
v___x_3975_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__3);
v___x_3976_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn_spec__0(v___x_3975_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_);
return v___x_3976_;
}
v___jp_3977_:
{
if (v___y_3978_ == 0)
{
lean_object* v___x_3979_; 
lean_dec_ref(v_x_3957_);
lean_inc(v_a_3966_);
lean_inc_ref(v_a_3965_);
lean_inc(v_a_3964_);
lean_inc_ref(v_a_3963_);
lean_inc(v_a_3962_);
lean_inc_ref(v_a_3961_);
v___x_3979_ = lean_apply_9(v_k_3960_, v_F_3958_, v_val_3959_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_, lean_box(0));
return v___x_3979_;
}
else
{
lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; uint8_t v___x_3986_; 
v___x_3980_ = lean_unsigned_to_nat(3u);
v___x_3981_ = l_Lean_Expr_getAppNumArgs(v_val_3959_);
v___x_3982_ = lean_nat_sub(v___x_3981_, v___x_3980_);
v___x_3983_ = lean_unsigned_to_nat(1u);
v___x_3984_ = lean_nat_sub(v___x_3982_, v___x_3983_);
lean_dec(v___x_3982_);
v___x_3985_ = l_Lean_Expr_getRevArg_x21(v_val_3959_, v___x_3984_);
v___x_3986_ = lean_expr_eqv(v___x_3985_, v_x_3957_);
lean_dec_ref(v___x_3985_);
if (v___x_3986_ == 0)
{
lean_object* v___x_3987_; 
lean_dec(v___x_3981_);
lean_dec_ref(v_x_3957_);
lean_inc(v_a_3966_);
lean_inc_ref(v_a_3965_);
lean_inc(v_a_3964_);
lean_inc_ref(v_a_3963_);
lean_inc(v_a_3962_);
lean_inc_ref(v_a_3961_);
v___x_3987_ = lean_apply_9(v_k_3960_, v_F_3958_, v_val_3959_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_, lean_box(0));
return v___x_3987_;
}
else
{
lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; uint8_t v___x_3992_; 
v___x_3988_ = lean_unsigned_to_nat(4u);
v___x_3989_ = lean_nat_sub(v___x_3981_, v___x_3988_);
v___x_3990_ = lean_nat_sub(v___x_3989_, v___x_3983_);
lean_dec(v___x_3989_);
v___x_3991_ = l_Lean_Expr_getRevArg_x21(v_val_3959_, v___x_3990_);
v___x_3992_ = l_Lean_Expr_isLambda(v___x_3991_);
if (v___x_3992_ == 0)
{
lean_object* v___x_3993_; 
lean_dec_ref(v___x_3991_);
lean_dec(v___x_3981_);
lean_dec_ref(v_x_3957_);
lean_inc(v_a_3966_);
lean_inc_ref(v_a_3965_);
lean_inc(v_a_3964_);
lean_inc_ref(v_a_3963_);
lean_inc(v_a_3962_);
lean_inc_ref(v_a_3961_);
v___x_3993_ = lean_apply_9(v_k_3960_, v_F_3958_, v_val_3959_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_, lean_box(0));
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
lean_dec_ref(v_x_3957_);
lean_inc(v_a_3966_);
lean_inc_ref(v_a_3965_);
lean_inc(v_a_3964_);
lean_inc_ref(v_a_3963_);
lean_inc(v_a_3962_);
lean_inc_ref(v_a_3961_);
v___x_3996_ = lean_apply_9(v_k_3960_, v_F_3958_, v_val_3959_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_, lean_box(0));
return v___x_3996_;
}
else
{
lean_object* v___x_3997_; lean_object* v___x_3998_; 
v___x_3997_ = l_Lean_Expr_getAppFn(v_val_3959_);
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
lean_object* v_tail_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4068_; 
v_tail_4001_ = lean_ctor_get(v_tail_4000_, 1);
v_isSharedCheck_4068_ = !lean_is_exclusive(v_tail_4000_);
if (v_isSharedCheck_4068_ == 0)
{
lean_object* v_unused_4069_; 
v_unused_4069_ = lean_ctor_get(v_tail_4000_, 0);
lean_dec(v_unused_4069_);
v___x_4003_ = v_tail_4000_;
v_isShared_4004_ = v_isSharedCheck_4068_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_tail_4001_);
lean_dec(v_tail_4000_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4068_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
if (lean_obj_tag(v_tail_4001_) == 0)
{
lean_object* v___x_4005_; lean_object* v___x_4006_; 
v___x_4005_ = l_Lean_Expr_fvarId_x21(v_F_3958_);
v___x_4006_ = l_Lean_FVarId_getDecl___redArg(v___x_4005_, v_a_3963_, v_a_3965_, v_a_3966_);
if (lean_obj_tag(v___x_4006_) == 0)
{
lean_object* v_a_4007_; lean_object* v___x_4008_; lean_object* v_dummy_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v_args_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___f_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; uint8_t v___x_4018_; lean_object* v___x_4019_; 
v_a_4007_ = lean_ctor_get(v___x_4006_, 0);
lean_inc_n(v_a_4007_, 2);
lean_dec_ref_known(v___x_4006_, 1);
v___x_4008_ = l_Lean_instInhabitedExpr;
v_dummy_4009_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loopGo_spec__13___closed__0);
lean_inc(v___x_3981_);
v___x_4010_ = lean_mk_array(v___x_3981_, v_dummy_4009_);
v___x_4011_ = lean_nat_sub(v___x_3981_, v___x_3983_);
lean_dec(v___x_3981_);
v_args_4012_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_val_3959_, v___x_4010_, v___x_4011_);
v___x_4013_ = lean_unsigned_to_nat(0u);
v___x_4014_ = lean_box(v___x_3992_);
lean_inc_ref(v_x_3957_);
v___f_4015_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn___lam__0___boxed), 14, 5);
lean_closure_set(v___f_4015_, 0, v_a_4007_);
lean_closure_set(v___f_4015_, 1, v___x_4008_);
lean_closure_set(v___f_4015_, 2, v___x_4013_);
lean_closure_set(v___f_4015_, 3, v_x_3957_);
lean_closure_set(v___f_4015_, 4, v___x_4014_);
v___x_4016_ = lean_unsigned_to_nat(2u);
v___x_4017_ = lean_array_get(v___x_4008_, v_args_4012_, v___x_4016_);
v___x_4018_ = 0;
v___x_4019_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_4017_, v___f_4015_, v___x_4018_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_);
if (lean_obj_tag(v___x_4019_) == 0)
{
lean_object* v_a_4020_; lean_object* v_fst_4021_; lean_object* v_snd_4022_; lean_object* v_00_u03b1_4023_; lean_object* v_00_u03b2_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___f_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; 
v_a_4020_ = lean_ctor_get(v___x_4019_, 0);
lean_inc(v_a_4020_);
lean_dec_ref_known(v___x_4019_, 1);
v_fst_4021_ = lean_ctor_get(v_a_4020_, 0);
lean_inc(v_fst_4021_);
v_snd_4022_ = lean_ctor_get(v_a_4020_, 1);
lean_inc(v_snd_4022_);
lean_dec(v_a_4020_);
v_00_u03b1_4023_ = lean_array_get(v___x_4008_, v_args_4012_, v___x_4013_);
v_00_u03b2_4024_ = lean_array_get(v___x_4008_, v_args_4012_, v___x_3983_);
v___x_4025_ = lean_box(v___x_4018_);
v___x_4026_ = lean_box(v___x_3992_);
lean_inc_ref(v_x_3957_);
lean_inc(v_00_u03b2_4024_);
lean_inc(v_00_u03b1_4023_);
v___f_4027_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__0___boxed), 22, 13);
lean_closure_set(v___f_4027_, 0, v___x_4008_);
lean_closure_set(v___f_4027_, 1, v___x_4013_);
lean_closure_set(v___f_4027_, 2, v___x_3983_);
lean_closure_set(v___f_4027_, 3, v___x_4016_);
lean_closure_set(v___f_4027_, 4, v___x_4025_);
lean_closure_set(v___f_4027_, 5, v___x_4026_);
lean_closure_set(v___f_4027_, 6, v_00_u03b1_4023_);
lean_closure_set(v___f_4027_, 7, v_00_u03b2_4024_);
lean_closure_set(v___f_4027_, 8, v___x_3988_);
lean_closure_set(v___f_4027_, 9, v_k_3960_);
lean_closure_set(v___f_4027_, 10, v___x_3980_);
lean_closure_set(v___f_4027_, 11, v_a_4007_);
lean_closure_set(v___f_4027_, 12, v_x_3957_);
v___x_4028_ = lean_array_get(v___x_4008_, v_args_4012_, v___x_3988_);
lean_dec_ref(v_args_4012_);
v___x_4029_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processSumCasesOn_spec__0___redArg(v___x_4028_, v___f_4027_, v___x_4018_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_);
if (lean_obj_tag(v___x_4029_) == 0)
{
lean_object* v_a_4030_; lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4051_; 
v_a_4030_ = lean_ctor_get(v___x_4029_, 0);
v_isSharedCheck_4051_ = !lean_is_exclusive(v___x_4029_);
if (v_isSharedCheck_4051_ == 0)
{
v___x_4032_ = v___x_4029_;
v_isShared_4033_ = v_isSharedCheck_4051_;
goto v_resetjp_4031_;
}
else
{
lean_inc(v_a_4030_);
lean_dec(v___x_4029_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4051_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
lean_object* v___x_4034_; lean_object* v___x_4036_; 
v___x_4034_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___closed__4));
if (v_isShared_4004_ == 0)
{
lean_ctor_set(v___x_4003_, 1, v_tail_3999_);
lean_ctor_set(v___x_4003_, 0, v_snd_4022_);
v___x_4036_ = v___x_4003_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_snd_4022_);
lean_ctor_set(v_reuseFailAlloc_4050_, 1, v_tail_3999_);
v___x_4036_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4048_; 
v___x_4037_ = l_Lean_mkConst(v___x_4034_, v___x_4036_);
v___x_4038_ = lean_unsigned_to_nat(6u);
v___x_4039_ = lean_mk_empty_array_with_capacity(v___x_4038_);
v___x_4040_ = lean_array_push(v___x_4039_, v_00_u03b1_4023_);
v___x_4041_ = lean_array_push(v___x_4040_, v_00_u03b2_4024_);
v___x_4042_ = lean_array_push(v___x_4041_, v_fst_4021_);
v___x_4043_ = lean_array_push(v___x_4042_, v_x_3957_);
v___x_4044_ = lean_array_push(v___x_4043_, v_a_4030_);
v___x_4045_ = lean_array_push(v___x_4044_, v_F_3958_);
v___x_4046_ = l_Lean_mkAppN(v___x_4037_, v___x_4045_);
lean_dec_ref(v___x_4045_);
if (v_isShared_4033_ == 0)
{
lean_ctor_set(v___x_4032_, 0, v___x_4046_);
v___x_4048_ = v___x_4032_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v___x_4046_);
v___x_4048_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
return v___x_4048_;
}
}
}
}
else
{
lean_dec(v_00_u03b2_4024_);
lean_dec(v_00_u03b1_4023_);
lean_dec(v_snd_4022_);
lean_dec(v_fst_4021_);
lean_del_object(v___x_4003_);
lean_dec_ref_known(v_tail_3999_, 2);
lean_dec_ref(v_F_3958_);
lean_dec_ref(v_x_3957_);
return v___x_4029_;
}
}
else
{
lean_object* v_a_4052_; lean_object* v___x_4054_; uint8_t v_isShared_4055_; uint8_t v_isSharedCheck_4059_; 
lean_dec_ref(v_args_4012_);
lean_dec(v_a_4007_);
lean_del_object(v___x_4003_);
lean_dec_ref_known(v_tail_3999_, 2);
lean_dec_ref(v_k_3960_);
lean_dec_ref(v_F_3958_);
lean_dec_ref(v_x_3957_);
v_a_4052_ = lean_ctor_get(v___x_4019_, 0);
v_isSharedCheck_4059_ = !lean_is_exclusive(v___x_4019_);
if (v_isSharedCheck_4059_ == 0)
{
v___x_4054_ = v___x_4019_;
v_isShared_4055_ = v_isSharedCheck_4059_;
goto v_resetjp_4053_;
}
else
{
lean_inc(v_a_4052_);
lean_dec(v___x_4019_);
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
lean_object* v_a_4060_; lean_object* v___x_4062_; uint8_t v_isShared_4063_; uint8_t v_isSharedCheck_4067_; 
lean_del_object(v___x_4003_);
lean_dec_ref_known(v_tail_3999_, 2);
lean_dec(v___x_3981_);
lean_dec_ref(v_k_3960_);
lean_dec_ref(v_val_3959_);
lean_dec_ref(v_F_3958_);
lean_dec_ref(v_x_3957_);
v_a_4060_ = lean_ctor_get(v___x_4006_, 0);
v_isSharedCheck_4067_ = !lean_is_exclusive(v___x_4006_);
if (v_isSharedCheck_4067_ == 0)
{
v___x_4062_ = v___x_4006_;
v_isShared_4063_ = v_isSharedCheck_4067_;
goto v_resetjp_4061_;
}
else
{
lean_inc(v_a_4060_);
lean_dec(v___x_4006_);
v___x_4062_ = lean_box(0);
v_isShared_4063_ = v_isSharedCheck_4067_;
goto v_resetjp_4061_;
}
v_resetjp_4061_:
{
lean_object* v___x_4065_; 
if (v_isShared_4063_ == 0)
{
v___x_4065_ = v___x_4062_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v_a_4060_);
v___x_4065_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
return v___x_4065_;
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
lean_dec_ref(v_k_3960_);
lean_dec_ref(v_val_3959_);
lean_dec_ref(v_F_3958_);
lean_dec_ref(v_x_3957_);
v___y_3969_ = v_a_3961_;
v___y_3970_ = v_a_3962_;
v___y_3971_ = v_a_3963_;
v___y_3972_ = v_a_3964_;
v___y_3973_ = v_a_3965_;
v___y_3974_ = v_a_3966_;
goto v___jp_3968_;
}
}
}
else
{
lean_dec(v_tail_4000_);
lean_dec_ref_known(v_tail_3999_, 2);
lean_dec(v___x_3981_);
lean_dec_ref(v_k_3960_);
lean_dec_ref(v_val_3959_);
lean_dec_ref(v_F_3958_);
lean_dec_ref(v_x_3957_);
v___y_3969_ = v_a_3961_;
v___y_3970_ = v_a_3962_;
v___y_3971_ = v_a_3963_;
v___y_3972_ = v_a_3964_;
v___y_3973_ = v_a_3965_;
v___y_3974_ = v_a_3966_;
goto v___jp_3968_;
}
}
else
{
lean_dec(v_tail_3999_);
lean_dec(v___x_3981_);
lean_dec_ref(v_k_3960_);
lean_dec_ref(v_val_3959_);
lean_dec_ref(v_F_3958_);
lean_dec_ref(v_x_3957_);
v___y_3969_ = v_a_3961_;
v___y_3970_ = v_a_3962_;
v___y_3971_ = v_a_3963_;
v___y_3972_ = v_a_3964_;
v___y_3973_ = v_a_3965_;
v___y_3974_ = v_a_3966_;
goto v___jp_3968_;
}
}
else
{
lean_dec(v___x_3998_);
lean_dec(v___x_3981_);
lean_dec_ref(v_k_3960_);
lean_dec_ref(v_val_3959_);
lean_dec_ref(v_F_3958_);
lean_dec_ref(v_x_3957_);
v___y_3969_ = v_a_3961_;
v___y_3970_ = v_a_3962_;
v___y_3971_ = v_a_3963_;
v___y_3972_ = v_a_3964_;
v___y_3973_ = v_a_3965_;
v___y_3974_ = v_a_3966_;
goto v___jp_3968_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___lam__1(lean_object* v___x_4074_, lean_object* v_a_4075_, lean_object* v_k_4076_, lean_object* v___x_4077_, lean_object* v___x_4078_, uint8_t v___x_4079_, uint8_t v___x_4080_, uint8_t v___x_4081_, lean_object* v_FNew_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_){
_start:
{
lean_object* v___x_4090_; 
lean_inc_ref(v_FNew_4082_);
lean_inc_ref(v___x_4074_);
v___x_4090_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v___x_4074_, v_FNew_4082_, v_a_4075_, v_k_4076_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_);
if (lean_obj_tag(v___x_4090_) == 0)
{
lean_object* v_a_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; 
v_a_4091_ = lean_ctor_get(v___x_4090_, 0);
lean_inc(v_a_4091_);
lean_dec_ref_known(v___x_4090_, 1);
v___x_4092_ = lean_mk_empty_array_with_capacity(v___x_4077_);
v___x_4093_ = lean_array_push(v___x_4092_, v___x_4078_);
v___x_4094_ = lean_array_push(v___x_4093_, v___x_4074_);
v___x_4095_ = lean_array_push(v___x_4094_, v_FNew_4082_);
v___x_4096_ = l_Lean_Meta_mkLambdaFVars(v___x_4095_, v_a_4091_, v___x_4079_, v___x_4080_, v___x_4079_, v___x_4080_, v___x_4081_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_);
lean_dec_ref(v___x_4095_);
return v___x_4096_;
}
else
{
lean_dec_ref(v_FNew_4082_);
lean_dec_ref(v___x_4078_);
lean_dec_ref(v___x_4074_);
return v___x_4090_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn___boxed(lean_object* v_x_4097_, lean_object* v_F_4098_, lean_object* v_val_4099_, lean_object* v_k_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_){
_start:
{
lean_object* v_res_4108_; 
v_res_4108_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_processPSigmaCasesOn(v_x_4097_, v_F_4098_, v_val_4099_, v_k_4100_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_);
lean_dec(v_a_4106_);
lean_dec_ref(v_a_4105_);
lean_dec(v_a_4104_);
lean_dec_ref(v_a_4103_);
lean_dec(v_a_4102_);
lean_dec_ref(v_a_4101_);
return v_res_4108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0(lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_){
_start:
{
lean_object* v___x_4122_; 
v___x_4122_ = l_Lean_Elab_WF_applyCleanWfTactic(v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_);
if (lean_obj_tag(v___x_4122_) == 0)
{
lean_object* v_ref_4123_; uint8_t v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; 
lean_dec_ref_known(v___x_4122_, 1);
v_ref_4123_ = lean_ctor_get(v___y_4119_, 5);
v___x_4124_ = 0;
v___x_4125_ = l_Lean_SourceInfo_fromRef(v_ref_4123_, v___x_4124_);
v___x_4126_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__1));
v___x_4127_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___closed__2));
lean_inc(v___x_4125_);
v___x_4128_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4128_, 0, v___x_4125_);
lean_ctor_set(v___x_4128_, 1, v___x_4127_);
v___x_4129_ = l_Lean_Syntax_node1(v___x_4125_, v___x_4126_, v___x_4128_);
v___x_4130_ = l_Lean_Elab_Tactic_evalTactic(v___x_4129_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_);
return v___x_4130_;
}
else
{
return v___x_4122_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0___boxed(lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_){
_start:
{
lean_object* v_res_4140_; 
v_res_4140_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___lam__0(v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_);
lean_dec(v___y_4138_);
lean_dec_ref(v___y_4137_);
lean_dec(v___y_4136_);
lean_dec_ref(v___y_4135_);
lean_dec(v___y_4134_);
lean_dec_ref(v___y_4133_);
lean_dec(v___y_4132_);
lean_dec_ref(v___y_4131_);
return v_res_4140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(lean_object* v_mvarId_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_){
_start:
{
lean_object* v___f_4150_; lean_object* v___x_4151_; 
v___f_4150_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___closed__0));
v___x_4151_ = l_Lean_Elab_Tactic_run(v_mvarId_4142_, v___f_4150_, v_a_4143_, v_a_4144_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_);
if (lean_obj_tag(v___x_4151_) == 0)
{
lean_object* v_a_4152_; lean_object* v___x_4154_; uint8_t v_isShared_4155_; uint8_t v_isSharedCheck_4162_; 
v_a_4152_ = lean_ctor_get(v___x_4151_, 0);
v_isSharedCheck_4162_ = !lean_is_exclusive(v___x_4151_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4154_ = v___x_4151_;
v_isShared_4155_ = v_isSharedCheck_4162_;
goto v_resetjp_4153_;
}
else
{
lean_inc(v_a_4152_);
lean_dec(v___x_4151_);
v___x_4154_ = lean_box(0);
v_isShared_4155_ = v_isSharedCheck_4162_;
goto v_resetjp_4153_;
}
v_resetjp_4153_:
{
uint8_t v___x_4156_; 
v___x_4156_ = l_List_isEmpty___redArg(v_a_4152_);
if (v___x_4156_ == 0)
{
lean_object* v___x_4157_; 
lean_del_object(v___x_4154_);
v___x_4157_ = l_Lean_Elab_Term_reportUnsolvedGoals(v_a_4152_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_);
return v___x_4157_;
}
else
{
lean_object* v___x_4158_; lean_object* v___x_4160_; 
lean_dec(v_a_4152_);
v___x_4158_ = lean_box(0);
if (v_isShared_4155_ == 0)
{
lean_ctor_set(v___x_4154_, 0, v___x_4158_);
v___x_4160_ = v___x_4154_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v___x_4158_);
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
else
{
lean_object* v_a_4163_; lean_object* v___x_4165_; uint8_t v_isShared_4166_; uint8_t v_isSharedCheck_4170_; 
v_a_4163_ = lean_ctor_get(v___x_4151_, 0);
v_isSharedCheck_4170_ = !lean_is_exclusive(v___x_4151_);
if (v_isSharedCheck_4170_ == 0)
{
v___x_4165_ = v___x_4151_;
v_isShared_4166_ = v_isSharedCheck_4170_;
goto v_resetjp_4164_;
}
else
{
lean_inc(v_a_4163_);
lean_dec(v___x_4151_);
v___x_4165_ = lean_box(0);
v_isShared_4166_ = v_isSharedCheck_4170_;
goto v_resetjp_4164_;
}
v_resetjp_4164_:
{
lean_object* v___x_4168_; 
if (v_isShared_4166_ == 0)
{
v___x_4168_ = v___x_4165_;
goto v_reusejp_4167_;
}
else
{
lean_object* v_reuseFailAlloc_4169_; 
v_reuseFailAlloc_4169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4169_, 0, v_a_4163_);
v___x_4168_ = v_reuseFailAlloc_4169_;
goto v_reusejp_4167_;
}
v_reusejp_4167_:
{
return v___x_4168_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic___boxed(lean_object* v_mvarId_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_){
_start:
{
lean_object* v_res_4179_; 
v_res_4179_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(v_mvarId_4171_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_, v_a_4176_, v_a_4177_);
lean_dec(v_a_4177_);
lean_dec_ref(v_a_4176_);
lean_dec(v_a_4175_);
lean_dec_ref(v_a_4174_);
lean_dec(v_a_4173_);
lean_dec_ref(v_a_4172_);
return v_res_4179_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(lean_object* v_x_4180_, lean_object* v_x_4181_, lean_object* v_x_4182_, lean_object* v_x_4183_){
_start:
{
lean_object* v_ks_4184_; lean_object* v_vs_4185_; lean_object* v___x_4187_; uint8_t v_isShared_4188_; uint8_t v_isSharedCheck_4209_; 
v_ks_4184_ = lean_ctor_get(v_x_4180_, 0);
v_vs_4185_ = lean_ctor_get(v_x_4180_, 1);
v_isSharedCheck_4209_ = !lean_is_exclusive(v_x_4180_);
if (v_isSharedCheck_4209_ == 0)
{
v___x_4187_ = v_x_4180_;
v_isShared_4188_ = v_isSharedCheck_4209_;
goto v_resetjp_4186_;
}
else
{
lean_inc(v_vs_4185_);
lean_inc(v_ks_4184_);
lean_dec(v_x_4180_);
v___x_4187_ = lean_box(0);
v_isShared_4188_ = v_isSharedCheck_4209_;
goto v_resetjp_4186_;
}
v_resetjp_4186_:
{
lean_object* v___x_4189_; uint8_t v___x_4190_; 
v___x_4189_ = lean_array_get_size(v_ks_4184_);
v___x_4190_ = lean_nat_dec_lt(v_x_4181_, v___x_4189_);
if (v___x_4190_ == 0)
{
lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4194_; 
lean_dec(v_x_4181_);
v___x_4191_ = lean_array_push(v_ks_4184_, v_x_4182_);
v___x_4192_ = lean_array_push(v_vs_4185_, v_x_4183_);
if (v_isShared_4188_ == 0)
{
lean_ctor_set(v___x_4187_, 1, v___x_4192_);
lean_ctor_set(v___x_4187_, 0, v___x_4191_);
v___x_4194_ = v___x_4187_;
goto v_reusejp_4193_;
}
else
{
lean_object* v_reuseFailAlloc_4195_; 
v_reuseFailAlloc_4195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4195_, 0, v___x_4191_);
lean_ctor_set(v_reuseFailAlloc_4195_, 1, v___x_4192_);
v___x_4194_ = v_reuseFailAlloc_4195_;
goto v_reusejp_4193_;
}
v_reusejp_4193_:
{
return v___x_4194_;
}
}
else
{
lean_object* v_k_x27_4196_; uint8_t v___x_4197_; 
v_k_x27_4196_ = lean_array_fget_borrowed(v_ks_4184_, v_x_4181_);
v___x_4197_ = l_Lean_instBEqMVarId_beq(v_x_4182_, v_k_x27_4196_);
if (v___x_4197_ == 0)
{
lean_object* v___x_4199_; 
if (v_isShared_4188_ == 0)
{
v___x_4199_ = v___x_4187_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4203_; 
v_reuseFailAlloc_4203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4203_, 0, v_ks_4184_);
lean_ctor_set(v_reuseFailAlloc_4203_, 1, v_vs_4185_);
v___x_4199_ = v_reuseFailAlloc_4203_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
lean_object* v___x_4200_; lean_object* v___x_4201_; 
v___x_4200_ = lean_unsigned_to_nat(1u);
v___x_4201_ = lean_nat_add(v_x_4181_, v___x_4200_);
lean_dec(v_x_4181_);
v_x_4180_ = v___x_4199_;
v_x_4181_ = v___x_4201_;
goto _start;
}
}
else
{
lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4207_; 
v___x_4204_ = lean_array_fset(v_ks_4184_, v_x_4181_, v_x_4182_);
v___x_4205_ = lean_array_fset(v_vs_4185_, v_x_4181_, v_x_4183_);
lean_dec(v_x_4181_);
if (v_isShared_4188_ == 0)
{
lean_ctor_set(v___x_4187_, 1, v___x_4205_);
lean_ctor_set(v___x_4187_, 0, v___x_4204_);
v___x_4207_ = v___x_4187_;
goto v_reusejp_4206_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v___x_4204_);
lean_ctor_set(v_reuseFailAlloc_4208_, 1, v___x_4205_);
v___x_4207_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4206_;
}
v_reusejp_4206_:
{
return v___x_4207_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_n_4210_, lean_object* v_k_4211_, lean_object* v_v_4212_){
_start:
{
lean_object* v___x_4213_; lean_object* v___x_4214_; 
v___x_4213_ = lean_unsigned_to_nat(0u);
v___x_4214_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_n_4210_, v___x_4213_, v_k_4211_, v_v_4212_);
return v___x_4214_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4215_; 
v___x_4215_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4215_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(lean_object* v_x_4216_, size_t v_x_4217_, size_t v_x_4218_, lean_object* v_x_4219_, lean_object* v_x_4220_){
_start:
{
if (lean_obj_tag(v_x_4216_) == 0)
{
lean_object* v_es_4221_; size_t v___x_4222_; size_t v___x_4223_; lean_object* v_j_4224_; lean_object* v___x_4225_; uint8_t v___x_4226_; 
v_es_4221_ = lean_ctor_get(v_x_4216_, 0);
v___x_4222_ = ((size_t)31ULL);
v___x_4223_ = lean_usize_land(v_x_4217_, v___x_4222_);
v_j_4224_ = lean_usize_to_nat(v___x_4223_);
v___x_4225_ = lean_array_get_size(v_es_4221_);
v___x_4226_ = lean_nat_dec_lt(v_j_4224_, v___x_4225_);
if (v___x_4226_ == 0)
{
lean_dec(v_j_4224_);
lean_dec(v_x_4220_);
lean_dec(v_x_4219_);
return v_x_4216_;
}
else
{
lean_object* v___x_4228_; uint8_t v_isShared_4229_; uint8_t v_isSharedCheck_4265_; 
lean_inc_ref(v_es_4221_);
v_isSharedCheck_4265_ = !lean_is_exclusive(v_x_4216_);
if (v_isSharedCheck_4265_ == 0)
{
lean_object* v_unused_4266_; 
v_unused_4266_ = lean_ctor_get(v_x_4216_, 0);
lean_dec(v_unused_4266_);
v___x_4228_ = v_x_4216_;
v_isShared_4229_ = v_isSharedCheck_4265_;
goto v_resetjp_4227_;
}
else
{
lean_dec(v_x_4216_);
v___x_4228_ = lean_box(0);
v_isShared_4229_ = v_isSharedCheck_4265_;
goto v_resetjp_4227_;
}
v_resetjp_4227_:
{
lean_object* v_v_4230_; lean_object* v___x_4231_; lean_object* v_xs_x27_4232_; lean_object* v___y_4234_; 
v_v_4230_ = lean_array_fget(v_es_4221_, v_j_4224_);
v___x_4231_ = lean_box(0);
v_xs_x27_4232_ = lean_array_fset(v_es_4221_, v_j_4224_, v___x_4231_);
switch(lean_obj_tag(v_v_4230_))
{
case 0:
{
lean_object* v_key_4239_; lean_object* v_val_4240_; lean_object* v___x_4242_; uint8_t v_isShared_4243_; uint8_t v_isSharedCheck_4250_; 
v_key_4239_ = lean_ctor_get(v_v_4230_, 0);
v_val_4240_ = lean_ctor_get(v_v_4230_, 1);
v_isSharedCheck_4250_ = !lean_is_exclusive(v_v_4230_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4242_ = v_v_4230_;
v_isShared_4243_ = v_isSharedCheck_4250_;
goto v_resetjp_4241_;
}
else
{
lean_inc(v_val_4240_);
lean_inc(v_key_4239_);
lean_dec(v_v_4230_);
v___x_4242_ = lean_box(0);
v_isShared_4243_ = v_isSharedCheck_4250_;
goto v_resetjp_4241_;
}
v_resetjp_4241_:
{
uint8_t v___x_4244_; 
v___x_4244_ = l_Lean_instBEqMVarId_beq(v_x_4219_, v_key_4239_);
if (v___x_4244_ == 0)
{
lean_object* v___x_4245_; lean_object* v___x_4246_; 
lean_del_object(v___x_4242_);
v___x_4245_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4239_, v_val_4240_, v_x_4219_, v_x_4220_);
v___x_4246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4246_, 0, v___x_4245_);
v___y_4234_ = v___x_4246_;
goto v___jp_4233_;
}
else
{
lean_object* v___x_4248_; 
lean_dec(v_val_4240_);
lean_dec(v_key_4239_);
if (v_isShared_4243_ == 0)
{
lean_ctor_set(v___x_4242_, 1, v_x_4220_);
lean_ctor_set(v___x_4242_, 0, v_x_4219_);
v___x_4248_ = v___x_4242_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v_x_4219_);
lean_ctor_set(v_reuseFailAlloc_4249_, 1, v_x_4220_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
v___y_4234_ = v___x_4248_;
goto v___jp_4233_;
}
}
}
}
case 1:
{
lean_object* v_node_4251_; lean_object* v___x_4253_; uint8_t v_isShared_4254_; uint8_t v_isSharedCheck_4263_; 
v_node_4251_ = lean_ctor_get(v_v_4230_, 0);
v_isSharedCheck_4263_ = !lean_is_exclusive(v_v_4230_);
if (v_isSharedCheck_4263_ == 0)
{
v___x_4253_ = v_v_4230_;
v_isShared_4254_ = v_isSharedCheck_4263_;
goto v_resetjp_4252_;
}
else
{
lean_inc(v_node_4251_);
lean_dec(v_v_4230_);
v___x_4253_ = lean_box(0);
v_isShared_4254_ = v_isSharedCheck_4263_;
goto v_resetjp_4252_;
}
v_resetjp_4252_:
{
size_t v___x_4255_; size_t v___x_4256_; size_t v___x_4257_; size_t v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4261_; 
v___x_4255_ = ((size_t)5ULL);
v___x_4256_ = lean_usize_shift_right(v_x_4217_, v___x_4255_);
v___x_4257_ = ((size_t)1ULL);
v___x_4258_ = lean_usize_add(v_x_4218_, v___x_4257_);
v___x_4259_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_node_4251_, v___x_4256_, v___x_4258_, v_x_4219_, v_x_4220_);
if (v_isShared_4254_ == 0)
{
lean_ctor_set(v___x_4253_, 0, v___x_4259_);
v___x_4261_ = v___x_4253_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v___x_4259_);
v___x_4261_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
v___y_4234_ = v___x_4261_;
goto v___jp_4233_;
}
}
}
default: 
{
lean_object* v___x_4264_; 
v___x_4264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4264_, 0, v_x_4219_);
lean_ctor_set(v___x_4264_, 1, v_x_4220_);
v___y_4234_ = v___x_4264_;
goto v___jp_4233_;
}
}
v___jp_4233_:
{
lean_object* v___x_4235_; lean_object* v___x_4237_; 
v___x_4235_ = lean_array_fset(v_xs_x27_4232_, v_j_4224_, v___y_4234_);
lean_dec(v_j_4224_);
if (v_isShared_4229_ == 0)
{
lean_ctor_set(v___x_4228_, 0, v___x_4235_);
v___x_4237_ = v___x_4228_;
goto v_reusejp_4236_;
}
else
{
lean_object* v_reuseFailAlloc_4238_; 
v_reuseFailAlloc_4238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4238_, 0, v___x_4235_);
v___x_4237_ = v_reuseFailAlloc_4238_;
goto v_reusejp_4236_;
}
v_reusejp_4236_:
{
return v___x_4237_;
}
}
}
}
}
else
{
lean_object* v_ks_4267_; lean_object* v_vs_4268_; lean_object* v___x_4270_; uint8_t v_isShared_4271_; uint8_t v_isSharedCheck_4288_; 
v_ks_4267_ = lean_ctor_get(v_x_4216_, 0);
v_vs_4268_ = lean_ctor_get(v_x_4216_, 1);
v_isSharedCheck_4288_ = !lean_is_exclusive(v_x_4216_);
if (v_isSharedCheck_4288_ == 0)
{
v___x_4270_ = v_x_4216_;
v_isShared_4271_ = v_isSharedCheck_4288_;
goto v_resetjp_4269_;
}
else
{
lean_inc(v_vs_4268_);
lean_inc(v_ks_4267_);
lean_dec(v_x_4216_);
v___x_4270_ = lean_box(0);
v_isShared_4271_ = v_isSharedCheck_4288_;
goto v_resetjp_4269_;
}
v_resetjp_4269_:
{
lean_object* v___x_4273_; 
if (v_isShared_4271_ == 0)
{
v___x_4273_ = v___x_4270_;
goto v_reusejp_4272_;
}
else
{
lean_object* v_reuseFailAlloc_4287_; 
v_reuseFailAlloc_4287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4287_, 0, v_ks_4267_);
lean_ctor_set(v_reuseFailAlloc_4287_, 1, v_vs_4268_);
v___x_4273_ = v_reuseFailAlloc_4287_;
goto v_reusejp_4272_;
}
v_reusejp_4272_:
{
lean_object* v_newNode_4274_; uint8_t v___y_4276_; size_t v___x_4282_; uint8_t v___x_4283_; 
v_newNode_4274_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(v___x_4273_, v_x_4219_, v_x_4220_);
v___x_4282_ = ((size_t)7ULL);
v___x_4283_ = lean_usize_dec_le(v___x_4282_, v_x_4218_);
if (v___x_4283_ == 0)
{
lean_object* v___x_4284_; lean_object* v___x_4285_; uint8_t v___x_4286_; 
v___x_4284_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4274_);
v___x_4285_ = lean_unsigned_to_nat(4u);
v___x_4286_ = lean_nat_dec_lt(v___x_4284_, v___x_4285_);
lean_dec(v___x_4284_);
v___y_4276_ = v___x_4286_;
goto v___jp_4275_;
}
else
{
v___y_4276_ = v___x_4283_;
goto v___jp_4275_;
}
v___jp_4275_:
{
if (v___y_4276_ == 0)
{
lean_object* v_ks_4277_; lean_object* v_vs_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; 
v_ks_4277_ = lean_ctor_get(v_newNode_4274_, 0);
lean_inc_ref(v_ks_4277_);
v_vs_4278_ = lean_ctor_get(v_newNode_4274_, 1);
lean_inc_ref(v_vs_4278_);
lean_dec_ref(v_newNode_4274_);
v___x_4279_ = lean_unsigned_to_nat(0u);
v___x_4280_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_4281_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_x_4218_, v_ks_4277_, v_vs_4278_, v___x_4279_, v___x_4280_);
lean_dec_ref(v_vs_4278_);
lean_dec_ref(v_ks_4277_);
return v___x_4281_;
}
else
{
return v_newNode_4274_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(size_t v_depth_4289_, lean_object* v_keys_4290_, lean_object* v_vals_4291_, lean_object* v_i_4292_, lean_object* v_entries_4293_){
_start:
{
lean_object* v___x_4294_; uint8_t v___x_4295_; 
v___x_4294_ = lean_array_get_size(v_keys_4290_);
v___x_4295_ = lean_nat_dec_lt(v_i_4292_, v___x_4294_);
if (v___x_4295_ == 0)
{
lean_dec(v_i_4292_);
return v_entries_4293_;
}
else
{
lean_object* v_k_4296_; lean_object* v_v_4297_; uint64_t v___x_4298_; size_t v_h_4299_; size_t v___x_4300_; lean_object* v___x_4301_; size_t v___x_4302_; size_t v___x_4303_; size_t v___x_4304_; size_t v_h_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; 
v_k_4296_ = lean_array_fget_borrowed(v_keys_4290_, v_i_4292_);
v_v_4297_ = lean_array_fget_borrowed(v_vals_4291_, v_i_4292_);
v___x_4298_ = l_Lean_instHashableMVarId_hash(v_k_4296_);
v_h_4299_ = lean_uint64_to_usize(v___x_4298_);
v___x_4300_ = ((size_t)5ULL);
v___x_4301_ = lean_unsigned_to_nat(1u);
v___x_4302_ = ((size_t)1ULL);
v___x_4303_ = lean_usize_sub(v_depth_4289_, v___x_4302_);
v___x_4304_ = lean_usize_mul(v___x_4300_, v___x_4303_);
v_h_4305_ = lean_usize_shift_right(v_h_4299_, v___x_4304_);
v___x_4306_ = lean_nat_add(v_i_4292_, v___x_4301_);
lean_dec(v_i_4292_);
lean_inc(v_v_4297_);
lean_inc(v_k_4296_);
v___x_4307_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_entries_4293_, v_h_4305_, v_depth_4289_, v_k_4296_, v_v_4297_);
v_i_4292_ = v___x_4306_;
v_entries_4293_ = v___x_4307_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_depth_4309_, lean_object* v_keys_4310_, lean_object* v_vals_4311_, lean_object* v_i_4312_, lean_object* v_entries_4313_){
_start:
{
size_t v_depth_boxed_4314_; lean_object* v_res_4315_; 
v_depth_boxed_4314_ = lean_unbox_usize(v_depth_4309_);
lean_dec(v_depth_4309_);
v_res_4315_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_4314_, v_keys_4310_, v_vals_4311_, v_i_4312_, v_entries_4313_);
lean_dec_ref(v_vals_4311_);
lean_dec_ref(v_keys_4310_);
return v_res_4315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_4316_, lean_object* v_x_4317_, lean_object* v_x_4318_, lean_object* v_x_4319_, lean_object* v_x_4320_){
_start:
{
size_t v_x_4249__boxed_4321_; size_t v_x_4250__boxed_4322_; lean_object* v_res_4323_; 
v_x_4249__boxed_4321_ = lean_unbox_usize(v_x_4317_);
lean_dec(v_x_4317_);
v_x_4250__boxed_4322_ = lean_unbox_usize(v_x_4318_);
lean_dec(v_x_4318_);
v_res_4323_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4316_, v_x_4249__boxed_4321_, v_x_4250__boxed_4322_, v_x_4319_, v_x_4320_);
return v_res_4323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(lean_object* v_x_4324_, lean_object* v_x_4325_, lean_object* v_x_4326_){
_start:
{
uint64_t v___x_4327_; size_t v___x_4328_; size_t v___x_4329_; lean_object* v___x_4330_; 
v___x_4327_ = l_Lean_instHashableMVarId_hash(v_x_4325_);
v___x_4328_ = lean_uint64_to_usize(v___x_4327_);
v___x_4329_ = ((size_t)1ULL);
v___x_4330_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4324_, v___x_4328_, v___x_4329_, v_x_4325_, v_x_4326_);
return v___x_4330_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(lean_object* v_mvarId_4331_, lean_object* v_val_4332_, lean_object* v___y_4333_){
_start:
{
lean_object* v___x_4335_; lean_object* v_mctx_4336_; lean_object* v_cache_4337_; lean_object* v_zetaDeltaFVarIds_4338_; lean_object* v_postponed_4339_; lean_object* v_diag_4340_; lean_object* v___x_4342_; uint8_t v_isShared_4343_; uint8_t v_isSharedCheck_4368_; 
v___x_4335_ = lean_st_ref_take(v___y_4333_);
v_mctx_4336_ = lean_ctor_get(v___x_4335_, 0);
v_cache_4337_ = lean_ctor_get(v___x_4335_, 1);
v_zetaDeltaFVarIds_4338_ = lean_ctor_get(v___x_4335_, 2);
v_postponed_4339_ = lean_ctor_get(v___x_4335_, 3);
v_diag_4340_ = lean_ctor_get(v___x_4335_, 4);
v_isSharedCheck_4368_ = !lean_is_exclusive(v___x_4335_);
if (v_isSharedCheck_4368_ == 0)
{
v___x_4342_ = v___x_4335_;
v_isShared_4343_ = v_isSharedCheck_4368_;
goto v_resetjp_4341_;
}
else
{
lean_inc(v_diag_4340_);
lean_inc(v_postponed_4339_);
lean_inc(v_zetaDeltaFVarIds_4338_);
lean_inc(v_cache_4337_);
lean_inc(v_mctx_4336_);
lean_dec(v___x_4335_);
v___x_4342_ = lean_box(0);
v_isShared_4343_ = v_isSharedCheck_4368_;
goto v_resetjp_4341_;
}
v_resetjp_4341_:
{
lean_object* v_depth_4344_; lean_object* v_levelAssignDepth_4345_; lean_object* v_lmvarCounter_4346_; lean_object* v_mvarCounter_4347_; lean_object* v_lDecls_4348_; lean_object* v_decls_4349_; lean_object* v_userNames_4350_; lean_object* v_lAssignment_4351_; lean_object* v_eAssignment_4352_; lean_object* v_dAssignment_4353_; lean_object* v___x_4355_; uint8_t v_isShared_4356_; uint8_t v_isSharedCheck_4367_; 
v_depth_4344_ = lean_ctor_get(v_mctx_4336_, 0);
v_levelAssignDepth_4345_ = lean_ctor_get(v_mctx_4336_, 1);
v_lmvarCounter_4346_ = lean_ctor_get(v_mctx_4336_, 2);
v_mvarCounter_4347_ = lean_ctor_get(v_mctx_4336_, 3);
v_lDecls_4348_ = lean_ctor_get(v_mctx_4336_, 4);
v_decls_4349_ = lean_ctor_get(v_mctx_4336_, 5);
v_userNames_4350_ = lean_ctor_get(v_mctx_4336_, 6);
v_lAssignment_4351_ = lean_ctor_get(v_mctx_4336_, 7);
v_eAssignment_4352_ = lean_ctor_get(v_mctx_4336_, 8);
v_dAssignment_4353_ = lean_ctor_get(v_mctx_4336_, 9);
v_isSharedCheck_4367_ = !lean_is_exclusive(v_mctx_4336_);
if (v_isSharedCheck_4367_ == 0)
{
v___x_4355_ = v_mctx_4336_;
v_isShared_4356_ = v_isSharedCheck_4367_;
goto v_resetjp_4354_;
}
else
{
lean_inc(v_dAssignment_4353_);
lean_inc(v_eAssignment_4352_);
lean_inc(v_lAssignment_4351_);
lean_inc(v_userNames_4350_);
lean_inc(v_decls_4349_);
lean_inc(v_lDecls_4348_);
lean_inc(v_mvarCounter_4347_);
lean_inc(v_lmvarCounter_4346_);
lean_inc(v_levelAssignDepth_4345_);
lean_inc(v_depth_4344_);
lean_dec(v_mctx_4336_);
v___x_4355_ = lean_box(0);
v_isShared_4356_ = v_isSharedCheck_4367_;
goto v_resetjp_4354_;
}
v_resetjp_4354_:
{
lean_object* v___x_4357_; lean_object* v___x_4359_; 
v___x_4357_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(v_eAssignment_4352_, v_mvarId_4331_, v_val_4332_);
if (v_isShared_4356_ == 0)
{
lean_ctor_set(v___x_4355_, 8, v___x_4357_);
v___x_4359_ = v___x_4355_;
goto v_reusejp_4358_;
}
else
{
lean_object* v_reuseFailAlloc_4366_; 
v_reuseFailAlloc_4366_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4366_, 0, v_depth_4344_);
lean_ctor_set(v_reuseFailAlloc_4366_, 1, v_levelAssignDepth_4345_);
lean_ctor_set(v_reuseFailAlloc_4366_, 2, v_lmvarCounter_4346_);
lean_ctor_set(v_reuseFailAlloc_4366_, 3, v_mvarCounter_4347_);
lean_ctor_set(v_reuseFailAlloc_4366_, 4, v_lDecls_4348_);
lean_ctor_set(v_reuseFailAlloc_4366_, 5, v_decls_4349_);
lean_ctor_set(v_reuseFailAlloc_4366_, 6, v_userNames_4350_);
lean_ctor_set(v_reuseFailAlloc_4366_, 7, v_lAssignment_4351_);
lean_ctor_set(v_reuseFailAlloc_4366_, 8, v___x_4357_);
lean_ctor_set(v_reuseFailAlloc_4366_, 9, v_dAssignment_4353_);
v___x_4359_ = v_reuseFailAlloc_4366_;
goto v_reusejp_4358_;
}
v_reusejp_4358_:
{
lean_object* v___x_4361_; 
if (v_isShared_4343_ == 0)
{
lean_ctor_set(v___x_4342_, 0, v___x_4359_);
v___x_4361_ = v___x_4342_;
goto v_reusejp_4360_;
}
else
{
lean_object* v_reuseFailAlloc_4365_; 
v_reuseFailAlloc_4365_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4365_, 0, v___x_4359_);
lean_ctor_set(v_reuseFailAlloc_4365_, 1, v_cache_4337_);
lean_ctor_set(v_reuseFailAlloc_4365_, 2, v_zetaDeltaFVarIds_4338_);
lean_ctor_set(v_reuseFailAlloc_4365_, 3, v_postponed_4339_);
lean_ctor_set(v_reuseFailAlloc_4365_, 4, v_diag_4340_);
v___x_4361_ = v_reuseFailAlloc_4365_;
goto v_reusejp_4360_;
}
v_reusejp_4360_:
{
lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; 
v___x_4362_ = lean_st_ref_set(v___y_4333_, v___x_4361_);
v___x_4363_ = lean_box(0);
v___x_4364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4364_, 0, v___x_4363_);
return v___x_4364_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg___boxed(lean_object* v_mvarId_4369_, lean_object* v_val_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_){
_start:
{
lean_object* v_res_4373_; 
v_res_4373_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mvarId_4369_, v_val_4370_, v___y_4371_);
lean_dec(v___y_4371_);
return v_res_4373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___lam__0(lean_object* v_mv_u2081_4378_, lean_object* v_mv_u2082_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_){
_start:
{
lean_object* v___x_4388_; 
lean_inc(v_mv_u2081_4378_);
v___x_4388_ = l_Lean_MVarId_getDecl(v_mv_u2081_4378_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_);
if (lean_obj_tag(v___x_4388_) == 0)
{
lean_object* v_a_4389_; lean_object* v___x_4390_; 
v_a_4389_ = lean_ctor_get(v___x_4388_, 0);
lean_inc(v_a_4389_);
lean_dec_ref_known(v___x_4388_, 1);
lean_inc(v_mv_u2082_4379_);
v___x_4390_ = l_Lean_MVarId_getDecl(v_mv_u2082_4379_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_);
if (lean_obj_tag(v___x_4390_) == 0)
{
lean_object* v_a_4391_; lean_object* v_lctx_4392_; lean_object* v_type_4393_; lean_object* v_lctx_4394_; lean_object* v_type_4395_; uint8_t v___x_4396_; 
v_a_4391_ = lean_ctor_get(v___x_4390_, 0);
lean_inc(v_a_4391_);
lean_dec_ref_known(v___x_4390_, 1);
v_lctx_4392_ = lean_ctor_get(v_a_4389_, 1);
lean_inc_ref(v_lctx_4392_);
v_type_4393_ = lean_ctor_get(v_a_4389_, 2);
lean_inc_ref(v_type_4393_);
lean_dec(v_a_4389_);
v_lctx_4394_ = lean_ctor_get(v_a_4391_, 1);
lean_inc_ref(v_lctx_4394_);
v_type_4395_ = lean_ctor_get(v_a_4391_, 2);
lean_inc_ref(v_type_4395_);
lean_dec(v_a_4391_);
v___x_4396_ = lean_expr_eqv(v_type_4393_, v_type_4395_);
lean_dec_ref(v_type_4395_);
lean_dec_ref(v_type_4393_);
if (v___x_4396_ == 0)
{
lean_dec_ref(v_lctx_4394_);
lean_dec_ref(v_lctx_4392_);
lean_dec(v_mv_u2082_4379_);
lean_dec(v_mv_u2081_4378_);
goto v___jp_4385_;
}
else
{
lean_object* v___x_4397_; uint8_t v___x_4398_; 
v___x_4397_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_processRec___closed__0));
v___x_4398_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_4392_, v_lctx_4394_, v___x_4397_);
if (v___x_4398_ == 0)
{
uint8_t v___x_4399_; 
v___x_4399_ = l_Lean_LocalContext_isSubPrefixOf(v_lctx_4394_, v_lctx_4392_, v___x_4397_);
lean_dec_ref(v_lctx_4392_);
lean_dec_ref(v_lctx_4394_);
if (v___x_4399_ == 0)
{
lean_dec(v_mv_u2082_4379_);
lean_dec(v_mv_u2081_4378_);
goto v___jp_4385_;
}
else
{
lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4411_; 
v___x_4400_ = l_Lean_Expr_mvar___override(v_mv_u2082_4379_);
v___x_4401_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mv_u2081_4378_, v___x_4400_, v___y_4381_);
v_isSharedCheck_4411_ = !lean_is_exclusive(v___x_4401_);
if (v_isSharedCheck_4411_ == 0)
{
lean_object* v_unused_4412_; 
v_unused_4412_ = lean_ctor_get(v___x_4401_, 0);
lean_dec(v_unused_4412_);
v___x_4403_ = v___x_4401_;
v_isShared_4404_ = v_isSharedCheck_4411_;
goto v_resetjp_4402_;
}
else
{
lean_dec(v___x_4401_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4411_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4409_; 
v___x_4405_ = lean_box(v___x_4398_);
v___x_4406_ = lean_box(v___x_4396_);
v___x_4407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4407_, 0, v___x_4405_);
lean_ctor_set(v___x_4407_, 1, v___x_4406_);
if (v_isShared_4404_ == 0)
{
lean_ctor_set(v___x_4403_, 0, v___x_4407_);
v___x_4409_ = v___x_4403_;
goto v_reusejp_4408_;
}
else
{
lean_object* v_reuseFailAlloc_4410_; 
v_reuseFailAlloc_4410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4410_, 0, v___x_4407_);
v___x_4409_ = v_reuseFailAlloc_4410_;
goto v_reusejp_4408_;
}
v_reusejp_4408_:
{
return v___x_4409_;
}
}
}
}
else
{
lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4416_; uint8_t v_isShared_4417_; uint8_t v_isSharedCheck_4425_; 
lean_dec_ref(v_lctx_4394_);
lean_dec_ref(v_lctx_4392_);
v___x_4413_ = l_Lean_Expr_mvar___override(v_mv_u2081_4378_);
v___x_4414_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mv_u2082_4379_, v___x_4413_, v___y_4381_);
v_isSharedCheck_4425_ = !lean_is_exclusive(v___x_4414_);
if (v_isSharedCheck_4425_ == 0)
{
lean_object* v_unused_4426_; 
v_unused_4426_ = lean_ctor_get(v___x_4414_, 0);
lean_dec(v_unused_4426_);
v___x_4416_ = v___x_4414_;
v_isShared_4417_ = v_isSharedCheck_4425_;
goto v_resetjp_4415_;
}
else
{
lean_dec(v___x_4414_);
v___x_4416_ = lean_box(0);
v_isShared_4417_ = v_isSharedCheck_4425_;
goto v_resetjp_4415_;
}
v_resetjp_4415_:
{
uint8_t v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4423_; 
v___x_4418_ = 0;
v___x_4419_ = lean_box(v___x_4396_);
v___x_4420_ = lean_box(v___x_4418_);
v___x_4421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4421_, 0, v___x_4419_);
lean_ctor_set(v___x_4421_, 1, v___x_4420_);
if (v_isShared_4417_ == 0)
{
lean_ctor_set(v___x_4416_, 0, v___x_4421_);
v___x_4423_ = v___x_4416_;
goto v_reusejp_4422_;
}
else
{
lean_object* v_reuseFailAlloc_4424_; 
v_reuseFailAlloc_4424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4424_, 0, v___x_4421_);
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
}
else
{
lean_object* v_a_4427_; lean_object* v___x_4429_; uint8_t v_isShared_4430_; uint8_t v_isSharedCheck_4434_; 
lean_dec(v_a_4389_);
lean_dec(v_mv_u2082_4379_);
lean_dec(v_mv_u2081_4378_);
v_a_4427_ = lean_ctor_get(v___x_4390_, 0);
v_isSharedCheck_4434_ = !lean_is_exclusive(v___x_4390_);
if (v_isSharedCheck_4434_ == 0)
{
v___x_4429_ = v___x_4390_;
v_isShared_4430_ = v_isSharedCheck_4434_;
goto v_resetjp_4428_;
}
else
{
lean_inc(v_a_4427_);
lean_dec(v___x_4390_);
v___x_4429_ = lean_box(0);
v_isShared_4430_ = v_isSharedCheck_4434_;
goto v_resetjp_4428_;
}
v_resetjp_4428_:
{
lean_object* v___x_4432_; 
if (v_isShared_4430_ == 0)
{
v___x_4432_ = v___x_4429_;
goto v_reusejp_4431_;
}
else
{
lean_object* v_reuseFailAlloc_4433_; 
v_reuseFailAlloc_4433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4433_, 0, v_a_4427_);
v___x_4432_ = v_reuseFailAlloc_4433_;
goto v_reusejp_4431_;
}
v_reusejp_4431_:
{
return v___x_4432_;
}
}
}
}
else
{
lean_object* v_a_4435_; lean_object* v___x_4437_; uint8_t v_isShared_4438_; uint8_t v_isSharedCheck_4442_; 
lean_dec(v_mv_u2082_4379_);
lean_dec(v_mv_u2081_4378_);
v_a_4435_ = lean_ctor_get(v___x_4388_, 0);
v_isSharedCheck_4442_ = !lean_is_exclusive(v___x_4388_);
if (v_isSharedCheck_4442_ == 0)
{
v___x_4437_ = v___x_4388_;
v_isShared_4438_ = v_isSharedCheck_4442_;
goto v_resetjp_4436_;
}
else
{
lean_inc(v_a_4435_);
lean_dec(v___x_4388_);
v___x_4437_ = lean_box(0);
v_isShared_4438_ = v_isSharedCheck_4442_;
goto v_resetjp_4436_;
}
v_resetjp_4436_:
{
lean_object* v___x_4440_; 
if (v_isShared_4438_ == 0)
{
v___x_4440_ = v___x_4437_;
goto v_reusejp_4439_;
}
else
{
lean_object* v_reuseFailAlloc_4441_; 
v_reuseFailAlloc_4441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4441_, 0, v_a_4435_);
v___x_4440_ = v_reuseFailAlloc_4441_;
goto v_reusejp_4439_;
}
v_reusejp_4439_:
{
return v___x_4440_;
}
}
}
v___jp_4385_:
{
lean_object* v___x_4386_; lean_object* v___x_4387_; 
v___x_4386_ = ((lean_object*)(l_Lean_Elab_WF_assignSubsumed___lam__0___closed__0));
v___x_4387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4387_, 0, v___x_4386_);
return v___x_4387_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___lam__0___boxed(lean_object* v_mv_u2081_4443_, lean_object* v_mv_u2082_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_){
_start:
{
lean_object* v_res_4450_; 
v_res_4450_ = l_Lean_Elab_WF_assignSubsumed___lam__0(v_mv_u2081_4443_, v_mv_u2082_4444_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_);
lean_dec(v___y_4448_);
lean_dec_ref(v___y_4447_);
lean_dec(v___y_4446_);
lean_dec_ref(v___y_4445_);
return v_res_4450_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1(lean_object* v___x_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_){
_start:
{
lean_object* v___x_4457_; 
v___x_4457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4457_, 0, v___x_4451_);
return v___x_4457_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1___boxed(lean_object* v___x_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_){
_start:
{
lean_object* v_res_4464_; 
v_res_4464_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1(v___x_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_);
lean_dec(v___y_4462_);
lean_dec_ref(v___y_4461_);
lean_dec(v___y_4460_);
lean_dec_ref(v___y_4459_);
return v_res_4464_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0(lean_object* v_f_4465_, lean_object* v___x_4466_, lean_object* v___x_4467_, lean_object* v___x_4468_, lean_object* v_a_4469_, uint8_t v___x_4470_, lean_object* v_snd_4471_, lean_object* v_fst_4472_, lean_object* v_next_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_){
_start:
{
lean_object* v___x_4479_; 
v___x_4479_ = lean_apply_7(v_f_4465_, v___x_4466_, v___x_4467_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_, lean_box(0));
if (lean_obj_tag(v___x_4479_) == 0)
{
lean_object* v_a_4480_; lean_object* v___x_4482_; uint8_t v_isShared_4483_; uint8_t v_isSharedCheck_4515_; 
v_a_4480_ = lean_ctor_get(v___x_4479_, 0);
v_isSharedCheck_4515_ = !lean_is_exclusive(v___x_4479_);
if (v_isSharedCheck_4515_ == 0)
{
v___x_4482_ = v___x_4479_;
v_isShared_4483_ = v_isSharedCheck_4515_;
goto v_resetjp_4481_;
}
else
{
lean_inc(v_a_4480_);
lean_dec(v___x_4479_);
v___x_4482_ = lean_box(0);
v_isShared_4483_ = v_isSharedCheck_4515_;
goto v_resetjp_4481_;
}
v_resetjp_4481_:
{
lean_object* v_fst_4484_; lean_object* v_snd_4485_; lean_object* v___x_4487_; uint8_t v_isShared_4488_; uint8_t v_isSharedCheck_4514_; 
v_fst_4484_ = lean_ctor_get(v_a_4480_, 0);
v_snd_4485_ = lean_ctor_get(v_a_4480_, 1);
v_isSharedCheck_4514_ = !lean_is_exclusive(v_a_4480_);
if (v_isSharedCheck_4514_ == 0)
{
v___x_4487_ = v_a_4480_;
v_isShared_4488_ = v_isSharedCheck_4514_;
goto v_resetjp_4486_;
}
else
{
lean_inc(v_snd_4485_);
lean_inc(v_fst_4484_);
lean_dec(v_a_4480_);
v___x_4487_ = lean_box(0);
v_isShared_4488_ = v_isSharedCheck_4514_;
goto v_resetjp_4486_;
}
v_resetjp_4486_:
{
lean_object* v_removed_4490_; lean_object* v_numRemoved_4491_; uint8_t v___x_4510_; 
v___x_4510_ = lean_unbox(v_fst_4484_);
lean_dec(v_fst_4484_);
if (v___x_4510_ == 0)
{
lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; 
v___x_4511_ = lean_nat_add(v_snd_4471_, v___x_4468_);
lean_dec(v_snd_4471_);
v___x_4512_ = lean_box(v___x_4470_);
v___x_4513_ = lean_array_set(v_fst_4472_, v_next_4473_, v___x_4512_);
v_removed_4490_ = v___x_4513_;
v_numRemoved_4491_ = v___x_4511_;
goto v___jp_4489_;
}
else
{
v_removed_4490_ = v_fst_4472_;
v_numRemoved_4491_ = v_snd_4471_;
goto v___jp_4489_;
}
v___jp_4489_:
{
uint8_t v___x_4492_; 
v___x_4492_ = lean_unbox(v_snd_4485_);
lean_dec(v_snd_4485_);
if (v___x_4492_ == 0)
{
lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4497_; 
v___x_4493_ = lean_nat_add(v_numRemoved_4491_, v___x_4468_);
lean_dec(v_numRemoved_4491_);
v___x_4494_ = lean_box(v___x_4470_);
v___x_4495_ = lean_array_set(v_removed_4490_, v_a_4469_, v___x_4494_);
if (v_isShared_4488_ == 0)
{
lean_ctor_set(v___x_4487_, 1, v___x_4493_);
lean_ctor_set(v___x_4487_, 0, v___x_4495_);
v___x_4497_ = v___x_4487_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4502_; 
v_reuseFailAlloc_4502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4502_, 0, v___x_4495_);
lean_ctor_set(v_reuseFailAlloc_4502_, 1, v___x_4493_);
v___x_4497_ = v_reuseFailAlloc_4502_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
lean_object* v___x_4498_; lean_object* v___x_4500_; 
v___x_4498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4498_, 0, v___x_4497_);
if (v_isShared_4483_ == 0)
{
lean_ctor_set(v___x_4482_, 0, v___x_4498_);
v___x_4500_ = v___x_4482_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4501_; 
v_reuseFailAlloc_4501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4501_, 0, v___x_4498_);
v___x_4500_ = v_reuseFailAlloc_4501_;
goto v_reusejp_4499_;
}
v_reusejp_4499_:
{
return v___x_4500_;
}
}
}
else
{
lean_object* v___x_4504_; 
if (v_isShared_4488_ == 0)
{
lean_ctor_set(v___x_4487_, 1, v_numRemoved_4491_);
lean_ctor_set(v___x_4487_, 0, v_removed_4490_);
v___x_4504_ = v___x_4487_;
goto v_reusejp_4503_;
}
else
{
lean_object* v_reuseFailAlloc_4509_; 
v_reuseFailAlloc_4509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4509_, 0, v_removed_4490_);
lean_ctor_set(v_reuseFailAlloc_4509_, 1, v_numRemoved_4491_);
v___x_4504_ = v_reuseFailAlloc_4509_;
goto v_reusejp_4503_;
}
v_reusejp_4503_:
{
lean_object* v___x_4505_; lean_object* v___x_4507_; 
v___x_4505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4505_, 0, v___x_4504_);
if (v_isShared_4483_ == 0)
{
lean_ctor_set(v___x_4482_, 0, v___x_4505_);
v___x_4507_ = v___x_4482_;
goto v_reusejp_4506_;
}
else
{
lean_object* v_reuseFailAlloc_4508_; 
v_reuseFailAlloc_4508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4508_, 0, v___x_4505_);
v___x_4507_ = v_reuseFailAlloc_4508_;
goto v_reusejp_4506_;
}
v_reusejp_4506_:
{
return v___x_4507_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4516_; lean_object* v___x_4518_; uint8_t v_isShared_4519_; uint8_t v_isSharedCheck_4523_; 
lean_dec(v_fst_4472_);
lean_dec(v_snd_4471_);
v_a_4516_ = lean_ctor_get(v___x_4479_, 0);
v_isSharedCheck_4523_ = !lean_is_exclusive(v___x_4479_);
if (v_isSharedCheck_4523_ == 0)
{
v___x_4518_ = v___x_4479_;
v_isShared_4519_ = v_isSharedCheck_4523_;
goto v_resetjp_4517_;
}
else
{
lean_inc(v_a_4516_);
lean_dec(v___x_4479_);
v___x_4518_ = lean_box(0);
v_isShared_4519_ = v_isSharedCheck_4523_;
goto v_resetjp_4517_;
}
v_resetjp_4517_:
{
lean_object* v___x_4521_; 
if (v_isShared_4519_ == 0)
{
v___x_4521_ = v___x_4518_;
goto v_reusejp_4520_;
}
else
{
lean_object* v_reuseFailAlloc_4522_; 
v_reuseFailAlloc_4522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4522_, 0, v_a_4516_);
v___x_4521_ = v_reuseFailAlloc_4522_;
goto v_reusejp_4520_;
}
v_reusejp_4520_:
{
return v___x_4521_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0___boxed(lean_object* v_f_4524_, lean_object* v___x_4525_, lean_object* v___x_4526_, lean_object* v___x_4527_, lean_object* v_a_4528_, lean_object* v___x_4529_, lean_object* v_snd_4530_, lean_object* v_fst_4531_, lean_object* v_next_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_){
_start:
{
uint8_t v___x_4626__boxed_4538_; lean_object* v_res_4539_; 
v___x_4626__boxed_4538_ = lean_unbox(v___x_4529_);
v_res_4539_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0(v_f_4524_, v___x_4525_, v___x_4526_, v___x_4527_, v_a_4528_, v___x_4626__boxed_4538_, v_snd_4530_, v_fst_4531_, v_next_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_);
lean_dec(v_next_4532_);
lean_dec(v_a_4528_);
lean_dec(v___x_4527_);
return v_res_4539_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(lean_object* v_upperBound_4540_, lean_object* v_a_4541_, lean_object* v_next_4542_, lean_object* v_f_4543_, lean_object* v_a_4544_, lean_object* v_b_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_){
_start:
{
uint8_t v___x_4551_; 
v___x_4551_ = lean_nat_dec_lt(v_a_4544_, v_upperBound_4540_);
if (v___x_4551_ == 0)
{
lean_object* v___x_4552_; 
lean_dec(v_a_4544_);
lean_dec_ref(v_f_4543_);
lean_dec(v_next_4542_);
v___x_4552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4552_, 0, v_b_4545_);
return v___x_4552_;
}
else
{
lean_object* v_fst_4553_; lean_object* v_snd_4554_; lean_object* v___x_4556_; uint8_t v_isShared_4557_; uint8_t v_isSharedCheck_4601_; 
v_fst_4553_ = lean_ctor_get(v_b_4545_, 0);
v_snd_4554_ = lean_ctor_get(v_b_4545_, 1);
v_isSharedCheck_4601_ = !lean_is_exclusive(v_b_4545_);
if (v_isSharedCheck_4601_ == 0)
{
v___x_4556_ = v_b_4545_;
v_isShared_4557_ = v_isSharedCheck_4601_;
goto v_resetjp_4555_;
}
else
{
lean_inc(v_snd_4554_);
lean_inc(v_fst_4553_);
lean_dec(v_b_4545_);
v___x_4556_ = lean_box(0);
v_isShared_4557_ = v_isSharedCheck_4601_;
goto v_resetjp_4555_;
}
v_resetjp_4555_:
{
lean_object* v___x_4558_; lean_object* v___y_4560_; uint8_t v___y_4583_; uint8_t v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; uint8_t v___x_4596_; 
v___x_4558_ = lean_unsigned_to_nat(1u);
v___x_4593_ = 0;
v___x_4594_ = lean_box(v___x_4593_);
v___x_4595_ = lean_array_get(v___x_4594_, v_fst_4553_, v_next_4542_);
lean_dec(v___x_4594_);
v___x_4596_ = lean_unbox(v___x_4595_);
if (v___x_4596_ == 0)
{
lean_object* v___x_4597_; lean_object* v___x_4598_; uint8_t v___x_4599_; 
lean_dec(v___x_4595_);
v___x_4597_ = lean_box(v___x_4593_);
v___x_4598_ = lean_array_get(v___x_4597_, v_fst_4553_, v_a_4544_);
lean_dec(v___x_4597_);
v___x_4599_ = lean_unbox(v___x_4598_);
lean_dec(v___x_4598_);
v___y_4583_ = v___x_4599_;
goto v___jp_4582_;
}
else
{
uint8_t v___x_4600_; 
v___x_4600_ = lean_unbox(v___x_4595_);
lean_dec(v___x_4595_);
v___y_4583_ = v___x_4600_;
goto v___jp_4582_;
}
v___jp_4559_:
{
lean_object* v___x_4561_; 
lean_inc(v___y_4549_);
lean_inc_ref(v___y_4548_);
lean_inc(v___y_4547_);
lean_inc_ref(v___y_4546_);
v___x_4561_ = lean_apply_5(v___y_4560_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_, lean_box(0));
if (lean_obj_tag(v___x_4561_) == 0)
{
lean_object* v_a_4562_; lean_object* v___x_4564_; uint8_t v_isShared_4565_; uint8_t v_isSharedCheck_4573_; 
v_a_4562_ = lean_ctor_get(v___x_4561_, 0);
v_isSharedCheck_4573_ = !lean_is_exclusive(v___x_4561_);
if (v_isSharedCheck_4573_ == 0)
{
v___x_4564_ = v___x_4561_;
v_isShared_4565_ = v_isSharedCheck_4573_;
goto v_resetjp_4563_;
}
else
{
lean_inc(v_a_4562_);
lean_dec(v___x_4561_);
v___x_4564_ = lean_box(0);
v_isShared_4565_ = v_isSharedCheck_4573_;
goto v_resetjp_4563_;
}
v_resetjp_4563_:
{
if (lean_obj_tag(v_a_4562_) == 0)
{
lean_object* v_a_4566_; lean_object* v___x_4568_; 
lean_dec(v_a_4544_);
lean_dec_ref(v_f_4543_);
lean_dec(v_next_4542_);
v_a_4566_ = lean_ctor_get(v_a_4562_, 0);
lean_inc(v_a_4566_);
lean_dec_ref_known(v_a_4562_, 1);
if (v_isShared_4565_ == 0)
{
lean_ctor_set(v___x_4564_, 0, v_a_4566_);
v___x_4568_ = v___x_4564_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4569_; 
v_reuseFailAlloc_4569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4569_, 0, v_a_4566_);
v___x_4568_ = v_reuseFailAlloc_4569_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
return v___x_4568_;
}
}
else
{
lean_object* v_a_4570_; lean_object* v___x_4571_; 
lean_del_object(v___x_4564_);
v_a_4570_ = lean_ctor_get(v_a_4562_, 0);
lean_inc(v_a_4570_);
lean_dec_ref_known(v_a_4562_, 1);
v___x_4571_ = lean_nat_add(v_a_4544_, v___x_4558_);
lean_dec(v_a_4544_);
v_a_4544_ = v___x_4571_;
v_b_4545_ = v_a_4570_;
goto _start;
}
}
}
else
{
lean_object* v_a_4574_; lean_object* v___x_4576_; uint8_t v_isShared_4577_; uint8_t v_isSharedCheck_4581_; 
lean_dec(v_a_4544_);
lean_dec_ref(v_f_4543_);
lean_dec(v_next_4542_);
v_a_4574_ = lean_ctor_get(v___x_4561_, 0);
v_isSharedCheck_4581_ = !lean_is_exclusive(v___x_4561_);
if (v_isSharedCheck_4581_ == 0)
{
v___x_4576_ = v___x_4561_;
v_isShared_4577_ = v_isSharedCheck_4581_;
goto v_resetjp_4575_;
}
else
{
lean_inc(v_a_4574_);
lean_dec(v___x_4561_);
v___x_4576_ = lean_box(0);
v_isShared_4577_ = v_isSharedCheck_4581_;
goto v_resetjp_4575_;
}
v_resetjp_4575_:
{
lean_object* v___x_4579_; 
if (v_isShared_4577_ == 0)
{
v___x_4579_ = v___x_4576_;
goto v_reusejp_4578_;
}
else
{
lean_object* v_reuseFailAlloc_4580_; 
v_reuseFailAlloc_4580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4580_, 0, v_a_4574_);
v___x_4579_ = v_reuseFailAlloc_4580_;
goto v_reusejp_4578_;
}
v_reusejp_4578_:
{
return v___x_4579_;
}
}
}
}
v___jp_4582_:
{
if (v___y_4583_ == 0)
{
lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___f_4587_; 
lean_del_object(v___x_4556_);
v___x_4584_ = lean_array_fget_borrowed(v_a_4541_, v_next_4542_);
v___x_4585_ = lean_array_fget_borrowed(v_a_4541_, v_a_4544_);
v___x_4586_ = lean_box(v___x_4551_);
lean_inc(v_next_4542_);
lean_inc(v_a_4544_);
lean_inc(v___x_4585_);
lean_inc(v___x_4584_);
lean_inc_ref(v_f_4543_);
v___f_4587_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_4587_, 0, v_f_4543_);
lean_closure_set(v___f_4587_, 1, v___x_4584_);
lean_closure_set(v___f_4587_, 2, v___x_4585_);
lean_closure_set(v___f_4587_, 3, v___x_4558_);
lean_closure_set(v___f_4587_, 4, v_a_4544_);
lean_closure_set(v___f_4587_, 5, v___x_4586_);
lean_closure_set(v___f_4587_, 6, v_snd_4554_);
lean_closure_set(v___f_4587_, 7, v_fst_4553_);
lean_closure_set(v___f_4587_, 8, v_next_4542_);
v___y_4560_ = v___f_4587_;
goto v___jp_4559_;
}
else
{
lean_object* v___x_4589_; 
if (v_isShared_4557_ == 0)
{
v___x_4589_ = v___x_4556_;
goto v_reusejp_4588_;
}
else
{
lean_object* v_reuseFailAlloc_4592_; 
v_reuseFailAlloc_4592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4592_, 0, v_fst_4553_);
lean_ctor_set(v_reuseFailAlloc_4592_, 1, v_snd_4554_);
v___x_4589_ = v_reuseFailAlloc_4592_;
goto v_reusejp_4588_;
}
v_reusejp_4588_:
{
lean_object* v___x_4590_; lean_object* v___f_4591_; 
v___x_4590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4590_, 0, v___x_4589_);
v___f_4591_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___lam__1___boxed), 6, 1);
lean_closure_set(v___f_4591_, 0, v___x_4590_);
v___y_4560_ = v___f_4591_;
goto v___jp_4559_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg___boxed(lean_object* v_upperBound_4602_, lean_object* v_a_4603_, lean_object* v_next_4604_, lean_object* v_f_4605_, lean_object* v_a_4606_, lean_object* v_b_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_){
_start:
{
lean_object* v_res_4613_; 
v_res_4613_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v_upperBound_4602_, v_a_4603_, v_next_4604_, v_f_4605_, v_a_4606_, v_b_4607_, v___y_4608_, v___y_4609_, v___y_4610_, v___y_4611_);
lean_dec(v___y_4611_);
lean_dec_ref(v___y_4610_);
lean_dec(v___y_4609_);
lean_dec_ref(v___y_4608_);
lean_dec_ref(v_a_4603_);
lean_dec(v_upperBound_4602_);
return v_res_4613_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(lean_object* v_upperBound_4614_, lean_object* v___x_4615_, lean_object* v_a_4616_, lean_object* v_f_4617_, lean_object* v_a_4618_, lean_object* v_b_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_){
_start:
{
uint8_t v___x_4625_; 
v___x_4625_ = lean_nat_dec_lt(v_a_4618_, v_upperBound_4614_);
if (v___x_4625_ == 0)
{
lean_object* v___x_4626_; 
lean_dec(v_a_4618_);
lean_dec_ref(v_f_4617_);
v___x_4626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4626_, 0, v_b_4619_);
return v___x_4626_;
}
else
{
lean_object* v_fst_4627_; lean_object* v_snd_4628_; lean_object* v___x_4630_; uint8_t v_isShared_4631_; uint8_t v_isSharedCheck_4649_; 
v_fst_4627_ = lean_ctor_get(v_b_4619_, 0);
v_snd_4628_ = lean_ctor_get(v_b_4619_, 1);
v_isSharedCheck_4649_ = !lean_is_exclusive(v_b_4619_);
if (v_isSharedCheck_4649_ == 0)
{
v___x_4630_ = v_b_4619_;
v_isShared_4631_ = v_isSharedCheck_4649_;
goto v_resetjp_4629_;
}
else
{
lean_inc(v_snd_4628_);
lean_inc(v_fst_4627_);
lean_dec(v_b_4619_);
v___x_4630_ = lean_box(0);
v_isShared_4631_ = v_isSharedCheck_4649_;
goto v_resetjp_4629_;
}
v_resetjp_4629_:
{
lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4635_; 
v___x_4632_ = lean_unsigned_to_nat(1u);
v___x_4633_ = lean_nat_add(v_a_4618_, v___x_4632_);
if (v_isShared_4631_ == 0)
{
v___x_4635_ = v___x_4630_;
goto v_reusejp_4634_;
}
else
{
lean_object* v_reuseFailAlloc_4648_; 
v_reuseFailAlloc_4648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4648_, 0, v_fst_4627_);
lean_ctor_set(v_reuseFailAlloc_4648_, 1, v_snd_4628_);
v___x_4635_ = v_reuseFailAlloc_4648_;
goto v_reusejp_4634_;
}
v_reusejp_4634_:
{
lean_object* v___x_4636_; 
lean_inc(v___x_4633_);
lean_inc_ref(v_f_4617_);
v___x_4636_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v___x_4615_, v_a_4616_, v_a_4618_, v_f_4617_, v___x_4633_, v___x_4635_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_);
if (lean_obj_tag(v___x_4636_) == 0)
{
lean_object* v_a_4637_; lean_object* v_fst_4638_; lean_object* v_snd_4639_; lean_object* v___x_4641_; uint8_t v_isShared_4642_; uint8_t v_isSharedCheck_4647_; 
v_a_4637_ = lean_ctor_get(v___x_4636_, 0);
lean_inc(v_a_4637_);
lean_dec_ref_known(v___x_4636_, 1);
v_fst_4638_ = lean_ctor_get(v_a_4637_, 0);
v_snd_4639_ = lean_ctor_get(v_a_4637_, 1);
v_isSharedCheck_4647_ = !lean_is_exclusive(v_a_4637_);
if (v_isSharedCheck_4647_ == 0)
{
v___x_4641_ = v_a_4637_;
v_isShared_4642_ = v_isSharedCheck_4647_;
goto v_resetjp_4640_;
}
else
{
lean_inc(v_snd_4639_);
lean_inc(v_fst_4638_);
lean_dec(v_a_4637_);
v___x_4641_ = lean_box(0);
v_isShared_4642_ = v_isSharedCheck_4647_;
goto v_resetjp_4640_;
}
v_resetjp_4640_:
{
lean_object* v___x_4644_; 
if (v_isShared_4642_ == 0)
{
v___x_4644_ = v___x_4641_;
goto v_reusejp_4643_;
}
else
{
lean_object* v_reuseFailAlloc_4646_; 
v_reuseFailAlloc_4646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4646_, 0, v_fst_4638_);
lean_ctor_set(v_reuseFailAlloc_4646_, 1, v_snd_4639_);
v___x_4644_ = v_reuseFailAlloc_4646_;
goto v_reusejp_4643_;
}
v_reusejp_4643_:
{
v_a_4618_ = v___x_4633_;
v_b_4619_ = v___x_4644_;
goto _start;
}
}
}
else
{
lean_dec(v___x_4633_);
lean_dec_ref(v_f_4617_);
return v___x_4636_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg___boxed(lean_object* v_upperBound_4650_, lean_object* v___x_4651_, lean_object* v_a_4652_, lean_object* v_f_4653_, lean_object* v_a_4654_, lean_object* v_b_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_){
_start:
{
lean_object* v_res_4661_; 
v_res_4661_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v_upperBound_4650_, v___x_4651_, v_a_4652_, v_f_4653_, v_a_4654_, v_b_4655_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_);
lean_dec(v___y_4659_);
lean_dec_ref(v___y_4658_);
lean_dec(v___y_4657_);
lean_dec_ref(v___y_4656_);
lean_dec_ref(v_a_4652_);
lean_dec(v___x_4651_);
lean_dec(v_upperBound_4650_);
return v_res_4661_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0(lean_object* v___x_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_){
_start:
{
lean_object* v___x_4668_; 
v___x_4668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4668_, 0, v___x_4662_);
return v___x_4668_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed(lean_object* v___x_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_){
_start:
{
lean_object* v_res_4675_; 
v_res_4675_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0(v___x_4669_, v___y_4670_, v___y_4671_, v___y_4672_, v___y_4673_);
lean_dec(v___y_4673_);
lean_dec_ref(v___y_4672_);
lean_dec(v___y_4671_);
lean_dec_ref(v___y_4670_);
return v_res_4675_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(lean_object* v_upperBound_4676_, lean_object* v_removed_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_b_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_){
_start:
{
lean_object* v___y_4687_; uint8_t v___x_4710_; 
v___x_4710_ = lean_nat_dec_lt(v_a_4679_, v_upperBound_4676_);
if (v___x_4710_ == 0)
{
lean_object* v___x_4711_; 
lean_dec(v_a_4679_);
v___x_4711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4711_, 0, v_b_4680_);
return v___x_4711_;
}
else
{
uint8_t v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; uint8_t v___x_4715_; 
v___x_4712_ = 0;
v___x_4713_ = lean_box(v___x_4712_);
v___x_4714_ = lean_array_get(v___x_4713_, v_removed_4677_, v_a_4679_);
lean_dec(v___x_4713_);
v___x_4715_ = lean_unbox(v___x_4714_);
lean_dec(v___x_4714_);
if (v___x_4715_ == 0)
{
lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___f_4719_; 
v___x_4716_ = lean_array_fget_borrowed(v_a_4678_, v_a_4679_);
lean_inc(v___x_4716_);
v___x_4717_ = lean_array_push(v_b_4680_, v___x_4716_);
v___x_4718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4718_, 0, v___x_4717_);
v___f_4719_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4719_, 0, v___x_4718_);
v___y_4687_ = v___f_4719_;
goto v___jp_4686_;
}
else
{
lean_object* v___x_4720_; lean_object* v___f_4721_; 
v___x_4720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4720_, 0, v_b_4680_);
v___f_4721_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4721_, 0, v___x_4720_);
v___y_4687_ = v___f_4721_;
goto v___jp_4686_;
}
}
v___jp_4686_:
{
lean_object* v___x_4688_; 
lean_inc(v___y_4684_);
lean_inc_ref(v___y_4683_);
lean_inc(v___y_4682_);
lean_inc_ref(v___y_4681_);
v___x_4688_ = lean_apply_5(v___y_4687_, v___y_4681_, v___y_4682_, v___y_4683_, v___y_4684_, lean_box(0));
if (lean_obj_tag(v___x_4688_) == 0)
{
lean_object* v_a_4689_; lean_object* v___x_4691_; uint8_t v_isShared_4692_; uint8_t v_isSharedCheck_4701_; 
v_a_4689_ = lean_ctor_get(v___x_4688_, 0);
v_isSharedCheck_4701_ = !lean_is_exclusive(v___x_4688_);
if (v_isSharedCheck_4701_ == 0)
{
v___x_4691_ = v___x_4688_;
v_isShared_4692_ = v_isSharedCheck_4701_;
goto v_resetjp_4690_;
}
else
{
lean_inc(v_a_4689_);
lean_dec(v___x_4688_);
v___x_4691_ = lean_box(0);
v_isShared_4692_ = v_isSharedCheck_4701_;
goto v_resetjp_4690_;
}
v_resetjp_4690_:
{
if (lean_obj_tag(v_a_4689_) == 0)
{
lean_object* v_a_4693_; lean_object* v___x_4695_; 
lean_dec(v_a_4679_);
v_a_4693_ = lean_ctor_get(v_a_4689_, 0);
lean_inc(v_a_4693_);
lean_dec_ref_known(v_a_4689_, 1);
if (v_isShared_4692_ == 0)
{
lean_ctor_set(v___x_4691_, 0, v_a_4693_);
v___x_4695_ = v___x_4691_;
goto v_reusejp_4694_;
}
else
{
lean_object* v_reuseFailAlloc_4696_; 
v_reuseFailAlloc_4696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4696_, 0, v_a_4693_);
v___x_4695_ = v_reuseFailAlloc_4696_;
goto v_reusejp_4694_;
}
v_reusejp_4694_:
{
return v___x_4695_;
}
}
else
{
lean_object* v_a_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; 
lean_del_object(v___x_4691_);
v_a_4697_ = lean_ctor_get(v_a_4689_, 0);
lean_inc(v_a_4697_);
lean_dec_ref_known(v_a_4689_, 1);
v___x_4698_ = lean_unsigned_to_nat(1u);
v___x_4699_ = lean_nat_add(v_a_4679_, v___x_4698_);
lean_dec(v_a_4679_);
v_a_4679_ = v___x_4699_;
v_b_4680_ = v_a_4697_;
goto _start;
}
}
}
else
{
lean_object* v_a_4702_; lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4709_; 
lean_dec(v_a_4679_);
v_a_4702_ = lean_ctor_get(v___x_4688_, 0);
v_isSharedCheck_4709_ = !lean_is_exclusive(v___x_4688_);
if (v_isSharedCheck_4709_ == 0)
{
v___x_4704_ = v___x_4688_;
v_isShared_4705_ = v_isSharedCheck_4709_;
goto v_resetjp_4703_;
}
else
{
lean_inc(v_a_4702_);
lean_dec(v___x_4688_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4709_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
lean_object* v___x_4707_; 
if (v_isShared_4705_ == 0)
{
v___x_4707_ = v___x_4704_;
goto v_reusejp_4706_;
}
else
{
lean_object* v_reuseFailAlloc_4708_; 
v_reuseFailAlloc_4708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4708_, 0, v_a_4702_);
v___x_4707_ = v_reuseFailAlloc_4708_;
goto v_reusejp_4706_;
}
v_reusejp_4706_:
{
return v___x_4707_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg___boxed(lean_object* v_upperBound_4722_, lean_object* v_removed_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_, lean_object* v_b_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_){
_start:
{
lean_object* v_res_4732_; 
v_res_4732_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v_upperBound_4722_, v_removed_4723_, v_a_4724_, v_a_4725_, v_b_4726_, v___y_4727_, v___y_4728_, v___y_4729_, v___y_4730_);
lean_dec(v___y_4730_);
lean_dec_ref(v___y_4729_);
lean_dec(v___y_4728_);
lean_dec_ref(v___y_4727_);
lean_dec_ref(v_a_4724_);
lean_dec_ref(v_removed_4723_);
lean_dec(v_upperBound_4722_);
return v_res_4732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(lean_object* v_a_4733_, lean_object* v_f_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_){
_start:
{
lean_object* v___x_4740_; uint8_t v___x_4741_; lean_object* v___x_4742_; lean_object* v_removed_4743_; lean_object* v_numRemoved_4744_; lean_object* v___x_4745_; lean_object* v___x_4746_; 
v___x_4740_ = lean_array_get_size(v_a_4733_);
v___x_4741_ = 0;
v___x_4742_ = lean_box(v___x_4741_);
v_removed_4743_ = lean_mk_array(v___x_4740_, v___x_4742_);
v_numRemoved_4744_ = lean_unsigned_to_nat(0u);
v___x_4745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4745_, 0, v_removed_4743_);
lean_ctor_set(v___x_4745_, 1, v_numRemoved_4744_);
v___x_4746_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v___x_4740_, v___x_4740_, v_a_4733_, v_f_4734_, v_numRemoved_4744_, v___x_4745_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_);
if (lean_obj_tag(v___x_4746_) == 0)
{
lean_object* v_a_4747_; lean_object* v_fst_4748_; lean_object* v_snd_4749_; lean_object* v_a_x27_4750_; lean_object* v___x_4751_; 
v_a_4747_ = lean_ctor_get(v___x_4746_, 0);
lean_inc(v_a_4747_);
lean_dec_ref_known(v___x_4746_, 1);
v_fst_4748_ = lean_ctor_get(v_a_4747_, 0);
lean_inc(v_fst_4748_);
v_snd_4749_ = lean_ctor_get(v_a_4747_, 1);
lean_inc(v_snd_4749_);
lean_dec(v_a_4747_);
v_a_x27_4750_ = lean_mk_empty_array_with_capacity(v_snd_4749_);
lean_dec(v_snd_4749_);
v___x_4751_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v___x_4740_, v_fst_4748_, v_a_4733_, v_numRemoved_4744_, v_a_x27_4750_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_);
lean_dec(v_fst_4748_);
return v___x_4751_;
}
else
{
lean_object* v_a_4752_; lean_object* v___x_4754_; uint8_t v_isShared_4755_; uint8_t v_isSharedCheck_4759_; 
v_a_4752_ = lean_ctor_get(v___x_4746_, 0);
v_isSharedCheck_4759_ = !lean_is_exclusive(v___x_4746_);
if (v_isSharedCheck_4759_ == 0)
{
v___x_4754_ = v___x_4746_;
v_isShared_4755_ = v_isSharedCheck_4759_;
goto v_resetjp_4753_;
}
else
{
lean_inc(v_a_4752_);
lean_dec(v___x_4746_);
v___x_4754_ = lean_box(0);
v_isShared_4755_ = v_isSharedCheck_4759_;
goto v_resetjp_4753_;
}
v_resetjp_4753_:
{
lean_object* v___x_4757_; 
if (v_isShared_4755_ == 0)
{
v___x_4757_ = v___x_4754_;
goto v_reusejp_4756_;
}
else
{
lean_object* v_reuseFailAlloc_4758_; 
v_reuseFailAlloc_4758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4758_, 0, v_a_4752_);
v___x_4757_ = v_reuseFailAlloc_4758_;
goto v_reusejp_4756_;
}
v_reusejp_4756_:
{
return v___x_4757_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg___boxed(lean_object* v_a_4760_, lean_object* v_f_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_){
_start:
{
lean_object* v_res_4767_; 
v_res_4767_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_a_4760_, v_f_4761_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_);
lean_dec(v___y_4765_);
lean_dec_ref(v___y_4764_);
lean_dec(v___y_4763_);
lean_dec_ref(v___y_4762_);
lean_dec_ref(v_a_4760_);
return v_res_4767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed(lean_object* v_mvars_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_){
_start:
{
lean_object* v___f_4775_; lean_object* v___x_4776_; 
v___f_4775_ = ((lean_object*)(l_Lean_Elab_WF_assignSubsumed___closed__0));
v___x_4776_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_mvars_4769_, v___f_4775_, v_a_4770_, v_a_4771_, v_a_4772_, v_a_4773_);
return v___x_4776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_assignSubsumed___boxed(lean_object* v_mvars_4777_, lean_object* v_a_4778_, lean_object* v_a_4779_, lean_object* v_a_4780_, lean_object* v_a_4781_, lean_object* v_a_4782_){
_start:
{
lean_object* v_res_4783_; 
v_res_4783_ = l_Lean_Elab_WF_assignSubsumed(v_mvars_4777_, v_a_4778_, v_a_4779_, v_a_4780_, v_a_4781_);
lean_dec(v_a_4781_);
lean_dec_ref(v_a_4780_);
lean_dec(v_a_4779_);
lean_dec_ref(v_a_4778_);
lean_dec_ref(v_mvars_4777_);
return v_res_4783_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0(lean_object* v_mvarId_4784_, lean_object* v_val_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_, lean_object* v___y_4789_){
_start:
{
lean_object* v___x_4791_; 
v___x_4791_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___redArg(v_mvarId_4784_, v_val_4785_, v___y_4787_);
return v___x_4791_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0___boxed(lean_object* v_mvarId_4792_, lean_object* v_val_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_){
_start:
{
lean_object* v_res_4799_; 
v_res_4799_ = l_Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0(v_mvarId_4792_, v_val_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_);
lean_dec(v___y_4797_);
lean_dec_ref(v___y_4796_);
lean_dec(v___y_4795_);
lean_dec_ref(v___y_4794_);
return v_res_4799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1(lean_object* v_00_u03b1_4800_, lean_object* v_a_4801_, lean_object* v_f_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_){
_start:
{
lean_object* v___x_4808_; 
v___x_4808_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___redArg(v_a_4801_, v_f_4802_, v___y_4803_, v___y_4804_, v___y_4805_, v___y_4806_);
return v___x_4808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1___boxed(lean_object* v_00_u03b1_4809_, lean_object* v_a_4810_, lean_object* v_f_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_, lean_object* v___y_4816_){
_start:
{
lean_object* v_res_4817_; 
v_res_4817_ = l_Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1(v_00_u03b1_4809_, v_a_4810_, v_f_4811_, v___y_4812_, v___y_4813_, v___y_4814_, v___y_4815_);
lean_dec(v___y_4815_);
lean_dec_ref(v___y_4814_);
lean_dec(v___y_4813_);
lean_dec_ref(v___y_4812_);
lean_dec_ref(v_a_4810_);
return v_res_4817_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0(lean_object* v_00_u03b2_4818_, lean_object* v_x_4819_, lean_object* v_x_4820_, lean_object* v_x_4821_){
_start:
{
lean_object* v___x_4822_; 
v___x_4822_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0___redArg(v_x_4819_, v_x_4820_, v_x_4821_);
return v___x_4822_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2(lean_object* v_upperBound_4823_, lean_object* v_00_u03b1_4824_, lean_object* v_a_4825_, lean_object* v_next_4826_, lean_object* v_f_4827_, lean_object* v_inst_4828_, lean_object* v_R_4829_, lean_object* v_a_4830_, lean_object* v_b_4831_, lean_object* v_c_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_){
_start:
{
lean_object* v___x_4838_; 
v___x_4838_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___redArg(v_upperBound_4823_, v_a_4825_, v_next_4826_, v_f_4827_, v_a_4830_, v_b_4831_, v___y_4833_, v___y_4834_, v___y_4835_, v___y_4836_);
return v___x_4838_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2___boxed(lean_object* v_upperBound_4839_, lean_object* v_00_u03b1_4840_, lean_object* v_a_4841_, lean_object* v_next_4842_, lean_object* v_f_4843_, lean_object* v_inst_4844_, lean_object* v_R_4845_, lean_object* v_a_4846_, lean_object* v_b_4847_, lean_object* v_c_4848_, lean_object* v___y_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_){
_start:
{
lean_object* v_res_4854_; 
v_res_4854_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__2(v_upperBound_4839_, v_00_u03b1_4840_, v_a_4841_, v_next_4842_, v_f_4843_, v_inst_4844_, v_R_4845_, v_a_4846_, v_b_4847_, v_c_4848_, v___y_4849_, v___y_4850_, v___y_4851_, v___y_4852_);
lean_dec(v___y_4852_);
lean_dec_ref(v___y_4851_);
lean_dec(v___y_4850_);
lean_dec_ref(v___y_4849_);
lean_dec_ref(v_a_4841_);
lean_dec(v_upperBound_4839_);
return v_res_4854_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3(lean_object* v_00_u03b1_4855_, lean_object* v_upperBound_4856_, lean_object* v_removed_4857_, lean_object* v_a_4858_, lean_object* v_inst_4859_, lean_object* v_R_4860_, lean_object* v_a_4861_, lean_object* v_b_4862_, lean_object* v_c_4863_, lean_object* v___y_4864_, lean_object* v___y_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_){
_start:
{
lean_object* v___x_4869_; 
v___x_4869_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___redArg(v_upperBound_4856_, v_removed_4857_, v_a_4858_, v_a_4861_, v_b_4862_, v___y_4864_, v___y_4865_, v___y_4866_, v___y_4867_);
return v___x_4869_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3___boxed(lean_object* v_00_u03b1_4870_, lean_object* v_upperBound_4871_, lean_object* v_removed_4872_, lean_object* v_a_4873_, lean_object* v_inst_4874_, lean_object* v_R_4875_, lean_object* v_a_4876_, lean_object* v_b_4877_, lean_object* v_c_4878_, lean_object* v___y_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_, lean_object* v___y_4882_, lean_object* v___y_4883_){
_start:
{
lean_object* v_res_4884_; 
v_res_4884_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__3(v_00_u03b1_4870_, v_upperBound_4871_, v_removed_4872_, v_a_4873_, v_inst_4874_, v_R_4875_, v_a_4876_, v_b_4877_, v_c_4878_, v___y_4879_, v___y_4880_, v___y_4881_, v___y_4882_);
lean_dec(v___y_4882_);
lean_dec_ref(v___y_4881_);
lean_dec(v___y_4880_);
lean_dec_ref(v___y_4879_);
lean_dec_ref(v_a_4873_);
lean_dec_ref(v_removed_4872_);
lean_dec(v_upperBound_4871_);
return v_res_4884_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4(lean_object* v_upperBound_4885_, lean_object* v___x_4886_, lean_object* v_00_u03b1_4887_, lean_object* v_a_4888_, lean_object* v_f_4889_, lean_object* v_inst_4890_, lean_object* v_R_4891_, lean_object* v_a_4892_, lean_object* v_b_4893_, lean_object* v_c_4894_, lean_object* v___y_4895_, lean_object* v___y_4896_, lean_object* v___y_4897_, lean_object* v___y_4898_){
_start:
{
lean_object* v___x_4900_; 
v___x_4900_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___redArg(v_upperBound_4885_, v___x_4886_, v_a_4888_, v_f_4889_, v_a_4892_, v_b_4893_, v___y_4895_, v___y_4896_, v___y_4897_, v___y_4898_);
return v___x_4900_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4___boxed(lean_object* v_upperBound_4901_, lean_object* v___x_4902_, lean_object* v_00_u03b1_4903_, lean_object* v_a_4904_, lean_object* v_f_4905_, lean_object* v_inst_4906_, lean_object* v_R_4907_, lean_object* v_a_4908_, lean_object* v_b_4909_, lean_object* v_c_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_, lean_object* v___y_4914_, lean_object* v___y_4915_){
_start:
{
lean_object* v_res_4916_; 
v_res_4916_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Array_filterPairsM___at___00Lean_Elab_WF_assignSubsumed_spec__1_spec__4(v_upperBound_4901_, v___x_4902_, v_00_u03b1_4903_, v_a_4904_, v_f_4905_, v_inst_4906_, v_R_4907_, v_a_4908_, v_b_4909_, v_c_4910_, v___y_4911_, v___y_4912_, v___y_4913_, v___y_4914_);
lean_dec(v___y_4914_);
lean_dec_ref(v___y_4913_);
lean_dec(v___y_4912_);
lean_dec_ref(v___y_4911_);
lean_dec_ref(v_a_4904_);
lean_dec(v___x_4902_);
lean_dec(v_upperBound_4901_);
return v_res_4916_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4917_, lean_object* v_x_4918_, size_t v_x_4919_, size_t v_x_4920_, lean_object* v_x_4921_, lean_object* v_x_4922_){
_start:
{
lean_object* v___x_4923_; 
v___x_4923_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___redArg(v_x_4918_, v_x_4919_, v_x_4920_, v_x_4921_, v_x_4922_);
return v___x_4923_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4924_, lean_object* v_x_4925_, lean_object* v_x_4926_, lean_object* v_x_4927_, lean_object* v_x_4928_, lean_object* v_x_4929_){
_start:
{
size_t v_x_5196__boxed_4930_; size_t v_x_5197__boxed_4931_; lean_object* v_res_4932_; 
v_x_5196__boxed_4930_ = lean_unbox_usize(v_x_4926_);
lean_dec(v_x_4926_);
v_x_5197__boxed_4931_ = lean_unbox_usize(v_x_4927_);
lean_dec(v_x_4927_);
v_res_4932_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1(v_00_u03b2_4924_, v_x_4925_, v_x_5196__boxed_4930_, v_x_5197__boxed_4931_, v_x_4928_, v_x_4929_);
return v_res_4932_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_4933_, lean_object* v_n_4934_, lean_object* v_k_4935_, lean_object* v_v_4936_){
_start:
{
lean_object* v___x_4937_; 
v___x_4937_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3___redArg(v_n_4934_, v_k_4935_, v_v_4936_);
return v___x_4937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_4938_, size_t v_depth_4939_, lean_object* v_keys_4940_, lean_object* v_vals_4941_, lean_object* v_heq_4942_, lean_object* v_i_4943_, lean_object* v_entries_4944_){
_start:
{
lean_object* v___x_4945_; 
v___x_4945_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___redArg(v_depth_4939_, v_keys_4940_, v_vals_4941_, v_i_4943_, v_entries_4944_);
return v___x_4945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_4946_, lean_object* v_depth_4947_, lean_object* v_keys_4948_, lean_object* v_vals_4949_, lean_object* v_heq_4950_, lean_object* v_i_4951_, lean_object* v_entries_4952_){
_start:
{
size_t v_depth_boxed_4953_; lean_object* v_res_4954_; 
v_depth_boxed_4953_ = lean_unbox_usize(v_depth_4947_);
lean_dec(v_depth_4947_);
v_res_4954_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_4946_, v_depth_boxed_4953_, v_keys_4948_, v_vals_4949_, v_heq_4950_, v_i_4951_, v_entries_4952_);
lean_dec_ref(v_vals_4949_);
lean_dec_ref(v_keys_4948_);
return v_res_4954_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_4955_, lean_object* v_x_4956_, lean_object* v_x_4957_, lean_object* v_x_4958_, lean_object* v_x_4959_){
_start:
{
lean_object* v___x_4960_; 
v___x_4960_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_WF_assignSubsumed_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_x_4956_, v_x_4957_, v_x_4958_, v_x_4959_);
return v___x_4960_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4962_; lean_object* v___x_4963_; 
v___x_4962_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__0));
v___x_4963_ = l_Lean_stringToMessageData(v___x_4962_);
return v___x_4963_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4965_; lean_object* v___x_4966_; 
v___x_4965_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__2));
v___x_4966_ = l_Lean_stringToMessageData(v___x_4965_);
return v___x_4966_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(lean_object* v_argsPacker_4967_, lean_object* v_as_4968_, size_t v_sz_4969_, size_t v_i_4970_, lean_object* v_b_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_){
_start:
{
lean_object* v_a_4978_; uint8_t v___x_4982_; 
v___x_4982_ = lean_usize_dec_lt(v_i_4970_, v_sz_4969_);
if (v___x_4982_ == 0)
{
lean_object* v___x_4983_; 
v___x_4983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4983_, 0, v_b_4971_);
return v___x_4983_;
}
else
{
lean_object* v_a_4984_; lean_object* v___x_4985_; 
v_a_4984_ = lean_array_uget_borrowed(v_as_4968_, v_i_4970_);
lean_inc(v_a_4984_);
v___x_4985_ = l_Lean_MVarId_getType(v_a_4984_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_);
if (lean_obj_tag(v___x_4985_) == 0)
{
lean_object* v_a_4986_; lean_object* v___y_4988_; lean_object* v___y_4989_; lean_object* v___y_4990_; lean_object* v___y_4991_; 
v_a_4986_ = lean_ctor_get(v___x_4985_, 0);
lean_inc(v_a_4986_);
lean_dec_ref_known(v___x_4985_, 1);
if (lean_obj_tag(v_a_4986_) == 10)
{
lean_object* v_expr_5004_; 
v_expr_5004_ = lean_ctor_get(v_a_4986_, 1);
if (lean_obj_tag(v_expr_5004_) == 5)
{
lean_object* v_arg_5005_; lean_object* v___x_5006_; 
lean_inc_ref(v_expr_5004_);
lean_dec_ref_known(v_a_4986_, 2);
v_arg_5005_ = lean_ctor_get(v_expr_5004_, 1);
lean_inc_ref_n(v_arg_5005_, 2);
lean_dec_ref_known(v_expr_5004_, 2);
v___x_5006_ = l_Lean_Meta_ArgsPacker_unpack(v_argsPacker_4967_, v_arg_5005_);
if (lean_obj_tag(v___x_5006_) == 1)
{
lean_object* v_val_5007_; lean_object* v_fst_5008_; lean_object* v___x_5009_; uint8_t v___x_5010_; 
lean_dec_ref(v_arg_5005_);
v_val_5007_ = lean_ctor_get(v___x_5006_, 0);
lean_inc(v_val_5007_);
lean_dec_ref_known(v___x_5006_, 1);
v_fst_5008_ = lean_ctor_get(v_val_5007_, 0);
lean_inc(v_fst_5008_);
lean_dec(v_val_5007_);
v___x_5009_ = lean_array_get_size(v_b_4971_);
v___x_5010_ = lean_nat_dec_lt(v_fst_5008_, v___x_5009_);
if (v___x_5010_ == 0)
{
lean_dec(v_fst_5008_);
v_a_4978_ = v_b_4971_;
goto v___jp_4977_;
}
else
{
lean_object* v_v_5011_; lean_object* v___x_5012_; lean_object* v_xs_x27_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; 
v_v_5011_ = lean_array_fget(v_b_4971_, v_fst_5008_);
v___x_5012_ = lean_box(0);
v_xs_x27_5013_ = lean_array_fset(v_b_4971_, v_fst_5008_, v___x_5012_);
lean_inc(v_a_4984_);
v___x_5014_ = lean_array_push(v_v_5011_, v_a_4984_);
v___x_5015_ = lean_array_fset(v_xs_x27_5013_, v_fst_5008_, v___x_5014_);
lean_dec(v_fst_5008_);
v_a_4978_ = v___x_5015_;
goto v___jp_4977_;
}
}
else
{
lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; 
lean_dec(v___x_5006_);
v___x_5016_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__3);
v___x_5017_ = l_Lean_indentExpr(v_arg_5005_);
v___x_5018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5018_, 0, v___x_5016_);
lean_ctor_set(v___x_5018_, 1, v___x_5017_);
v___x_5019_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v___x_5018_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_);
if (lean_obj_tag(v___x_5019_) == 0)
{
lean_dec_ref_known(v___x_5019_, 1);
v_a_4978_ = v_b_4971_;
goto v___jp_4977_;
}
else
{
lean_object* v_a_5020_; lean_object* v___x_5022_; uint8_t v_isShared_5023_; uint8_t v_isSharedCheck_5027_; 
lean_dec_ref(v_b_4971_);
v_a_5020_ = lean_ctor_get(v___x_5019_, 0);
v_isSharedCheck_5027_ = !lean_is_exclusive(v___x_5019_);
if (v_isSharedCheck_5027_ == 0)
{
v___x_5022_ = v___x_5019_;
v_isShared_5023_ = v_isSharedCheck_5027_;
goto v_resetjp_5021_;
}
else
{
lean_inc(v_a_5020_);
lean_dec(v___x_5019_);
v___x_5022_ = lean_box(0);
v_isShared_5023_ = v_isSharedCheck_5027_;
goto v_resetjp_5021_;
}
v_resetjp_5021_:
{
lean_object* v___x_5025_; 
if (v_isShared_5023_ == 0)
{
v___x_5025_ = v___x_5022_;
goto v_reusejp_5024_;
}
else
{
lean_object* v_reuseFailAlloc_5026_; 
v_reuseFailAlloc_5026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5026_, 0, v_a_5020_);
v___x_5025_ = v_reuseFailAlloc_5026_;
goto v_reusejp_5024_;
}
v_reusejp_5024_:
{
return v___x_5025_;
}
}
}
}
}
else
{
v___y_4988_ = v___y_4972_;
v___y_4989_ = v___y_4973_;
v___y_4990_ = v___y_4974_;
v___y_4991_ = v___y_4975_;
goto v___jp_4987_;
}
}
else
{
v___y_4988_ = v___y_4972_;
v___y_4989_ = v___y_4973_;
v___y_4990_ = v___y_4974_;
v___y_4991_ = v___y_4975_;
goto v___jp_4987_;
}
v___jp_4987_:
{
lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; 
v___x_4992_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___closed__1);
v___x_4993_ = l_Lean_indentExpr(v_a_4986_);
v___x_4994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4994_, 0, v___x_4992_);
lean_ctor_set(v___x_4994_, 1, v___x_4993_);
v___x_4995_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1___redArg(v___x_4994_, v___y_4988_, v___y_4989_, v___y_4990_, v___y_4991_);
if (lean_obj_tag(v___x_4995_) == 0)
{
lean_dec_ref_known(v___x_4995_, 1);
v_a_4978_ = v_b_4971_;
goto v___jp_4977_;
}
else
{
lean_object* v_a_4996_; lean_object* v___x_4998_; uint8_t v_isShared_4999_; uint8_t v_isSharedCheck_5003_; 
lean_dec_ref(v_b_4971_);
v_a_4996_ = lean_ctor_get(v___x_4995_, 0);
v_isSharedCheck_5003_ = !lean_is_exclusive(v___x_4995_);
if (v_isSharedCheck_5003_ == 0)
{
v___x_4998_ = v___x_4995_;
v_isShared_4999_ = v_isSharedCheck_5003_;
goto v_resetjp_4997_;
}
else
{
lean_inc(v_a_4996_);
lean_dec(v___x_4995_);
v___x_4998_ = lean_box(0);
v_isShared_4999_ = v_isSharedCheck_5003_;
goto v_resetjp_4997_;
}
v_resetjp_4997_:
{
lean_object* v___x_5001_; 
if (v_isShared_4999_ == 0)
{
v___x_5001_ = v___x_4998_;
goto v_reusejp_5000_;
}
else
{
lean_object* v_reuseFailAlloc_5002_; 
v_reuseFailAlloc_5002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5002_, 0, v_a_4996_);
v___x_5001_ = v_reuseFailAlloc_5002_;
goto v_reusejp_5000_;
}
v_reusejp_5000_:
{
return v___x_5001_;
}
}
}
}
}
else
{
lean_object* v_a_5028_; lean_object* v___x_5030_; uint8_t v_isShared_5031_; uint8_t v_isSharedCheck_5035_; 
lean_dec_ref(v_b_4971_);
v_a_5028_ = lean_ctor_get(v___x_4985_, 0);
v_isSharedCheck_5035_ = !lean_is_exclusive(v___x_4985_);
if (v_isSharedCheck_5035_ == 0)
{
v___x_5030_ = v___x_4985_;
v_isShared_5031_ = v_isSharedCheck_5035_;
goto v_resetjp_5029_;
}
else
{
lean_inc(v_a_5028_);
lean_dec(v___x_4985_);
v___x_5030_ = lean_box(0);
v_isShared_5031_ = v_isSharedCheck_5035_;
goto v_resetjp_5029_;
}
v_resetjp_5029_:
{
lean_object* v___x_5033_; 
if (v_isShared_5031_ == 0)
{
v___x_5033_ = v___x_5030_;
goto v_reusejp_5032_;
}
else
{
lean_object* v_reuseFailAlloc_5034_; 
v_reuseFailAlloc_5034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5034_, 0, v_a_5028_);
v___x_5033_ = v_reuseFailAlloc_5034_;
goto v_reusejp_5032_;
}
v_reusejp_5032_:
{
return v___x_5033_;
}
}
}
}
v___jp_4977_:
{
size_t v___x_4979_; size_t v___x_4980_; 
v___x_4979_ = ((size_t)1ULL);
v___x_4980_ = lean_usize_add(v_i_4970_, v___x_4979_);
v_i_4970_ = v___x_4980_;
v_b_4971_ = v_a_4978_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0___boxed(lean_object* v_argsPacker_5036_, lean_object* v_as_5037_, lean_object* v_sz_5038_, lean_object* v_i_5039_, lean_object* v_b_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_){
_start:
{
size_t v_sz_boxed_5046_; size_t v_i_boxed_5047_; lean_object* v_res_5048_; 
v_sz_boxed_5046_ = lean_unbox_usize(v_sz_5038_);
lean_dec(v_sz_5038_);
v_i_boxed_5047_ = lean_unbox_usize(v_i_5039_);
lean_dec(v_i_5039_);
v_res_5048_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(v_argsPacker_5036_, v_as_5037_, v_sz_boxed_5046_, v_i_boxed_5047_, v_b_5040_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_);
lean_dec(v___y_5044_);
lean_dec_ref(v___y_5043_);
lean_dec(v___y_5042_);
lean_dec_ref(v___y_5041_);
lean_dec_ref(v_as_5037_);
lean_dec_ref(v_argsPacker_5036_);
return v_res_5048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_groupGoalsByFunction(lean_object* v_argsPacker_5049_, lean_object* v_numFuncs_5050_, lean_object* v_goals_5051_, lean_object* v_a_5052_, lean_object* v_a_5053_, lean_object* v_a_5054_, lean_object* v_a_5055_){
_start:
{
lean_object* v___x_5057_; lean_object* v_r_5058_; size_t v_sz_5059_; size_t v___x_5060_; lean_object* v___x_5061_; 
v___x_5057_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_mkDecreasingProof___redArg___closed__0));
v_r_5058_ = lean_mk_array(v_numFuncs_5050_, v___x_5057_);
v_sz_5059_ = lean_array_size(v_goals_5051_);
v___x_5060_ = ((size_t)0ULL);
v___x_5061_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_groupGoalsByFunction_spec__0(v_argsPacker_5049_, v_goals_5051_, v_sz_5059_, v___x_5060_, v_r_5058_, v_a_5052_, v_a_5053_, v_a_5054_, v_a_5055_);
return v___x_5061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_groupGoalsByFunction___boxed(lean_object* v_argsPacker_5062_, lean_object* v_numFuncs_5063_, lean_object* v_goals_5064_, lean_object* v_a_5065_, lean_object* v_a_5066_, lean_object* v_a_5067_, lean_object* v_a_5068_, lean_object* v_a_5069_){
_start:
{
lean_object* v_res_5070_; 
v_res_5070_ = l_Lean_Elab_WF_groupGoalsByFunction(v_argsPacker_5062_, v_numFuncs_5063_, v_goals_5064_, v_a_5065_, v_a_5066_, v_a_5067_, v_a_5068_);
lean_dec(v_a_5068_);
lean_dec_ref(v_a_5067_);
lean_dec(v_a_5066_);
lean_dec_ref(v_a_5065_);
lean_dec_ref(v_goals_5064_);
lean_dec_ref(v_argsPacker_5062_);
return v_res_5070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(lean_object* v_t_5071_, lean_object* v___y_5072_){
_start:
{
lean_object* v___x_5074_; lean_object* v_infoState_5075_; uint8_t v_enabled_5076_; 
v___x_5074_ = lean_st_ref_get(v___y_5072_);
v_infoState_5075_ = lean_ctor_get(v___x_5074_, 7);
lean_inc_ref(v_infoState_5075_);
lean_dec(v___x_5074_);
v_enabled_5076_ = lean_ctor_get_uint8(v_infoState_5075_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5075_);
if (v_enabled_5076_ == 0)
{
lean_object* v___x_5077_; lean_object* v___x_5078_; 
lean_dec_ref(v_t_5071_);
v___x_5077_ = lean_box(0);
v___x_5078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5078_, 0, v___x_5077_);
return v___x_5078_;
}
else
{
lean_object* v___x_5079_; lean_object* v_infoState_5080_; lean_object* v_env_5081_; lean_object* v_nextMacroScope_5082_; lean_object* v_ngen_5083_; lean_object* v_auxDeclNGen_5084_; lean_object* v_traceState_5085_; lean_object* v_cache_5086_; lean_object* v_messages_5087_; lean_object* v_snapshotTasks_5088_; lean_object* v___x_5090_; uint8_t v_isShared_5091_; uint8_t v_isSharedCheck_5110_; 
v___x_5079_ = lean_st_ref_take(v___y_5072_);
v_infoState_5080_ = lean_ctor_get(v___x_5079_, 7);
v_env_5081_ = lean_ctor_get(v___x_5079_, 0);
v_nextMacroScope_5082_ = lean_ctor_get(v___x_5079_, 1);
v_ngen_5083_ = lean_ctor_get(v___x_5079_, 2);
v_auxDeclNGen_5084_ = lean_ctor_get(v___x_5079_, 3);
v_traceState_5085_ = lean_ctor_get(v___x_5079_, 4);
v_cache_5086_ = lean_ctor_get(v___x_5079_, 5);
v_messages_5087_ = lean_ctor_get(v___x_5079_, 6);
v_snapshotTasks_5088_ = lean_ctor_get(v___x_5079_, 8);
v_isSharedCheck_5110_ = !lean_is_exclusive(v___x_5079_);
if (v_isSharedCheck_5110_ == 0)
{
v___x_5090_ = v___x_5079_;
v_isShared_5091_ = v_isSharedCheck_5110_;
goto v_resetjp_5089_;
}
else
{
lean_inc(v_snapshotTasks_5088_);
lean_inc(v_infoState_5080_);
lean_inc(v_messages_5087_);
lean_inc(v_cache_5086_);
lean_inc(v_traceState_5085_);
lean_inc(v_auxDeclNGen_5084_);
lean_inc(v_ngen_5083_);
lean_inc(v_nextMacroScope_5082_);
lean_inc(v_env_5081_);
lean_dec(v___x_5079_);
v___x_5090_ = lean_box(0);
v_isShared_5091_ = v_isSharedCheck_5110_;
goto v_resetjp_5089_;
}
v_resetjp_5089_:
{
uint8_t v_enabled_5092_; lean_object* v_assignment_5093_; lean_object* v_lazyAssignment_5094_; lean_object* v_trees_5095_; lean_object* v___x_5097_; uint8_t v_isShared_5098_; uint8_t v_isSharedCheck_5109_; 
v_enabled_5092_ = lean_ctor_get_uint8(v_infoState_5080_, sizeof(void*)*3);
v_assignment_5093_ = lean_ctor_get(v_infoState_5080_, 0);
v_lazyAssignment_5094_ = lean_ctor_get(v_infoState_5080_, 1);
v_trees_5095_ = lean_ctor_get(v_infoState_5080_, 2);
v_isSharedCheck_5109_ = !lean_is_exclusive(v_infoState_5080_);
if (v_isSharedCheck_5109_ == 0)
{
v___x_5097_ = v_infoState_5080_;
v_isShared_5098_ = v_isSharedCheck_5109_;
goto v_resetjp_5096_;
}
else
{
lean_inc(v_trees_5095_);
lean_inc(v_lazyAssignment_5094_);
lean_inc(v_assignment_5093_);
lean_dec(v_infoState_5080_);
v___x_5097_ = lean_box(0);
v_isShared_5098_ = v_isSharedCheck_5109_;
goto v_resetjp_5096_;
}
v_resetjp_5096_:
{
lean_object* v___x_5099_; lean_object* v___x_5101_; 
v___x_5099_ = l_Lean_PersistentArray_push___redArg(v_trees_5095_, v_t_5071_);
if (v_isShared_5098_ == 0)
{
lean_ctor_set(v___x_5097_, 2, v___x_5099_);
v___x_5101_ = v___x_5097_;
goto v_reusejp_5100_;
}
else
{
lean_object* v_reuseFailAlloc_5108_; 
v_reuseFailAlloc_5108_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5108_, 0, v_assignment_5093_);
lean_ctor_set(v_reuseFailAlloc_5108_, 1, v_lazyAssignment_5094_);
lean_ctor_set(v_reuseFailAlloc_5108_, 2, v___x_5099_);
lean_ctor_set_uint8(v_reuseFailAlloc_5108_, sizeof(void*)*3, v_enabled_5092_);
v___x_5101_ = v_reuseFailAlloc_5108_;
goto v_reusejp_5100_;
}
v_reusejp_5100_:
{
lean_object* v___x_5103_; 
if (v_isShared_5091_ == 0)
{
lean_ctor_set(v___x_5090_, 7, v___x_5101_);
v___x_5103_ = v___x_5090_;
goto v_reusejp_5102_;
}
else
{
lean_object* v_reuseFailAlloc_5107_; 
v_reuseFailAlloc_5107_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5107_, 0, v_env_5081_);
lean_ctor_set(v_reuseFailAlloc_5107_, 1, v_nextMacroScope_5082_);
lean_ctor_set(v_reuseFailAlloc_5107_, 2, v_ngen_5083_);
lean_ctor_set(v_reuseFailAlloc_5107_, 3, v_auxDeclNGen_5084_);
lean_ctor_set(v_reuseFailAlloc_5107_, 4, v_traceState_5085_);
lean_ctor_set(v_reuseFailAlloc_5107_, 5, v_cache_5086_);
lean_ctor_set(v_reuseFailAlloc_5107_, 6, v_messages_5087_);
lean_ctor_set(v_reuseFailAlloc_5107_, 7, v___x_5101_);
lean_ctor_set(v_reuseFailAlloc_5107_, 8, v_snapshotTasks_5088_);
v___x_5103_ = v_reuseFailAlloc_5107_;
goto v_reusejp_5102_;
}
v_reusejp_5102_:
{
lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; 
v___x_5104_ = lean_st_ref_set(v___y_5072_, v___x_5103_);
v___x_5105_ = lean_box(0);
v___x_5106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5106_, 0, v___x_5105_);
return v___x_5106_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg___boxed(lean_object* v_t_5111_, lean_object* v___y_5112_, lean_object* v___y_5113_){
_start:
{
lean_object* v_res_5114_; 
v_res_5114_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v_t_5111_, v___y_5112_);
lean_dec(v___y_5112_);
return v_res_5114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0(lean_object* v_t_5115_, lean_object* v___y_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_){
_start:
{
lean_object* v___x_5123_; 
v___x_5123_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v_t_5115_, v___y_5121_);
return v___x_5123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___boxed(lean_object* v_t_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_){
_start:
{
lean_object* v_res_5132_; 
v_res_5132_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0(v_t_5124_, v___y_5125_, v___y_5126_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_);
lean_dec(v___y_5130_);
lean_dec_ref(v___y_5129_);
lean_dec(v___y_5128_);
lean_dec_ref(v___y_5127_);
lean_dec(v___y_5126_);
lean_dec_ref(v___y_5125_);
return v_res_5132_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(lean_object* v_e_5133_, lean_object* v___y_5134_){
_start:
{
uint8_t v___x_5136_; 
v___x_5136_ = l_Lean_Expr_hasMVar(v_e_5133_);
if (v___x_5136_ == 0)
{
lean_object* v___x_5137_; 
v___x_5137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5137_, 0, v_e_5133_);
return v___x_5137_;
}
else
{
lean_object* v___x_5138_; lean_object* v_mctx_5139_; lean_object* v___x_5140_; lean_object* v_fst_5141_; lean_object* v_snd_5142_; lean_object* v___x_5143_; lean_object* v_cache_5144_; lean_object* v_zetaDeltaFVarIds_5145_; lean_object* v_postponed_5146_; lean_object* v_diag_5147_; lean_object* v___x_5149_; uint8_t v_isShared_5150_; uint8_t v_isSharedCheck_5156_; 
v___x_5138_ = lean_st_ref_get(v___y_5134_);
v_mctx_5139_ = lean_ctor_get(v___x_5138_, 0);
lean_inc_ref(v_mctx_5139_);
lean_dec(v___x_5138_);
v___x_5140_ = l_Lean_instantiateMVarsCore(v_mctx_5139_, v_e_5133_);
v_fst_5141_ = lean_ctor_get(v___x_5140_, 0);
lean_inc(v_fst_5141_);
v_snd_5142_ = lean_ctor_get(v___x_5140_, 1);
lean_inc(v_snd_5142_);
lean_dec_ref(v___x_5140_);
v___x_5143_ = lean_st_ref_take(v___y_5134_);
v_cache_5144_ = lean_ctor_get(v___x_5143_, 1);
v_zetaDeltaFVarIds_5145_ = lean_ctor_get(v___x_5143_, 2);
v_postponed_5146_ = lean_ctor_get(v___x_5143_, 3);
v_diag_5147_ = lean_ctor_get(v___x_5143_, 4);
v_isSharedCheck_5156_ = !lean_is_exclusive(v___x_5143_);
if (v_isSharedCheck_5156_ == 0)
{
lean_object* v_unused_5157_; 
v_unused_5157_ = lean_ctor_get(v___x_5143_, 0);
lean_dec(v_unused_5157_);
v___x_5149_ = v___x_5143_;
v_isShared_5150_ = v_isSharedCheck_5156_;
goto v_resetjp_5148_;
}
else
{
lean_inc(v_diag_5147_);
lean_inc(v_postponed_5146_);
lean_inc(v_zetaDeltaFVarIds_5145_);
lean_inc(v_cache_5144_);
lean_dec(v___x_5143_);
v___x_5149_ = lean_box(0);
v_isShared_5150_ = v_isSharedCheck_5156_;
goto v_resetjp_5148_;
}
v_resetjp_5148_:
{
lean_object* v___x_5152_; 
if (v_isShared_5150_ == 0)
{
lean_ctor_set(v___x_5149_, 0, v_snd_5142_);
v___x_5152_ = v___x_5149_;
goto v_reusejp_5151_;
}
else
{
lean_object* v_reuseFailAlloc_5155_; 
v_reuseFailAlloc_5155_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5155_, 0, v_snd_5142_);
lean_ctor_set(v_reuseFailAlloc_5155_, 1, v_cache_5144_);
lean_ctor_set(v_reuseFailAlloc_5155_, 2, v_zetaDeltaFVarIds_5145_);
lean_ctor_set(v_reuseFailAlloc_5155_, 3, v_postponed_5146_);
lean_ctor_set(v_reuseFailAlloc_5155_, 4, v_diag_5147_);
v___x_5152_ = v_reuseFailAlloc_5155_;
goto v_reusejp_5151_;
}
v_reusejp_5151_:
{
lean_object* v___x_5153_; lean_object* v___x_5154_; 
v___x_5153_ = lean_st_ref_set(v___y_5134_, v___x_5152_);
v___x_5154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5154_, 0, v_fst_5141_);
return v___x_5154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg___boxed(lean_object* v_e_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_){
_start:
{
lean_object* v_res_5161_; 
v_res_5161_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_e_5158_, v___y_5159_);
lean_dec(v___y_5159_);
return v_res_5161_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7(lean_object* v_e_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_, lean_object* v___y_5165_, lean_object* v___y_5166_){
_start:
{
lean_object* v___x_5168_; 
v___x_5168_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___redArg(v_e_5162_, v___y_5164_);
return v___x_5168_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7___boxed(lean_object* v_e_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_, lean_object* v___y_5174_){
_start:
{
lean_object* v_res_5175_; 
v_res_5175_ = l_Lean_instantiateMVars___at___00Lean_Elab_WF_solveDecreasingGoals_spec__7(v_e_5169_, v___y_5170_, v___y_5171_, v___y_5172_, v___y_5173_);
lean_dec(v___y_5173_);
lean_dec_ref(v___y_5172_);
lean_dec(v___y_5171_);
lean_dec_ref(v___y_5170_);
return v_res_5175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(lean_object* v_as_5176_, size_t v_i_5177_, size_t v_stop_5178_, lean_object* v_b_5179_, lean_object* v___y_5180_, lean_object* v___y_5181_, lean_object* v___y_5182_, lean_object* v___y_5183_, lean_object* v___y_5184_, lean_object* v___y_5185_){
_start:
{
uint8_t v___x_5187_; 
v___x_5187_ = lean_usize_dec_eq(v_i_5177_, v_stop_5178_);
if (v___x_5187_ == 0)
{
lean_object* v___x_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; 
v___x_5188_ = lean_array_uget_borrowed(v_as_5176_, v_i_5177_);
lean_inc(v___x_5188_);
v___x_5189_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_5189_, 0, v___x_5188_);
v___x_5190_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_WF_solveDecreasingGoals_spec__0___redArg(v___x_5189_, v___y_5185_);
if (lean_obj_tag(v___x_5190_) == 0)
{
lean_object* v_a_5191_; size_t v___x_5192_; size_t v___x_5193_; 
v_a_5191_ = lean_ctor_get(v___x_5190_, 0);
lean_inc(v_a_5191_);
lean_dec_ref_known(v___x_5190_, 1);
v___x_5192_ = ((size_t)1ULL);
v___x_5193_ = lean_usize_add(v_i_5177_, v___x_5192_);
v_i_5177_ = v___x_5193_;
v_b_5179_ = v_a_5191_;
goto _start;
}
else
{
return v___x_5190_;
}
}
else
{
lean_object* v___x_5195_; 
v___x_5195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5195_, 0, v_b_5179_);
return v___x_5195_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4___boxed(lean_object* v_as_5196_, lean_object* v_i_5197_, lean_object* v_stop_5198_, lean_object* v_b_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_, lean_object* v___y_5206_){
_start:
{
size_t v_i_boxed_5207_; size_t v_stop_boxed_5208_; lean_object* v_res_5209_; 
v_i_boxed_5207_ = lean_unbox_usize(v_i_5197_);
lean_dec(v_i_5197_);
v_stop_boxed_5208_ = lean_unbox_usize(v_stop_5198_);
lean_dec(v_stop_5198_);
v_res_5209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v_as_5196_, v_i_boxed_5207_, v_stop_boxed_5208_, v_b_5199_, v___y_5200_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_, v___y_5205_);
lean_dec(v___y_5205_);
lean_dec_ref(v___y_5204_);
lean_dec(v___y_5203_);
lean_dec_ref(v___y_5202_);
lean_dec(v___y_5201_);
lean_dec_ref(v___y_5200_);
lean_dec_ref(v_as_5196_);
return v_res_5209_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; 
v___x_5210_ = lean_unsigned_to_nat(32u);
v___x_5211_ = lean_mk_empty_array_with_capacity(v___x_5210_);
v___x_5212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5212_, 0, v___x_5211_);
return v___x_5212_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; 
v___x_5213_ = ((size_t)5ULL);
v___x_5214_ = lean_unsigned_to_nat(0u);
v___x_5215_ = lean_unsigned_to_nat(32u);
v___x_5216_ = lean_mk_empty_array_with_capacity(v___x_5215_);
v___x_5217_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__0);
v___x_5218_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5218_, 0, v___x_5217_);
lean_ctor_set(v___x_5218_, 1, v___x_5216_);
lean_ctor_set(v___x_5218_, 2, v___x_5214_);
lean_ctor_set(v___x_5218_, 3, v___x_5214_);
lean_ctor_set_usize(v___x_5218_, 4, v___x_5213_);
return v___x_5218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(lean_object* v___y_5219_){
_start:
{
lean_object* v___x_5221_; lean_object* v_infoState_5222_; lean_object* v_trees_5223_; lean_object* v___x_5224_; lean_object* v_infoState_5225_; lean_object* v_env_5226_; lean_object* v_nextMacroScope_5227_; lean_object* v_ngen_5228_; lean_object* v_auxDeclNGen_5229_; lean_object* v_traceState_5230_; lean_object* v_cache_5231_; lean_object* v_messages_5232_; lean_object* v_snapshotTasks_5233_; lean_object* v___x_5235_; uint8_t v_isShared_5236_; uint8_t v_isSharedCheck_5254_; 
v___x_5221_ = lean_st_ref_get(v___y_5219_);
v_infoState_5222_ = lean_ctor_get(v___x_5221_, 7);
lean_inc_ref(v_infoState_5222_);
lean_dec(v___x_5221_);
v_trees_5223_ = lean_ctor_get(v_infoState_5222_, 2);
lean_inc_ref(v_trees_5223_);
lean_dec_ref(v_infoState_5222_);
v___x_5224_ = lean_st_ref_take(v___y_5219_);
v_infoState_5225_ = lean_ctor_get(v___x_5224_, 7);
v_env_5226_ = lean_ctor_get(v___x_5224_, 0);
v_nextMacroScope_5227_ = lean_ctor_get(v___x_5224_, 1);
v_ngen_5228_ = lean_ctor_get(v___x_5224_, 2);
v_auxDeclNGen_5229_ = lean_ctor_get(v___x_5224_, 3);
v_traceState_5230_ = lean_ctor_get(v___x_5224_, 4);
v_cache_5231_ = lean_ctor_get(v___x_5224_, 5);
v_messages_5232_ = lean_ctor_get(v___x_5224_, 6);
v_snapshotTasks_5233_ = lean_ctor_get(v___x_5224_, 8);
v_isSharedCheck_5254_ = !lean_is_exclusive(v___x_5224_);
if (v_isSharedCheck_5254_ == 0)
{
v___x_5235_ = v___x_5224_;
v_isShared_5236_ = v_isSharedCheck_5254_;
goto v_resetjp_5234_;
}
else
{
lean_inc(v_snapshotTasks_5233_);
lean_inc(v_infoState_5225_);
lean_inc(v_messages_5232_);
lean_inc(v_cache_5231_);
lean_inc(v_traceState_5230_);
lean_inc(v_auxDeclNGen_5229_);
lean_inc(v_ngen_5228_);
lean_inc(v_nextMacroScope_5227_);
lean_inc(v_env_5226_);
lean_dec(v___x_5224_);
v___x_5235_ = lean_box(0);
v_isShared_5236_ = v_isSharedCheck_5254_;
goto v_resetjp_5234_;
}
v_resetjp_5234_:
{
uint8_t v_enabled_5237_; lean_object* v_assignment_5238_; lean_object* v_lazyAssignment_5239_; lean_object* v___x_5241_; uint8_t v_isShared_5242_; uint8_t v_isSharedCheck_5252_; 
v_enabled_5237_ = lean_ctor_get_uint8(v_infoState_5225_, sizeof(void*)*3);
v_assignment_5238_ = lean_ctor_get(v_infoState_5225_, 0);
v_lazyAssignment_5239_ = lean_ctor_get(v_infoState_5225_, 1);
v_isSharedCheck_5252_ = !lean_is_exclusive(v_infoState_5225_);
if (v_isSharedCheck_5252_ == 0)
{
lean_object* v_unused_5253_; 
v_unused_5253_ = lean_ctor_get(v_infoState_5225_, 2);
lean_dec(v_unused_5253_);
v___x_5241_ = v_infoState_5225_;
v_isShared_5242_ = v_isSharedCheck_5252_;
goto v_resetjp_5240_;
}
else
{
lean_inc(v_lazyAssignment_5239_);
lean_inc(v_assignment_5238_);
lean_dec(v_infoState_5225_);
v___x_5241_ = lean_box(0);
v_isShared_5242_ = v_isSharedCheck_5252_;
goto v_resetjp_5240_;
}
v_resetjp_5240_:
{
lean_object* v___x_5243_; lean_object* v___x_5245_; 
v___x_5243_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___closed__1);
if (v_isShared_5242_ == 0)
{
lean_ctor_set(v___x_5241_, 2, v___x_5243_);
v___x_5245_ = v___x_5241_;
goto v_reusejp_5244_;
}
else
{
lean_object* v_reuseFailAlloc_5251_; 
v_reuseFailAlloc_5251_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5251_, 0, v_assignment_5238_);
lean_ctor_set(v_reuseFailAlloc_5251_, 1, v_lazyAssignment_5239_);
lean_ctor_set(v_reuseFailAlloc_5251_, 2, v___x_5243_);
lean_ctor_set_uint8(v_reuseFailAlloc_5251_, sizeof(void*)*3, v_enabled_5237_);
v___x_5245_ = v_reuseFailAlloc_5251_;
goto v_reusejp_5244_;
}
v_reusejp_5244_:
{
lean_object* v___x_5247_; 
if (v_isShared_5236_ == 0)
{
lean_ctor_set(v___x_5235_, 7, v___x_5245_);
v___x_5247_ = v___x_5235_;
goto v_reusejp_5246_;
}
else
{
lean_object* v_reuseFailAlloc_5250_; 
v_reuseFailAlloc_5250_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5250_, 0, v_env_5226_);
lean_ctor_set(v_reuseFailAlloc_5250_, 1, v_nextMacroScope_5227_);
lean_ctor_set(v_reuseFailAlloc_5250_, 2, v_ngen_5228_);
lean_ctor_set(v_reuseFailAlloc_5250_, 3, v_auxDeclNGen_5229_);
lean_ctor_set(v_reuseFailAlloc_5250_, 4, v_traceState_5230_);
lean_ctor_set(v_reuseFailAlloc_5250_, 5, v_cache_5231_);
lean_ctor_set(v_reuseFailAlloc_5250_, 6, v_messages_5232_);
lean_ctor_set(v_reuseFailAlloc_5250_, 7, v___x_5245_);
lean_ctor_set(v_reuseFailAlloc_5250_, 8, v_snapshotTasks_5233_);
v___x_5247_ = v_reuseFailAlloc_5250_;
goto v_reusejp_5246_;
}
v_reusejp_5246_:
{
lean_object* v___x_5248_; lean_object* v___x_5249_; 
v___x_5248_ = lean_st_ref_set(v___y_5219_, v___x_5247_);
v___x_5249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5249_, 0, v_trees_5223_);
return v___x_5249_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg___boxed(lean_object* v___y_5255_, lean_object* v___y_5256_){
_start:
{
lean_object* v_res_5257_; 
v_res_5257_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_5255_);
lean_dec(v___y_5255_);
return v_res_5257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(lean_object* v___y_5258_, lean_object* v_mkInfoTree_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_, lean_object* v___y_5262_, lean_object* v___y_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_, lean_object* v_a_5267_, lean_object* v_a_x3f_5268_){
_start:
{
lean_object* v___x_5270_; lean_object* v_infoState_5271_; lean_object* v_trees_5272_; lean_object* v___x_5273_; 
v___x_5270_ = lean_st_ref_get(v___y_5258_);
v_infoState_5271_ = lean_ctor_get(v___x_5270_, 7);
lean_inc_ref(v_infoState_5271_);
lean_dec(v___x_5270_);
v_trees_5272_ = lean_ctor_get(v_infoState_5271_, 2);
lean_inc_ref(v_trees_5272_);
lean_dec_ref(v_infoState_5271_);
lean_inc(v___y_5258_);
lean_inc_ref(v___y_5266_);
lean_inc(v___y_5265_);
lean_inc_ref(v___y_5264_);
lean_inc(v___y_5263_);
lean_inc_ref(v___y_5262_);
lean_inc(v___y_5261_);
lean_inc_ref(v___y_5260_);
v___x_5273_ = lean_apply_10(v_mkInfoTree_5259_, v_trees_5272_, v___y_5260_, v___y_5261_, v___y_5262_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_, v___y_5258_, lean_box(0));
if (lean_obj_tag(v___x_5273_) == 0)
{
lean_object* v_a_5274_; lean_object* v___x_5276_; uint8_t v_isShared_5277_; uint8_t v_isSharedCheck_5312_; 
v_a_5274_ = lean_ctor_get(v___x_5273_, 0);
v_isSharedCheck_5312_ = !lean_is_exclusive(v___x_5273_);
if (v_isSharedCheck_5312_ == 0)
{
v___x_5276_ = v___x_5273_;
v_isShared_5277_ = v_isSharedCheck_5312_;
goto v_resetjp_5275_;
}
else
{
lean_inc(v_a_5274_);
lean_dec(v___x_5273_);
v___x_5276_ = lean_box(0);
v_isShared_5277_ = v_isSharedCheck_5312_;
goto v_resetjp_5275_;
}
v_resetjp_5275_:
{
lean_object* v___x_5278_; lean_object* v_infoState_5279_; lean_object* v_env_5280_; lean_object* v_nextMacroScope_5281_; lean_object* v_ngen_5282_; lean_object* v_auxDeclNGen_5283_; lean_object* v_traceState_5284_; lean_object* v_cache_5285_; lean_object* v_messages_5286_; lean_object* v_snapshotTasks_5287_; lean_object* v___x_5289_; uint8_t v_isShared_5290_; uint8_t v_isSharedCheck_5311_; 
v___x_5278_ = lean_st_ref_take(v___y_5258_);
v_infoState_5279_ = lean_ctor_get(v___x_5278_, 7);
v_env_5280_ = lean_ctor_get(v___x_5278_, 0);
v_nextMacroScope_5281_ = lean_ctor_get(v___x_5278_, 1);
v_ngen_5282_ = lean_ctor_get(v___x_5278_, 2);
v_auxDeclNGen_5283_ = lean_ctor_get(v___x_5278_, 3);
v_traceState_5284_ = lean_ctor_get(v___x_5278_, 4);
v_cache_5285_ = lean_ctor_get(v___x_5278_, 5);
v_messages_5286_ = lean_ctor_get(v___x_5278_, 6);
v_snapshotTasks_5287_ = lean_ctor_get(v___x_5278_, 8);
v_isSharedCheck_5311_ = !lean_is_exclusive(v___x_5278_);
if (v_isSharedCheck_5311_ == 0)
{
v___x_5289_ = v___x_5278_;
v_isShared_5290_ = v_isSharedCheck_5311_;
goto v_resetjp_5288_;
}
else
{
lean_inc(v_snapshotTasks_5287_);
lean_inc(v_infoState_5279_);
lean_inc(v_messages_5286_);
lean_inc(v_cache_5285_);
lean_inc(v_traceState_5284_);
lean_inc(v_auxDeclNGen_5283_);
lean_inc(v_ngen_5282_);
lean_inc(v_nextMacroScope_5281_);
lean_inc(v_env_5280_);
lean_dec(v___x_5278_);
v___x_5289_ = lean_box(0);
v_isShared_5290_ = v_isSharedCheck_5311_;
goto v_resetjp_5288_;
}
v_resetjp_5288_:
{
uint8_t v_enabled_5291_; lean_object* v_assignment_5292_; lean_object* v_lazyAssignment_5293_; lean_object* v___x_5295_; uint8_t v_isShared_5296_; uint8_t v_isSharedCheck_5309_; 
v_enabled_5291_ = lean_ctor_get_uint8(v_infoState_5279_, sizeof(void*)*3);
v_assignment_5292_ = lean_ctor_get(v_infoState_5279_, 0);
v_lazyAssignment_5293_ = lean_ctor_get(v_infoState_5279_, 1);
v_isSharedCheck_5309_ = !lean_is_exclusive(v_infoState_5279_);
if (v_isSharedCheck_5309_ == 0)
{
lean_object* v_unused_5310_; 
v_unused_5310_ = lean_ctor_get(v_infoState_5279_, 2);
lean_dec(v_unused_5310_);
v___x_5295_ = v_infoState_5279_;
v_isShared_5296_ = v_isSharedCheck_5309_;
goto v_resetjp_5294_;
}
else
{
lean_inc(v_lazyAssignment_5293_);
lean_inc(v_assignment_5292_);
lean_dec(v_infoState_5279_);
v___x_5295_ = lean_box(0);
v_isShared_5296_ = v_isSharedCheck_5309_;
goto v_resetjp_5294_;
}
v_resetjp_5294_:
{
lean_object* v___x_5297_; lean_object* v___x_5299_; 
v___x_5297_ = l_Lean_PersistentArray_push___redArg(v_a_5267_, v_a_5274_);
if (v_isShared_5296_ == 0)
{
lean_ctor_set(v___x_5295_, 2, v___x_5297_);
v___x_5299_ = v___x_5295_;
goto v_reusejp_5298_;
}
else
{
lean_object* v_reuseFailAlloc_5308_; 
v_reuseFailAlloc_5308_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5308_, 0, v_assignment_5292_);
lean_ctor_set(v_reuseFailAlloc_5308_, 1, v_lazyAssignment_5293_);
lean_ctor_set(v_reuseFailAlloc_5308_, 2, v___x_5297_);
lean_ctor_set_uint8(v_reuseFailAlloc_5308_, sizeof(void*)*3, v_enabled_5291_);
v___x_5299_ = v_reuseFailAlloc_5308_;
goto v_reusejp_5298_;
}
v_reusejp_5298_:
{
lean_object* v___x_5301_; 
if (v_isShared_5290_ == 0)
{
lean_ctor_set(v___x_5289_, 7, v___x_5299_);
v___x_5301_ = v___x_5289_;
goto v_reusejp_5300_;
}
else
{
lean_object* v_reuseFailAlloc_5307_; 
v_reuseFailAlloc_5307_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5307_, 0, v_env_5280_);
lean_ctor_set(v_reuseFailAlloc_5307_, 1, v_nextMacroScope_5281_);
lean_ctor_set(v_reuseFailAlloc_5307_, 2, v_ngen_5282_);
lean_ctor_set(v_reuseFailAlloc_5307_, 3, v_auxDeclNGen_5283_);
lean_ctor_set(v_reuseFailAlloc_5307_, 4, v_traceState_5284_);
lean_ctor_set(v_reuseFailAlloc_5307_, 5, v_cache_5285_);
lean_ctor_set(v_reuseFailAlloc_5307_, 6, v_messages_5286_);
lean_ctor_set(v_reuseFailAlloc_5307_, 7, v___x_5299_);
lean_ctor_set(v_reuseFailAlloc_5307_, 8, v_snapshotTasks_5287_);
v___x_5301_ = v_reuseFailAlloc_5307_;
goto v_reusejp_5300_;
}
v_reusejp_5300_:
{
lean_object* v___x_5302_; lean_object* v___x_5303_; lean_object* v___x_5305_; 
v___x_5302_ = lean_st_ref_set(v___y_5258_, v___x_5301_);
v___x_5303_ = lean_box(0);
if (v_isShared_5277_ == 0)
{
lean_ctor_set(v___x_5276_, 0, v___x_5303_);
v___x_5305_ = v___x_5276_;
goto v_reusejp_5304_;
}
else
{
lean_object* v_reuseFailAlloc_5306_; 
v_reuseFailAlloc_5306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5306_, 0, v___x_5303_);
v___x_5305_ = v_reuseFailAlloc_5306_;
goto v_reusejp_5304_;
}
v_reusejp_5304_:
{
return v___x_5305_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5313_; lean_object* v___x_5315_; uint8_t v_isShared_5316_; uint8_t v_isSharedCheck_5320_; 
lean_dec_ref(v_a_5267_);
v_a_5313_ = lean_ctor_get(v___x_5273_, 0);
v_isSharedCheck_5320_ = !lean_is_exclusive(v___x_5273_);
if (v_isSharedCheck_5320_ == 0)
{
v___x_5315_ = v___x_5273_;
v_isShared_5316_ = v_isSharedCheck_5320_;
goto v_resetjp_5314_;
}
else
{
lean_inc(v_a_5313_);
lean_dec(v___x_5273_);
v___x_5315_ = lean_box(0);
v_isShared_5316_ = v_isSharedCheck_5320_;
goto v_resetjp_5314_;
}
v_resetjp_5314_:
{
lean_object* v___x_5318_; 
if (v_isShared_5316_ == 0)
{
v___x_5318_ = v___x_5315_;
goto v_reusejp_5317_;
}
else
{
lean_object* v_reuseFailAlloc_5319_; 
v_reuseFailAlloc_5319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5319_, 0, v_a_5313_);
v___x_5318_ = v_reuseFailAlloc_5319_;
goto v_reusejp_5317_;
}
v_reusejp_5317_:
{
return v___x_5318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0___boxed(lean_object* v___y_5321_, lean_object* v_mkInfoTree_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_, lean_object* v_a_5330_, lean_object* v_a_x3f_5331_, lean_object* v___y_5332_){
_start:
{
lean_object* v_res_5333_; 
v_res_5333_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5321_, v_mkInfoTree_5322_, v___y_5323_, v___y_5324_, v___y_5325_, v___y_5326_, v___y_5327_, v___y_5328_, v___y_5329_, v_a_5330_, v_a_x3f_5331_);
lean_dec(v_a_x3f_5331_);
lean_dec_ref(v___y_5329_);
lean_dec(v___y_5328_);
lean_dec_ref(v___y_5327_);
lean_dec(v___y_5326_);
lean_dec_ref(v___y_5325_);
lean_dec(v___y_5324_);
lean_dec_ref(v___y_5323_);
lean_dec(v___y_5321_);
return v_res_5333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(lean_object* v_x_5334_, lean_object* v_mkInfoTree_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_){
_start:
{
lean_object* v___x_5345_; lean_object* v_infoState_5346_; uint8_t v_enabled_5347_; 
v___x_5345_ = lean_st_ref_get(v___y_5343_);
v_infoState_5346_ = lean_ctor_get(v___x_5345_, 7);
lean_inc_ref(v_infoState_5346_);
lean_dec(v___x_5345_);
v_enabled_5347_ = lean_ctor_get_uint8(v_infoState_5346_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5346_);
if (v_enabled_5347_ == 0)
{
lean_object* v___x_5348_; 
lean_dec_ref(v_mkInfoTree_5335_);
lean_inc(v___y_5343_);
lean_inc_ref(v___y_5342_);
lean_inc(v___y_5341_);
lean_inc_ref(v___y_5340_);
lean_inc(v___y_5339_);
lean_inc_ref(v___y_5338_);
lean_inc(v___y_5337_);
lean_inc_ref(v___y_5336_);
v___x_5348_ = lean_apply_9(v_x_5334_, v___y_5336_, v___y_5337_, v___y_5338_, v___y_5339_, v___y_5340_, v___y_5341_, v___y_5342_, v___y_5343_, lean_box(0));
return v___x_5348_;
}
else
{
lean_object* v___x_5349_; lean_object* v_a_5350_; lean_object* v_r_5351_; 
v___x_5349_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3_spec__4___redArg(v___y_5343_);
v_a_5350_ = lean_ctor_get(v___x_5349_, 0);
lean_inc(v_a_5350_);
lean_dec_ref(v___x_5349_);
lean_inc(v___y_5343_);
lean_inc_ref(v___y_5342_);
lean_inc(v___y_5341_);
lean_inc_ref(v___y_5340_);
lean_inc(v___y_5339_);
lean_inc_ref(v___y_5338_);
lean_inc(v___y_5337_);
lean_inc_ref(v___y_5336_);
v_r_5351_ = lean_apply_9(v_x_5334_, v___y_5336_, v___y_5337_, v___y_5338_, v___y_5339_, v___y_5340_, v___y_5341_, v___y_5342_, v___y_5343_, lean_box(0));
if (lean_obj_tag(v_r_5351_) == 0)
{
lean_object* v_a_5352_; lean_object* v___x_5354_; uint8_t v_isShared_5355_; uint8_t v_isSharedCheck_5376_; 
v_a_5352_ = lean_ctor_get(v_r_5351_, 0);
v_isSharedCheck_5376_ = !lean_is_exclusive(v_r_5351_);
if (v_isSharedCheck_5376_ == 0)
{
v___x_5354_ = v_r_5351_;
v_isShared_5355_ = v_isSharedCheck_5376_;
goto v_resetjp_5353_;
}
else
{
lean_inc(v_a_5352_);
lean_dec(v_r_5351_);
v___x_5354_ = lean_box(0);
v_isShared_5355_ = v_isSharedCheck_5376_;
goto v_resetjp_5353_;
}
v_resetjp_5353_:
{
lean_object* v___x_5357_; 
lean_inc(v_a_5352_);
if (v_isShared_5355_ == 0)
{
lean_ctor_set_tag(v___x_5354_, 1);
v___x_5357_ = v___x_5354_;
goto v_reusejp_5356_;
}
else
{
lean_object* v_reuseFailAlloc_5375_; 
v_reuseFailAlloc_5375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5375_, 0, v_a_5352_);
v___x_5357_ = v_reuseFailAlloc_5375_;
goto v_reusejp_5356_;
}
v_reusejp_5356_:
{
lean_object* v___x_5358_; 
v___x_5358_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5343_, v_mkInfoTree_5335_, v___y_5336_, v___y_5337_, v___y_5338_, v___y_5339_, v___y_5340_, v___y_5341_, v___y_5342_, v_a_5350_, v___x_5357_);
lean_dec_ref(v___x_5357_);
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
lean_ctor_set(v___x_5360_, 0, v_a_5352_);
v___x_5363_ = v___x_5360_;
goto v_reusejp_5362_;
}
else
{
lean_object* v_reuseFailAlloc_5364_; 
v_reuseFailAlloc_5364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5364_, 0, v_a_5352_);
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
lean_dec(v_a_5352_);
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
else
{
lean_object* v_a_5377_; lean_object* v___x_5378_; lean_object* v___x_5379_; 
v_a_5377_ = lean_ctor_get(v_r_5351_, 0);
lean_inc(v_a_5377_);
lean_dec_ref_known(v_r_5351_, 1);
v___x_5378_ = lean_box(0);
v___x_5379_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___lam__0(v___y_5343_, v_mkInfoTree_5335_, v___y_5336_, v___y_5337_, v___y_5338_, v___y_5339_, v___y_5340_, v___y_5341_, v___y_5342_, v_a_5350_, v___x_5378_);
if (lean_obj_tag(v___x_5379_) == 0)
{
lean_object* v___x_5381_; uint8_t v_isShared_5382_; uint8_t v_isSharedCheck_5386_; 
v_isSharedCheck_5386_ = !lean_is_exclusive(v___x_5379_);
if (v_isSharedCheck_5386_ == 0)
{
lean_object* v_unused_5387_; 
v_unused_5387_ = lean_ctor_get(v___x_5379_, 0);
lean_dec(v_unused_5387_);
v___x_5381_ = v___x_5379_;
v_isShared_5382_ = v_isSharedCheck_5386_;
goto v_resetjp_5380_;
}
else
{
lean_dec(v___x_5379_);
v___x_5381_ = lean_box(0);
v_isShared_5382_ = v_isSharedCheck_5386_;
goto v_resetjp_5380_;
}
v_resetjp_5380_:
{
lean_object* v___x_5384_; 
if (v_isShared_5382_ == 0)
{
lean_ctor_set_tag(v___x_5381_, 1);
lean_ctor_set(v___x_5381_, 0, v_a_5377_);
v___x_5384_ = v___x_5381_;
goto v_reusejp_5383_;
}
else
{
lean_object* v_reuseFailAlloc_5385_; 
v_reuseFailAlloc_5385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5385_, 0, v_a_5377_);
v___x_5384_ = v_reuseFailAlloc_5385_;
goto v_reusejp_5383_;
}
v_reusejp_5383_:
{
return v___x_5384_;
}
}
}
else
{
lean_object* v_a_5388_; lean_object* v___x_5390_; uint8_t v_isShared_5391_; uint8_t v_isSharedCheck_5395_; 
lean_dec(v_a_5377_);
v_a_5388_ = lean_ctor_get(v___x_5379_, 0);
v_isSharedCheck_5395_ = !lean_is_exclusive(v___x_5379_);
if (v_isSharedCheck_5395_ == 0)
{
v___x_5390_ = v___x_5379_;
v_isShared_5391_ = v_isSharedCheck_5395_;
goto v_resetjp_5389_;
}
else
{
lean_inc(v_a_5388_);
lean_dec(v___x_5379_);
v___x_5390_ = lean_box(0);
v_isShared_5391_ = v_isSharedCheck_5395_;
goto v_resetjp_5389_;
}
v_resetjp_5389_:
{
lean_object* v___x_5393_; 
if (v_isShared_5391_ == 0)
{
v___x_5393_ = v___x_5390_;
goto v_reusejp_5392_;
}
else
{
lean_object* v_reuseFailAlloc_5394_; 
v_reuseFailAlloc_5394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5394_, 0, v_a_5388_);
v___x_5393_ = v_reuseFailAlloc_5394_;
goto v_reusejp_5392_;
}
v_reusejp_5392_:
{
return v___x_5393_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg___boxed(lean_object* v_x_5396_, lean_object* v_mkInfoTree_5397_, lean_object* v___y_5398_, lean_object* v___y_5399_, lean_object* v___y_5400_, lean_object* v___y_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_, lean_object* v___y_5405_, lean_object* v___y_5406_){
_start:
{
lean_object* v_res_5407_; 
v_res_5407_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v_x_5396_, v_mkInfoTree_5397_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_, v___y_5402_, v___y_5403_, v___y_5404_, v___y_5405_);
lean_dec(v___y_5405_);
lean_dec_ref(v___y_5404_);
lean_dec(v___y_5403_);
lean_dec_ref(v___y_5402_);
lean_dec(v___y_5401_);
lean_dec_ref(v___y_5400_);
lean_dec(v___y_5399_);
lean_dec_ref(v___y_5398_);
return v_res_5407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1(lean_object* v_a_5408_, lean_object* v_trees_5409_, lean_object* v___y_5410_, lean_object* v___y_5411_, lean_object* v___y_5412_, lean_object* v___y_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_, lean_object* v___y_5417_){
_start:
{
lean_object* v___x_5419_; 
lean_inc(v___y_5417_);
lean_inc_ref(v___y_5416_);
lean_inc(v___y_5415_);
lean_inc_ref(v___y_5414_);
lean_inc(v___y_5413_);
lean_inc_ref(v___y_5412_);
lean_inc(v___y_5411_);
lean_inc_ref(v___y_5410_);
v___x_5419_ = lean_apply_9(v_a_5408_, v___y_5410_, v___y_5411_, v___y_5412_, v___y_5413_, v___y_5414_, v___y_5415_, v___y_5416_, v___y_5417_, lean_box(0));
if (lean_obj_tag(v___x_5419_) == 0)
{
lean_object* v_a_5420_; lean_object* v___x_5422_; uint8_t v_isShared_5423_; uint8_t v_isSharedCheck_5428_; 
v_a_5420_ = lean_ctor_get(v___x_5419_, 0);
v_isSharedCheck_5428_ = !lean_is_exclusive(v___x_5419_);
if (v_isSharedCheck_5428_ == 0)
{
v___x_5422_ = v___x_5419_;
v_isShared_5423_ = v_isSharedCheck_5428_;
goto v_resetjp_5421_;
}
else
{
lean_inc(v_a_5420_);
lean_dec(v___x_5419_);
v___x_5422_ = lean_box(0);
v_isShared_5423_ = v_isSharedCheck_5428_;
goto v_resetjp_5421_;
}
v_resetjp_5421_:
{
lean_object* v___x_5424_; lean_object* v___x_5426_; 
v___x_5424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5424_, 0, v_a_5420_);
lean_ctor_set(v___x_5424_, 1, v_trees_5409_);
if (v_isShared_5423_ == 0)
{
lean_ctor_set(v___x_5422_, 0, v___x_5424_);
v___x_5426_ = v___x_5422_;
goto v_reusejp_5425_;
}
else
{
lean_object* v_reuseFailAlloc_5427_; 
v_reuseFailAlloc_5427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5427_, 0, v___x_5424_);
v___x_5426_ = v_reuseFailAlloc_5427_;
goto v_reusejp_5425_;
}
v_reusejp_5425_:
{
return v___x_5426_;
}
}
}
else
{
lean_object* v_a_5429_; lean_object* v___x_5431_; uint8_t v_isShared_5432_; uint8_t v_isSharedCheck_5436_; 
lean_dec_ref(v_trees_5409_);
v_a_5429_ = lean_ctor_get(v___x_5419_, 0);
v_isSharedCheck_5436_ = !lean_is_exclusive(v___x_5419_);
if (v_isSharedCheck_5436_ == 0)
{
v___x_5431_ = v___x_5419_;
v_isShared_5432_ = v_isSharedCheck_5436_;
goto v_resetjp_5430_;
}
else
{
lean_inc(v_a_5429_);
lean_dec(v___x_5419_);
v___x_5431_ = lean_box(0);
v_isShared_5432_ = v_isSharedCheck_5436_;
goto v_resetjp_5430_;
}
v_resetjp_5430_:
{
lean_object* v___x_5434_; 
if (v_isShared_5432_ == 0)
{
v___x_5434_ = v___x_5431_;
goto v_reusejp_5433_;
}
else
{
lean_object* v_reuseFailAlloc_5435_; 
v_reuseFailAlloc_5435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5435_, 0, v_a_5429_);
v___x_5434_ = v_reuseFailAlloc_5435_;
goto v_reusejp_5433_;
}
v_reusejp_5433_:
{
return v___x_5434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1___boxed(lean_object* v_a_5437_, lean_object* v_trees_5438_, lean_object* v___y_5439_, lean_object* v___y_5440_, lean_object* v___y_5441_, lean_object* v___y_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_, lean_object* v___y_5446_, lean_object* v___y_5447_){
_start:
{
lean_object* v_res_5448_; 
v_res_5448_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1(v_a_5437_, v_trees_5438_, v___y_5439_, v___y_5440_, v___y_5441_, v___y_5442_, v___y_5443_, v___y_5444_, v___y_5445_, v___y_5446_);
lean_dec(v___y_5446_);
lean_dec_ref(v___y_5445_);
lean_dec(v___y_5444_);
lean_dec_ref(v___y_5443_);
lean_dec(v___y_5442_);
lean_dec_ref(v___y_5441_);
lean_dec(v___y_5440_);
lean_dec_ref(v___y_5439_);
return v_res_5448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2(lean_object* v___x_5449_, lean_object* v_ref_5450_, lean_object* v_tactic_5451_, lean_object* v___y_5452_, lean_object* v___y_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_){
_start:
{
lean_object* v___x_5461_; 
v___x_5461_ = l_Lean_Elab_Tactic_setGoals___redArg(v___x_5449_, v___y_5453_);
if (lean_obj_tag(v___x_5461_) == 0)
{
lean_object* v___x_5462_; 
lean_dec_ref_known(v___x_5461_, 1);
v___x_5462_ = l_Lean_Elab_WF_applyCleanWfTactic(v___y_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_);
if (lean_obj_tag(v___x_5462_) == 0)
{
lean_object* v___x_5463_; 
lean_dec_ref_known(v___x_5462_, 1);
v___x_5463_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v_ref_5450_, v___y_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_);
if (lean_obj_tag(v___x_5463_) == 0)
{
lean_object* v_a_5464_; lean_object* v___f_5465_; lean_object* v___x_5466_; lean_object* v___x_5467_; 
v_a_5464_ = lean_ctor_get(v___x_5463_, 0);
lean_inc(v_a_5464_);
lean_dec_ref_known(v___x_5463_, 1);
v___f_5465_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__1___boxed), 11, 1);
lean_closure_set(v___f_5465_, 0, v_a_5464_);
v___x_5466_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_5466_, 0, v_tactic_5451_);
v___x_5467_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_WF_solveDecreasingGoals_spec__3___redArg(v___x_5466_, v___f_5465_, v___y_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_);
return v___x_5467_;
}
else
{
lean_object* v_a_5468_; lean_object* v___x_5470_; uint8_t v_isShared_5471_; uint8_t v_isSharedCheck_5475_; 
lean_dec(v_tactic_5451_);
v_a_5468_ = lean_ctor_get(v___x_5463_, 0);
v_isSharedCheck_5475_ = !lean_is_exclusive(v___x_5463_);
if (v_isSharedCheck_5475_ == 0)
{
v___x_5470_ = v___x_5463_;
v_isShared_5471_ = v_isSharedCheck_5475_;
goto v_resetjp_5469_;
}
else
{
lean_inc(v_a_5468_);
lean_dec(v___x_5463_);
v___x_5470_ = lean_box(0);
v_isShared_5471_ = v_isSharedCheck_5475_;
goto v_resetjp_5469_;
}
v_resetjp_5469_:
{
lean_object* v___x_5473_; 
if (v_isShared_5471_ == 0)
{
v___x_5473_ = v___x_5470_;
goto v_reusejp_5472_;
}
else
{
lean_object* v_reuseFailAlloc_5474_; 
v_reuseFailAlloc_5474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5474_, 0, v_a_5468_);
v___x_5473_ = v_reuseFailAlloc_5474_;
goto v_reusejp_5472_;
}
v_reusejp_5472_:
{
return v___x_5473_;
}
}
}
}
else
{
lean_dec(v_tactic_5451_);
lean_dec(v_ref_5450_);
return v___x_5462_;
}
}
else
{
lean_dec(v_tactic_5451_);
lean_dec(v_ref_5450_);
return v___x_5461_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2___boxed(lean_object* v___x_5476_, lean_object* v_ref_5477_, lean_object* v_tactic_5478_, lean_object* v___y_5479_, lean_object* v___y_5480_, lean_object* v___y_5481_, lean_object* v___y_5482_, lean_object* v___y_5483_, lean_object* v___y_5484_, lean_object* v___y_5485_, lean_object* v___y_5486_, lean_object* v___y_5487_){
_start:
{
lean_object* v_res_5488_; 
v_res_5488_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2(v___x_5476_, v_ref_5477_, v_tactic_5478_, v___y_5479_, v___y_5480_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_);
lean_dec(v___y_5486_);
lean_dec_ref(v___y_5485_);
lean_dec(v___y_5484_);
lean_dec_ref(v___y_5483_);
lean_dec(v___y_5482_);
lean_dec_ref(v___y_5481_);
lean_dec(v___y_5480_);
lean_dec_ref(v___y_5479_);
return v_res_5488_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5489_; lean_object* v___x_5490_; 
v___x_5489_ = lean_box(1);
v___x_5490_ = l_Lean_MessageData_ofFormat(v___x_5489_);
return v___x_5490_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_5494_; lean_object* v___x_5495_; 
v___x_5494_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__2));
v___x_5495_ = l_Lean_MessageData_ofFormat(v___x_5494_);
return v___x_5495_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3(lean_object* v_x_5496_, lean_object* v_x_5497_){
_start:
{
if (lean_obj_tag(v_x_5497_) == 0)
{
return v_x_5496_;
}
else
{
lean_object* v_head_5498_; lean_object* v_tail_5499_; lean_object* v___x_5501_; uint8_t v_isShared_5502_; uint8_t v_isSharedCheck_5521_; 
v_head_5498_ = lean_ctor_get(v_x_5497_, 0);
v_tail_5499_ = lean_ctor_get(v_x_5497_, 1);
v_isSharedCheck_5521_ = !lean_is_exclusive(v_x_5497_);
if (v_isSharedCheck_5521_ == 0)
{
v___x_5501_ = v_x_5497_;
v_isShared_5502_ = v_isSharedCheck_5521_;
goto v_resetjp_5500_;
}
else
{
lean_inc(v_tail_5499_);
lean_inc(v_head_5498_);
lean_dec(v_x_5497_);
v___x_5501_ = lean_box(0);
v_isShared_5502_ = v_isSharedCheck_5521_;
goto v_resetjp_5500_;
}
v_resetjp_5500_:
{
lean_object* v_before_5503_; lean_object* v___x_5505_; uint8_t v_isShared_5506_; uint8_t v_isSharedCheck_5519_; 
v_before_5503_ = lean_ctor_get(v_head_5498_, 0);
v_isSharedCheck_5519_ = !lean_is_exclusive(v_head_5498_);
if (v_isSharedCheck_5519_ == 0)
{
lean_object* v_unused_5520_; 
v_unused_5520_ = lean_ctor_get(v_head_5498_, 1);
lean_dec(v_unused_5520_);
v___x_5505_ = v_head_5498_;
v_isShared_5506_ = v_isSharedCheck_5519_;
goto v_resetjp_5504_;
}
else
{
lean_inc(v_before_5503_);
lean_dec(v_head_5498_);
v___x_5505_ = lean_box(0);
v_isShared_5506_ = v_isSharedCheck_5519_;
goto v_resetjp_5504_;
}
v_resetjp_5504_:
{
lean_object* v___x_5507_; lean_object* v___x_5509_; 
v___x_5507_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_5506_ == 0)
{
lean_ctor_set_tag(v___x_5505_, 7);
lean_ctor_set(v___x_5505_, 1, v___x_5507_);
lean_ctor_set(v___x_5505_, 0, v_x_5496_);
v___x_5509_ = v___x_5505_;
goto v_reusejp_5508_;
}
else
{
lean_object* v_reuseFailAlloc_5518_; 
v_reuseFailAlloc_5518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5518_, 0, v_x_5496_);
lean_ctor_set(v_reuseFailAlloc_5518_, 1, v___x_5507_);
v___x_5509_ = v_reuseFailAlloc_5518_;
goto v_reusejp_5508_;
}
v_reusejp_5508_:
{
lean_object* v___x_5510_; lean_object* v___x_5512_; 
v___x_5510_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__3);
if (v_isShared_5502_ == 0)
{
lean_ctor_set_tag(v___x_5501_, 7);
lean_ctor_set(v___x_5501_, 1, v___x_5510_);
lean_ctor_set(v___x_5501_, 0, v___x_5509_);
v___x_5512_ = v___x_5501_;
goto v_reusejp_5511_;
}
else
{
lean_object* v_reuseFailAlloc_5517_; 
v_reuseFailAlloc_5517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5517_, 0, v___x_5509_);
lean_ctor_set(v_reuseFailAlloc_5517_, 1, v___x_5510_);
v___x_5512_ = v_reuseFailAlloc_5517_;
goto v_reusejp_5511_;
}
v_reusejp_5511_:
{
lean_object* v___x_5513_; lean_object* v___x_5514_; lean_object* v___x_5515_; 
v___x_5513_ = l_Lean_MessageData_ofSyntax(v_before_5503_);
v___x_5514_ = l_Lean_indentD(v___x_5513_);
v___x_5515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5515_, 0, v___x_5512_);
lean_ctor_set(v___x_5515_, 1, v___x_5514_);
v_x_5496_ = v___x_5515_;
v_x_5497_ = v_tail_5499_;
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
lean_object* v___x_5525_; lean_object* v___x_5526_; 
v___x_5525_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__1));
v___x_5526_ = l_Lean_MessageData_ofFormat(v___x_5525_);
return v___x_5526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(lean_object* v_msgData_5527_, lean_object* v_macroStack_5528_, lean_object* v___y_5529_){
_start:
{
lean_object* v_options_5531_; lean_object* v___x_5532_; uint8_t v___x_5533_; 
v_options_5531_ = lean_ctor_get(v___y_5529_, 2);
v___x_5532_ = l_Lean_Elab_pp_macroStack;
v___x_5533_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_replaceRecApps_loop_spec__5(v_options_5531_, v___x_5532_);
if (v___x_5533_ == 0)
{
lean_object* v___x_5534_; 
lean_dec(v_macroStack_5528_);
v___x_5534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5534_, 0, v_msgData_5527_);
return v___x_5534_;
}
else
{
if (lean_obj_tag(v_macroStack_5528_) == 0)
{
lean_object* v___x_5535_; 
v___x_5535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5535_, 0, v_msgData_5527_);
return v___x_5535_;
}
else
{
lean_object* v_head_5536_; lean_object* v_after_5537_; lean_object* v___x_5539_; uint8_t v_isShared_5540_; uint8_t v_isSharedCheck_5552_; 
v_head_5536_ = lean_ctor_get(v_macroStack_5528_, 0);
lean_inc(v_head_5536_);
v_after_5537_ = lean_ctor_get(v_head_5536_, 1);
v_isSharedCheck_5552_ = !lean_is_exclusive(v_head_5536_);
if (v_isSharedCheck_5552_ == 0)
{
lean_object* v_unused_5553_; 
v_unused_5553_ = lean_ctor_get(v_head_5536_, 0);
lean_dec(v_unused_5553_);
v___x_5539_ = v_head_5536_;
v_isShared_5540_ = v_isSharedCheck_5552_;
goto v_resetjp_5538_;
}
else
{
lean_inc(v_after_5537_);
lean_dec(v_head_5536_);
v___x_5539_ = lean_box(0);
v_isShared_5540_ = v_isSharedCheck_5552_;
goto v_resetjp_5538_;
}
v_resetjp_5538_:
{
lean_object* v___x_5541_; lean_object* v___x_5543_; 
v___x_5541_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_5540_ == 0)
{
lean_ctor_set_tag(v___x_5539_, 7);
lean_ctor_set(v___x_5539_, 1, v___x_5541_);
lean_ctor_set(v___x_5539_, 0, v_msgData_5527_);
v___x_5543_ = v___x_5539_;
goto v_reusejp_5542_;
}
else
{
lean_object* v_reuseFailAlloc_5551_; 
v_reuseFailAlloc_5551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5551_, 0, v_msgData_5527_);
lean_ctor_set(v_reuseFailAlloc_5551_, 1, v___x_5541_);
v___x_5543_ = v_reuseFailAlloc_5551_;
goto v_reusejp_5542_;
}
v_reusejp_5542_:
{
lean_object* v___x_5544_; lean_object* v___x_5545_; lean_object* v___x_5546_; lean_object* v___x_5547_; lean_object* v_msgData_5548_; lean_object* v___x_5549_; lean_object* v___x_5550_; 
v___x_5544_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___closed__2);
v___x_5545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5545_, 0, v___x_5543_);
lean_ctor_set(v___x_5545_, 1, v___x_5544_);
v___x_5546_ = l_Lean_MessageData_ofSyntax(v_after_5537_);
v___x_5547_ = l_Lean_indentD(v___x_5546_);
v_msgData_5548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_5548_, 0, v___x_5545_);
lean_ctor_set(v_msgData_5548_, 1, v___x_5547_);
v___x_5549_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1_spec__3(v_msgData_5548_, v_macroStack_5528_);
v___x_5550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5550_, 0, v___x_5549_);
return v___x_5550_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_5554_, lean_object* v_macroStack_5555_, lean_object* v___y_5556_, lean_object* v___y_5557_){
_start:
{
lean_object* v_res_5558_; 
v_res_5558_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_msgData_5554_, v_macroStack_5555_, v___y_5556_);
lean_dec_ref(v___y_5556_);
return v_res_5558_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(lean_object* v_msg_5559_, lean_object* v___y_5560_, lean_object* v___y_5561_, lean_object* v___y_5562_, lean_object* v___y_5563_, lean_object* v___y_5564_, lean_object* v___y_5565_){
_start:
{
lean_object* v_ref_5567_; lean_object* v___x_5568_; lean_object* v_a_5569_; lean_object* v_macroStack_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; lean_object* v_a_5573_; lean_object* v___x_5575_; uint8_t v_isShared_5576_; uint8_t v_isSharedCheck_5581_; 
v_ref_5567_ = lean_ctor_get(v___y_5564_, 5);
v___x_5568_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_getLCtxId_spec__1_spec__1(v_msg_5559_, v___y_5562_, v___y_5563_, v___y_5564_, v___y_5565_);
v_a_5569_ = lean_ctor_get(v___x_5568_, 0);
lean_inc(v_a_5569_);
lean_dec_ref(v___x_5568_);
v_macroStack_5570_ = lean_ctor_get(v___y_5560_, 1);
v___x_5571_ = l_Lean_Elab_getBetterRef(v_ref_5567_, v_macroStack_5570_);
lean_inc(v_macroStack_5570_);
v___x_5572_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1_spec__1___redArg(v_a_5569_, v_macroStack_5570_, v___y_5564_);
v_a_5573_ = lean_ctor_get(v___x_5572_, 0);
v_isSharedCheck_5581_ = !lean_is_exclusive(v___x_5572_);
if (v_isSharedCheck_5581_ == 0)
{
v___x_5575_ = v___x_5572_;
v_isShared_5576_ = v_isSharedCheck_5581_;
goto v_resetjp_5574_;
}
else
{
lean_inc(v_a_5573_);
lean_dec(v___x_5572_);
v___x_5575_ = lean_box(0);
v_isShared_5576_ = v_isSharedCheck_5581_;
goto v_resetjp_5574_;
}
v_resetjp_5574_:
{
lean_object* v___x_5577_; lean_object* v___x_5579_; 
v___x_5577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5577_, 0, v___x_5571_);
lean_ctor_set(v___x_5577_, 1, v_a_5573_);
if (v_isShared_5576_ == 0)
{
lean_ctor_set_tag(v___x_5575_, 1);
lean_ctor_set(v___x_5575_, 0, v___x_5577_);
v___x_5579_ = v___x_5575_;
goto v_reusejp_5578_;
}
else
{
lean_object* v_reuseFailAlloc_5580_; 
v_reuseFailAlloc_5580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5580_, 0, v___x_5577_);
v___x_5579_ = v_reuseFailAlloc_5580_;
goto v_reusejp_5578_;
}
v_reusejp_5578_:
{
return v___x_5579_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg___boxed(lean_object* v_msg_5582_, lean_object* v___y_5583_, lean_object* v___y_5584_, lean_object* v___y_5585_, lean_object* v___y_5586_, lean_object* v___y_5587_, lean_object* v___y_5588_, lean_object* v___y_5589_){
_start:
{
lean_object* v_res_5590_; 
v_res_5590_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v_msg_5582_, v___y_5583_, v___y_5584_, v___y_5585_, v___y_5586_, v___y_5587_, v___y_5588_);
lean_dec(v___y_5588_);
lean_dec_ref(v___y_5587_);
lean_dec(v___y_5586_);
lean_dec_ref(v___y_5585_);
lean_dec(v___y_5584_);
lean_dec_ref(v___y_5583_);
return v_res_5590_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1(void){
_start:
{
lean_object* v___x_5592_; lean_object* v___x_5593_; 
v___x_5592_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__0));
v___x_5593_ = l_Lean_stringToMessageData(v___x_5592_);
return v___x_5593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(lean_object* v_as_5594_, size_t v_sz_5595_, size_t v_i_5596_, lean_object* v_b_5597_, lean_object* v___y_5598_, lean_object* v___y_5599_, lean_object* v___y_5600_, lean_object* v___y_5601_, lean_object* v___y_5602_, lean_object* v___y_5603_){
_start:
{
lean_object* v_a_5606_; uint8_t v___x_5610_; 
v___x_5610_ = lean_usize_dec_lt(v_i_5596_, v_sz_5595_);
if (v___x_5610_ == 0)
{
lean_object* v___x_5611_; 
v___x_5611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5611_, 0, v_b_5597_);
return v___x_5611_;
}
else
{
lean_object* v_a_5612_; lean_object* v___x_5613_; 
v_a_5612_ = lean_array_uget_borrowed(v_as_5594_, v_i_5596_);
lean_inc(v_a_5612_);
v___x_5613_ = l_Lean_MVarId_getType(v_a_5612_, v___y_5600_, v___y_5601_, v___y_5602_, v___y_5603_);
if (lean_obj_tag(v___x_5613_) == 0)
{
lean_object* v_a_5614_; lean_object* v___x_5615_; 
v_a_5614_ = lean_ctor_get(v___x_5613_, 0);
lean_inc(v_a_5614_);
lean_dec_ref_known(v___x_5613_, 1);
lean_inc(v_a_5612_);
v___x_5615_ = l_Lean_MVarId_getType(v_a_5612_, v___y_5600_, v___y_5601_, v___y_5602_, v___y_5603_);
if (lean_obj_tag(v___x_5615_) == 0)
{
lean_object* v_a_5616_; lean_object* v___x_5617_; lean_object* v___x_5618_; 
v_a_5616_ = lean_ctor_get(v___x_5615_, 0);
lean_inc(v_a_5616_);
lean_dec_ref_known(v___x_5615_, 1);
v___x_5617_ = lean_box(0);
v___x_5618_ = l_Lean_getRecAppSyntax_x3f(v_a_5616_);
lean_dec(v_a_5616_);
if (lean_obj_tag(v___x_5618_) == 1)
{
lean_object* v_val_5619_; lean_object* v___x_5620_; lean_object* v___x_5621_; 
v_val_5619_ = lean_ctor_get(v___x_5618_, 0);
lean_inc(v_val_5619_);
lean_dec_ref_known(v___x_5618_, 1);
v___x_5620_ = l_Lean_Expr_mdataExpr_x21(v_a_5614_);
lean_dec(v_a_5614_);
lean_inc(v_a_5612_);
v___x_5621_ = l_Lean_MVarId_setType___redArg(v_a_5612_, v___x_5620_, v___y_5601_);
if (lean_obj_tag(v___x_5621_) == 0)
{
lean_object* v_fileName_5622_; lean_object* v_fileMap_5623_; lean_object* v_options_5624_; lean_object* v_currRecDepth_5625_; lean_object* v_maxRecDepth_5626_; lean_object* v_ref_5627_; lean_object* v_currNamespace_5628_; lean_object* v_openDecls_5629_; lean_object* v_initHeartbeats_5630_; lean_object* v_maxHeartbeats_5631_; lean_object* v_quotContext_5632_; lean_object* v_currMacroScope_5633_; uint8_t v_diag_5634_; lean_object* v_cancelTk_x3f_5635_; uint8_t v_suppressElabErrors_5636_; lean_object* v_inheritedTraceOptions_5637_; lean_object* v_ref_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; 
lean_dec_ref_known(v___x_5621_, 1);
v_fileName_5622_ = lean_ctor_get(v___y_5602_, 0);
v_fileMap_5623_ = lean_ctor_get(v___y_5602_, 1);
v_options_5624_ = lean_ctor_get(v___y_5602_, 2);
v_currRecDepth_5625_ = lean_ctor_get(v___y_5602_, 3);
v_maxRecDepth_5626_ = lean_ctor_get(v___y_5602_, 4);
v_ref_5627_ = lean_ctor_get(v___y_5602_, 5);
v_currNamespace_5628_ = lean_ctor_get(v___y_5602_, 6);
v_openDecls_5629_ = lean_ctor_get(v___y_5602_, 7);
v_initHeartbeats_5630_ = lean_ctor_get(v___y_5602_, 8);
v_maxHeartbeats_5631_ = lean_ctor_get(v___y_5602_, 9);
v_quotContext_5632_ = lean_ctor_get(v___y_5602_, 10);
v_currMacroScope_5633_ = lean_ctor_get(v___y_5602_, 11);
v_diag_5634_ = lean_ctor_get_uint8(v___y_5602_, sizeof(void*)*14);
v_cancelTk_x3f_5635_ = lean_ctor_get(v___y_5602_, 12);
v_suppressElabErrors_5636_ = lean_ctor_get_uint8(v___y_5602_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5637_ = lean_ctor_get(v___y_5602_, 13);
v_ref_5638_ = l_Lean_replaceRef(v_val_5619_, v_ref_5627_);
lean_dec(v_val_5619_);
lean_inc_ref(v_inheritedTraceOptions_5637_);
lean_inc(v_cancelTk_x3f_5635_);
lean_inc(v_currMacroScope_5633_);
lean_inc(v_quotContext_5632_);
lean_inc(v_maxHeartbeats_5631_);
lean_inc(v_initHeartbeats_5630_);
lean_inc(v_openDecls_5629_);
lean_inc(v_currNamespace_5628_);
lean_inc(v_maxRecDepth_5626_);
lean_inc(v_currRecDepth_5625_);
lean_inc_ref(v_options_5624_);
lean_inc_ref(v_fileMap_5623_);
lean_inc_ref(v_fileName_5622_);
v___x_5639_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5639_, 0, v_fileName_5622_);
lean_ctor_set(v___x_5639_, 1, v_fileMap_5623_);
lean_ctor_set(v___x_5639_, 2, v_options_5624_);
lean_ctor_set(v___x_5639_, 3, v_currRecDepth_5625_);
lean_ctor_set(v___x_5639_, 4, v_maxRecDepth_5626_);
lean_ctor_set(v___x_5639_, 5, v_ref_5638_);
lean_ctor_set(v___x_5639_, 6, v_currNamespace_5628_);
lean_ctor_set(v___x_5639_, 7, v_openDecls_5629_);
lean_ctor_set(v___x_5639_, 8, v_initHeartbeats_5630_);
lean_ctor_set(v___x_5639_, 9, v_maxHeartbeats_5631_);
lean_ctor_set(v___x_5639_, 10, v_quotContext_5632_);
lean_ctor_set(v___x_5639_, 11, v_currMacroScope_5633_);
lean_ctor_set(v___x_5639_, 12, v_cancelTk_x3f_5635_);
lean_ctor_set(v___x_5639_, 13, v_inheritedTraceOptions_5637_);
lean_ctor_set_uint8(v___x_5639_, sizeof(void*)*14, v_diag_5634_);
lean_ctor_set_uint8(v___x_5639_, sizeof(void*)*14 + 1, v_suppressElabErrors_5636_);
lean_inc(v_a_5612_);
v___x_5640_ = l___private_Lean_Elab_PreDefinition_WF_Fix_0__Lean_Elab_WF_applyDefaultDecrTactic(v_a_5612_, v___y_5598_, v___y_5599_, v___y_5600_, v___y_5601_, v___x_5639_, v___y_5603_);
lean_dec_ref_known(v___x_5639_, 14);
if (lean_obj_tag(v___x_5640_) == 0)
{
lean_dec_ref_known(v___x_5640_, 1);
v_a_5606_ = v___x_5617_;
goto v___jp_5605_;
}
else
{
return v___x_5640_;
}
}
else
{
lean_dec(v_val_5619_);
return v___x_5621_;
}
}
else
{
lean_object* v___x_5641_; lean_object* v___x_5642_; lean_object* v___x_5643_; lean_object* v___x_5644_; 
lean_dec(v___x_5618_);
v___x_5641_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___closed__1);
v___x_5642_ = l_Lean_indentExpr(v_a_5614_);
v___x_5643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5643_, 0, v___x_5641_);
lean_ctor_set(v___x_5643_, 1, v___x_5642_);
v___x_5644_ = l_Lean_throwError___at___00Lean_Elab_WF_solveDecreasingGoals_spec__1___redArg(v___x_5643_, v___y_5598_, v___y_5599_, v___y_5600_, v___y_5601_, v___y_5602_, v___y_5603_);
if (lean_obj_tag(v___x_5644_) == 0)
{
lean_dec_ref_known(v___x_5644_, 1);
v_a_5606_ = v___x_5617_;
goto v___jp_5605_;
}
else
{
return v___x_5644_;
}
}
}
else
{
lean_object* v_a_5645_; lean_object* v___x_5647_; uint8_t v_isShared_5648_; uint8_t v_isSharedCheck_5652_; 
lean_dec(v_a_5614_);
v_a_5645_ = lean_ctor_get(v___x_5615_, 0);
v_isSharedCheck_5652_ = !lean_is_exclusive(v___x_5615_);
if (v_isSharedCheck_5652_ == 0)
{
v___x_5647_ = v___x_5615_;
v_isShared_5648_ = v_isSharedCheck_5652_;
goto v_resetjp_5646_;
}
else
{
lean_inc(v_a_5645_);
lean_dec(v___x_5615_);
v___x_5647_ = lean_box(0);
v_isShared_5648_ = v_isSharedCheck_5652_;
goto v_resetjp_5646_;
}
v_resetjp_5646_:
{
lean_object* v___x_5650_; 
if (v_isShared_5648_ == 0)
{
v___x_5650_ = v___x_5647_;
goto v_reusejp_5649_;
}
else
{
lean_object* v_reuseFailAlloc_5651_; 
v_reuseFailAlloc_5651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5651_, 0, v_a_5645_);
v___x_5650_ = v_reuseFailAlloc_5651_;
goto v_reusejp_5649_;
}
v_reusejp_5649_:
{
return v___x_5650_;
}
}
}
}
else
{
lean_object* v_a_5653_; lean_object* v___x_5655_; uint8_t v_isShared_5656_; uint8_t v_isSharedCheck_5660_; 
v_a_5653_ = lean_ctor_get(v___x_5613_, 0);
v_isSharedCheck_5660_ = !lean_is_exclusive(v___x_5613_);
if (v_isSharedCheck_5660_ == 0)
{
v___x_5655_ = v___x_5613_;
v_isShared_5656_ = v_isSharedCheck_5660_;
goto v_resetjp_5654_;
}
else
{
lean_inc(v_a_5653_);
lean_dec(v___x_5613_);
v___x_5655_ = lean_box(0);
v_isShared_5656_ = v_isSharedCheck_5660_;
goto v_resetjp_5654_;
}
v_resetjp_5654_:
{
lean_object* v___x_5658_; 
if (v_isShared_5656_ == 0)
{
v___x_5658_ = v___x_5655_;
goto v_reusejp_5657_;
}
else
{
lean_object* v_reuseFailAlloc_5659_; 
v_reuseFailAlloc_5659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5659_, 0, v_a_5653_);
v___x_5658_ = v_reuseFailAlloc_5659_;
goto v_reusejp_5657_;
}
v_reusejp_5657_:
{
return v___x_5658_;
}
}
}
}
v___jp_5605_:
{
size_t v___x_5607_; size_t v___x_5608_; 
v___x_5607_ = ((size_t)1ULL);
v___x_5608_ = lean_usize_add(v_i_5596_, v___x_5607_);
v_i_5596_ = v___x_5608_;
v_b_5597_ = v_a_5606_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2___boxed(lean_object* v_as_5661_, lean_object* v_sz_5662_, lean_object* v_i_5663_, lean_object* v_b_5664_, lean_object* v___y_5665_, lean_object* v___y_5666_, lean_object* v___y_5667_, lean_object* v___y_5668_, lean_object* v___y_5669_, lean_object* v___y_5670_, lean_object* v___y_5671_){
_start:
{
size_t v_sz_boxed_5672_; size_t v_i_boxed_5673_; lean_object* v_res_5674_; 
v_sz_boxed_5672_ = lean_unbox_usize(v_sz_5662_);
lean_dec(v_sz_5662_);
v_i_boxed_5673_ = lean_unbox_usize(v_i_5663_);
lean_dec(v_i_5663_);
v_res_5674_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(v_as_5661_, v_sz_boxed_5672_, v_i_boxed_5673_, v_b_5664_, v___y_5665_, v___y_5666_, v___y_5667_, v___y_5668_, v___y_5669_, v___y_5670_);
lean_dec(v___y_5670_);
lean_dec_ref(v___y_5669_);
lean_dec(v___y_5668_);
lean_dec_ref(v___y_5667_);
lean_dec(v___y_5666_);
lean_dec_ref(v___y_5665_);
lean_dec_ref(v_as_5661_);
return v_res_5674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(lean_object* v_as_5675_, size_t v_i_5676_, size_t v_stop_5677_, lean_object* v_b_5678_, lean_object* v___y_5679_, lean_object* v___y_5680_, lean_object* v___y_5681_, lean_object* v___y_5682_){
_start:
{
uint8_t v___x_5684_; 
v___x_5684_ = lean_usize_dec_eq(v_i_5676_, v_stop_5677_);
if (v___x_5684_ == 0)
{
lean_object* v___x_5685_; lean_object* v___x_5686_; 
v___x_5685_ = lean_array_uget_borrowed(v_as_5675_, v_i_5676_);
lean_inc(v___x_5685_);
v___x_5686_ = l_Lean_MVarId_getType(v___x_5685_, v___y_5679_, v___y_5680_, v___y_5681_, v___y_5682_);
if (lean_obj_tag(v___x_5686_) == 0)
{
lean_object* v_a_5687_; lean_object* v___x_5688_; lean_object* v___x_5689_; 
v_a_5687_ = lean_ctor_get(v___x_5686_, 0);
lean_inc(v_a_5687_);
lean_dec_ref_known(v___x_5686_, 1);
v___x_5688_ = l_Lean_Expr_mdataExpr_x21(v_a_5687_);
lean_dec(v_a_5687_);
lean_inc(v___x_5685_);
v___x_5689_ = l_Lean_MVarId_setType___redArg(v___x_5685_, v___x_5688_, v___y_5680_);
if (lean_obj_tag(v___x_5689_) == 0)
{
lean_object* v_a_5690_; size_t v___x_5691_; size_t v___x_5692_; 
v_a_5690_ = lean_ctor_get(v___x_5689_, 0);
lean_inc(v_a_5690_);
lean_dec_ref_known(v___x_5689_, 1);
v___x_5691_ = ((size_t)1ULL);
v___x_5692_ = lean_usize_add(v_i_5676_, v___x_5691_);
v_i_5676_ = v___x_5692_;
v_b_5678_ = v_a_5690_;
goto _start;
}
else
{
return v___x_5689_;
}
}
else
{
lean_object* v_a_5694_; lean_object* v___x_5696_; uint8_t v_isShared_5697_; uint8_t v_isSharedCheck_5701_; 
v_a_5694_ = lean_ctor_get(v___x_5686_, 0);
v_isSharedCheck_5701_ = !lean_is_exclusive(v___x_5686_);
if (v_isSharedCheck_5701_ == 0)
{
v___x_5696_ = v___x_5686_;
v_isShared_5697_ = v_isSharedCheck_5701_;
goto v_resetjp_5695_;
}
else
{
lean_inc(v_a_5694_);
lean_dec(v___x_5686_);
v___x_5696_ = lean_box(0);
v_isShared_5697_ = v_isSharedCheck_5701_;
goto v_resetjp_5695_;
}
v_resetjp_5695_:
{
lean_object* v___x_5699_; 
if (v_isShared_5697_ == 0)
{
v___x_5699_ = v___x_5696_;
goto v_reusejp_5698_;
}
else
{
lean_object* v_reuseFailAlloc_5700_; 
v_reuseFailAlloc_5700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5700_, 0, v_a_5694_);
v___x_5699_ = v_reuseFailAlloc_5700_;
goto v_reusejp_5698_;
}
v_reusejp_5698_:
{
return v___x_5699_;
}
}
}
}
else
{
lean_object* v___x_5702_; 
v___x_5702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5702_, 0, v_b_5678_);
return v___x_5702_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg___boxed(lean_object* v_as_5703_, lean_object* v_i_5704_, lean_object* v_stop_5705_, lean_object* v_b_5706_, lean_object* v___y_5707_, lean_object* v___y_5708_, lean_object* v___y_5709_, lean_object* v___y_5710_, lean_object* v___y_5711_){
_start:
{
size_t v_i_boxed_5712_; size_t v_stop_boxed_5713_; lean_object* v_res_5714_; 
v_i_boxed_5712_ = lean_unbox_usize(v_i_5704_);
lean_dec(v_i_5704_);
v_stop_boxed_5713_ = lean_unbox_usize(v_stop_5705_);
lean_dec(v_stop_5705_);
v_res_5714_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v_as_5703_, v_i_boxed_5712_, v_stop_boxed_5713_, v_b_5706_, v___y_5707_, v___y_5708_, v___y_5709_, v___y_5710_);
lean_dec(v___y_5710_);
lean_dec_ref(v___y_5709_);
lean_dec(v___y_5708_);
lean_dec_ref(v___y_5707_);
lean_dec_ref(v_as_5703_);
return v_res_5714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3(lean_object* v___x_5715_, lean_object* v___x_5716_, lean_object* v___y_5717_, lean_object* v___y_5718_, lean_object* v___y_5719_, lean_object* v___y_5720_, lean_object* v___y_5721_, lean_object* v___y_5722_){
_start:
{
if (lean_obj_tag(v___x_5715_) == 0)
{
lean_object* v___x_5724_; size_t v_sz_5725_; size_t v___x_5726_; lean_object* v___x_5727_; 
v___x_5724_ = lean_box(0);
v_sz_5725_ = lean_array_size(v___x_5716_);
v___x_5726_ = ((size_t)0ULL);
v___x_5727_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__2(v___x_5716_, v_sz_5725_, v___x_5726_, v___x_5724_, v___y_5717_, v___y_5718_, v___y_5719_, v___y_5720_, v___y_5721_, v___y_5722_);
lean_dec_ref(v___x_5716_);
if (lean_obj_tag(v___x_5727_) == 0)
{
lean_object* v___x_5729_; uint8_t v_isShared_5730_; uint8_t v_isSharedCheck_5734_; 
v_isSharedCheck_5734_ = !lean_is_exclusive(v___x_5727_);
if (v_isSharedCheck_5734_ == 0)
{
lean_object* v_unused_5735_; 
v_unused_5735_ = lean_ctor_get(v___x_5727_, 0);
lean_dec(v_unused_5735_);
v___x_5729_ = v___x_5727_;
v_isShared_5730_ = v_isSharedCheck_5734_;
goto v_resetjp_5728_;
}
else
{
lean_dec(v___x_5727_);
v___x_5729_ = lean_box(0);
v_isShared_5730_ = v_isSharedCheck_5734_;
goto v_resetjp_5728_;
}
v_resetjp_5728_:
{
lean_object* v___x_5732_; 
if (v_isShared_5730_ == 0)
{
lean_ctor_set(v___x_5729_, 0, v___x_5724_);
v___x_5732_ = v___x_5729_;
goto v_reusejp_5731_;
}
else
{
lean_object* v_reuseFailAlloc_5733_; 
v_reuseFailAlloc_5733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5733_, 0, v___x_5724_);
v___x_5732_ = v_reuseFailAlloc_5733_;
goto v_reusejp_5731_;
}
v_reusejp_5731_:
{
return v___x_5732_;
}
}
}
else
{
return v___x_5727_;
}
}
else
{
lean_object* v_val_5736_; lean_object* v___x_5738_; uint8_t v_isShared_5739_; uint8_t v_isSharedCheck_5815_; 
v_val_5736_ = lean_ctor_get(v___x_5715_, 0);
v_isSharedCheck_5815_ = !lean_is_exclusive(v___x_5715_);
if (v_isSharedCheck_5815_ == 0)
{
v___x_5738_ = v___x_5715_;
v_isShared_5739_ = v_isSharedCheck_5815_;
goto v_resetjp_5737_;
}
else
{
lean_inc(v_val_5736_);
lean_dec(v___x_5715_);
v___x_5738_ = lean_box(0);
v_isShared_5739_ = v_isSharedCheck_5815_;
goto v_resetjp_5737_;
}
v_resetjp_5737_:
{
lean_object* v_ref_5740_; lean_object* v_tactic_5741_; lean_object* v_fileName_5742_; lean_object* v_fileMap_5743_; lean_object* v_options_5744_; lean_object* v_currRecDepth_5745_; lean_object* v_maxRecDepth_5746_; lean_object* v_ref_5747_; lean_object* v_currNamespace_5748_; lean_object* v_openDecls_5749_; lean_object* v_initHeartbeats_5750_; lean_object* v_maxHeartbeats_5751_; lean_object* v_quotContext_5752_; lean_object* v_currMacroScope_5753_; uint8_t v_diag_5754_; lean_object* v_cancelTk_x3f_5755_; uint8_t v_suppressElabErrors_5756_; lean_object* v_inheritedTraceOptions_5757_; lean_object* v___x_5758_; lean_object* v___x_5759_; lean_object* v_ref_5760_; lean_object* v___x_5761_; lean_object* v___y_5788_; lean_object* v___y_5805_; uint8_t v___x_5806_; 
v_ref_5740_ = lean_ctor_get(v_val_5736_, 0);
lean_inc(v_ref_5740_);
v_tactic_5741_ = lean_ctor_get(v_val_5736_, 1);
lean_inc(v_tactic_5741_);
lean_dec(v_val_5736_);
v_fileName_5742_ = lean_ctor_get(v___y_5721_, 0);
v_fileMap_5743_ = lean_ctor_get(v___y_5721_, 1);
v_options_5744_ = lean_ctor_get(v___y_5721_, 2);
v_currRecDepth_5745_ = lean_ctor_get(v___y_5721_, 3);
v_maxRecDepth_5746_ = lean_ctor_get(v___y_5721_, 4);
v_ref_5747_ = lean_ctor_get(v___y_5721_, 5);
v_currNamespace_5748_ = lean_ctor_get(v___y_5721_, 6);
v_openDecls_5749_ = lean_ctor_get(v___y_5721_, 7);
v_initHeartbeats_5750_ = lean_ctor_get(v___y_5721_, 8);
v_maxHeartbeats_5751_ = lean_ctor_get(v___y_5721_, 9);
v_quotContext_5752_ = lean_ctor_get(v___y_5721_, 10);
v_currMacroScope_5753_ = lean_ctor_get(v___y_5721_, 11);
v_diag_5754_ = lean_ctor_get_uint8(v___y_5721_, sizeof(void*)*14);
v_cancelTk_x3f_5755_ = lean_ctor_get(v___y_5721_, 12);
v_suppressElabErrors_5756_ = lean_ctor_get_uint8(v___y_5721_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5757_ = lean_ctor_get(v___y_5721_, 13);
v___x_5758_ = lean_unsigned_to_nat(0u);
v___x_5759_ = lean_array_get_size(v___x_5716_);
v_ref_5760_ = l_Lean_replaceRef(v_ref_5740_, v_ref_5747_);
lean_inc_ref(v_inheritedTraceOptions_5757_);
lean_inc(v_cancelTk_x3f_5755_);
lean_inc(v_currMacroScope_5753_);
lean_inc(v_quotContext_5752_);
lean_inc(v_maxHeartbeats_5751_);
lean_inc(v_initHeartbeats_5750_);
lean_inc(v_openDecls_5749_);
lean_inc(v_currNamespace_5748_);
lean_inc(v_maxRecDepth_5746_);
lean_inc(v_currRecDepth_5745_);
lean_inc_ref(v_options_5744_);
lean_inc_ref(v_fileMap_5743_);
lean_inc_ref(v_fileName_5742_);
v___x_5761_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5761_, 0, v_fileName_5742_);
lean_ctor_set(v___x_5761_, 1, v_fileMap_5743_);
lean_ctor_set(v___x_5761_, 2, v_options_5744_);
lean_ctor_set(v___x_5761_, 3, v_currRecDepth_5745_);
lean_ctor_set(v___x_5761_, 4, v_maxRecDepth_5746_);
lean_ctor_set(v___x_5761_, 5, v_ref_5760_);
lean_ctor_set(v___x_5761_, 6, v_currNamespace_5748_);
lean_ctor_set(v___x_5761_, 7, v_openDecls_5749_);
lean_ctor_set(v___x_5761_, 8, v_initHeartbeats_5750_);
lean_ctor_set(v___x_5761_, 9, v_maxHeartbeats_5751_);
lean_ctor_set(v___x_5761_, 10, v_quotContext_5752_);
lean_ctor_set(v___x_5761_, 11, v_currMacroScope_5753_);
lean_ctor_set(v___x_5761_, 12, v_cancelTk_x3f_5755_);
lean_ctor_set(v___x_5761_, 13, v_inheritedTraceOptions_5757_);
lean_ctor_set_uint8(v___x_5761_, sizeof(void*)*14, v_diag_5754_);
lean_ctor_set_uint8(v___x_5761_, sizeof(void*)*14 + 1, v_suppressElabErrors_5756_);
v___x_5806_ = lean_nat_dec_lt(v___x_5758_, v___x_5759_);
if (v___x_5806_ == 0)
{
goto v___jp_5789_;
}
else
{
lean_object* v___x_5807_; uint8_t v___x_5808_; 
v___x_5807_ = lean_box(0);
v___x_5808_ = lean_nat_dec_le(v___x_5759_, v___x_5759_);
if (v___x_5808_ == 0)
{
if (v___x_5806_ == 0)
{
goto v___jp_5789_;
}
else
{
size_t v___x_5809_; size_t v___x_5810_; lean_object* v___x_5811_; 
v___x_5809_ = ((size_t)0ULL);
v___x_5810_ = lean_usize_of_nat(v___x_5759_);
v___x_5811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v___x_5716_, v___x_5809_, v___x_5810_, v___x_5807_, v___y_5719_, v___y_5720_, v___x_5761_, v___y_5722_);
v___y_5805_ = v___x_5811_;
goto v___jp_5804_;
}
}
else
{
size_t v___x_5812_; size_t v___x_5813_; lean_object* v___x_5814_; 
v___x_5812_ = ((size_t)0ULL);
v___x_5813_ = lean_usize_of_nat(v___x_5759_);
v___x_5814_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__5___redArg(v___x_5716_, v___x_5812_, v___x_5813_, v___x_5807_, v___y_5719_, v___y_5720_, v___x_5761_, v___y_5722_);
v___y_5805_ = v___x_5814_;
goto v___jp_5804_;
}
}
v___jp_5762_:
{
lean_object* v___x_5763_; lean_object* v___x_5764_; lean_object* v___x_5765_; lean_object* v___f_5766_; lean_object* v___x_5767_; 
v___x_5763_ = lean_box(0);
v___x_5764_ = lean_array_get(v___x_5763_, v___x_5716_, v___x_5758_);
v___x_5765_ = lean_array_to_list(v___x_5716_);
v___f_5766_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__2___boxed), 12, 3);
lean_closure_set(v___f_5766_, 0, v___x_5765_);
lean_closure_set(v___f_5766_, 1, v_ref_5740_);
lean_closure_set(v___f_5766_, 2, v_tactic_5741_);
v___x_5767_ = l_Lean_Elab_Tactic_run(v___x_5764_, v___f_5766_, v___y_5717_, v___y_5718_, v___y_5719_, v___y_5720_, v___x_5761_, v___y_5722_);
if (lean_obj_tag(v___x_5767_) == 0)
{
lean_object* v_a_5768_; lean_object* v___x_5770_; uint8_t v_isShared_5771_; uint8_t v_isSharedCheck_5778_; 
v_a_5768_ = lean_ctor_get(v___x_5767_, 0);
v_isSharedCheck_5778_ = !lean_is_exclusive(v___x_5767_);
if (v_isSharedCheck_5778_ == 0)
{
v___x_5770_ = v___x_5767_;
v_isShared_5771_ = v_isSharedCheck_5778_;
goto v_resetjp_5769_;
}
else
{
lean_inc(v_a_5768_);
lean_dec(v___x_5767_);
v___x_5770_ = lean_box(0);
v_isShared_5771_ = v_isSharedCheck_5778_;
goto v_resetjp_5769_;
}
v_resetjp_5769_:
{
uint8_t v___x_5772_; 
v___x_5772_ = l_List_isEmpty___redArg(v_a_5768_);
if (v___x_5772_ == 0)
{
lean_object* v___x_5773_; 
lean_del_object(v___x_5770_);
v___x_5773_ = l_Lean_Elab_Term_reportUnsolvedGoals(v_a_5768_, v___y_5719_, v___y_5720_, v___x_5761_, v___y_5722_);
lean_dec_ref_known(v___x_5761_, 14);
return v___x_5773_;
}
else
{
lean_object* v___x_5774_; lean_object* v___x_5776_; 
lean_dec(v_a_5768_);
lean_dec_ref_known(v___x_5761_, 14);
v___x_5774_ = lean_box(0);
if (v_isShared_5771_ == 0)
{
lean_ctor_set(v___x_5770_, 0, v___x_5774_);
v___x_5776_ = v___x_5770_;
goto v_reusejp_5775_;
}
else
{
lean_object* v_reuseFailAlloc_5777_; 
v_reuseFailAlloc_5777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5777_, 0, v___x_5774_);
v___x_5776_ = v_reuseFailAlloc_5777_;
goto v_reusejp_5775_;
}
v_reusejp_5775_:
{
return v___x_5776_;
}
}
}
}
else
{
lean_object* v_a_5779_; lean_object* v___x_5781_; uint8_t v_isShared_5782_; uint8_t v_isSharedCheck_5786_; 
lean_dec_ref_known(v___x_5761_, 14);
v_a_5779_ = lean_ctor_get(v___x_5767_, 0);
v_isSharedCheck_5786_ = !lean_is_exclusive(v___x_5767_);
if (v_isSharedCheck_5786_ == 0)
{
v___x_5781_ = v___x_5767_;
v_isShared_5782_ = v_isSharedCheck_5786_;
goto v_resetjp_5780_;
}
else
{
lean_inc(v_a_5779_);
lean_dec(v___x_5767_);
v___x_5781_ = lean_box(0);
v_isShared_5782_ = v_isSharedCheck_5786_;
goto v_resetjp_5780_;
}
v_resetjp_5780_:
{
lean_object* v___x_5784_; 
if (v_isShared_5782_ == 0)
{
v___x_5784_ = v___x_5781_;
goto v_reusejp_5783_;
}
else
{
lean_object* v_reuseFailAlloc_5785_; 
v_reuseFailAlloc_5785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5785_, 0, v_a_5779_);
v___x_5784_ = v_reuseFailAlloc_5785_;
goto v_reusejp_5783_;
}
v_reusejp_5783_:
{
return v___x_5784_;
}
}
}
}
v___jp_5787_:
{
if (lean_obj_tag(v___y_5788_) == 0)
{
lean_dec_ref_known(v___y_5788_, 1);
goto v___jp_5762_;
}
else
{
lean_dec_ref_known(v___x_5761_, 14);
lean_dec(v_tactic_5741_);
lean_dec(v_ref_5740_);
lean_dec_ref(v___x_5716_);
return v___y_5788_;
}
}
v___jp_5789_:
{
uint8_t v___x_5790_; 
v___x_5790_ = lean_nat_dec_eq(v___x_5759_, v___x_5758_);
if (v___x_5790_ == 0)
{
uint8_t v___x_5791_; 
lean_del_object(v___x_5738_);
v___x_5791_ = lean_nat_dec_lt(v___x_5758_, v___x_5759_);
if (v___x_5791_ == 0)
{
goto v___jp_5762_;
}
else
{
lean_object* v___x_5792_; uint8_t v___x_5793_; 
v___x_5792_ = lean_box(0);
v___x_5793_ = lean_nat_dec_le(v___x_5759_, v___x_5759_);
if (v___x_5793_ == 0)
{
if (v___x_5791_ == 0)
{
goto v___jp_5762_;
}
else
{
size_t v___x_5794_; size_t v___x_5795_; lean_object* v___x_5796_; 
v___x_5794_ = ((size_t)0ULL);
v___x_5795_ = lean_usize_of_nat(v___x_5759_);
v___x_5796_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v___x_5716_, v___x_5794_, v___x_5795_, v___x_5792_, v___y_5717_, v___y_5718_, v___y_5719_, v___y_5720_, v___x_5761_, v___y_5722_);
v___y_5788_ = v___x_5796_;
goto v___jp_5787_;
}
}
else
{
size_t v___x_5797_; size_t v___x_5798_; lean_object* v___x_5799_; 
v___x_5797_ = ((size_t)0ULL);
v___x_5798_ = lean_usize_of_nat(v___x_5759_);
v___x_5799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_WF_solveDecreasingGoals_spec__4(v___x_5716_, v___x_5797_, v___x_5798_, v___x_5792_, v___y_5717_, v___y_5718_, v___y_5719_, v___y_5720_, v___x_5761_, v___y_5722_);
v___y_5788_ = v___x_5799_;
goto v___jp_5787_;
}
}
}
else
{
lean_object* v___x_5800_; lean_object* v___x_5802_; 
lean_dec_ref_known(v___x_5761_, 14);
lean_dec(v_tactic_5741_);
lean_dec(v_ref_5740_);
lean_dec_ref(v___x_5716_);
v___x_5800_ = lean_box(0);
if (v_isShared_5739_ == 0)
{
lean_ctor_set_tag(v___x_5738_, 0);
lean_ctor_set(v___x_5738_, 0, v___x_5800_);
v___x_5802_ = v___x_5738_;
goto v_reusejp_5801_;
}
else
{
lean_object* v_reuseFailAlloc_5803_; 
v_reuseFailAlloc_5803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5803_, 0, v___x_5800_);
v___x_5802_ = v_reuseFailAlloc_5803_;
goto v_reusejp_5801_;
}
v_reusejp_5801_:
{
return v___x_5802_;
}
}
}
v___jp_5804_:
{
if (lean_obj_tag(v___y_5805_) == 0)
{
lean_dec_ref_known(v___y_5805_, 1);
goto v___jp_5789_;
}
else
{
lean_dec_ref_known(v___x_5761_, 14);
lean_dec(v_tactic_5741_);
lean_dec(v_ref_5740_);
lean_del_object(v___x_5738_);
lean_dec_ref(v___x_5716_);
return v___y_5805_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3___boxed(lean_object* v___x_5816_, lean_object* v___x_5817_, lean_object* v___y_5818_, lean_object* v___y_5819_, lean_object* v___y_5820_, lean_object* v___y_5821_, lean_object* v___y_5822_, lean_object* v___y_5823_, lean_object* v___y_5824_){
_start:
{
lean_object* v_res_5825_; 
v_res_5825_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3(v___x_5816_, v___x_5817_, v___y_5818_, v___y_5819_, v___y_5820_, v___y_5821_, v___y_5822_, v___y_5823_);
lean_dec(v___y_5823_);
lean_dec_ref(v___y_5822_);
lean_dec(v___y_5821_);
lean_dec_ref(v___y_5820_);
lean_dec(v___y_5819_);
lean_dec_ref(v___y_5818_);
return v_res_5825_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0(lean_object* v_x_5826_){
_start:
{
uint8_t v___x_5827_; 
v___x_5827_ = 0;
return v___x_5827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0___boxed(lean_object* v_x_5828_){
_start:
{
uint8_t v_res_5829_; lean_object* v_r_5830_; 
v_res_5829_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__0(v_x_5828_);
lean_dec(v_x_5828_);
v_r_5830_ = lean_box(v_res_5829_);
return v_r_5830_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6(lean_object* v_as_5837_, size_t v_sz_5838_, size_t v_i_5839_, lean_object* v_b_5840_, lean_object* v___y_5841_, lean_object* v___y_5842_, lean_object* v___y_5843_, lean_object* v___y_5844_){
_start:
{
uint8_t v___x_5846_; 
v___x_5846_ = lean_usize_dec_lt(v_i_5839_, v_sz_5838_);
if (v___x_5846_ == 0)
{
lean_object* v___x_5847_; 
v___x_5847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5847_, 0, v_b_5840_);
return v___x_5847_;
}
else
{
lean_object* v_snd_5848_; lean_object* v_fst_5849_; lean_object* v___x_5851_; uint8_t v_isShared_5852_; uint8_t v_isSharedCheck_5920_; 
v_snd_5848_ = lean_ctor_get(v_b_5840_, 1);
v_fst_5849_ = lean_ctor_get(v_b_5840_, 0);
v_isSharedCheck_5920_ = !lean_is_exclusive(v_b_5840_);
if (v_isSharedCheck_5920_ == 0)
{
v___x_5851_ = v_b_5840_;
v_isShared_5852_ = v_isSharedCheck_5920_;
goto v_resetjp_5850_;
}
else
{
lean_inc(v_snd_5848_);
lean_inc(v_fst_5849_);
lean_dec(v_b_5840_);
v___x_5851_ = lean_box(0);
v_isShared_5852_ = v_isSharedCheck_5920_;
goto v_resetjp_5850_;
}
v_resetjp_5850_:
{
lean_object* v_array_5853_; lean_object* v_start_5854_; lean_object* v_stop_5855_; uint8_t v___x_5856_; 
v_array_5853_ = lean_ctor_get(v_snd_5848_, 0);
v_start_5854_ = lean_ctor_get(v_snd_5848_, 1);
v_stop_5855_ = lean_ctor_get(v_snd_5848_, 2);
v___x_5856_ = lean_nat_dec_lt(v_start_5854_, v_stop_5855_);
if (v___x_5856_ == 0)
{
lean_object* v___x_5858_; 
if (v_isShared_5852_ == 0)
{
v___x_5858_ = v___x_5851_;
goto v_reusejp_5857_;
}
else
{
lean_object* v_reuseFailAlloc_5860_; 
v_reuseFailAlloc_5860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5860_, 0, v_fst_5849_);
lean_ctor_set(v_reuseFailAlloc_5860_, 1, v_snd_5848_);
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
lean_object* v___x_5862_; uint8_t v_isShared_5863_; uint8_t v_isSharedCheck_5916_; 
lean_inc(v_stop_5855_);
lean_inc(v_start_5854_);
lean_inc_ref(v_array_5853_);
v_isSharedCheck_5916_ = !lean_is_exclusive(v_snd_5848_);
if (v_isSharedCheck_5916_ == 0)
{
lean_object* v_unused_5917_; lean_object* v_unused_5918_; lean_object* v_unused_5919_; 
v_unused_5917_ = lean_ctor_get(v_snd_5848_, 2);
lean_dec(v_unused_5917_);
v_unused_5918_ = lean_ctor_get(v_snd_5848_, 1);
lean_dec(v_unused_5918_);
v_unused_5919_ = lean_ctor_get(v_snd_5848_, 0);
lean_dec(v_unused_5919_);
v___x_5862_ = v_snd_5848_;
v_isShared_5863_ = v_isSharedCheck_5916_;
goto v_resetjp_5861_;
}
else
{
lean_dec(v_snd_5848_);
v___x_5862_ = lean_box(0);
v_isShared_5863_ = v_isSharedCheck_5916_;
goto v_resetjp_5861_;
}
v_resetjp_5861_:
{
lean_object* v_array_5864_; lean_object* v_start_5865_; lean_object* v_stop_5866_; lean_object* v___x_5867_; lean_object* v___x_5868_; lean_object* v___x_5869_; lean_object* v___x_5871_; 
v_array_5864_ = lean_ctor_get(v_fst_5849_, 0);
v_start_5865_ = lean_ctor_get(v_fst_5849_, 1);
v_stop_5866_ = lean_ctor_get(v_fst_5849_, 2);
v___x_5867_ = lean_array_fget(v_array_5853_, v_start_5854_);
v___x_5868_ = lean_unsigned_to_nat(1u);
v___x_5869_ = lean_nat_add(v_start_5854_, v___x_5868_);
lean_dec(v_start_5854_);
if (v_isShared_5863_ == 0)
{
lean_ctor_set(v___x_5862_, 1, v___x_5869_);
v___x_5871_ = v___x_5862_;
goto v_reusejp_5870_;
}
else
{
lean_object* v_reuseFailAlloc_5915_; 
v_reuseFailAlloc_5915_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5915_, 0, v_array_5853_);
lean_ctor_set(v_reuseFailAlloc_5915_, 1, v___x_5869_);
lean_ctor_set(v_reuseFailAlloc_5915_, 2, v_stop_5855_);
v___x_5871_ = v_reuseFailAlloc_5915_;
goto v_reusejp_5870_;
}
v_reusejp_5870_:
{
uint8_t v___x_5872_; 
v___x_5872_ = lean_nat_dec_lt(v_start_5865_, v_stop_5866_);
if (v___x_5872_ == 0)
{
lean_object* v___x_5874_; 
lean_dec(v___x_5867_);
if (v_isShared_5852_ == 0)
{
lean_ctor_set(v___x_5851_, 1, v___x_5871_);
v___x_5874_ = v___x_5851_;
goto v_reusejp_5873_;
}
else
{
lean_object* v_reuseFailAlloc_5876_; 
v_reuseFailAlloc_5876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5876_, 0, v_fst_5849_);
lean_ctor_set(v_reuseFailAlloc_5876_, 1, v___x_5871_);
v___x_5874_ = v_reuseFailAlloc_5876_;
goto v_reusejp_5873_;
}
v_reusejp_5873_:
{
lean_object* v___x_5875_; 
v___x_5875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5875_, 0, v___x_5874_);
return v___x_5875_;
}
}
else
{
lean_object* v___x_5878_; uint8_t v_isShared_5879_; uint8_t v_isSharedCheck_5911_; 
lean_inc(v_stop_5866_);
lean_inc(v_start_5865_);
lean_inc_ref(v_array_5864_);
v_isSharedCheck_5911_ = !lean_is_exclusive(v_fst_5849_);
if (v_isSharedCheck_5911_ == 0)
{
lean_object* v_unused_5912_; lean_object* v_unused_5913_; lean_object* v_unused_5914_; 
v_unused_5912_ = lean_ctor_get(v_fst_5849_, 2);
lean_dec(v_unused_5912_);
v_unused_5913_ = lean_ctor_get(v_fst_5849_, 1);
lean_dec(v_unused_5913_);
v_unused_5914_ = lean_ctor_get(v_fst_5849_, 0);
lean_dec(v_unused_5914_);
v___x_5878_ = v_fst_5849_;
v_isShared_5879_ = v_isSharedCheck_5911_;
goto v_resetjp_5877_;
}
else
{
lean_dec(v_fst_5849_);
v___x_5878_ = lean_box(0);
v_isShared_5879_ = v_isSharedCheck_5911_;
goto v_resetjp_5877_;
}
v_resetjp_5877_:
{
lean_object* v___f_5880_; lean_object* v_a_5881_; lean_object* v___x_5882_; lean_object* v___y_5883_; lean_object* v___x_5884_; lean_object* v___x_5885_; lean_object* v___x_5886_; lean_object* v___x_5887_; uint8_t v___x_5888_; lean_object* v___x_5889_; lean_object* v___x_5890_; lean_object* v___x_5891_; lean_object* v___x_5892_; 
v___f_5880_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__0));
v_a_5881_ = lean_array_uget_borrowed(v_as_5837_, v_i_5839_);
v___x_5882_ = lean_array_fget_borrowed(v_array_5864_, v_start_5865_);
lean_inc(v___x_5882_);
v___y_5883_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___lam__3___boxed), 9, 2);
lean_closure_set(v___y_5883_, 0, v___x_5867_);
lean_closure_set(v___y_5883_, 1, v___x_5882_);
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
lean_ctor_set(v___x_5890_, 3, v___f_5880_);
lean_ctor_set(v___x_5890_, 4, v___x_5887_);
lean_ctor_set(v___x_5890_, 5, v___x_5887_);
lean_ctor_set(v___x_5890_, 6, v___x_5885_);
lean_ctor_set(v___x_5890_, 7, v___x_5889_);
lean_ctor_set_uint8(v___x_5890_, sizeof(void*)*8, v___x_5872_);
lean_ctor_set_uint8(v___x_5890_, sizeof(void*)*8 + 1, v___x_5872_);
lean_ctor_set_uint8(v___x_5890_, sizeof(void*)*8 + 2, v___x_5872_);
lean_ctor_set_uint8(v___x_5890_, sizeof(void*)*8 + 3, v___x_5872_);
lean_ctor_set_uint8(v___x_5890_, sizeof(void*)*8 + 4, v___x_5888_);
lean_ctor_set_uint8(v___x_5890_, sizeof(void*)*8 + 5, v___x_5888_);
lean_ctor_set_uint8(v___x_5890_, sizeof(void*)*8 + 6, v___x_5888_);
lean_ctor_set_uint8(v___x_5890_, sizeof(void*)*8 + 7, v___x_5888_);
lean_ctor_set_uint8(v___x_5890_, sizeof(void*)*8 + 8, v___x_5872_);
lean_ctor_set_uint8(v___x_5890_, sizeof(void*)*8 + 9, v___x_5888_);
lean_ctor_set_uint8(v___x_5890_, sizeof(void*)*8 + 10, v___x_5872_);
v___x_5891_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_WF_solveDecreasingGoals_spec__6___closed__2));
v___x_5892_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_5884_, v___x_5890_, v___x_5891_, v___y_5841_, v___y_5842_, v___y_5843_, v___y_5844_);
if (lean_obj_tag(v___x_5892_) == 0)
{
lean_object* v___x_5893_; lean_object* v___x_5895_; 
lean_dec_ref_known(v___x_5892_, 1);
v___x_5893_ = lean_nat_add(v_start_5865_, v___x_5868_);
lean_dec(v_start_5865_);
if (v_isShared_5879_ == 0)
{
lean_ctor_set(v___x_5878_, 1, v___x_5893_);
v___x_5895_ = v___x_5878_;
goto v_reusejp_5894_;
}
else
{
lean_object* v_reuseFailAlloc_5902_; 
v_reuseFailAlloc_5902_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5902_, 0, v_array_5864_);
lean_ctor_set(v_reuseFailAlloc_5902_, 1, v___x_5893_);
lean_ctor_set(v_reuseFailAlloc_5902_, 2, v_stop_5866_);
v___x_5895_ = v_reuseFailAlloc_5902_;
goto v_reusejp_5894_;
}
v_reusejp_5894_:
{
lean_object* v___x_5897_; 
if (v_isShared_5852_ == 0)
{
lean_ctor_set(v___x_5851_, 1, v___x_5871_);
lean_ctor_set(v___x_5851_, 0, v___x_5895_);
v___x_5897_ = v___x_5851_;
goto v_reusejp_5896_;
}
else
{
lean_object* v_reuseFailAlloc_5901_; 
v_reuseFailAlloc_5901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5901_, 0, v___x_5895_);
lean_ctor_set(v_reuseFailAlloc_5901_, 1, v___x_5871_);
v___x_5897_ = v_reuseFailAlloc_5901_;
goto v_reusejp_5896_;
}
v_reusejp_5896_:
{
size_t v___x_5898_; size_t v___x_5899_; 
v___x_5898_ = ((size_t)1ULL);
v___x_5899_ = lean_usize_add(v_i_5839_, v___x_5898_);
v_i_5839_ = v___x_5899_;
v_b_5840_ = v___x_5897_;
goto _start;
}
}
}
else
{
lean_object* v_a_5903_; lean_object* v___x_5905_; uint8_t v_isShared_5906_; uint8_t v_isSharedCheck_5910_; 
lean_del_object(v___x_5878_);
lean_dec_ref(v___x_5871_);
lean_dec(v_stop_5866_);
lean_dec(v_start_5865_);
lean_dec_ref(v_array_5864_);
lean_del_object(v___x_5851_);
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
v___x_6022_ = lean_st_ref_set(v___y_6000_, v___x_6021_);
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
v___x_6033_ = lean_st_ref_set(v___y_6003_, v___x_6032_);
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
lean_object* v___x_6065_; lean_object* v_env_6066_; uint8_t v_isExporting_6067_; lean_object* v___x_6133_; uint8_t v_isModule_6134_; 
v___x_6065_ = lean_st_ref_get(v___y_6063_);
v_env_6066_ = lean_ctor_get(v___x_6065_, 0);
lean_inc_ref(v_env_6066_);
lean_dec(v___x_6065_);
v_isExporting_6067_ = lean_ctor_get_uint8(v_env_6066_, sizeof(void*)*8);
v___x_6133_ = l_Lean_Environment_header(v_env_6066_);
lean_dec_ref(v_env_6066_);
v_isModule_6134_ = lean_ctor_get_uint8(v___x_6133_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_6133_);
if (v_isModule_6134_ == 0)
{
lean_object* v___x_6135_; 
lean_inc(v___y_6063_);
lean_inc_ref(v___y_6062_);
lean_inc(v___y_6061_);
lean_inc_ref(v___y_6060_);
v___x_6135_ = lean_apply_5(v_x_6058_, v___y_6060_, v___y_6061_, v___y_6062_, v___y_6063_, lean_box(0));
return v___x_6135_;
}
else
{
if (v_isExporting_6067_ == 0)
{
if (v_isExporting_6059_ == 0)
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
goto v___jp_6068_;
}
}
else
{
if (v_isExporting_6059_ == 0)
{
goto v___jp_6068_;
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
}
v___jp_6068_:
{
lean_object* v___x_6069_; lean_object* v_env_6070_; lean_object* v_nextMacroScope_6071_; lean_object* v_ngen_6072_; lean_object* v_auxDeclNGen_6073_; lean_object* v_traceState_6074_; lean_object* v_messages_6075_; lean_object* v_infoState_6076_; lean_object* v_snapshotTasks_6077_; lean_object* v___x_6079_; uint8_t v_isShared_6080_; uint8_t v_isSharedCheck_6131_; 
v___x_6069_ = lean_st_ref_take(v___y_6063_);
v_env_6070_ = lean_ctor_get(v___x_6069_, 0);
v_nextMacroScope_6071_ = lean_ctor_get(v___x_6069_, 1);
v_ngen_6072_ = lean_ctor_get(v___x_6069_, 2);
v_auxDeclNGen_6073_ = lean_ctor_get(v___x_6069_, 3);
v_traceState_6074_ = lean_ctor_get(v___x_6069_, 4);
v_messages_6075_ = lean_ctor_get(v___x_6069_, 6);
v_infoState_6076_ = lean_ctor_get(v___x_6069_, 7);
v_snapshotTasks_6077_ = lean_ctor_get(v___x_6069_, 8);
v_isSharedCheck_6131_ = !lean_is_exclusive(v___x_6069_);
if (v_isSharedCheck_6131_ == 0)
{
lean_object* v_unused_6132_; 
v_unused_6132_ = lean_ctor_get(v___x_6069_, 5);
lean_dec(v_unused_6132_);
v___x_6079_ = v___x_6069_;
v_isShared_6080_ = v_isSharedCheck_6131_;
goto v_resetjp_6078_;
}
else
{
lean_inc(v_snapshotTasks_6077_);
lean_inc(v_infoState_6076_);
lean_inc(v_messages_6075_);
lean_inc(v_traceState_6074_);
lean_inc(v_auxDeclNGen_6073_);
lean_inc(v_ngen_6072_);
lean_inc(v_nextMacroScope_6071_);
lean_inc(v_env_6070_);
lean_dec(v___x_6069_);
v___x_6079_ = lean_box(0);
v_isShared_6080_ = v_isSharedCheck_6131_;
goto v_resetjp_6078_;
}
v_resetjp_6078_:
{
lean_object* v___x_6081_; lean_object* v___x_6082_; lean_object* v___x_6084_; 
v___x_6081_ = l_Lean_Environment_setExporting(v_env_6070_, v_isExporting_6059_);
v___x_6082_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__2);
if (v_isShared_6080_ == 0)
{
lean_ctor_set(v___x_6079_, 5, v___x_6082_);
lean_ctor_set(v___x_6079_, 0, v___x_6081_);
v___x_6084_ = v___x_6079_;
goto v_reusejp_6083_;
}
else
{
lean_object* v_reuseFailAlloc_6130_; 
v_reuseFailAlloc_6130_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6130_, 0, v___x_6081_);
lean_ctor_set(v_reuseFailAlloc_6130_, 1, v_nextMacroScope_6071_);
lean_ctor_set(v_reuseFailAlloc_6130_, 2, v_ngen_6072_);
lean_ctor_set(v_reuseFailAlloc_6130_, 3, v_auxDeclNGen_6073_);
lean_ctor_set(v_reuseFailAlloc_6130_, 4, v_traceState_6074_);
lean_ctor_set(v_reuseFailAlloc_6130_, 5, v___x_6082_);
lean_ctor_set(v_reuseFailAlloc_6130_, 6, v_messages_6075_);
lean_ctor_set(v_reuseFailAlloc_6130_, 7, v_infoState_6076_);
lean_ctor_set(v_reuseFailAlloc_6130_, 8, v_snapshotTasks_6077_);
v___x_6084_ = v_reuseFailAlloc_6130_;
goto v_reusejp_6083_;
}
v_reusejp_6083_:
{
lean_object* v___x_6085_; lean_object* v___x_6086_; lean_object* v_mctx_6087_; lean_object* v_zetaDeltaFVarIds_6088_; lean_object* v_postponed_6089_; lean_object* v_diag_6090_; lean_object* v___x_6092_; uint8_t v_isShared_6093_; uint8_t v_isSharedCheck_6128_; 
v___x_6085_ = lean_st_ref_set(v___y_6063_, v___x_6084_);
v___x_6086_ = lean_st_ref_take(v___y_6061_);
v_mctx_6087_ = lean_ctor_get(v___x_6086_, 0);
v_zetaDeltaFVarIds_6088_ = lean_ctor_get(v___x_6086_, 2);
v_postponed_6089_ = lean_ctor_get(v___x_6086_, 3);
v_diag_6090_ = lean_ctor_get(v___x_6086_, 4);
v_isSharedCheck_6128_ = !lean_is_exclusive(v___x_6086_);
if (v_isSharedCheck_6128_ == 0)
{
lean_object* v_unused_6129_; 
v_unused_6129_ = lean_ctor_get(v___x_6086_, 1);
lean_dec(v_unused_6129_);
v___x_6092_ = v___x_6086_;
v_isShared_6093_ = v_isSharedCheck_6128_;
goto v_resetjp_6091_;
}
else
{
lean_inc(v_diag_6090_);
lean_inc(v_postponed_6089_);
lean_inc(v_zetaDeltaFVarIds_6088_);
lean_inc(v_mctx_6087_);
lean_dec(v___x_6086_);
v___x_6092_ = lean_box(0);
v_isShared_6093_ = v_isSharedCheck_6128_;
goto v_resetjp_6091_;
}
v_resetjp_6091_:
{
lean_object* v___x_6094_; lean_object* v___x_6096_; 
v___x_6094_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___closed__3);
if (v_isShared_6093_ == 0)
{
lean_ctor_set(v___x_6092_, 1, v___x_6094_);
v___x_6096_ = v___x_6092_;
goto v_reusejp_6095_;
}
else
{
lean_object* v_reuseFailAlloc_6127_; 
v_reuseFailAlloc_6127_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6127_, 0, v_mctx_6087_);
lean_ctor_set(v_reuseFailAlloc_6127_, 1, v___x_6094_);
lean_ctor_set(v_reuseFailAlloc_6127_, 2, v_zetaDeltaFVarIds_6088_);
lean_ctor_set(v_reuseFailAlloc_6127_, 3, v_postponed_6089_);
lean_ctor_set(v_reuseFailAlloc_6127_, 4, v_diag_6090_);
v___x_6096_ = v_reuseFailAlloc_6127_;
goto v_reusejp_6095_;
}
v_reusejp_6095_:
{
lean_object* v___x_6097_; lean_object* v_r_6098_; 
v___x_6097_ = lean_st_ref_set(v___y_6061_, v___x_6096_);
lean_inc(v___y_6063_);
lean_inc_ref(v___y_6062_);
lean_inc(v___y_6061_);
lean_inc_ref(v___y_6060_);
v_r_6098_ = lean_apply_5(v_x_6058_, v___y_6060_, v___y_6061_, v___y_6062_, v___y_6063_, lean_box(0));
if (lean_obj_tag(v_r_6098_) == 0)
{
lean_object* v_a_6099_; lean_object* v___x_6101_; uint8_t v_isShared_6102_; uint8_t v_isSharedCheck_6115_; 
v_a_6099_ = lean_ctor_get(v_r_6098_, 0);
v_isSharedCheck_6115_ = !lean_is_exclusive(v_r_6098_);
if (v_isSharedCheck_6115_ == 0)
{
v___x_6101_ = v_r_6098_;
v_isShared_6102_ = v_isSharedCheck_6115_;
goto v_resetjp_6100_;
}
else
{
lean_inc(v_a_6099_);
lean_dec(v_r_6098_);
v___x_6101_ = lean_box(0);
v_isShared_6102_ = v_isSharedCheck_6115_;
goto v_resetjp_6100_;
}
v_resetjp_6100_:
{
lean_object* v___x_6104_; 
lean_inc(v_a_6099_);
if (v_isShared_6102_ == 0)
{
lean_ctor_set_tag(v___x_6101_, 1);
v___x_6104_ = v___x_6101_;
goto v_reusejp_6103_;
}
else
{
lean_object* v_reuseFailAlloc_6114_; 
v_reuseFailAlloc_6114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6114_, 0, v_a_6099_);
v___x_6104_ = v_reuseFailAlloc_6114_;
goto v_reusejp_6103_;
}
v_reusejp_6103_:
{
lean_object* v___x_6105_; lean_object* v___x_6107_; uint8_t v_isShared_6108_; uint8_t v_isSharedCheck_6112_; 
v___x_6105_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6063_, v_isExporting_6067_, v___x_6082_, v___y_6061_, v___x_6094_, v___x_6104_);
lean_dec_ref(v___x_6104_);
v_isSharedCheck_6112_ = !lean_is_exclusive(v___x_6105_);
if (v_isSharedCheck_6112_ == 0)
{
lean_object* v_unused_6113_; 
v_unused_6113_ = lean_ctor_get(v___x_6105_, 0);
lean_dec(v_unused_6113_);
v___x_6107_ = v___x_6105_;
v_isShared_6108_ = v_isSharedCheck_6112_;
goto v_resetjp_6106_;
}
else
{
lean_dec(v___x_6105_);
v___x_6107_ = lean_box(0);
v_isShared_6108_ = v_isSharedCheck_6112_;
goto v_resetjp_6106_;
}
v_resetjp_6106_:
{
lean_object* v___x_6110_; 
if (v_isShared_6108_ == 0)
{
lean_ctor_set(v___x_6107_, 0, v_a_6099_);
v___x_6110_ = v___x_6107_;
goto v_reusejp_6109_;
}
else
{
lean_object* v_reuseFailAlloc_6111_; 
v_reuseFailAlloc_6111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6111_, 0, v_a_6099_);
v___x_6110_ = v_reuseFailAlloc_6111_;
goto v_reusejp_6109_;
}
v_reusejp_6109_:
{
return v___x_6110_;
}
}
}
}
}
else
{
lean_object* v_a_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; lean_object* v___x_6120_; uint8_t v_isShared_6121_; uint8_t v_isSharedCheck_6125_; 
v_a_6116_ = lean_ctor_get(v_r_6098_, 0);
lean_inc(v_a_6116_);
lean_dec_ref_known(v_r_6098_, 1);
v___x_6117_ = lean_box(0);
v___x_6118_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_WF_solveDecreasingGoals_spec__8_spec__10___redArg___lam__0(v___y_6063_, v_isExporting_6067_, v___x_6082_, v___y_6061_, v___x_6094_, v___x_6117_);
v_isSharedCheck_6125_ = !lean_is_exclusive(v___x_6118_);
if (v_isSharedCheck_6125_ == 0)
{
lean_object* v_unused_6126_; 
v_unused_6126_ = lean_ctor_get(v___x_6118_, 0);
lean_dec(v_unused_6126_);
v___x_6120_ = v___x_6118_;
v_isShared_6121_ = v_isSharedCheck_6125_;
goto v_resetjp_6119_;
}
else
{
lean_dec(v___x_6118_);
v___x_6120_ = lean_box(0);
v_isShared_6121_ = v_isSharedCheck_6125_;
goto v_resetjp_6119_;
}
v_resetjp_6119_:
{
lean_object* v___x_6123_; 
if (v_isShared_6121_ == 0)
{
lean_ctor_set_tag(v___x_6120_, 1);
lean_ctor_set(v___x_6120_, 0, v_a_6116_);
v___x_6123_ = v___x_6120_;
goto v_reusejp_6122_;
}
else
{
lean_object* v_reuseFailAlloc_6124_; 
v_reuseFailAlloc_6124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6124_, 0, v_a_6116_);
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
uint8_t v___x_5940__boxed_6801_; lean_object* v_res_6802_; 
v___x_5940__boxed_6801_ = lean_unbox(v___x_6791_);
v_res_6802_ = l_Lean_Elab_WF_mkFix___lam__2(v___x_6784_, v___x_6785_, v___x_6786_, v___f_6787_, v_funNames_6788_, v_argsPacker_6789_, v_decrTactics_6790_, v___x_5940__boxed_6801_, v_fst_6792_, v_prefixArgs_6793_, v___y_6794_, v___y_6795_, v___y_6796_, v___y_6797_, v___y_6798_, v___y_6799_);
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
uint8_t v___x_6010__boxed_6854_; lean_object* v_res_6855_; 
v___x_6010__boxed_6854_ = lean_unbox(v___x_6843_);
v_res_6855_ = l_Lean_Elab_WF_mkFix___lam__3(v___x_6834_, v_snd_6835_, v___x_6836_, v_prefixArgs_6837_, v_value_6838_, v___f_6839_, v_funNames_6840_, v_argsPacker_6841_, v_decrTactics_6842_, v___x_6010__boxed_6854_, v_fst_6844_, v_xs_6845_, v_x_6846_, v___y_6847_, v___y_6848_, v___y_6849_, v___y_6850_, v___y_6851_, v___y_6852_);
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Fix(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
